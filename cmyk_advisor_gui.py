#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
RM200 Color Advisor + полный набор инструментов rm200lib + палитры.

Вкладки:
  1. Измерения         — эталон/образец, сравнение по CMYK или палитре,
                         источник эталона: измерения / ручной CMYK / RGB.
  2. Палитры           — свои палитры с неограниченным числом цветов,
                         измерение через RM200, ручной ввод, JSON.
  3. Устройство        — Info, FW/BL, SN, ChipID, Battery, Mode, Time,
                         Aperture, Temperature, DeltaE.
  4. Файлы             — список, скачать, загрузить, удалить, dump.
  5. Fan Decks         — список, активация, удаление, добавление.
  6. Калибровка        — состояние, время до истечения, backup.
  7. Экран и клавиатура— скриншот LCD, эмуляция клавиш.
  8. Preview           — Live Preview, GetPreview, SavePreview.
  9. Консоль           — GenericCmd, UnlockExtendedCommands.

Запуск:
    python cmyk_advisor_gui.py
    python cmyk_advisor_gui.py --icc printer.icc --aperture 2
    python cmyk_advisor_gui.py --reconnect-after-measure
    python cmyk_advisor_gui.py --reboot-after-measure
"""

import argparse
import datetime as dt
import json
import math
import os
import struct
import sys
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog

import rm200lib as rm

try:
    from PIL import Image, ImageTk, ImageCms
    HAS_PIL = True
except ImportError:
    HAS_PIL = False


# ==========================================================================
#  ПАРАМЕТРЫ
# ==========================================================================

RECORD_SIZE     = 0x5158
HEADER_SIZE     = 0x0
VALID_ID        = 0x21B76F30

USB_RETRIES     = 5
USB_DELAY       = 2.0
POST_MEAS_PAUSE = 2.0
POLL_INTERVAL   = 1.0

MAX_AGE_SECONDS = 300

REBOOT_TIMEOUT  = 5.0
RECONNECT_MAX   = 15
RECONNECT_DELAY = 2.0

DEFAULT_UNLOCK_PASSWORD = '873gwe31xah1'

PALETTES_FILE = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), 'palettes.json'
)

PSEUDO_CMYK = 'CMYK (встроенная)'


# ==========================================================================
#  БЕЗОПАСНЫЕ ВЫЗОВЫ
# ==========================================================================

USB_ERROR_HINTS = (
    'usb', 'device', 'timeout', 'broken', 'pipe',
    'disconnected', 'reset', 'libusb', 'input/output',
)


def _is_usb_error(exc):
    msg = str(exc).lower()
    return any(h in msg for h in USB_ERROR_HINTS)


def safe_command(func, *args, retries=USB_RETRIES, delay=USB_DELAY, **kwargs):
    last_exc = None
    for attempt in range(1, retries + 1):
        try:
            return func(*args, **kwargs)
        except Exception as e:
            last_exc = e
            if not _is_usb_error(e):
                raise
            try:
                rm.Disconnect()
            except Exception:
                pass
            time.sleep(delay)
            try:
                rm.Connect()
            except Exception:
                time.sleep(delay)
    raise RuntimeError(f"Команда не выполнилась за {retries} попыток: {last_exc}")


def try_call(func, *args, **kwargs):
    if func is None:
        return False, RuntimeError("функция недоступна в rm200lib")
    try:
        return True, func(*args, **kwargs)
    except Exception as e:
        return False, e


def _call_with_timeout(func, timeout, *args, **kwargs):
    result = {'ok': False, 'exc': None}

    def target():
        try:
            func(*args, **kwargs)
            result['ok'] = True
        except Exception as e:
            result['exc'] = e

    t = threading.Thread(target=target, daemon=True)
    t.start()
    t.join(timeout)
    if t.is_alive():
        return False, TimeoutError("timeout")
    return result['ok'], result['exc']


# ==========================================================================
#  ПАРСЕР MeasDataV05.dat
# ==========================================================================

def _u16(b, o): return struct.unpack_from('<H', b, o)[0]
def _u32(b, o): return struct.unpack_from('<I', b, o)[0]
def _f32(b, o): return struct.unpack_from('<f', b, o)[0]


def _str_utf16(b, o, max_len):
    end = o
    lim = min(o + max_len, len(b))
    while end + 1 < lim:
        if b[end] == 0 and b[end + 1] == 0:
            break
        end += 2
    return b[o:end].decode('utf-16-le', errors='replace')


def _str_ascii(b, o, max_len):
    end = o
    lim = min(o + max_len, len(b))
    while end < lim and b[end] != 0:
        end += 1
    return b[o:end].decode('ascii', errors='replace')


def _datetime_valid(rec):
    try:
        year   = _u16(rec, 0x08)
        month  = rec[0x0A]
        day    = rec[0x0B]
        hour   = rec[0x0C]
        minute = rec[0x0D]
        second = rec[0x0E]
    except Exception:
        return False
    return (2000 <= year <= 2100 and 1 <= month <= 12 and 1 <= day <= 31
            and hour <= 23 and minute <= 59 and second <= 59)


def _parse_record(rec):
    return {
        'datetime':   (f"{_u16(rec, 0x08):04d}-"
                       f"{rec[0x0A]:02d}-{rec[0x0B]:02d} "
                       f"{rec[0x0C]:02d}:{rec[0x0D]:02d}:{rec[0x0E]:02d}"),
        'id':         _u32(rec, 0x0010),
        'counter':    _u32(rec, 0x0014),
        'name':       _str_utf16(rec, 0x00A4, 0x3C).strip(),
        'fandeck':    _str_ascii(rec, 0x00E0, 0x28).strip(),
        'sample_lab': (_f32(rec, 0x01DC),
                       _f32(rec, 0x01E0),
                       _f32(rec, 0x01E4)),
        'sample_xyz': (_f32(rec, 0x01E8),
                       _f32(rec, 0x01EC),
                       _f32(rec, 0x01F0)),
    }


def parse_measdata(data):
    n = len(data)
    if n < RECORD_SIZE:
        return []
    records = []
    pos = HEADER_SIZE
    while pos + RECORD_SIZE <= n:
        rec = data[pos:pos + RECORD_SIZE]
        if _datetime_valid(rec):
            try:
                r = _parse_record(rec)
                r['offset'] = pos
                records.append(r)
            except struct.error:
                pass
        pos += RECORD_SIZE
    return records


def newest_record(records):
    if not records:
        return None
    return sorted(records, key=lambda r: (r['datetime'], r['counter']))[-1]


def record_age_seconds(rec):
    try:
        t = dt.datetime.strptime(rec['datetime'], "%Y-%m-%d %H:%M:%S")
        return (dt.datetime.now() - t).total_seconds()
    except Exception:
        return None


def format_age(sec):
    if sec is None:
        return "?"
    if sec < 60:
        return f"{int(sec)} сек назад"
    if sec < 3600:
        return f"{int(sec / 60)} мин назад"
    return f"{sec / 3600:.1f} ч назад"


# ==========================================================================
#  ЦВЕТОВЫЕ ПРЕОБРАЗОВАНИЯ
# ==========================================================================

def lab_to_rgb(L, a, b):
    fy = (L + 16) / 116
    fx = a / 500 + fy
    fz = fy - b / 200

    def f_inv(t):
        return t ** 3 if t > 6 / 29 else 3 * (6 / 29) ** 2 * (t - 4 / 29)

    X = 0.95047 * f_inv(fx)
    Y = 1.00000 * f_inv(fy)
    Z = 1.08883 * f_inv(fz)

    r  =  3.2406 * X - 1.5372 * Y - 0.4986 * Z
    g  = -0.9689 * X + 1.8758 * Y + 0.0415 * Z
    b_ =  0.0557 * X - 0.2040 * Y + 1.0570 * Z

    def gamma(c):
        c = max(0.0, min(1.0, c))
        return 12.92 * c if c <= 0.0031308 else 1.055 * c ** (1 / 2.4) - 0.055

    return (int(round(gamma(r)  * 255)),
            int(round(gamma(g)  * 255)),
            int(round(gamma(b_) * 255)))


def srgb_to_lab(r, g, b):
    """sRGB 0..255 -> CIE Lab (D65)."""
    def srgb_to_linear(c):
        c = c / 255.0
        return c / 12.92 if c <= 0.04045 else ((c + 0.055) / 1.055) ** 2.4

    rl = srgb_to_linear(r)
    gl = srgb_to_linear(g)
    bl = srgb_to_linear(b)

    X = rl * 0.4124 + gl * 0.3576 + bl * 0.1805
    Y = rl * 0.2126 + gl * 0.7152 + bl * 0.0722
    Z = rl * 0.0193 + gl * 0.1192 + bl * 0.9505

    Xn, Yn, Zn = 0.95047, 1.00000, 1.08883

    def f(t):
        return t ** (1 / 3) if t > (6 / 29) ** 3 else t / (3 * (6 / 29) ** 2) + 4 / 29

    fx = f(X / Xn)
    fy = f(Y / Yn)
    fz = f(Z / Zn)

    L = 116 * fy - 16
    a = 500 * (fx - fy)
    b_ = 200 * (fy - fz)
    return (L, a, b_)


def cmyk_to_lab(c, m, y, k):
    """
    Наивное CMYK -> Lab: без ICC-профиля принтера это только приближение.
    Значения c,m,y,k в 0..100.
    """
    c = c / 100.0
    m = m / 100.0
    y = y / 100.0
    k = k / 100.0
    r = 255.0 * (1 - c) * (1 - k)
    g = 255.0 * (1 - m) * (1 - k)
    b = 255.0 * (1 - y) * (1 - k)
    return srgb_to_lab(r, g, b)


def lab_to_cmyk_heuristic(L, a, b):
    C = 50.0 - 0.5 * a - 0.3 * b
    M = 50.0 + 0.6 * a
    Y = 50.0 + 0.6 * b
    K = max(0.0, 100.0 - L)
    return (C, M, Y, K)


def lab_to_cmyk_icc(L, a, b, icc_path):
    if not HAS_PIL:
        raise RuntimeError("Pillow не установлен")
    Lp = int(round(max(0, min(100, L)) * 255 / 100))
    ap = int(round(max(0, min(255, a + 128))))
    bp = int(round(max(0, min(255, b + 128))))
    img = Image.new("LAB", (1, 1), (Lp, ap, bp))
    lab_p  = ImageCms.createProfile("LAB")
    cmyk_p = ImageCms.getOpenProfile(icc_path)
    tr = ImageCms.buildTransform(lab_p, cmyk_p, "LAB", "CMYK",
                                 renderingIntent=ImageCms.Intent.PERCEPTUAL)
    c, m, y, k = ImageCms.applyTransform(img, tr).getpixel((0, 0))
    return (c / 2.55, m / 2.55, y / 2.55, k / 2.55)


# ==========================================================================
#  СРАВНЕНИЕ: CMYK и палитра
# ==========================================================================

def format_correction(dc, dm, dy, dk, thr=1.0):
    parts = []

    def add(name, val):
        if abs(val) < thr:
            parts.append(f"{name} не меняем")
        elif val > 0:
            parts.append(f"на {abs(val):.0f}% больше {name}")
        else:
            parts.append(f"на {abs(val):.0f}% меньше {name}")

    add("Cyan", dc)
    add("Magenta", dm)
    add("Yellow", dy)
    add("Black", dk)
    return "Коррекция: " + ", ".join(parts) + "."


def format_result_cmyk(ref_lab, sample_lab, icc_path=None, threshold=1.0):
    Lr, ar, br = ref_lab
    Ls, as_, bs = sample_lab
    dL, da, db = Lr - Ls, ar - as_, br - bs
    dE = (dL ** 2 + da ** 2 + db ** 2) ** 0.5

    lines = []
    lines.append(f"Эталон:   L*={Lr:8.3f}  a*={ar:8.3f}  b*={br:8.3f}")
    lines.append(f"Образец:  L*={Ls:8.3f}  a*={as_:8.3f}  b*={bs:8.3f}")
    lines.append(f"ΔL*={dL:+.3f}  Δa*={da:+.3f}  Δb*={db:+.3f}  ΔE76={dE:.3f}")
    lines.append("")

    if icc_path:
        try:
            Cr, Mr, Yr, Kr = lab_to_cmyk_icc(Lr, ar, br, icc_path)
            Cs, Ms, Ys, Ks = lab_to_cmyk_icc(Ls, as_, bs, icc_path)
            lines.append("Расчёт по ICC-профилю.")
        except Exception as e:
            lines.append(f"ICC ошибка: {e}. Переход на эвристику.")
            Cr, Mr, Yr, Kr = lab_to_cmyk_heuristic(Lr, ar, br)
            Cs, Ms, Ys, Ks = lab_to_cmyk_heuristic(Ls, as_, bs)
    else:
        Cr, Mr, Yr, Kr = lab_to_cmyk_heuristic(Lr, ar, br)
        Cs, Ms, Ys, Ks = lab_to_cmyk_heuristic(Ls, as_, bs)
        lines.append("Расчёт по эвристике (ICC не указан).")

    dc, dm, dy, dk = Cr - Cs, Mr - Ms, Yr - Ys, Kr - Ks

    lines.append(f"Эталон CMYK:  C={Cr:6.2f} M={Mr:6.2f} Y={Yr:6.2f} K={Kr:6.2f}")
    lines.append(f"Образец CMYK: C={Cs:6.2f} M={Ms:6.2f} Y={Ys:6.2f} K={Ks:6.2f}")
    lines.append(f"ΔCMYK:       ΔC={dc:+6.2f} ΔM={dm:+6.2f} ΔY={dy:+6.2f} ΔK={dk:+6.2f}")
    lines.append("")
    lines.append(format_correction(dc, dm, dy, dk, threshold))
    return "\n".join(lines)


def propose_palette_mix(target_lab, entries, n_max):
    """
    Возвращает список (entry, percent) — предложение по смешиванию
    N ближайших цветов палитры, чтобы приблизиться к target_lab.
    """
    if not entries:
        return []

    dists = []
    for e in entries:
        L, a, b = e['lab']
        d = math.sqrt((L - target_lab[0]) ** 2 +
                      (a - target_lab[1]) ** 2 +
                      (b - target_lab[2]) ** 2)
        dists.append((d, e))
    dists.sort(key=lambda x: x[0])

    top = dists[:max(1, n_max)]
    if len(top) == 1:
        return [(top[0][1], 100.0)]

    eps = 0.5
    weights = [1.0 / ((d + eps) ** 2) for d, _ in top]
    total = sum(weights)
    probs = [w / total * 100.0 for w in weights]

    # отбрасываем доли меньше 0.1%, перераспределяем
    probs = [p if p >= 0.1 else 0.0 for p in probs]
    s = sum(probs)
    if s <= 0:
        probs = [100.0 / len(top)] * len(top)
    else:
        probs = [p / s * 100.0 for p in probs]

    result = []
    for (d, e), p in zip(top, probs):
        if p > 0:
            result.append((e, p))
    return result


def format_result_palette(ref_lab, sample_lab, palette_name, mix):
    Lr, ar, br = ref_lab
    Ls, as_, bs = sample_lab
    dE = math.sqrt((Lr - Ls) ** 2 + (ar - as_) ** 2 + (br - bs) ** 2)

    lines = []
    lines.append(f"Палитра:  {palette_name}")
    lines.append(f"Эталон:   L*={Lr:8.3f}  a*={ar:8.3f}  b*={br:8.3f}")
    lines.append(f"Образец:  L*={Ls:8.3f}  a*={as_:8.3f}  b*={bs:8.3f}  "
                 f"ΔE(эт-обр)={dE:.3f}")
    lines.append("")

    if not mix:
        lines.append("Не удалось подобрать смесь (нет данных).")
        return "\n".join(lines)

    # проверим, насколько микс близок к эталону
    Lm = sum(e['lab'][0] * p / 100.0 for e, p in mix)
    am = sum(e['lab'][1] * p / 100.0 for e, p in mix)
    bm = sum(e['lab'][2] * p / 100.0 for e, p in mix)
    dEm = math.sqrt((Lr - Lm) ** 2 + (ar - am) ** 2 + (br - bm) ** 2)

    lines.append(f"Предлагаемая смесь (для достижения эталона):")
    for e, p in mix:
        L, a, b = e['lab']
        lines.append(f"  {p:6.2f}%  {e['name']:24}  "
                     f"(L={L:7.3f} a={a:7.3f} b={b:7.3f})")
    lines.append("")
    lines.append(f"Итоговый цвет смеси: L*={Lm:.3f} a*={am:.3f} b*={bm:.3f}")
    lines.append(f"ΔE смесь ↔ эталон: {dEm:.3f}")
    return "\n".join(lines)


# ==========================================================================
#  ГЛАВНОЕ ОКНО
# ==========================================================================

class AdvisorApp(tk.Tk):

    def __init__(self, aperture=2, icc=None, timeout=180.0, threshold=1.0,
                 reboot_after=False, reconnect_after=False):
        super().__init__()
        self.title("RM200 Color Advisor")
        self.geometry("1220x920")
        self.minsize(1000, 720)

        self.aperture        = aperture
        self.icc             = icc
        self.timeout         = timeout
        self.threshold       = threshold
        self.reboot_after    = reboot_after
        self.reconnect_after = reconnect_after

        self.connected = False
        self.busy      = False

        self.device_info = {'fw': None, 'sn': None, 'count': None,
                            'dev_time': None}

        self.state_data = {
            'ref': {'title': 'ЭТАЛОН',  'measurements': []},
            'smp': {'title': 'ОБРАЗЕЦ', 'measurements': []},
        }
        self.widgets = {'ref': {}, 'smp': {}}

        # Палитры:  name -> {'entries': [{'name': str, 'lab': (L,a,b)}, ...]}
        self.palettes = {}
        self._load_palettes()

        # Live preview
        self.preview_running = False
        self.preview_after_id = None

        self._build_menu()
        self._build_ui()
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.after(100, self._connect_async)

    # ----------------------------------------------------------------- Палитры (load/save)

    def _load_palettes(self):
        self.palettes = {}
        if os.path.exists(PALETTES_FILE):
            try:
                with open(PALETTES_FILE, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                for p in data.get('palettes', []):
                    name = p.get('name', 'Unnamed')
                    ents = []
                    for e in p.get('entries', []):
                        lab = e.get('lab', [0, 0, 0])
                        ents.append({
                            'name': e.get('name', 'Color'),
                            'lab': (float(lab[0]), float(lab[1]), float(lab[2])),
                        })
                    self.palettes[name] = {'entries': ents}
            except Exception as e:
                print(f"[PALETTES] load error: {e}")

    def _save_palettes(self):
        try:
            data = {'palettes': [
                {
                    'name': n,
                    'entries': [
                        {'name': e['name'], 'lab': list(e['lab'])}
                        for e in p['entries']
                    ],
                }
                for n, p in self.palettes.items()
            ]}
            with open(PALETTES_FILE, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
        except Exception as e:
            print(f"[PALETTES] save error: {e}")

    def _palette_names_for_compare(self):
        return [PSEUDO_CMYK] + list(self.palettes.keys())

    # ----------------------------------------------------------------- Меню

    def _build_menu(self):
        menubar = tk.Menu(self)

        m_file = tk.Menu(menubar, tearoff=0)
        m_file.add_command(label="Сохранить дамп MeasDataV05.dat...",
                           command=self._menu_save_dump)
        m_file.add_separator()
        m_file.add_command(label="Экспорт палитр (JSON)...",
                           command=self._on_palette_export_all)
        m_file.add_command(label="Импорт палитр (JSON)...",
                           command=self._on_palette_import_all)
        m_file.add_separator()
        m_file.add_command(label="Выход", command=self._on_close)
        menubar.add_cascade(label="Файл", menu=m_file)

        m_dev = tk.Menu(menubar, tearoff=0)
        m_dev.add_command(label="Подключиться", command=self._connect_async)
        m_dev.add_command(label="Переподключиться", command=self._menu_reconnect)
        m_dev.add_command(label="Перезагрузить (Reboot)", command=self._menu_reboot)
        m_dev.add_separator()
        m_dev.add_command(label="Информация об устройстве",
                          command=lambda: self._notebook.select(2))
        menubar.add_cascade(label="Устройство", menu=m_dev)

        m_tools = tk.Menu(menubar, tearoff=0)
        m_tools.add_command(label="Сделать скриншот LCD...",
                            command=self._menu_screenshot)
        m_tools.add_command(label="Прочитать температуру",
                            command=self._menu_temperature)
        m_tools.add_command(label="Live Preview",
                            command=lambda: self._notebook.select(7))
        menubar.add_cascade(label="Инструменты", menu=m_tools)

        m_help = tk.Menu(menubar, tearoff=0)
        m_help.add_command(label="О программе", command=self._menu_about)
        menubar.add_cascade(label="Помощь", menu=m_help)

        self.config(menu=menubar)

    # ------------------------------------------------------------------ UI

    def _build_ui(self):
        self._build_status_bar()

        self._notebook = ttk.Notebook(self)
        self._notebook.pack(fill=tk.BOTH, expand=True, padx=6, pady=(6, 0))

        self._tab_measurement(self._notebook)   # 0
        self._tab_palettes(self._notebook)      # 1
        self._tab_device(self._notebook)        # 2
        self._tab_files(self._notebook)         # 3
        self._tab_fandecks(self._notebook)      # 4
        self._tab_calibration(self._notebook)   # 5
        self._tab_screen_keys(self._notebook)   # 6
        self._tab_preview(self._notebook)       # 7
        self._tab_console(self._notebook)       # 8

    def _build_status_bar(self):
        self.status_var = tk.StringVar(value="Инициализация...")
        status_bar = ttk.Label(self, textvariable=self.status_var,
                               relief=tk.SUNKEN, anchor=tk.W, padding=(6, 3))
        status_bar.pack(fill=tk.X, side=tk.BOTTOM)

    def _set_status(self, text):
        self.status_var.set(text)

    def _set_busy(self, busy, text=None):
        self.busy = busy
        state = tk.DISABLED if busy else tk.NORMAL
        for side in ('ref', 'smp'):
            try:
                self.widgets[side]['measure_btn'].config(state=state)
            except Exception:
                pass
        if text:
            self._set_status(text)

    def _update_status_bar(self, extra=None):
        parts = []
        parts.append("Подключено." if self.connected else "Нет подключения.")
        if self.device_info.get('fw'):
            parts.append(f"FW: {self.device_info['fw']}")
        if self.device_info.get('sn'):
            parts.append(f"SN: {self.device_info['sn']}")
        if self.device_info.get('count') is not None:
            parts.append(f"Записей: {self.device_info['count']}")
        if self.device_info.get('dev_time'):
            parts.append(f"Время RM200: {self.device_info['dev_time']}")
        if extra:
            parts.append(extra)
        self._set_status("  ".join(parts))

    # ======================================================================
    #  ВКЛАДКА 1. ИЗМЕРЕНИЯ
    # ======================================================================

    def _tab_measurement(self, nb):
        frame = ttk.Frame(nb, padding=8)
        nb.add(frame, text="Измерения")

        top = ttk.Frame(frame)
        top.pack(fill=tk.BOTH, expand=True)

        self._build_panel(top, 'ref').pack(side=tk.LEFT, fill=tk.BOTH,
                                           expand=True, padx=(0, 5))
        self._build_panel(top, 'smp').pack(side=tk.LEFT, fill=tk.BOTH,
                                           expand=True, padx=(5, 0))

        # ---- Режим сравнения ----
        cmp_frame = ttk.LabelFrame(frame, text="Режим сравнения")
        cmp_frame.pack(fill=tk.X, pady=(10, 0))

        row1 = ttk.Frame(cmp_frame)
        row1.pack(fill=tk.X, padx=4, pady=4)

        ttk.Label(row1, text="Палитра:").pack(side=tk.LEFT, padx=4)
        self.compare_palette_var = tk.StringVar(value=PSEUDO_CMYK)
        self.compare_palette_combo = ttk.Combobox(
            row1, textvariable=self.compare_palette_var,
            values=self._palette_names_for_compare(),
            width=28, state='readonly')
        self.compare_palette_combo.pack(side=tk.LEFT, padx=4)
        self.compare_palette_combo.bind(
            '<<ComboboxSelected>>', lambda e: self._on_palette_changed())

        ttk.Label(row1, text="N смешиваемых цветов:").pack(side=tk.LEFT, padx=(16, 4))
        self.n_mix_var = tk.StringVar(value="3")
        self.n_mix_spin = ttk.Spinbox(row1, from_=1, to=20, width=5,
                                      textvariable=self.n_mix_var)
        self.n_mix_spin.pack(side=tk.LEFT, padx=4)

        # ---- Источник эталона ----
        row2 = ttk.Frame(cmp_frame)
        row2.pack(fill=tk.X, padx=4, pady=4)

        ttk.Label(row2, text="Эталон:").pack(side=tk.LEFT, padx=4)
        self.ref_source_var = tk.StringVar(value='measure')
        ttk.Radiobutton(row2, text="Из измерений", value='measure',
                        variable=self.ref_source_var,
                        command=self._on_ref_source_changed).pack(side=tk.LEFT, padx=4)
        ttk.Radiobutton(row2, text="Ручной CMYK", value='cmyk',
                        variable=self.ref_source_var,
                        command=self._on_ref_source_changed).pack(side=tk.LEFT, padx=4)
        ttk.Radiobutton(row2, text="Ручной RGB", value='rgb',
                        variable=self.ref_source_var,
                        command=self._on_ref_source_changed).pack(side=tk.LEFT, padx=4)

        # ---- Поля ручного CMYK ----
        self.manual_cmyk_frame = ttk.Frame(cmp_frame)
        self.manual_cmyk_frame.pack(fill=tk.X, padx=4, pady=2)
        self.man_c_var = tk.StringVar(value="0")
        self.man_m_var = tk.StringVar(value="0")
        self.man_y_var = tk.StringVar(value="0")
        self.man_k_var = tk.StringVar(value="0")
        for label, var in (("C %", self.man_c_var), ("M %", self.man_m_var),
                           ("Y %", self.man_y_var), ("K %", self.man_k_var)):
            ttk.Label(self.manual_cmyk_frame, text=label).pack(side=tk.LEFT, padx=(4, 0))
            ttk.Entry(self.manual_cmyk_frame, textvariable=var, width=7).pack(
                side=tk.LEFT, padx=2)

        # ---- Поля ручного RGB ----
        self.manual_rgb_frame = ttk.Frame(cmp_frame)
        self.manual_rgb_frame.pack(fill=tk.X, padx=4, pady=2)
        self.man_r_var = tk.StringVar(value="128")
        self.man_g_var = tk.StringVar(value="128")
        self.man_b_var = tk.StringVar(value="128")
        for label, var in (("R", self.man_r_var), ("G", self.man_g_var),
                           ("B", self.man_b_var)):
            ttk.Label(self.manual_rgb_frame, text=label).pack(side=tk.LEFT, padx=(4, 0))
            ttk.Entry(self.manual_rgb_frame, textvariable=var, width=5).pack(
                side=tk.LEFT, padx=2)

        # ---- Кнопки ----
        actions = ttk.Frame(frame)
        actions.pack(fill=tk.X, pady=(8, 0))

        ttk.Button(actions, text="Рассчитать",
                   command=self._on_calculate).pack(side=tk.LEFT)
        ttk.Button(actions, text="Импорт после power-cycle (обе стороны)",
                   command=self._on_import_both).pack(side=tk.LEFT, padx=5)
        ttk.Button(actions, text="Переподключить RM200",
                   command=self._connect_async).pack(side=tk.LEFT, padx=5)

        res_frame = ttk.LabelFrame(frame, text="Результат")
        res_frame.pack(fill=tk.BOTH, expand=False, pady=(8, 0))
        self.result_text = tk.Text(res_frame, height=12, wrap=tk.NONE,
                                   font=("Consolas", 10))
        self.result_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        self._on_ref_source_changed()
        self._on_palette_changed()

    def _on_ref_source_changed(self):
        src = self.ref_source_var.get()
        # Скрываем всё
        self.manual_cmyk_frame.pack_forget()
        self.manual_rgb_frame.pack_forget()
        if src == 'cmyk':
            self.manual_cmyk_frame.pack(fill=tk.X, padx=4, pady=2)
        elif src == 'rgb':
            self.manual_rgb_frame.pack(fill=tk.X, padx=4, pady=2)

    def _on_palette_changed(self):
        pal = self.compare_palette_var.get()
        if pal == PSEUDO_CMYK:
            self.n_mix_spin.config(state=tk.DISABLED)
        else:
            self.n_mix_spin.config(state=tk.NORMAL)

    def _build_panel(self, parent, side):
        data = self.state_data[side]
        w = self.widgets[side]

        frame = ttk.LabelFrame(parent, text=data['title'], padding=10)

        w['swatch'] = tk.Canvas(frame, width=300, height=120, bg='white',
                                highlightthickness=1,
                                highlightbackground='#888')
        w['swatch'].pack()
        w['swatch'].create_text(150, 60, text="нет данных", fill="#888")

        w['lab_var'] = tk.StringVar(value="—")
        ttk.Label(frame, textvariable=w['lab_var'],
                  font=("Consolas", 11)).pack(pady=(6, 2))

        list_frame = ttk.LabelFrame(frame, text="Измерения", padding=4)
        list_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        w['listbox'] = tk.Text(list_frame, height=8, width=40,
                               font=("Consolas", 9), state=tk.DISABLED)
        w['listbox'].pack(fill=tk.BOTH, expand=True)

        btns = ttk.Frame(frame)
        btns.pack(fill=tk.X, pady=(5, 0))
        w['measure_btn'] = ttk.Button(btns, text="Измерить",
                                      command=lambda: self._on_measure(side))
        w['measure_btn'].pack(side=tk.LEFT, padx=(0, 3))
        ttk.Button(btns, text="Импорт",
                   command=lambda: self._on_import_latest(side)).pack(side=tk.LEFT, padx=3)
        ttk.Button(btns, text="Очистить",
                   command=lambda: self._on_clear(side)).pack(side=tk.LEFT, padx=3)

        return frame

    # ======================================================================
    #  ВКЛАДКА 2. ПАЛИТРЫ
    # ======================================================================

    def _tab_palettes(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="Палитры")

        # --- Верхняя панель: выбор палитры + операции ---
        top = ttk.Frame(frame)
        top.pack(fill=tk.X, pady=(0, 6))

        ttk.Label(top, text="Палитра:").pack(side=tk.LEFT, padx=4)
        self.palettes_tab_selector_var = tk.StringVar()
        self.palettes_tab_selector = ttk.Combobox(
            top, textvariable=self.palettes_tab_selector_var,
            values=list(self.palettes.keys()), width=30, state='readonly')
        self.palettes_tab_selector.pack(side=tk.LEFT, padx=4)
        self.palettes_tab_selector.bind(
            '<<ComboboxSelected>>', lambda e: self._refresh_palette_entries())

        ttk.Button(top, text="Добавить палитру",
                   command=self._on_palette_add).pack(side=tk.LEFT, padx=4)
        ttk.Button(top, text="Переименовать",
                   command=self._on_palette_rename).pack(side=tk.LEFT, padx=4)
        ttk.Button(top, text="Удалить",
                   command=self._on_palette_delete).pack(side=tk.LEFT, padx=4)

        # --- Список цветов (Treeview) ---
        tree_frame = ttk.Frame(frame)
        tree_frame.pack(fill=tk.BOTH, expand=True)

        columns = ('name', 'L', 'a', 'b')
        self.palette_tree = ttk.Treeview(tree_frame, columns=columns,
                                         show='headings', selectmode='extended')
        self.palette_tree.heading('name', text='Название')
        self.palette_tree.heading('L', text='L*')
        self.palette_tree.heading('a', text='a*')
        self.palette_tree.heading('b', text='b*')
        self.palette_tree.column('name', width=260, anchor='w')
        self.palette_tree.column('L', width=90, anchor='e')
        self.palette_tree.column('a', width=90, anchor='e')
        self.palette_tree.column('b', width=90, anchor='e')

        scrollbar = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL,
                                  command=self.palette_tree.yview)
        self.palette_tree.configure(yscrollcommand=scrollbar.set)
        self.palette_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # --- Нижняя панель: операции с цветами ---
        bottom = ttk.Frame(frame)
        bottom.pack(fill=tk.X, pady=(6, 0))

        ttk.Button(bottom, text="Измерить новый цвет",
                   command=self._on_palette_measure).pack(side=tk.LEFT, padx=3)
        ttk.Button(bottom, text="Ручной ввод",
                   command=self._on_palette_manual).pack(side=tk.LEFT, padx=3)
        ttk.Button(bottom, text="Переименовать цвет",
                   command=self._on_palette_entry_rename).pack(side=tk.LEFT, padx=3)
        ttk.Button(bottom, text="Удалить цвет",
                   command=self._on_palette_entry_delete).pack(side=tk.LEFT, padx=3)
        ttk.Button(bottom, text="Дублировать цвет",
                   command=self._on_palette_entry_dup).pack(side=tk.LEFT, padx=3)

        self.palettes_status = tk.StringVar(value="")
        ttk.Label(frame, textvariable=self.palettes_status,
                  padding=(0, 6, 0, 0), foreground="#555").pack(anchor=tk.W)

        # Инициализация
        if self.palettes:
            first = list(self.palettes.keys())[0]
            self.palettes_tab_selector_var.set(first)
        self._refresh_palette_entries()

    def _refresh_palette_list(self):
        # обновляем оба комбобокса
        try:
            self.palettes_tab_selector['values'] = list(self.palettes.keys())
        except Exception:
            pass
        try:
            self.compare_palette_combo['values'] = self._palette_names_for_compare()
        except Exception:
            pass

    def _current_palette_name(self):
        return self.palettes_tab_selector_var.get()

    def _current_palette(self):
        n = self._current_palette_name()
        return self.palettes.get(n)

    def _refresh_palette_entries(self):
        for item in self.palette_tree.get_children():
            self.palette_tree.delete(item)

        p = self._current_palette()
        if not p:
            self.palettes_status.set("Палитра не выбрана.")
            return

        for i, e in enumerate(p['entries']):
            L, a, b = e['lab']
            self.palette_tree.insert('', 'end', iid=str(i),
                                     values=(e['name'],
                                             f"{L:.3f}", f"{a:.3f}", f"{b:.3f}"))
        self.palettes_status.set(f"Цветов в палитре: {len(p['entries'])}")

    def _selected_palette_indices(self):
        sel = self.palette_tree.selection()
        return [int(i) for i in sel]

    # --- операции с палитрами ---

    def _on_palette_add(self):
        name = simpledialog.askstring("Новая палитра",
                                      "Название палитры:",
                                      parent=self)
        if not name:
            return
        name = name.strip()
        if not name:
            return
        if name in self.palettes:
            messagebox.showwarning("Палитры", "Палитра с таким именем уже есть.")
            return
        self.palettes[name] = {'entries': []}
        self._save_palettes()
        self._refresh_palette_list()
        self.palettes_tab_selector_var.set(name)
        self._refresh_palette_entries()

    def _on_palette_rename(self):
        old = self._current_palette_name()
        if old not in self.palettes:
            return
        new = simpledialog.askstring("Переименовать палитру",
                                     "Новое имя:",
                                     initialvalue=old, parent=self)
        if not new:
            return
        new = new.strip()
        if not new or new == old:
            return
        if new in self.palettes:
            messagebox.showwarning("Палитры", "Палитра с таким именем уже есть.")
            return
        # сохраняем порядок
        items = list(self.palettes.items())
        self.palettes = {}
        for k, v in items:
            self.palettes[new if k == old else k] = v
        self._save_palettes()
        self._refresh_palette_list()
        self.palettes_tab_selector_var.set(new)
        self._refresh_palette_entries()

    def _on_palette_delete(self):
        name = self._current_palette_name()
        if name not in self.palettes:
            return
        if not messagebox.askyesno("Удалить палитру",
                                   f"Удалить палитру '{name}' "
                                   f"({len(self.palettes[name]['entries'])} цветов)?"):
            return
        del self.palettes[name]
        self._save_palettes()
        self._refresh_palette_list()
        if self.palettes:
            self.palettes_tab_selector_var.set(list(self.palettes.keys())[0])
        else:
            self.palettes_tab_selector_var.set('')
        self._refresh_palette_entries()

    # --- операции с цветами палитры ---

    def _auto_entry_name(self, p):
        used = {e['name'] for e in p['entries']}
        i = 1
        while True:
            n = f"Color {i}"
            if n not in used:
                return n
            i += 1

    def _add_entry_to_current_palette(self, lab, name=None):
        p = self._current_palette()
        if not p:
            messagebox.showwarning("Палитры",
                                   "Сначала создайте или выберите палитру.")
            return
        if name is None:
            name = self._auto_entry_name(p)
        p['entries'].append({'name': name, 'lab': tuple(lab)})
        self._save_palettes()
        self._refresh_palette_entries()

    def _on_palette_measure(self):
        if not self.connected:
            messagebox.showerror("Ошибка", "Нет подключения к RM200")
            return
        if self.busy:
            return
        if self._current_palette() is None:
            messagebox.showwarning("Палитры",
                                   "Сначала создайте или выберите палитру.")
            return

        self._set_busy(True, "Идёт измерение... Нажмите кнопку на RM200.")

        def worker():
            try:
                prev_count = safe_command(rm.GetNumberOfEntries) or 0
                safe_command(rm.TriggerMeasurement, self.aperture)

                deadline = time.time() + self.timeout
                got = False
                while time.time() < deadline:
                    try:
                        cnt = safe_command(rm.GetNumberOfEntries)
                    except Exception:
                        cnt = None
                    if cnt is not None and cnt > prev_count:
                        got = True
                        break
                    time.sleep(POLL_INTERVAL)

                if not got:
                    raise TimeoutError("Измерение не завершилось за отведённое время")

                time.sleep(POST_MEAS_PAUSE)

                if self.reconnect_after:
                    self._reconnect_device()

                data = safe_command(rm.FetchFile, "MeasDataV05.dat")
                records = parse_measdata(data)
                if not records:
                    raise RuntimeError("В файле нет валидных записей")

                self.after(0, lambda: self._on_palette_pick_records(records, None))
            except Exception as e:
                self.after(0, lambda: self._on_palette_pick_records(None, e))

        threading.Thread(target=worker, daemon=True).start()

    def _on_palette_pick_records(self, records, error):
        self._set_busy(False)
        if error:
            self._set_status(f"Ошибка измерения: {error}")
            messagebox.showerror("Ошибка измерения", str(error))
            return
        chosen = self._show_pick_record_dialog('ref', records)
        if chosen is None:
            self._set_status("Запись не добавлена в палитру")
            return
        self._add_entry_to_current_palette(chosen['sample_lab'])
        self._set_status("Цвет добавлен в палитру")

    def _on_palette_manual(self):
        if self._current_palette() is None:
            messagebox.showwarning("Палитры",
                                   "Сначала создайте или выберите палитру.")
            return
        lab = self._ask_manual_color("Новый цвет в палитру")
        if lab is None:
            return
        self._add_entry_to_current_palette(lab)

    def _on_palette_entry_rename(self):
        idxs = self._selected_palette_indices()
        if not idxs:
            return
        p = self._current_palette()
        if not p:
            return
        i = idxs[0]
        if i < 0 or i >= len(p['entries']):
            return
        old = p['entries'][i]['name']
        new = simpledialog.askstring("Переименовать цвет",
                                     "Новое имя:",
                                     initialvalue=old, parent=self)
        if not new:
            return
        new = new.strip()
        if not new:
            return
        p['entries'][i]['name'] = new
        self._save_palettes()
        self._refresh_palette_entries()

    def _on_palette_entry_dup(self):
        idxs = self._selected_palette_indices()
        if not idxs:
            return
        p = self._current_palette()
        if not p:
            return
        i = idxs[0]
        if i < 0 or i >= len(p['entries']):
            return
        src = p['entries'][i]
        dup = {'name': self._auto_entry_name(p), 'lab': tuple(src['lab'])}
        p['entries'].append(dup)
        self._save_palettes()
        self._refresh_palette_entries()

    def _on_palette_entry_delete(self):
        idxs = sorted(self._selected_palette_indices(), reverse=True)
        if not idxs:
            return
        p = self._current_palette()
        if not p:
            return
        if not messagebox.askyesno("Удалить",
                                   f"Удалить {len(idxs)} цвет(ов)?"):
            return
        for i in idxs:
            if 0 <= i < len(p['entries']):
                del p['entries'][i]
        self._save_palettes()
        self._refresh_palette_entries()

    # --- импорт/экспорт ---

    def _on_palette_export(self):
        name = self._current_palette_name()
        if name not in self.palettes:
            return
        target = filedialog.asksaveasfilename(
            title="Экспорт палитры",
            initialfile=f"{name}.json",
            defaultextension=".json",
            filetypes=[("JSON", "*.json")])
        if not target:
            return
        try:
            data = {
                'name': name,
                'entries': [
                    {'name': e['name'], 'lab': list(e['lab'])}
                    for e in self.palettes[name]['entries']
                ],
            }
            with open(target, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
            self.palettes_status.set(f"Экспортировано в {target}")
        except Exception as e:
            messagebox.showerror("Ошибка", str(e))

    def _on_palette_import(self):
        src = filedialog.askopenfilename(
            title="Импорт палитры",
            filetypes=[("JSON", "*.json"), ("Все файлы", "*.*")])
        if not src:
            return
        try:
            with open(src, 'r', encoding='utf-8') as f:
                data = json.load(f)
            name = data.get('name') or os.path.splitext(os.path.basename(src))[0]
            entries = data.get('entries', [])
            if name in self.palettes:
                if not messagebox.askyesno(
                        "Импорт",
                        f"Палитра '{name}' уже существует. Перезаписать?"):
                    return
            self.palettes[name] = {'entries': [
                {'name': e.get('name', 'Color'),
                 'lab': (float(e['lab'][0]), float(e['lab'][1]), float(e['lab'][2]))}
                for e in entries if 'lab' in e
            ]}
            self._save_palettes()
            self._refresh_palette_list()
            self.palettes_tab_selector_var.set(name)
            self._refresh_palette_entries()
            self.palettes_status.set(f"Импортировано: {name}")
        except Exception as e:
            messagebox.showerror("Ошибка", str(e))

    def _on_palette_export_all(self):
        target = filedialog.asksaveasfilename(
            title="Экспорт всех палитр",
            initialfile="palettes.json",
            defaultextension=".json",
            filetypes=[("JSON", "*.json")])
        if not target:
            return
        try:
            data = {'palettes': [
                {
                    'name': n,
                    'entries': [
                        {'name': e['name'], 'lab': list(e['lab'])}
                        for e in p['entries']
                    ],
                }
                for n, p in self.palettes.items()
            ]}
            with open(target, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
            self._set_status(f"Экспортировано в {target}")
        except Exception as e:
            messagebox.showerror("Ошибка", str(e))

    def _on_palette_import_all(self):
        src = filedialog.askopenfilename(
            title="Импорт палитр",
            filetypes=[("JSON", "*.json"), ("Все файлы", "*.*")])
        if not src:
            return
        try:
            with open(src, 'r', encoding='utf-8') as f:
                data = json.load(f)
            count = 0
            for p in data.get('palettes', []):
                name = p.get('name', 'Unnamed')
                self.palettes[name] = {'entries': [
                    {'name': e.get('name', 'Color'),
                     'lab': (float(e['lab'][0]), float(e['lab'][1]), float(e['lab'][2]))}
                    for e in p.get('entries', []) if 'lab' in e
                ]}
                count += 1
            self._save_palettes()
            self._refresh_palette_list()
            self._set_status(f"Импортировано палитр: {count}")
        except Exception as e:
            messagebox.showerror("Ошибка", str(e))

    # --- Диалог ручного ввода цвета ---

    def _ask_manual_color(self, title="Ввод цвета", initial=None):
        """
        Возвращает Lab-tuple или None.
        """
        dlg = tk.Toplevel(self)
        dlg.title(title)
        dlg.transient(self)
        dlg.grab_set()
        dlg.geometry("380x220")

        mode_var = tk.StringVar(value='cmyk')

        ttk.Radiobutton(dlg, text="CMYK", value='cmyk',
                        variable=mode_var).grid(row=0, column=0, padx=8, pady=8, sticky='w')
        ttk.Radiobutton(dlg, text="RGB", value='rgb',
                        variable=mode_var).grid(row=0, column=1, padx=8, pady=8, sticky='w')

        c_var = tk.StringVar(value="0")
        m_var = tk.StringVar(value="0")
        y_var = tk.StringVar(value="0")
        k_var = tk.StringVar(value="0")
        r_var = tk.StringVar(value="128")
        g_var = tk.StringVar(value="128")
        b_var = tk.StringVar(value="128")

        def build_fields():
            for w in dlg.grid_slaves():
                info = w.grid_info()
                if int(info.get('row', -1)) >= 1:
                    w.grid_forget()

            if mode_var.get() == 'cmyk':
                for i, (label, var) in enumerate(
                        (("C %", c_var), ("M %", m_var),
                         ("Y %", y_var), ("K %", k_var))):
                    ttk.Label(dlg, text=label).grid(row=1, column=i*2, padx=4,
                                                    pady=8, sticky='e')
                    ttk.Entry(dlg, textvariable=var, width=8).grid(
                        row=1, column=i*2+1, padx=4, pady=8)
            else:
                for i, (label, var) in enumerate(
                        (("R", r_var), ("G", g_var), ("B", b_var))):
                    ttk.Label(dlg, text=label).grid(row=1, column=i*2, padx=4,
                                                    pady=8, sticky='e')
                    ttk.Entry(dlg, textvariable=var, width=8).grid(
                        row=1, column=i*2+1, padx=4, pady=8)

        mode_var.trace_add('write', lambda *a: build_fields())
        build_fields()

        result = {'lab': None}

        def on_ok():
            try:
                if mode_var.get() == 'cmyk':
                    c = float(c_var.get())
                    m = float(m_var.get())
                    y = float(y_var.get())
                    k = float(k_var.get())
                    result['lab'] = cmyk_to_lab(c, m, y, k)
                else:
                    r = int(r_var.get())
                    g = int(g_var.get())
                    b = int(b_var.get())
                    result['lab'] = srgb_to_lab(r, g, b)
            except Exception as e:
                messagebox.showerror("Ошибка", f"Некорректное значение: {e}",
                                     parent=dlg)
                return
            dlg.destroy()

        def on_cancel():
            dlg.destroy()

        btns = ttk.Frame(dlg)
        btns.grid(row=3, column=0, columnspan=8, pady=10)
        ttk.Button(btns, text="OK", command=on_ok).pack(side=tk.LEFT, padx=6)
        ttk.Button(btns, text="Отмена", command=on_cancel).pack(side=tk.LEFT, padx=6)

        self.wait_window(dlg)
        return result['lab']

    # ======================================================================
    #  ВКЛАДКА 3. УСТРОЙСТВО
    # ======================================================================

    def _tab_device(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="Устройство")

        info = ttk.LabelFrame(frame, text="Информация")
        info.pack(fill=tk.X, pady=(0, 8))

        self.dev_text = tk.Text(info, height=12, font=("Consolas", 10),
                                state=tk.DISABLED, wrap=tk.NONE)
        self.dev_text.pack(fill=tk.X, padx=4, pady=4)

        row = ttk.Frame(info)
        row.pack(fill=tk.X, padx=4, pady=(0, 4))
        ttk.Button(row, text="Прочитать всё",
                   command=self._on_device_read_all).pack(side=tk.LEFT, padx=2)
        ttk.Button(row, text="Battery",
                   command=self._on_device_battery).pack(side=tk.LEFT, padx=2)
        ttk.Button(row, text="Temperature",
                   command=self._menu_temperature).pack(side=tk.LEFT, padx=2)
        ttk.Button(row, text="DeltaE params",
                   command=self._on_device_deltae).pack(side=tk.LEFT, padx=2)

        mode = ttk.LabelFrame(frame, text="Режим устройства")
        mode.pack(fill=tk.X, pady=(0, 8))
        self.mode_var = tk.StringVar(value="?")
        ttk.Entry(mode, textvariable=self.mode_var, width=30).pack(side=tk.LEFT, padx=4, pady=4)
        ttk.Button(mode, text="Get",
                   command=self._on_device_get_mode).pack(side=tk.LEFT, padx=2)
        ttk.Button(mode, text="Set",
                   command=self._on_device_set_mode).pack(side=tk.LEFT, padx=2)

        time_frame = ttk.LabelFrame(frame, text="Время устройства")
        time_frame.pack(fill=tk.X, pady=(0, 8))
        self.time_var = tk.StringVar(value="")
        ttk.Entry(time_frame, textvariable=self.time_var, width=30).pack(
            side=tk.LEFT, padx=4, pady=4)
        ttk.Button(time_frame, text="Get",
                   command=self._on_device_get_time).pack(side=tk.LEFT, padx=2)
        ttk.Button(time_frame, text="Set",
                   command=self._on_device_set_time).pack(side=tk.LEFT, padx=2)
        ttk.Button(time_frame, text="Сейчас → Set",
                   command=self._on_device_set_time_now).pack(side=tk.LEFT, padx=2)

        ap = ttk.LabelFrame(frame, text="Апертура")
        ap.pack(fill=tk.X, pady=(0, 8))
        self.ap_var = tk.StringVar(value=str(self.aperture))
        ttk.Combobox(ap, textvariable=self.ap_var,
                     values=["0", "1", "2"], width=6,
                     state="readonly").pack(side=tk.LEFT, padx=4, pady=4)
        ttk.Button(ap, text="Get",
                   command=self._on_device_get_aperture).pack(side=tk.LEFT, padx=2)
        ttk.Button(ap, text="Set",
                   command=self._on_device_set_aperture).pack(side=tk.LEFT, padx=2)

        svc = ttk.LabelFrame(frame, text="Сервис")
        svc.pack(fill=tk.X, pady=(0, 8))
        ttk.Button(svc, text="ChipID",
                   command=self._on_device_chipid).pack(side=tk.LEFT, padx=2)

        self._device_log("Готово. Нажмите «Прочитать всё».")

    def _device_log(self, text, append=True):
        self.dev_text.config(state=tk.NORMAL)
        if not append:
            self.dev_text.delete('1.0', tk.END)
        self.dev_text.insert(tk.END, text + "\n")
        self.dev_text.see(tk.END)
        self.dev_text.config(state=tk.DISABLED)

    def _on_device_read_all(self):
        if not self.connected:
            messagebox.showerror("Ошибка", "Нет подключения")
            return
        self._device_log("--- Прочитать всё ---", append=False)

        def worker():
            results = []
            checks = [
                ("GetInfo",               "GetInfo"),
                ("GetSerialNum",          "GetSerialNum"),
                ("GetFWInfo",             "GetFWInfo"),
                ("GetBLInfo",             "GetBLInfo"),
                ("GetChipId",             "GetChipId"),
                ("GetBatteryState",       "GetBatteryState"),
                ("GetDeviceMode",         "GetDeviceMode"),
                ("GetTime",               "GetTime"),
                ("GetTimeString",         "GetTimeString"),
                ("GetAperture",           "GetAperture"),
                ("GetCalibrationState",   "GetCalibrationState"),
                ("GetTimeToCalibExpired", "GetTimeToCalibExpired"),
                ("GetDeltaEParameter",    "GetDeltaEParameter"),
                ("MeasureTemperature",    "MeasureTemperature"),
            ]
            for label, fname in checks:
                fn = getattr(rm, fname, None)
                ok, val = try_call(fn)
                if fn is None:
                    results.append(f"{label:24} : <нет в библиотеке>")
                elif ok:
                    results.append(f"{label:24} : {val!r}")
                else:
                    results.append(f"{label:24} : ошибка: {val}")

            self.after(0, lambda: self._device_log("\n".join(results), append=False))
            self.after(0, lambda: self._set_status("Информация прочитана"))

        threading.Thread(target=worker, daemon=True).start()

    def _on_device_battery(self):
        ok, val = try_call(getattr(rm, "GetBatteryState", None))
        self._device_log(f"Battery: {val!r}" if ok else f"Battery: ошибка {val}")

    def _on_device_deltae(self):
        ok, val = try_call(getattr(rm, "GetDeltaEParameter", None))
        self._device_log(f"DeltaE: {val!r}" if ok else f"DeltaE: ошибка {val}")

    def _on_device_get_mode(self):
        ok, val = try_call(getattr(rm, "GetDeviceMode", None))
        if ok:
            self.mode_var.set(str(val))
            self._device_log(f"Mode = {val!r}")
        else:
            self._device_log(f"GetMode: ошибка {val}")

    def _on_device_set_mode(self):
        mode = self.mode_var.get().strip()
        if not mode:
            return
        ok, val = try_call(getattr(rm, "SetDeviceMode", None), mode)
        self._device_log(f"SetMode({mode!r}) -> "
                         + ("OK" if ok else f"ошибка {val}"))

    def _on_device_get_time(self):
        ok, val = try_call(getattr(rm, "GetTimeString", None))
        if not ok:
            ok, val = try_call(getattr(rm, "GetTime", None))
        if ok:
            self.time_var.set(str(val))
            self._device_log(f"Time = {val!r}")
        else:
            self._device_log(f"GetTime: ошибка {val}")

    def _on_device_set_time(self):
        t = self.time_var.get().strip()
        if not t:
            return
        ok, val = try_call(getattr(rm, "SetTime", None), t)
        self._device_log(f"SetTime({t!r}) -> " + ("OK" if ok else f"ошибка {val}"))

    def _on_device_set_time_now(self):
        now = dt.datetime.now()
        for fmt in ("%Y-%m-%d %H:%M:%S", "%Y.%m.%d %H:%M:%S", "%Y-%m-%dT%H:%M:%S"):
            s = now.strftime(fmt)
            ok, val = try_call(getattr(rm, "SetTime", None), s)
            if ok:
                self.time_var.set(s)
                self._device_log(f"SetTime({s!r}) -> OK")
                return
        self._device_log("SetTime: не удалось ни в одном формате")

    def _on_device_get_aperture(self):
        ok, val = try_call(getattr(rm, "GetAperture", None))
        if ok:
            self.ap_var.set(str(val))
            self._device_log(f"Aperture = {val!r}")
        else:
            self._device_log(f"GetAperture: ошибка {val}")

    def _on_device_set_aperture(self):
        try:
            ap = int(self.ap_var.get())
        except Exception:
            return
        ok, val = try_call(getattr(rm, "SetAperture", None), ap)
        if ok:
            self.aperture = ap
        self._device_log(f"SetAperture({ap}) -> " + ("OK" if ok else f"ошибка {val}"))

    def _on_device_chipid(self):
        ok, val = try_call(getattr(rm, "GetChipId", None))
        self._device_log(f"ChipID: {val!r}" if ok else f"ChipID: ошибка {val}")

    # ======================================================================
    #  ВКЛАДКА 4. ФАЙЛЫ
    # ======================================================================

    def _tab_files(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="Файлы")

        top = ttk.Frame(frame)
        top.pack(fill=tk.X, pady=(0, 6))
        ttk.Button(top, text="Обновить список",
                   command=self._on_files_refresh).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="Скачать выбранный...",
                   command=self._on_files_download).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="Загрузить на устройство...",
                   command=self._on_files_upload).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="Удалить выбранный",
                   command=self._on_files_delete).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="Сохранить MeasDataV05.dat...",
                   command=self._menu_save_dump).pack(side=tk.LEFT, padx=2)

        list_frame = ttk.Frame(frame)
        list_frame.pack(fill=tk.BOTH, expand=True)

        scrollbar = ttk.Scrollbar(list_frame, orient=tk.VERTICAL)
        self.files_list = tk.Listbox(list_frame, font=("Consolas", 10),
                                     yscrollcommand=scrollbar.set)
        scrollbar.config(command=self.files_list.yview)
        self.files_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        self.files_status = tk.StringVar(value="Нажмите «Обновить список».")
        ttk.Label(frame, textvariable=self.files_status,
                  padding=(0, 6, 0, 0)).pack(anchor=tk.W)

    def _on_files_refresh(self):
        if not self.connected:
            messagebox.showerror("Ошибка", "Нет подключения")
            return

        def worker():
            fn = getattr(rm, "FileDir", None)
            ok, val = try_call(fn)
            self.after(0, lambda: self._on_files_list(ok, val))

        threading.Thread(target=worker, daemon=True).start()

    def _on_files_list(self, ok, val):
        self.files_list.delete(0, tk.END)
        if not ok:
            self.files_status.set(f"Ошибка: {val}")
            return

        files = val
        if isinstance(files, str):
            lines = files.splitlines()
        elif isinstance(files, (list, tuple)):
            lines = []
            for item in files:
                if isinstance(item, str):
                    lines.append(item)
                elif isinstance(item, dict):
                    size = item.get('size', '')
                    name = item.get('name', item.get('file', ''))
                    lines.append(f"{size:>12}  {name}" if size != '' else str(name))
                else:
                    lines.append(str(item))
        else:
            lines = [str(files)]

        for line in lines:
            self.files_list.insert(tk.END, line)

        self.files_status.set(f"Файлов: {len(lines)}")

    def _get_selected_filename(self):
        sel = self.files_list.curselection()
        if not sel:
            return None
        line = self.files_list.get(sel[0])
        parts = line.strip().split()
        if not parts:
            return None
        return parts[-1]

    def _on_files_download(self):
        name = self._get_selected_filename()
        if not name:
            messagebox.showwarning("Файл", "Выберите файл в списке")
            return
        target = filedialog.asksaveasfilename(
            title="Сохранить как", initialfile=name)
        if not target:
            return

        def worker():
            fn = getattr(rm, "FetchFile", None) or getattr(rm, "DownloadFile", None)
            ok, val = try_call(fn, name)
            if not ok:
                self.after(0, lambda: messagebox.showerror("Ошибка", str(val)))
                return
            try:
                with open(target, 'wb') as f:
                    f.write(val)
                self.after(0, lambda: self.files_status.set(
                    f"Сохранено {len(val)} байт в {target}"))
            except Exception as e:
                self.after(0, lambda: messagebox.showerror("Ошибка", str(e)))

        threading.Thread(target=worker, daemon=True).start()

    def _on_files_upload(self):
        src = filedialog.askopenfilename(title="Выберите файл для загрузки")
        if not src:
            return
        name = os.path.basename(src)
        if not messagebox.askyesno("Загрузка",
                                   f"Загрузить {name} на RM200?\n"
                                   f"(может перезаписать одноимённый файл)"):
            return

        def worker():
            try:
                with open(src, 'rb') as f:
                    data = f.read()
            except Exception as e:
                self.after(0, lambda: messagebox.showerror("Ошибка", str(e)))
                return
            fn = getattr(rm, "PutFile", None) or getattr(rm, "UploadFile", None)
            if fn is None:
                self.after(0, lambda: messagebox.showerror(
                    "Ошибка", "Нет UploadFile/PutFile"))
                return
            try:
                if fn.__name__ == "PutFile":
                    ok, val = try_call(fn, name, data)
                else:
                    ok, val = try_call(fn, name)
                self.after(0, lambda: self.files_status.set(
                    f"Загрузка {name}: " + ("OK" if ok else f"ошибка {val}")))
            except Exception as e:
                self.after(0, lambda: messagebox.showerror("Ошибка", str(e)))

        threading.Thread(target=worker, daemon=True).start()

    def _on_files_delete(self):
        name = self._get_selected_filename()
        if not name:
            messagebox.showwarning("Файл", "Выберите файл в списке")
            return
        if not messagebox.askyesno("Удалить", f"Удалить {name} с RM200?"):
            return
        ok, val = try_call(getattr(rm, "FileDelete", None), name)
        self.files_status.set(f"Удаление {name}: " + ("OK" if ok else f"ошибка {val}"))

    # ======================================================================
    #  ВКЛАДКА 5. FAN DECKS
    # ======================================================================

    def _tab_fandecks(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="Fan Decks")

        top = ttk.Frame(frame)
        top.pack(fill=tk.X, pady=(0, 6))
        ttk.Button(top, text="Обновить список",
                   command=self._on_fd_refresh).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="Активировать выбранный",
                   command=self._on_fd_activate).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="Деактивировать выбранный",
                   command=self._on_fd_deactivate).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="Удалить выбранный",
                   command=self._on_fd_delete).pack(side=tk.LEFT, padx=2)
        ttk.Button(top, text="Добавить Fan Deck (.fdk)...",
                   command=self._on_fd_add).pack(side=tk.LEFT, padx=2)

        list_frame = ttk.Frame(frame)
        list_frame.pack(fill=tk.BOTH, expand=True)

        scrollbar = ttk.Scrollbar(list_frame, orient=tk.VERTICAL)
        self.fd_list = tk.Listbox(list_frame, font=("Consolas", 10),
                                  yscrollcommand=scrollbar.set)
        scrollbar.config(command=self.fd_list.yview)
        self.fd_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        self.fd_status = tk.StringVar(value="Нажмите «Обновить список».")
        ttk.Label(frame, textvariable=self.fd_status,
                  padding=(0, 6, 0, 0)).pack(anchor=tk.W)

    def _on_fd_refresh(self):
        if not self.connected:
            messagebox.showerror("Ошибка", "Нет подключения")
            return

        def worker():
            ok, val = try_call(getattr(rm, "GetFandecks", None))
            self.after(0, lambda: self._on_fd_list(ok, val))

        threading.Thread(target=worker, daemon=True).start()

    def _on_fd_list(self, ok, val):
        self.fd_list.delete(0, tk.END)
        if not ok:
            self.fd_status.set(f"Ошибка: {val}")
            return
        items = val if isinstance(val, (list, tuple)) else [val]
        for it in items:
            self.fd_list.insert(tk.END, str(it))
        self.fd_status.set(f"Fan decks: {len(items)}")

    def _selected_fd(self):
        sel = self.fd_list.curselection()
        if not sel:
            return None
        return self.fd_list.get(sel[0]).strip().split()[-1]

    def _on_fd_activate(self):
        name = self._selected_fd()
        if not name:
            return
        ok, val = try_call(getattr(rm, "SetFandeckActive", None), name, True)
        self.fd_status.set(f"Активация {name}: " + ("OK" if ok else f"ошибка {val}"))
        self._on_fd_refresh()

    def _on_fd_deactivate(self):
        name = self._selected_fd()
        if not name:
            return
        ok, val = try_call(getattr(rm, "SetFandeckActive", None), name, False)
        self.fd_status.set(f"Деактивация {name}: " + ("OK" if ok else f"ошибка {val}"))
        self._on_fd_refresh()

    def _on_fd_delete(self):
        name = self._selected_fd()
        if not name:
            return
        if not messagebox.askyesno("Удалить", f"Удалить fan deck {name}?"):
            return
        ok, val = try_call(getattr(rm, "DeleteFandeck", None), name)
        self.fd_status.set(f"Удаление {name}: " + ("OK" if ok else f"ошибка {val}"))
        self._on_fd_refresh()

    def _on_fd_add(self):
        src = filedialog.askopenfilename(
            title="Выберите файл Fan Deck (.fdk)",
            filetypes=[("Fan Deck", "*.fdk"), ("Все файлы", "*.*")])
        if not src:
            return
        name = os.path.basename(src)
        if not messagebox.askyesno("Добавить Fan Deck",
                                   f"Загрузить '{name}' на RM200?"):
            return

        def worker():
            try:
                with open(src, 'rb') as f:
                    data = f.read()
            except Exception as e:
                self.after(0, lambda: messagebox.showerror("Ошибка", str(e)))
                return

            fn = getattr(rm, "PutFile", None)
            if fn is None:
                self.after(0, lambda: messagebox.showerror(
                    "Ошибка", "Нет функции PutFile"))
                return

            ok, val = try_call(fn, name, data)
            if ok:
                self.after(0, lambda: self.fd_status.set(
                    f"Fan Deck '{name}' загружен. Нажмите «Обновить список»."))
                self.after(0, self._on_fd_refresh)
            else:
                self.after(0, lambda: self.fd_status.set(
                    f"Ошибка загрузки: {val}"))

        threading.Thread(target=worker, daemon=True).start()

    # ======================================================================
    #  ВКЛАДКА 6. КАЛИБРОВКА
    # ======================================================================

    def _tab_calibration(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="Калибровка")

        info = ttk.LabelFrame(frame, text="Состояние")
        info.pack(fill=tk.X, pady=(0, 8))

        self.cal_text = tk.Text(info, height=10, font=("Consolas", 10),
                                state=tk.DISABLED, wrap=tk.NONE)
        self.cal_text.pack(fill=tk.X, padx=4, pady=4)

        row = ttk.Frame(info)
        row.pack(fill=tk.X, padx=4, pady=(0, 4))
        ttk.Button(row, text="Проверить состояние",
                   command=self._on_cal_state).pack(side=tk.LEFT, padx=2)
        ttk.Button(row, text="Время до истечения",
                   command=self._on_cal_expiry).pack(side=tk.LEFT, padx=2)

        backup = ttk.LabelFrame(frame, text="BackupCalibData")
        backup.pack(fill=tk.X, pady=(0, 8))
        self.cal_mode_var = tk.StringVar(value="0")
        ttk.Label(backup, text="Режим:").pack(side=tk.LEFT, padx=4)
        ttk.Combobox(backup, textvariable=self.cal_mode_var,
                     values=["0", "1", "2"], width=5,
                     state="readonly").pack(side=tk.LEFT, padx=2)
        ttk.Button(backup, text="BackupCalibData",
                   command=self._on_cal_backup).pack(side=tk.LEFT, padx=6)

        vers = ttk.LabelFrame(frame, text="Versions.dat")
        vers.pack(fill=tk.X, pady=(0, 8))
        ttk.Button(vers, text="Читать (ReadVersionsDotDat)",
                   command=self._on_cal_read_versions).pack(side=tk.LEFT, padx=2)

        self._cal_log("Готово.")

    def _cal_log(self, text, append=True):
        self.cal_text.config(state=tk.NORMAL)
        if not append:
            self.cal_text.delete('1.0', tk.END)
        self.cal_text.insert(tk.END, text + "\n")
        self.cal_text.see(tk.END)
        self.cal_text.config(state=tk.DISABLED)

    def _on_cal_state(self):
        ok, val = try_call(getattr(rm, "GetCalibrationState", None))
        self._cal_log(f"CalibState: {val!r}" if ok else f"Ошибка: {val}")

    def _on_cal_expiry(self):
        ok, val = try_call(getattr(rm, "GetTimeToCalibExpired", None))
        self._cal_log(f"TimeToCalibExpired: {val!r}" if ok else f"Ошибка: {val}")

    def _on_cal_backup(self):
        try:
            mode = int(self.cal_mode_var.get())
        except Exception:
            mode = 0
        ok, val = try_call(getattr(rm, "BackupCalibData", None), mode)
        self._cal_log(f"BackupCalibData({mode}) -> "
                      + ("OK" if ok else f"ошибка {val}"))

    def _on_cal_read_versions(self):
        def worker():
            fn = getattr(rm, "ReadVersionsDotDat", None)
            ok, val = try_call(fn)
            if not ok:
                self.after(0, lambda: self._cal_log(f"Ошибка: {val}"))
                return
            self.after(0, lambda: self._cal_log(repr(val)[:2000], append=False))

        threading.Thread(target=worker, daemon=True).start()

    # ======================================================================
    #  ВКЛАДКА 7. ЭКРАН И КЛАВИАТУРА
    # ======================================================================

    def _tab_screen_keys(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="Экран и клавиатура")

        screen = ttk.LabelFrame(frame, text="Экран LCD")
        screen.pack(fill=tk.X, pady=(0, 8))
        ttk.Button(screen, text="Сохранить скриншот...",
                   command=self._on_screen_screenshot).pack(side=tk.LEFT, padx=4, pady=4)
        ttk.Button(screen, text="GetLcdData (в лог)",
                   command=self._on_screen_lcd_data).pack(side=tk.LEFT, padx=4, pady=4)
        ttk.Button(screen, text="Показать скриншот в окне",
                   command=self._on_screen_show).pack(side=tk.LEFT, padx=4, pady=4)

        keys = ttk.LabelFrame(frame, text="Эмуляция клавиш")
        keys.pack(fill=tk.X, pady=(0, 8))

        key_buttons = [
            ('Центр\n(Measure)', 1), ('Вверх', 2), ('Вниз', 3),
            ('Влево', 4), ('Вправо', 5),
            ('Preview\n(release)', 6), ('Preview\n(hold)', 7),
            ('Захват\n(Capture)', 8),
        ]
        for i, (label, code) in enumerate(key_buttons):
            btn = ttk.Button(keys, text=label, width=10,
                             command=lambda c=code: self._on_key_press(c))
            btn.grid(row=0, column=i, padx=2, pady=4)

        ttk.Button(keys, text="Прочитать состояние клавиш",
                   command=self._on_keys_get_code).grid(row=1, column=0,
                                                        columnspan=8, pady=4)

        self.keys_log = tk.Text(frame, height=10, font=("Consolas", 10),
                                state=tk.DISABLED, wrap=tk.NONE)
        self.keys_log.pack(fill=tk.BOTH, expand=True)

    def _keys_print(self, text):
        self.keys_log.config(state=tk.NORMAL)
        self.keys_log.insert(tk.END, text + "\n")
        self.keys_log.see(tk.END)
        self.keys_log.config(state=tk.DISABLED)

    def _on_screen_screenshot(self):
        target = filedialog.asksaveasfilename(
            title="Сохранить скриншот", initialfile="screenshot.png",
            defaultextension=".png",
            filetypes=[("PNG", "*.png"), ("BMP", "*.bmp"), ("Все файлы", "*.*")])
        if not target:
            return

        def worker():
            fn = getattr(rm, "SaveScreenshot", None)
            ok, val = try_call(fn, target)
            if not ok:
                self.after(0, lambda: self._keys_print(f"SaveScreenshot: {val}"))
                return
            self.after(0, lambda: self._keys_print(f"Screenshot: {target}"))

        threading.Thread(target=worker, daemon=True).start()

    def _on_screen_show(self):
        if not HAS_PIL:
            messagebox.showerror("Ошибка", "Pillow не установлен")
            return

        target = filedialog.asksaveasfilename(
            title="Временный скриншот", initialfile="temp_screen.bmp",
            defaultextension=".bmp",
            filetypes=[("BMP", "*.bmp")])
        if not target:
            return

        def worker():
            fn = getattr(rm, "SaveScreenshot", None)
            ok, val = try_call(fn, target)
            if not ok:
                self.after(0, lambda: messagebox.showerror("Ошибка", str(val)))
                return

            try:
                img = Image.open(target)
                img = img.resize((640, 480), Image.NEAREST)
                photo = ImageTk.PhotoImage(img)

                top = tk.Toplevel(self)
                top.title("Скриншот LCD")
                label = ttk.Label(top, image=photo)
                label.image = photo
                label.pack()
            except Exception as e:
                self.after(0, lambda: messagebox.showerror("Ошибка", str(e)))

        threading.Thread(target=worker, daemon=True).start()

    def _on_screen_lcd_data(self):
        def worker():
            fn = getattr(rm, "GetLcdData", None)
            ok, val = try_call(fn)
            if ok:
                if isinstance(val, (bytes, bytearray)):
                    self.after(0, lambda: self._keys_print(
                        f"GetLcdData: {len(val)} байт"))
                else:
                    self.after(0, lambda: self._keys_print(
                        f"GetLcdData: {str(val)[:500]}"))
            else:
                self.after(0, lambda: self._keys_print(f"Ошибка: {val}"))

        threading.Thread(target=worker, daemon=True).start()

    def _on_key_press(self, code):
        def worker():
            fn = getattr(rm, "GenerateKeyboardEvent", None)
            ok, val = try_call(fn, code)
            if ok:
                self.after(0, lambda: self._keys_print(
                    f"GenerateKeyboardEvent({code}) -> OK"))
            else:
                self.after(0, lambda: self._keys_print(
                    f"GenerateKeyboardEvent({code}) -> ошибка: {val}"))

        threading.Thread(target=worker, daemon=True).start()

    def _on_keys_get_code(self):
        fn = getattr(rm, "GetKeyCode", None)
        ok, val = try_call(fn)
        if ok:
            self._keys_print(f"GetKeyCode: {val:#x} ({val})")
        else:
            self._keys_print(f"GetKeyCode: ошибка: {val}")

    # ======================================================================
    #  ВКЛАДКА 8. PREVIEW
    # ======================================================================

    def _tab_preview(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="Preview")

        ctrl = ttk.Frame(frame)
        ctrl.pack(fill=tk.X, pady=(0, 8))

        self.preview_running = False
        self.preview_btn = ttk.Button(ctrl, text="▶ Запустить Live Preview",
                                      command=self._toggle_live_preview)
        self.preview_btn.pack(side=tk.LEFT, padx=4)

        ttk.Button(ctrl, text="Остановить",
                   command=self._stop_live_preview).pack(side=tk.LEFT, padx=4)
        ttk.Button(ctrl, text="Сделать скриншот Preview...",
                   command=self._preview_save).pack(side=tk.LEFT, padx=4)

        ttk.Label(ctrl, text="Интервал (мс):").pack(side=tk.LEFT, padx=(20, 4))
        self.preview_interval_var = tk.StringVar(value="500")
        ttk.Entry(ctrl, textvariable=self.preview_interval_var,
                  width=6).pack(side=tk.LEFT)

        preview_frame = ttk.LabelFrame(frame, text="Preview")
        preview_frame.pack(fill=tk.BOTH, expand=True)

        self.preview_canvas = tk.Canvas(preview_frame, width=640, height=480,
                                        bg='black')
        self.preview_canvas.pack(padx=4, pady=4)
        self.preview_canvas.create_text(320, 240, text="Preview не запущен",
                                        fill="#666", font=("Segoe UI", 12))

        self.preview_log = tk.Text(frame, height=6, font=("Consolas", 9),
                                   state=tk.DISABLED, wrap=tk.NONE)
        self.preview_log.pack(fill=tk.X, pady=(8, 0))

    def _preview_print(self, text):
        self.preview_log.config(state=tk.NORMAL)
        self.preview_log.insert(tk.END, text + "\n")
        self.preview_log.see(tk.END)
        self.preview_log.config(state=tk.DISABLED)

    def _toggle_live_preview(self):
        if self.preview_running:
            self._stop_live_preview()
        else:
            self._start_live_preview()

    def _start_live_preview(self):
        if not self.connected:
            messagebox.showerror("Ошибка", "Нет подключения")
            return
        if not HAS_PIL:
            messagebox.showerror("Ошибка", "Pillow не установлен")
            return

        fn = getattr(rm, "StartPreview", None)
        ok, val = try_call(fn)
        if not ok:
            self._preview_print(f"StartPreview: ошибка {val}")
            return

        self.preview_running = True
        self.preview_btn.config(text="⏹ Остановить Live Preview")
        self._preview_print("Live Preview запущен.")
        self._preview_tick()

    def _stop_live_preview(self):
        self.preview_running = False
        if self.preview_after_id:
            try:
                self.after_cancel(self.preview_after_id)
            except Exception:
                pass
            self.preview_after_id = None

        fn = getattr(rm, "StopPreview", None)
        try_call(fn)
        try:
            self.preview_btn.config(text="▶ Запустить Live Preview")
            self.preview_canvas.delete("all")
            self.preview_canvas.create_text(320, 240,
                                            text="Preview остановлен",
                                            fill="#666", font=("Segoe UI", 12))
        except Exception:
            pass
        self._preview_print("Live Preview остановлен.")

    def _preview_tick(self):
        if not self.preview_running:
            return

        try:
            interval = max(100, int(self.preview_interval_var.get()))
        except Exception:
            interval = 500

        fn = getattr(rm, "GetPreview", None)
        ok, data = try_call(fn)

        if ok and data and len(data) > 4:
            try:
                width = int.from_bytes(data[0:2], 'big')
                height = int.from_bytes(data[2:4], 'big')
                pixels = data[4:]

                img = Image.new("RGB", (width, height))
                expected = width * height * 2
                if len(pixels) < expected:
                    self._preview_print(
                        f"Недостаточно пикселей: {len(pixels)} < {expected}")
                    self.preview_after_id = self.after(interval, self._preview_tick)
                    return

                pix_data = []
                for i in range(0, expected, 2):
                    v = int.from_bytes(pixels[i:i+2], 'big')
                    r = (v >> 11) & 0x1F
                    g = (v >> 5) & 0x3F
                    b = v & 0x1F
                    pix_data.append((
                        (r * 255) // 31,
                        (g * 255) // 63,
                        (b * 255) // 31,
                    ))

                img.putdata(pix_data)
                img = img.resize((640, 480), Image.NEAREST)
                photo = ImageTk.PhotoImage(img)

                self.preview_canvas.delete("all")
                self.preview_canvas.create_image(320, 240, image=photo)
                self.preview_canvas.image = photo
            except Exception as e:
                self._preview_print(f"Ошибка отрисовки: {e}")
        elif not ok:
            self._preview_print(f"GetPreview: {data}")

        if self.preview_running:
            self.preview_after_id = self.after(interval, self._preview_tick)

    def _preview_save(self):
        target = filedialog.asksaveasfilename(
            title="SavePreview", initialfile="preview.bmp",
            defaultextension=".bmp")

        if not target:
            return

        def worker():
            fn = getattr(rm, "SavePreview", None)
            ok, val = try_call(fn, target)
            self.after(0, lambda: self._preview_print(
                f"SavePreview: " + ("OK" if ok else f"ошибка {val}")))

        threading.Thread(target=worker, daemon=True).start()

    # ======================================================================
    #  ВКЛАДКА 9. КОНСОЛЬ
    # ======================================================================

    def _tab_console(self, nb):
        frame = ttk.Frame(nb, padding=10)
        nb.add(frame, text="Консоль")

        unlock = ttk.LabelFrame(frame, text="Unlock Extended Commands")
        unlock.pack(fill=tk.X, pady=(0, 8))

        ttk.Label(unlock, text="Пароль:").grid(row=0, column=0, padx=4, pady=4, sticky='w')
        self.unlock_pass_var = tk.StringVar(value=DEFAULT_UNLOCK_PASSWORD)
        ttk.Entry(unlock, textvariable=self.unlock_pass_var, width=30).grid(
            row=0, column=1, padx=4, pady=4, sticky='we')
        ttk.Button(unlock, text="Unlock",
                   command=self._on_unlock).grid(row=0, column=2, padx=4, pady=4)

        gen = ttk.LabelFrame(frame, text="GenericCmd")
        gen.pack(fill=tk.X, pady=(0, 8))

        self.preset_commands = {
            "SetSerialNum": {
                "cmd": "0x032a", "v1": "0x00001d7e", "v2": "0x000005de",
                "v3": "0", "v4": "0", "v5": "0", "v6": "0", "string": "0",
            },
            "BackupCalibData (text)": {
                "cmd": "0x0167", "v1": "0x00bc614e", "v2": "0x00001fa9",
                "v3": "0x0000", "v4": "0", "v5": "0", "v6": "0", "string": "",
            },
            "BackupCalibData (binary)": {
                "cmd": "0x0167", "v1": "0x00bc614e", "v2": "0x00001fa9",
                "v3": "0x1d7e", "v4": "0", "v5": "0", "v6": "0", "string": "",
            },
            "GetMultiColorCmd": {
                "cmd": "0x7823", "v1": "0", "v2": "0", "v3": "0",
                "v4": "0", "v5": "0", "v6": "0", "string": "",
            },
        }

        ttk.Label(gen, text="Команда:").grid(row=0, column=0, padx=4, pady=4, sticky='w')
        self.gen_cmd_var = tk.StringVar(value="")
        self.gen_cmd_combo = ttk.Combobox(gen, textvariable=self.gen_cmd_var,
                                          values=list(self.preset_commands.keys()),
                                          width=30)
        self.gen_cmd_combo.grid(row=0, column=1, padx=4, pady=4, sticky='we')
        self.gen_cmd_combo.bind('<<ComboboxSelected>>', self._on_preset_selected)

        params = ['v1', 'v2', 'v3', 'v4', 'v5', 'v6']
        self.gen_param_vars = {}
        for i, p in enumerate(params):
            ttk.Label(gen, text=f"{p}:").grid(row=1, column=i*2, padx=2, pady=2, sticky='e')
            var = tk.StringVar(value="0")
            self.gen_param_vars[p] = var
            ttk.Entry(gen, textvariable=var, width=12).grid(
                row=1, column=i*2+1, padx=2, pady=2)

        ttk.Label(gen, text="String:").grid(row=2, column=0, padx=4, pady=4, sticky='w')
        self.gen_string_var = tk.StringVar(value="")
        ttk.Entry(gen, textvariable=self.gen_string_var, width=50).grid(
            row=2, column=1, columnspan=5, padx=4, pady=4, sticky='we')

        ttk.Button(gen, text="Отправить GenericCmd",
                   command=self._console_generic).grid(row=3, column=1,
                                                       padx=4, pady=4, sticky='w')

        self.console_log = tk.Text(frame, height=20, font=("Consolas", 10),
                                   state=tk.DISABLED, wrap=tk.NONE)
        self.console_log.pack(fill=tk.BOTH, expand=True)

    def _on_preset_selected(self, event=None):
        name = self.gen_cmd_var.get()
        if name in self.preset_commands:
            preset = self.preset_commands[name]
            self.gen_cmd_var.set(preset['cmd'])
            for p in ['v1', 'v2', 'v3', 'v4', 'v5', 'v6']:
                self.gen_param_vars[p].set(preset.get(p, '0'))
            self.gen_string_var.set(preset.get('string', ''))

    def _console_print(self, text):
        self.console_log.config(state=tk.NORMAL)
        self.console_log.insert(tk.END, text + "\n")
        self.console_log.see(tk.END)
        self.console_log.config(state=tk.DISABLED)

    def _on_unlock(self):
        password = self.unlock_pass_var.get().strip()
        if not password:
            messagebox.showwarning("Пароль", "Введите пароль")
            return

        def worker():
            fn = getattr(rm, "UnlockExtendedCommands", None)
            ok, val = try_call(fn, password)
            if ok:
                self.after(0, lambda: self._console_print(
                    f"UnlockExtendedCommands -> OK (пароль: {password!r})"))
                self.after(0, lambda: self._set_status(
                    "Extended commands разблокированы"))
            else:
                self.after(0, lambda: self._console_print(
                    f"UnlockExtendedCommands -> ошибка: {val}"))

        threading.Thread(target=worker, daemon=True).start()

    def _console_generic(self):
        cmd_str = self.gen_cmd_var.get().strip()
        if not cmd_str:
            return

        try:
            cmd = int(cmd_str, 0)
        except Exception:
            self._console_print(f"Неверный формат команды: {cmd_str}")
            return

        params = []
        for p in ['v1', 'v2', 'v3', 'v4', 'v5', 'v6']:
            try:
                params.append(int(self.gen_param_vars[p].get(), 0))
            except Exception:
                self._console_print(f"Неверный формат {p}")
                return

        string = self.gen_string_var.get()

        def worker():
            fn = getattr(rm, "GenericCmd", None)
            if fn is None:
                self.after(0, lambda: self._console_print("GenericCmd нет"))
                return
            ok, val = try_call(fn, cmd, params[0], params[1], params[2],
                               params[3], params[4], params[5], string)
            if ok:
                self.after(0, lambda: self._console_print(
                    f"GenericCmd(0x{cmd:04x}, {params}, {string!r}) -> OK"))
            else:
                self.after(0, lambda: self._console_print(
                    f"GenericCmd(0x{cmd:04x}) -> ошибка: {val}"))

        threading.Thread(target=worker, daemon=True).start()

    # ======================================================================
    #  ПОДКЛЮЧЕНИЕ И СЛУЖЕБНЫЕ
    # ======================================================================

    def _connect_async(self):
        if self.busy:
            return
        self._set_busy(True, "Подключение к RM200...")

        def worker():
            try:
                safe_command(rm.Connect)
                fw = None
                try:
                    fw = safe_command(rm.GetFWVersion)
                except Exception:
                    try:
                        ok, fw = try_call(getattr(rm, "GetFWInfo", None))
                    except Exception:
                        pass
                sn = None
                try:
                    sn = safe_command(rm.GetSerialNum)
                except Exception:
                    pass
                cnt = safe_command(rm.GetNumberOfEntries)
                dev_time = None
                for fname in ("GetTimeString", "GetTime", "GetDateTime", "GetRTCTime"):
                    fn = getattr(rm, fname, None)
                    if fn is not None:
                        try:
                            dev_time = safe_command(fn)
                            break
                        except Exception:
                            pass
                self.after(0, lambda: self._on_connect_ok(fw, sn, cnt, dev_time))
            except Exception as e:
                self.after(0, lambda: self._on_connect_fail(e))

        threading.Thread(target=worker, daemon=True).start()

    def _on_connect_ok(self, fw, sn, cnt, dev_time):
        self.connected = True
        self.device_info = {'fw': fw, 'sn': sn, 'count': cnt, 'dev_time': dev_time}
        self._set_busy(False)
        self._update_status_bar()
        self._refresh_file_info_async()

    def _on_connect_fail(self, e):
        self.connected = False
        self._set_busy(False)
        self._set_status(f"Нет подключения: {e}")
        messagebox.showerror(
            "Ошибка подключения",
            f"Не удалось подключиться к RM200:\n{e}\n\n"
            "Проверьте USB и нажмите 'Переподключить RM200'."
        )

    def _refresh_file_info_async(self):
        if not self.connected:
            return

        def worker():
            try:
                data = safe_command(rm.FetchFile, "MeasDataV05.dat")
                records = parse_measdata(data)
                newest = newest_record(records)
                self.after(0, lambda: self._on_file_info(newest, records, None))
            except Exception as e:
                self.after(0, lambda: self._on_file_info(None, None, e))

        threading.Thread(target=worker, daemon=True).start()

    def _on_file_info(self, newest, records, error):
        if error:
            self._update_status_bar(extra=f"файл: ошибка чтения ({error})")
            return
        if newest is None:
            self._update_status_bar(extra="файл: нет записей")
            return
        age = record_age_seconds(newest)
        extra = f"Последняя в файле: {newest['datetime']} ({format_age(age)})"
        self._update_status_bar(extra=extra)

    def _menu_reconnect(self):
        def worker():
            ok = self._reconnect_device()
            self.after(0, lambda: self._update_status_bar(
                extra=("переподключение OK" if ok else "переподключение FAIL")))
        threading.Thread(target=worker, daemon=True).start()

    def _menu_reboot(self):
        def worker():
            ok = self._reboot_device()
            self.after(0, lambda: self._update_status_bar(
                extra=("reboot OK" if ok else "reboot FAIL")))
        threading.Thread(target=worker, daemon=True).start()

    def _menu_save_dump(self):
        if not self.connected:
            messagebox.showerror("Ошибка", "Нет подключения")
            return
        target = filedialog.asksaveasfilename(
            title="Сохранить MeasDataV05.dat", initialfile="MeasDataV05.dat")
        if not target:
            return

        def worker():
            try:
                data = safe_command(rm.FetchFile, "MeasDataV05.dat")
                with open(target, 'wb') as f:
                    f.write(data)
                self.after(0, lambda: self._set_status(
                    f"Дамп {len(data)} байт сохранён в {target}"))
            except Exception as e:
                self.after(0, lambda: messagebox.showerror("Ошибка", str(e)))

        threading.Thread(target=worker, daemon=True).start()

    def _menu_screenshot(self):
        self._notebook.select(6)
        self._on_screen_screenshot()

    def _menu_temperature(self):
        ok, val = try_call(getattr(rm, "MeasureTemperature", None))
        messagebox.showinfo("Температура",
                            f"{val!r}" if ok else f"Ошибка: {val}")

    def _menu_about(self):
        messagebox.showinfo(
            "О программе",
            "RM200 Color Advisor\n\n"
            "Измерения эталона/образца, коррекция CMYK, палитры,\n"
            "управление устройством, файлами, fan decks, калибровкой,\n"
            "экраном, клавиатурой, preview и расширенными командами.\n\n"
            "Использует библиотеку rm200lib (raburton)."
        )

    def _reconnect_device(self):
        print("[RECONNECT] Disconnect + Connect...")
        try:
            rm.Disconnect()
        except Exception:
            pass
        time.sleep(1.0)

        for attempt in range(1, RECONNECT_MAX + 1):
            try:
                rm.Connect()
                print(f"[RECONNECT] Успех (попытка {attempt}).")
                try:
                    self.device_info['count'] = safe_command(rm.GetNumberOfEntries)
                except Exception:
                    pass
                self.connected = True
                return True
            except Exception as e:
                print(f"[RECONNECT] Попытка {attempt}: {e}")
                time.sleep(RECONNECT_DELAY)

        self.connected = False
        print("[RECONNECT] Не удалось переподключиться.")
        return False

    def _reboot_device(self):
        reboot_fn = getattr(rm, "Reboot", None)
        if reboot_fn is None:
            print("[REBOOT] В библиотеке нет функции Reboot().")
            return False

        print("[REBOOT] Отправка команды Reboot()...")
        ok, exc = _call_with_timeout(reboot_fn, REBOOT_TIMEOUT)
        if not ok:
            print(f"[REBOOT] Reboot() не сработал: {exc}")
            return False

        for attempt in range(1, RECONNECT_MAX + 1):
            time.sleep(RECONNECT_DELAY)
            try:
                rm.Connect()
                print(f"[REBOOT] Переподключение выполнено (попытка {attempt}).")
                try:
                    self.device_info['count'] = safe_command(rm.GetNumberOfEntries)
                except Exception:
                    pass
                self.connected = True
                return True
            except Exception as e:
                print(f"[REBOOT] Попытка {attempt}: {e}")

        self.connected = False
        print("[REBOOT] Не удалось переподключиться после сброса.")
        return False

    # ======================================================================
    #  ИЗМЕРЕНИЕ / СРАВНЕНИЕ
    # ======================================================================

    def _on_measure(self, side):
        if not self.connected:
            messagebox.showerror("Ошибка", "Нет подключения к RM200")
            return
        if self.busy:
            return

        self._set_busy(True, "Идёт измерение... Нажмите кнопку на RM200.")

        def worker():
            try:
                prev_count = safe_command(rm.GetNumberOfEntries) or 0
                safe_command(rm.TriggerMeasurement, self.aperture)

                deadline = time.time() + self.timeout
                got = False
                while time.time() < deadline:
                    try:
                        cnt = safe_command(rm.GetNumberOfEntries)
                    except Exception:
                        cnt = None
                    if cnt is not None and cnt > prev_count:
                        got = True
                        break
                    time.sleep(POLL_INTERVAL)

                if not got:
                    raise TimeoutError("Измерение не завершилось за отведённое время")

                time.sleep(POST_MEAS_PAUSE)

                if self.reboot_after:
                    self.after(0, lambda: self._set_status("Перезагрузка RM200..."))
                    ok = self._reboot_device()
                    if not ok:
                        self.after(0, lambda: self._set_status(
                            "Не удалось перезагрузить RM200."))
                elif self.reconnect_after:
                    self.after(0, lambda: self._set_status("Переподключение RM200..."))
                    ok = self._reconnect_device()
                    if not ok:
                        self.after(0, lambda: self._set_status(
                            "Не удалось переподключиться к RM200."))

                data = safe_command(rm.FetchFile, "MeasDataV05.dat")
                records = parse_measdata(data)
                if not records:
                    raise RuntimeError("В файле нет валидных записей")

                self.after(0, lambda: self._on_pick_records(side, records, None))
            except Exception as e:
                self.after(0, lambda: self._on_pick_records(side, None, e))

        threading.Thread(target=worker, daemon=True).start()

    def _on_pick_records(self, side, records, error):
        self._set_busy(False)

        if error:
            self._set_status(f"Ошибка измерения: {error}")
            messagebox.showerror("Ошибка измерения", str(error))
            return

        newest = newest_record(records)
        if newest is not None:
            age = record_age_seconds(newest)
            if age is not None and age > MAX_AGE_SECONDS:
                self._set_status(
                    f"[!] Самая свежая запись от {newest['datetime']} "
                    f"({format_age(age)})."
                )
            else:
                self._update_status_bar(
                    extra=f"Последняя в файле: {newest['datetime']} "
                          f"({format_age(age)})"
                )

        chosen = self._show_pick_record_dialog(side, records)
        if chosen is None:
            self._set_status("Измерение не добавлено")
            return

        self.state_data[side]['measurements'].append(chosen['sample_lab'])
        self._update_panel(side)
        side_ru = "эталона" if side == 'ref' else "образца"
        n = len(self.state_data[side]['measurements'])
        self._set_status(
            f"Добавлено {side_ru}: {chosen['datetime']}  "
            f"L={chosen['sample_lab'][0]:.2f} "
            f"a={chosen['sample_lab'][1]:.2f} "
            f"b={chosen['sample_lab'][2]:.2f}  (всего: {n})"
        )

    def _show_pick_record_dialog(self, side, records):
        side_ru = "эталон" if side == 'ref' else "образец"

        state = {'records': sorted(records,
                                   key=lambda r: (r['datetime'], r['counter']),
                                   reverse=True)}

        dlg = tk.Toplevel(self)
        dlg.title(f"Выберите измерение ({side_ru})")
        dlg.transient(self)
        dlg.grab_set()
        dlg.geometry("900x600")
        dlg.minsize(720, 480)

        header_var = tk.StringVar()
        age_var    = tk.StringVar()
        status_var = tk.StringVar(value="")

        ttk.Label(dlg, textvariable=header_var, padding=(8, 8, 8, 2),
                  font=("Segoe UI", 9, "bold")).pack(anchor=tk.W)
        ttk.Label(dlg, textvariable=age_var, padding=(8, 0, 8, 2),
                  font=("Segoe UI", 9)).pack(anchor=tk.W)

        warn_text = ("Если ваш свежий замер ещё не появился — RM200 не сбросил "
                     "данные на флешку.\nИспользуйте «Обновить» / "
                     "«Обновить с перезагрузкой» ниже.")
        ttk.Label(dlg, text=warn_text, foreground="#a00",
                  padding=(8, 4, 8, 8), wraplength=860,
                  justify=tk.LEFT).pack(anchor=tk.W)

        list_frame = ttk.Frame(dlg)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

        scrollbar = ttk.Scrollbar(list_frame, orient=tk.VERTICAL)
        listbox = tk.Listbox(list_frame, font=("Consolas", 10), height=16,
                             yscrollcommand=scrollbar.set)
        scrollbar.config(command=listbox.yview)
        listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        ttk.Label(dlg, textvariable=status_var, padding=(8, 0, 8, 0),
                  foreground="#555").pack(anchor=tk.W)

        result = {'rec': None}

        def update_header():
            total = len(state['records'])
            ram_count = self.device_info.get('count')
            header_var.set(
                f"Записей в файле MeasDataV05.dat: {total}.  "
                f"RAM-счётчик: {ram_count}."
            )
            if state['records']:
                newest = state['records'][0]
                age = record_age_seconds(newest)
                age_var.set(f"Самая свежая: {newest['datetime']} "
                            f"({format_age(age)}).")
            else:
                age_var.set("Нет записей.")

        def rebuild_list():
            listbox.delete(0, tk.END)
            for r in state['records']:
                L, a, b = r['sample_lab']
                tag = " <-- Solid C" if r['id'] == VALID_ID else ""
                age = record_age_seconds(r)
                listbox.insert(
                    tk.END,
                    f"{r['datetime']} ({format_age(age):>11})  "
                    f"L={L:7.3f} a={a:7.3f} b={b:7.3f}"
                    f"  {r['name']!r:12}{tag}"
                )
            if state['records']:
                listbox.selection_set(0)

        update_header()
        rebuild_list()

        btns = ttk.Frame(dlg)
        btns.pack(fill=tk.X, padx=8, pady=8)

        btn_refresh = ttk.Button(btns, text="Обновить",
                                 command=lambda: do_refresh(False))
        btn_refresh.pack(side=tk.LEFT, padx=3)
        btn_refresh_reboot = ttk.Button(btns, text="Обновить с перезагрузкой",
                                        command=lambda: do_refresh(True))
        btn_refresh_reboot.pack(side=tk.LEFT, padx=3)

        btn_cancel = ttk.Button(btns, text="Отмена", command=lambda: on_cancel())
        btn_cancel.pack(side=tk.RIGHT, padx=3)
        btn_add = ttk.Button(btns, text="Добавить", command=lambda: on_ok())
        btn_add.pack(side=tk.RIGHT, padx=3)

        def set_buttons_state(st):
            for b in (btn_refresh, btn_refresh_reboot, btn_add, btn_cancel):
                try:
                    b.config(state=st)
                except Exception:
                    pass

        def safe_after(func, *args):
            try:
                if dlg.winfo_exists():
                    dlg.after(0, lambda: func(*args))
            except Exception:
                pass

        def do_refresh(with_reboot):
            set_buttons_state(tk.DISABLED)
            status_var.set("Перезагрузка..." if with_reboot
                           else "Переподключение...")

            def worker():
                try:
                    ok = self._reboot_device() if with_reboot \
                        else self._reconnect_device()
                    if not ok:
                        raise RuntimeError("Не удалось переподключиться")
                    data = safe_command(rm.FetchFile, "MeasDataV05.dat")
                    new_records = parse_measdata(data)
                    new_sorted = sorted(
                        new_records,
                        key=lambda r: (r['datetime'], r['counter']),
                        reverse=True)
                    safe_after(on_refresh_done, new_sorted, None)
                except Exception as e:
                    safe_after(on_refresh_done, None, e)

            threading.Thread(target=worker, daemon=True).start()

        def on_refresh_done(new_records, error):
            set_buttons_state(tk.NORMAL)
            if error:
                status_var.set(f"Ошибка: {error}")
                return
            state['records'] = new_records
            update_header()
            rebuild_list()
            status_var.set(f"Обновлено. Записей: {len(new_records)}.")
            try:
                self._update_status_bar()
            except Exception:
                pass

        def on_ok():
            sel = listbox.curselection()
            if sel:
                result['rec'] = state['records'][sel[0]]
            dlg.destroy()

        def on_cancel():
            dlg.destroy()

        listbox.bind("<Double-Button-1>", lambda ev: on_ok())
        dlg.protocol("WM_DELETE_WINDOW", on_cancel)

        self.wait_window(dlg)
        return result['rec']

    def _on_import_latest(self, side):
        if not self.connected:
            messagebox.showerror("Ошибка", "Нет подключения к RM200")
            return
        if self.busy:
            return

        self._set_busy(True, "Чтение MeasDataV05.dat...")

        def worker():
            try:
                data = safe_command(rm.FetchFile, "MeasDataV05.dat")
                records = parse_measdata(data)
                if not records:
                    raise RuntimeError("В файле нет валидных записей")
                self.after(0, lambda: self._on_pick_records(side, records, None))
            except Exception as e:
                self.after(0, lambda: self._on_pick_records(side, None, e))

        threading.Thread(target=worker, daemon=True).start()

    def _on_import_both(self):
        if not self.connected:
            messagebox.showerror("Ошибка", "Нет подключения к RM200")
            return
        if self.busy:
            return

        self._set_busy(True, "Чтение MeasDataV05.dat...")

        def worker():
            try:
                data = safe_command(rm.FetchFile, "MeasDataV05.dat")
                records = parse_measdata(data)
                records.sort(key=lambda r: (r['datetime'], r['counter']))
                if len(records) < 2:
                    raise RuntimeError("Нужно минимум 2 записи в файле")
                ref = records[-2]
                smp = records[-1]
                self.after(0, lambda: self._on_import_both_done(ref, smp, None))
            except Exception as e:
                self.after(0, lambda: self._on_import_both_done(None, None, e))

        threading.Thread(target=worker, daemon=True).start()

    def _on_import_both_done(self, ref, smp, error):
        self._set_busy(False)
        if error:
            self._set_status(f"Ошибка импорта: {error}")
            messagebox.showerror("Ошибка", str(error))
            return

        age_ref = record_age_seconds(ref)
        age_smp = record_age_seconds(smp)

        msg = (f"Импортировать две последние записи?\n\n"
               f"Эталон (предпоследняя):\n"
               f"  {ref['datetime']}  ({format_age(age_ref)})\n"
               f"  L*={ref['sample_lab'][0]:.2f} "
               f"a*={ref['sample_lab'][1]:.2f} "
               f"b*={ref['sample_lab'][2]:.2f}\n\n"
               f"Образец (последняя):\n"
               f"  {smp['datetime']}  ({format_age(age_smp)})\n"
               f"  L*={smp['sample_lab'][0]:.2f} "
               f"a*={smp['sample_lab'][1]:.2f} "
               f"b*={smp['sample_lab'][2]:.2f}")

        if messagebox.askyesno("Импорт двух записей", msg):
            self.state_data['ref']['measurements'].append(ref['sample_lab'])
            self.state_data['smp']['measurements'].append(smp['sample_lab'])
            self._update_panel('ref')
            self._update_panel('smp')
            self._set_status("Импортированы две последние записи")
        else:
            self._set_status("Импорт отменён")

    def _on_clear(self, side):
        if not self.state_data[side]['measurements']:
            return
        side_ru = "эталона" if side == 'ref' else "образца"
        if messagebox.askyesno("Очистить", f"Удалить все измерения {side_ru}?"):
            self.state_data[side]['measurements'].clear()
            self._update_panel(side)
            self._set_status(f"Измерения {side_ru} очищены")

    def _update_panel(self, side):
        w = self.widgets[side]
        measurements = self.state_data[side]['measurements']

        w['swatch'].delete("all")
        if not measurements:
            w['swatch'].create_text(150, 60, text="нет данных", fill="#888")
            w['lab_var'].set("—")
        else:
            L = sum(m[0] for m in measurements) / len(measurements)
            a = sum(m[1] for m in measurements) / len(measurements)
            b = sum(m[2] for m in measurements) / len(measurements)
            r, g, b_ = lab_to_rgb(L, a, b)
            color = f"#{r:02x}{g:02x}{b_:02x}"
            w['swatch'].create_rectangle(0, 0, 300, 120,
                                         fill=color, outline=color)
            brightness = (r * 299 + g * 587 + b_ * 114) / 1000
            txt_color = 'black' if brightness > 128 else 'white'
            w['swatch'].create_text(150, 50, text=color.upper(),
                                    fill=txt_color,
                                    font=("Consolas", 12, "bold"))
            w['swatch'].create_text(150, 78,
                                    text=f"среднее по {len(measurements)} изм.",
                                    fill=txt_color, font=("Segoe UI", 8))
            w['lab_var'].set(f"L*={L:7.3f}  a*={a:7.3f}  b*={b:7.3f}")

        w['listbox'].config(state=tk.NORMAL)
        w['listbox'].delete('1.0', tk.END)
        for i, (L, a, b) in enumerate(measurements, 1):
            w['listbox'].insert(tk.END,
                                f"#{i:>2}:  L={L:7.3f}  a={a:7.3f}  b={b:7.3f}\n")
        w['listbox'].config(state=tk.DISABLED)

    def _on_calculate(self):
        # --- Источник эталона ---
        src = self.ref_source_var.get()
        ref_lab = None
        src_label = ""

        if src == 'measure':
            ref_list = self.state_data['ref']['measurements']
            if not ref_list:
                messagebox.showwarning(
                    "Недостаточно данных",
                    "Введите эталон вручную или сделайте измерение.")
                return
            ref_lab = tuple(sum(m[i] for m in ref_list) / len(ref_list)
                            for i in range(3))
            src_label = "Эталон (измерения)"
        elif src == 'cmyk':
            try:
                c = float(self.man_c_var.get())
                m = float(self.man_m_var.get())
                y = float(self.man_y_var.get())
                k = float(self.man_k_var.get())
            except Exception as e:
                messagebox.showerror("Ошибка ввода", f"Некорректный CMYK: {e}")
                return
            ref_lab = cmyk_to_lab(c, m, y, k)
            src_label = f"Эталон (CMYK {c:.0f},{m:.0f},{y:.0f},{k:.0f})"
        elif src == 'rgb':
            try:
                r = int(self.man_r_var.get())
                g = int(self.man_g_var.get())
                b = int(self.man_b_var.get())
            except Exception as e:
                messagebox.showerror("Ошибка ввода", f"Некорректный RGB: {e}")
                return
            ref_lab = srgb_to_lab(r, g, b)
            src_label = f"Эталон (RGB {r},{g},{b})"
        else:
            return

        # --- Образец ---
        smp_list = self.state_data['smp']['measurements']
        if not smp_list:
            messagebox.showwarning(
                "Недостаточно данных",
                "Сделайте хотя бы одно измерение образца.")
            return
        smp_lab = tuple(sum(m[i] for m in smp_list) / len(smp_list)
                        for i in range(3))

        # --- Режим сравнения ---
        palette_name = self.compare_palette_var.get()

        if palette_name == PSEUDO_CMYK:
            text = format_result_cmyk(ref_lab, smp_lab,
                                      icc_path=self.icc,
                                      threshold=self.threshold)
            header = f"=== Режим: CMYK ===\n{src_label}\n" \
                     f"Образец (среднее по {len(smp_list)} изм.)\n\n"
            text = header + text
        else:
            pal = self.palettes.get(palette_name)
            if not pal or not pal['entries']:
                messagebox.showwarning(
                    "Палитра",
                    f"Палитра '{palette_name}' пуста.")
                return
            try:
                n_max = int(self.n_mix_var.get())
                if n_max < 1:
                    n_max = 1
            except Exception:
                n_max = 3

            mix = propose_palette_mix(ref_lab, pal['entries'], n_max)
            text = format_result_palette(ref_lab, smp_lab,
                                         palette_name, mix)
            header = f"=== Режим: Палитра '{palette_name}' ===\n" \
                     f"{src_label}\n" \
                     f"Образец (среднее по {len(smp_list)} изм.)\n\n"
            text = header + text

        self.result_text.delete('1.0', tk.END)
        self.result_text.insert(tk.END, text)
        self._set_status("Расчёт выполнен")

    def _on_close(self):
        self._stop_live_preview()
        self._save_palettes()

        if self.connected:
            try:
                rm.Disconnect()
            except Exception:
                pass
        self.destroy()


# ==========================================================================
#  MAIN
# ==========================================================================

def main():
    ap = argparse.ArgumentParser(description="RM200 Color Advisor (GUI)")
    ap.add_argument("--icc", default=None)
    ap.add_argument("--aperture", type=int, default=2, choices=[0, 1, 2])
    ap.add_argument("--timeout", type=float, default=180.0)
    ap.add_argument("--threshold", type=float, default=1.0)

    g = ap.add_mutually_exclusive_group()
    g.add_argument("--reconnect-after-measure", action="store_true",
                   help="Переподключать RM200 после каждого измерения")
    g.add_argument("--reboot-after-measure", action="store_true",
                   help="Перезагружать RM200 после каждого измерения")

    args = ap.parse_args()

    app = AdvisorApp(aperture=args.aperture, icc=args.icc,
                     timeout=args.timeout, threshold=args.threshold,
                     reboot_after=args.reboot_after_measure,
                     reconnect_after=args.reconnect_after_measure)
    app.mainloop()


if __name__ == "__main__":
    main()
