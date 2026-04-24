from __future__ import annotations

import ctypes
import ctypes.wintypes
import gc
import json
import os
import queue
import subprocess
import sys
import threading
import time
import traceback
from dataclasses import dataclass
from datetime import datetime
from json import JSONDecodeError
from pathlib import Path
from typing import Any, Callable

import mss
from PIL import Image
import tkinter as tk
from tkinter import filedialog, messagebox


def get_app_dir() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


APP_DIR = get_app_dir()
CONFIG_PATH = APP_DIR / "config.json"
ERROR_LOG_PATH = APP_DIR / "region_capture_error.log"
KEY_INPUT_LOG_PATH = APP_DIR / "region_capture_key_input.log"
HOTKEY_PROCESS_LOG_PATH = APP_DIR / "region_capture_hotkey_process.log"
HOTKEY_EVENT_LOG_PATH = APP_DIR / "region_capture_hotkey_event.log"
DEFAULT_CONFIG = {
    "select_hotkey": "Ctrl+Alt+S",
    "quick_capture_hotkey": "Ctrl+Alt+C",
    "auto_capture_hotkey": "Ctrl+Alt+A",
    "output_dir": r"%USERPROFILE%\Pictures\RegionCaptures",
    "filename_prefix": "capture",
    "image_format": "png",
    "open_folder_after_capture": False,
    "hotkeys_enabled": True,
    "last_region": None,
    "auto_capture_interval_seconds": 1.0,
}
MIN_CAPTURE_SIZE = 4
MIN_AUTO_CAPTURE_INTERVAL_SECONDS = 0.2
MAX_AUTO_CAPTURE_INTERVAL_SECONDS = 3600.0
ENABLE_LOW_LEVEL_HOTKEY_HOOK = True
WM_HOTKEY = 0x0312
WM_QUIT = 0x0012
WH_KEYBOARD_LL = 13
WM_KEYDOWN = 0x0100
WM_KEYUP = 0x0101
WM_SYSKEYDOWN = 0x0104
WM_SYSKEYUP = 0x0105
GWLP_WNDPROC = -4
LLKHF_ALTDOWN = 0x20
VK_SHIFT = 0x10
VK_CONTROL = 0x11
VK_MENU = 0x12
VK_LWIN = 0x5B
VK_RWIN = 0x5C
VK_LSHIFT = 0xA0
VK_RSHIFT = 0xA1
VK_LCONTROL = 0xA2
VK_RCONTROL = 0xA3
VK_LMENU = 0xA4
VK_RMENU = 0xA5
MOD_ALT = 0x0001
MOD_CONTROL = 0x0002
MOD_SHIFT = 0x0004
MOD_WIN = 0x0008
MOD_NOREPEAT = 0x4000

VK_BY_NAME = {
    "BACKSPACE": 0x08,
    "TAB": 0x09,
    "ENTER": 0x0D,
    "ESC": 0x1B,
    "ESCAPE": 0x1B,
    "SPACE": 0x20,
    "PAGEUP": 0x21,
    "PAGEDOWN": 0x22,
    "END": 0x23,
    "HOME": 0x24,
    "LEFT": 0x25,
    "UP": 0x26,
    "RIGHT": 0x27,
    "DOWN": 0x28,
    "INSERT": 0x2D,
    "DELETE": 0x2E,
    ".": 0x6E,
    "DECIMAL": 0x6E,
    "NUMDECIMAL": 0x6E,
    "NUMPADDECIMAL": 0x6E,
    "KP_DECIMAL": 0x6E,
    "KP_DELETE": 0x6E,
    "PERIOD": 0xBE,
    "OEM_PERIOD": 0xBE,
}
for index in range(1, 25):
    VK_BY_NAME[f"F{index}"] = 0x70 + index - 1
for index in range(0, 10):
    VK_BY_NAME[f"NUM{index}"] = 0x60 + index
    VK_BY_NAME[f"KP_{index}"] = 0x60 + index


class KBDLLHOOKSTRUCT(ctypes.Structure):
    _fields_ = [
        ("vkCode", ctypes.wintypes.DWORD),
        ("scanCode", ctypes.wintypes.DWORD),
        ("flags", ctypes.wintypes.DWORD),
        ("time", ctypes.wintypes.DWORD),
        ("dwExtraInfo", ctypes.c_void_p),
    ]


LowLevelKeyboardProc = ctypes.WINFUNCTYPE(
    ctypes.c_ssize_t,
    ctypes.c_int,
    ctypes.wintypes.WPARAM,
    ctypes.wintypes.LPARAM,
) if sys.platform == "win32" else None

WindowProc = ctypes.WINFUNCTYPE(
    ctypes.c_ssize_t,
    ctypes.wintypes.HWND,
    ctypes.wintypes.UINT,
    ctypes.wintypes.WPARAM,
    ctypes.wintypes.LPARAM,
) if sys.platform == "win32" else None


@dataclass
class CaptureConfig:
    select_hotkey: str
    quick_capture_hotkey: str
    auto_capture_hotkey: str
    output_dir: Path
    filename_prefix: str
    image_format: str
    open_folder_after_capture: bool
    hotkeys_enabled: bool
    last_region: tuple[int, int, int, int] | None
    auto_capture_interval_seconds: float


def enable_dpi_awareness() -> None:
    if sys.platform != "win32":
        return

    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass


def normalize_region(raw: Any) -> tuple[int, int, int, int] | None:
    if not isinstance(raw, list | tuple) or len(raw) != 4:
        return None
    try:
        left, top, right, bottom = [int(value) for value in raw]
    except (TypeError, ValueError):
        return None
    if right - left < MIN_CAPTURE_SIZE or bottom - top < MIN_CAPTURE_SIZE:
        return None
    return left, top, right, bottom


def normalize_auto_capture_interval(raw: Any) -> float:
    try:
        interval = float(raw)
    except (TypeError, ValueError):
        interval = float(DEFAULT_CONFIG["auto_capture_interval_seconds"])
    return max(MIN_AUTO_CAPTURE_INTERVAL_SECONDS, min(MAX_AUTO_CAPTURE_INTERVAL_SECONDS, interval))


def backup_broken_config() -> None:
    if not CONFIG_PATH.exists():
        return
    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    backup_path = APP_DIR / f"config.broken-{stamp}.json"
    try:
        CONFIG_PATH.replace(backup_path)
    except OSError:
        pass


def append_log(path: Path, message: str) -> None:
    stamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    try:
        with path.open("a", encoding="utf-8") as file:
            file.write(f"[{stamp}] {message}\n")
    except OSError:
        pass


def log_error(message: str) -> None:
    append_log(ERROR_LOG_PATH, message)


def log_key_input(message: str) -> None:
    append_log(KEY_INPUT_LOG_PATH, message)


def log_hotkey_process(message: str) -> None:
    append_log(HOTKEY_PROCESS_LOG_PATH, message)


def log_hotkey_event(message: str) -> None:
    append_log(HOTKEY_EVENT_LOG_PATH, message)


def normalize_hotkey_text(raw: Any, fallback: str) -> str:
    text = str(raw).strip()
    if not text:
        return fallback
    replacements = {
        "<ctrl>": "Ctrl",
        "<control>": "Ctrl",
        "<shift>": "Shift",
        "<alt>": "Alt",
        "<cmd>": "Win",
        "<win>": "Win",
    }
    normalized = text.lower()
    for source, target in replacements.items():
        normalized = normalized.replace(source, target)
    return "+".join(part.strip() for part in normalized.split("+") if part.strip())


def config_to_json(config: CaptureConfig) -> dict[str, Any]:
    return {
        "select_hotkey": config.select_hotkey,
        "quick_capture_hotkey": config.quick_capture_hotkey,
        "auto_capture_hotkey": config.auto_capture_hotkey,
        "output_dir": str(config.output_dir),
        "filename_prefix": config.filename_prefix,
        "image_format": config.image_format,
        "open_folder_after_capture": config.open_folder_after_capture,
        "hotkeys_enabled": config.hotkeys_enabled,
        "last_region": list(config.last_region) if config.last_region else None,
        "auto_capture_interval_seconds": config.auto_capture_interval_seconds,
    }


def load_config() -> CaptureConfig:
    if not CONFIG_PATH.exists():
        save_raw_config(DEFAULT_CONFIG)

    try:
        raw: dict[str, Any] = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
    except (JSONDecodeError, OSError) as exc:
        log_error(f"config load failed: {exc}")
        backup_broken_config()
        raw = dict(DEFAULT_CONFIG)
        save_raw_config(raw)
    if "hotkey" in raw and "select_hotkey" not in raw:
        raw["select_hotkey"] = raw["hotkey"]

    merged = {**DEFAULT_CONFIG, **raw}
    output_dir = Path(os.path.expandvars(str(merged["output_dir"]))).expanduser()
    image_format = str(merged["image_format"]).lower().strip(".")
    if image_format not in {"png", "jpg", "jpeg", "bmp"}:
        image_format = "png"

    return CaptureConfig(
        select_hotkey=normalize_hotkey_text(merged["select_hotkey"], DEFAULT_CONFIG["select_hotkey"]),
        quick_capture_hotkey=normalize_hotkey_text(
            merged["quick_capture_hotkey"],
            DEFAULT_CONFIG["quick_capture_hotkey"],
        ),
        auto_capture_hotkey=normalize_hotkey_text(
            merged["auto_capture_hotkey"],
            DEFAULT_CONFIG["auto_capture_hotkey"],
        ),
        output_dir=output_dir,
        filename_prefix=str(merged["filename_prefix"]).strip() or "capture",
        image_format=image_format,
        open_folder_after_capture=bool(merged["open_folder_after_capture"]),
        hotkeys_enabled=bool(merged["hotkeys_enabled"]),
        last_region=normalize_region(merged.get("last_region")),
        auto_capture_interval_seconds=normalize_auto_capture_interval(
            merged.get("auto_capture_interval_seconds")
        ),
    )


def save_config(config: CaptureConfig) -> None:
    save_raw_config(config_to_json(config))


def save_raw_config(payload: dict[str, Any]) -> None:
    tmp_path = CONFIG_PATH.with_suffix(".json.tmp")
    tmp_path.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    tmp_path.replace(CONFIG_PATH)


def parse_hotkey(text: str) -> tuple[int, int]:
    parts = [part.strip().upper() for part in text.replace(" ", "").split("+") if part.strip()]
    if not parts:
        raise ValueError("단축키가 비어 있습니다.")

    modifiers = MOD_NOREPEAT
    key_name = ""
    for part in parts:
        if part in {"CTRL", "CONTROL"}:
            modifiers |= MOD_CONTROL
        elif part == "ALT":
            modifiers |= MOD_ALT
        elif part == "SHIFT":
            modifiers |= MOD_SHIFT
        elif part in {"WIN", "WINDOWS", "CMD"}:
            modifiers |= MOD_WIN
        else:
            key_name = part

    if not key_name:
        raise ValueError("마지막 키를 함께 입력해야 합니다. 예: Ctrl+Alt+S")
    if len(key_name) == 1 and "A" <= key_name <= "Z":
        return modifiers, ord(key_name)
    if len(key_name) == 1 and "0" <= key_name <= "9":
        return modifiers, ord(key_name)
    if key_name in VK_BY_NAME:
        return modifiers, VK_BY_NAME[key_name]
    raise ValueError(f"지원하지 않는 키입니다: {key_name}")


def format_modifiers(modifiers: int) -> str:
    labels: list[str] = []
    if modifiers & MOD_CONTROL:
        labels.append("Ctrl")
    if modifiers & MOD_ALT:
        labels.append("Alt")
    if modifiers & MOD_SHIFT:
        labels.append("Shift")
    if modifiers & MOD_WIN:
        labels.append("Win")
    return "+".join(labels) or "None"


def format_vk(vk: int) -> str:
    preferred = {
        0x60: "Num0",
        0x61: "Num1",
        0x62: "Num2",
        0x63: "Num3",
        0x64: "Num4",
        0x65: "Num5",
        0x66: "Num6",
        0x67: "Num7",
        0x68: "Num8",
        0x69: "Num9",
        0x6E: "NumDecimal",
        0xBE: "Period",
    }
    if vk in preferred:
        return preferred[vk]
    if 0x41 <= vk <= 0x5A or 0x30 <= vk <= 0x39:
        return chr(vk)
    for name, code in VK_BY_NAME.items():
        if code == vk:
            return name
    return f"VK{vk}"


def get_event_keycode(event: tk.Event) -> int:
    try:
        return int(getattr(event, "keycode", 0))
    except (TypeError, ValueError):
        return 0


def is_windows_key_down(*vks: int) -> bool:
    if sys.platform != "win32":
        return False
    user32 = ctypes.windll.user32
    try:
        user32.GetAsyncKeyState.argtypes = [ctypes.c_int]
        user32.GetAsyncKeyState.restype = ctypes.c_short
        user32.GetKeyState.argtypes = [ctypes.c_int]
        user32.GetKeyState.restype = ctypes.c_short
        return any(
            (user32.GetAsyncKeyState(vk) & 0x8000) or (user32.GetKeyState(vk) & 0x8000)
            for vk in vks
        )
    except Exception as exc:
        log_key_input(f"windows key state lookup failed: {exc}")
        return False


def grab_virtual_screen() -> tuple[Image.Image, dict[str, int]]:
    with mss.MSS() as sct:
        monitor = sct.monitors[0]
        shot = sct.grab(monitor)
        image = Image.frombytes("RGB", shot.size, shot.rgb)
        return image, normalize_monitor(monitor)


def get_virtual_monitor() -> dict[str, int]:
    with mss.MSS() as sct:
        return normalize_monitor(sct.monitors[0])


def normalize_monitor(monitor: dict[str, Any]) -> dict[str, int]:
    return {
        "left": int(monitor["left"]),
        "top": int(monitor["top"]),
        "width": int(monitor["width"]),
        "height": int(monitor["height"]),
    }


def crop_region_from_screen(region: tuple[int, int, int, int]) -> Image.Image:
    left, top, right, bottom = region
    with mss.MSS() as sct:
        shot = sct.grab(
            {
                "left": left,
                "top": top,
                "width": right - left,
                "height": bottom - top,
            }
        )
        return Image.frombytes("RGB", shot.size, shot.rgb)


class WindowsHotkeyManager:
    def __init__(self, root: tk.Tk, on_error: Callable[[str], None]) -> None:
        self.root = root
        self.on_error = on_error
        self.main_thread_id = threading.get_ident()
        self.thread: threading.Thread | None = None
        self.thread_id: int | None = None
        self.stop_event = threading.Event()
        self.callbacks: dict[int, Callable[[], None]] = {}
        self.hotkey_specs: dict[int, tuple[int, int]] = {}
        self.registered_ids: set[int] = set()
        self.hwnd: int | None = None
        self.window_proc = None
        self.old_window_proc: int | None = None
        self.hook_handle: int | None = None
        self.hook_proc = None
        self.pressed_keys: set[int] = set()
        self.last_triggered_at: dict[int, float] = {}
        self.pending_hotkeys: queue.Queue[int] = queue.Queue()
        self.pending_after_id: str | None = None
        self.ready = threading.Event()
        self.lock = threading.Lock()

    def start(self, hotkeys: dict[int, tuple[str, Callable[[], None]]]) -> bool:
        if sys.platform != "win32":
            self.on_error("전역 단축키 등록은 Windows에서만 지원됩니다.")
            return False

        log_hotkey_process(
            "start requested: "
            + ", ".join(f"id={hotkey_id} text={text}" for hotkey_id, (text, _) in hotkeys.items())
        )
        self.stop()
        self.callbacks = {hotkey_id: callback for hotkey_id, (_, callback) in hotkeys.items()}
        self.hotkey_specs = {}
        self.last_triggered_at = {}
        self._start_pending_pump()

        for hotkey_id, (text, _) in hotkeys.items():
            try:
                modifiers, vk = parse_hotkey(text)
            except ValueError as exc:
                self.notify_error(f"{text}: {exc}")
                continue
            clean_modifiers = modifiers & ~MOD_NOREPEAT
            self.hotkey_specs[hotkey_id] = (clean_modifiers, vk)
            log_hotkey_process(
                f"parsed id={hotkey_id} text={text} modifiers={format_modifiers(clean_modifiers)} "
                f"vk={format_vk(vk)}({vk})"
            )

        hwnd = self._ensure_window_proc()
        if hwnd:
            self._register_hotkeys(hwnd, hotkeys)
        self._start_keyboard_hook_thread()
        if self.thread:
            self.ready.wait(timeout=2.0)
        with self.lock:
            ok = bool(self.registered_ids or self.hook_handle)
        log_hotkey_process(
            f"start result ok={ok} hwnd={self.hwnd} registered={sorted(self.registered_ids)} "
            f"hook={bool(self.hook_handle)}"
        )
        return ok

    def stop(self) -> None:
        if sys.platform != "win32":
            return
        log_hotkey_process("stop requested")
        self._stop_pending_pump()
        user32 = ctypes.windll.user32
        kernel32 = ctypes.windll.kernel32
        self._configure_windows_api(user32, kernel32)
        hwnd = self.hwnd
        for hotkey_id in list(self.registered_ids):
            if hwnd:
                if user32.UnregisterHotKey(hwnd, hotkey_id):
                    log_hotkey_process(f"UnregisterHotKey ok id={hotkey_id} hwnd={hwnd}")
                else:
                    log_hotkey_process(f"UnregisterHotKey failed id={hotkey_id} hwnd={hwnd}")
        self.registered_ids = set()
        if self.hook_handle:
            if user32.UnhookWindowsHookEx(self.hook_handle):
                log_hotkey_process(f"UnhookWindowsHookEx ok handle={int(self.hook_handle)}")
            else:
                log_hotkey_process(f"UnhookWindowsHookEx failed handle={int(self.hook_handle)}")
        with self.lock:
            thread_id = self.thread_id
        if thread_id:
            user32.PostThreadMessageW(thread_id, WM_QUIT, 0, 0)
        if self.thread and self.thread.is_alive() and self.thread is not threading.current_thread():
            self.thread.join(timeout=1.0)
        self.thread = None
        self.thread_id = None
        self.callbacks = {}
        self.hotkey_specs = {}
        self.hook_handle = None
        self.hook_proc = None
        self.pressed_keys = set()
        self.last_triggered_at = {}

    def dispose(self) -> None:
        self.stop()
        self._restore_window_proc()

    def _configure_windows_api(self, user32, kernel32) -> None:
        if LowLevelKeyboardProc is not None:
            user32.SetWindowsHookExW.argtypes = [
                ctypes.c_int,
                LowLevelKeyboardProc,
                ctypes.wintypes.HINSTANCE,
                ctypes.wintypes.DWORD,
            ]
        user32.SetWindowsHookExW.restype = ctypes.wintypes.HHOOK
        user32.CallNextHookEx.argtypes = [
            ctypes.wintypes.HHOOK,
            ctypes.c_int,
            ctypes.wintypes.WPARAM,
            ctypes.wintypes.LPARAM,
        ]
        user32.CallNextHookEx.restype = ctypes.c_ssize_t
        user32.UnhookWindowsHookEx.argtypes = [ctypes.wintypes.HHOOK]
        user32.UnhookWindowsHookEx.restype = ctypes.wintypes.BOOL
        user32.RegisterHotKey.argtypes = [
            ctypes.wintypes.HWND,
            ctypes.c_int,
            ctypes.wintypes.UINT,
            ctypes.wintypes.UINT,
        ]
        user32.RegisterHotKey.restype = ctypes.wintypes.BOOL
        user32.UnregisterHotKey.argtypes = [ctypes.wintypes.HWND, ctypes.c_int]
        user32.UnregisterHotKey.restype = ctypes.wintypes.BOOL
        user32.GetMessageW.argtypes = [
            ctypes.POINTER(ctypes.wintypes.MSG),
            ctypes.wintypes.HWND,
            ctypes.wintypes.UINT,
            ctypes.wintypes.UINT,
        ]
        user32.GetMessageW.restype = ctypes.c_int
        user32.GetAsyncKeyState.argtypes = [ctypes.c_int]
        user32.GetAsyncKeyState.restype = ctypes.c_short
        user32.GetKeyState.argtypes = [ctypes.c_int]
        user32.GetKeyState.restype = ctypes.c_short
        user32.PostThreadMessageW.argtypes = [
            ctypes.wintypes.DWORD,
            ctypes.wintypes.UINT,
            ctypes.wintypes.WPARAM,
            ctypes.wintypes.LPARAM,
        ]
        user32.PostThreadMessageW.restype = ctypes.wintypes.BOOL
        user32.CallWindowProcW.argtypes = [
            ctypes.c_void_p,
            ctypes.wintypes.HWND,
            ctypes.wintypes.UINT,
            ctypes.wintypes.WPARAM,
            ctypes.wintypes.LPARAM,
        ]
        user32.CallWindowProcW.restype = ctypes.c_ssize_t
        user32.DefWindowProcW.argtypes = [
            ctypes.wintypes.HWND,
            ctypes.wintypes.UINT,
            ctypes.wintypes.WPARAM,
            ctypes.wintypes.LPARAM,
        ]
        user32.DefWindowProcW.restype = ctypes.c_ssize_t
        if hasattr(user32, "SetWindowLongPtrW"):
            user32.SetWindowLongPtrW.argtypes = [
                ctypes.wintypes.HWND,
                ctypes.c_int,
                ctypes.c_void_p,
            ]
            user32.SetWindowLongPtrW.restype = ctypes.c_void_p
        user32.SetWindowLongW.argtypes = [
            ctypes.wintypes.HWND,
            ctypes.c_int,
            ctypes.c_long,
        ]
        user32.SetWindowLongW.restype = ctypes.c_long
        kernel32.GetCurrentThreadId.restype = ctypes.wintypes.DWORD
        kernel32.GetModuleHandleW.argtypes = [ctypes.wintypes.LPCWSTR]
        kernel32.GetModuleHandleW.restype = ctypes.wintypes.HMODULE
        kernel32.GetLastError.restype = ctypes.wintypes.DWORD
        kernel32.SetLastError.argtypes = [ctypes.wintypes.DWORD]

    def notify_error(self, message: str) -> None:
        log_error(message)
        log_hotkey_process(f"error: {message}")
        try:
            self.root.after(0, self.on_error, message)
        except tk.TclError:
            pass

    def notify_status(self, message: str) -> None:
        log_hotkey_process(f"status: {message}")
        try:
            self.root.after(0, self.on_error, message)
        except tk.TclError:
            pass

    def trigger_hotkey(self, hotkey_id: int) -> None:
        if threading.get_ident() != self.main_thread_id:
            self.pending_hotkeys.put(hotkey_id)
            log_hotkey_event(f"trigger queued id={hotkey_id}")
            return
        self._trigger_hotkey_now(hotkey_id)

    def _trigger_hotkey_now(self, hotkey_id: int) -> None:
        callback = self.callbacks.get(hotkey_id)
        if callback is None:
            return
        now = time.monotonic()
        if now - self.last_triggered_at.get(hotkey_id, 0.0) < 0.25:
            log_hotkey_event(f"trigger ignored debounce id={hotkey_id}")
            return
        self.last_triggered_at[hotkey_id] = now
        log_hotkey_event(f"trigger id={hotkey_id}")
        try:
            self.root.after(0, callback)
        except tk.TclError:
            pass

    def _start_pending_pump(self) -> None:
        self._stop_pending_pump()
        try:
            self.pending_after_id = self.root.after(40, self._drain_pending_hotkeys)
        except tk.TclError:
            self.pending_after_id = None

    def _stop_pending_pump(self) -> None:
        if self.pending_after_id is not None:
            try:
                self.root.after_cancel(self.pending_after_id)
            except tk.TclError:
                pass
            self.pending_after_id = None
        while True:
            try:
                self.pending_hotkeys.get_nowait()
            except queue.Empty:
                break

    def _drain_pending_hotkeys(self) -> None:
        self.pending_after_id = None
        handled = 0
        while handled < 50:
            try:
                hotkey_id = self.pending_hotkeys.get_nowait()
            except queue.Empty:
                break
            self._trigger_hotkey_now(hotkey_id)
            handled += 1
        if self.callbacks:
            try:
                self.pending_after_id = self.root.after(40, self._drain_pending_hotkeys)
            except tk.TclError:
                self.pending_after_id = None

    def _ensure_window_proc(self) -> int | None:
        if WindowProc is None:
            return None
        if self.hwnd and self.window_proc and self.old_window_proc:
            return self.hwnd

        user32 = ctypes.windll.user32
        kernel32 = ctypes.windll.kernel32
        self._configure_windows_api(user32, kernel32)

        try:
            self.root.update_idletasks()
            hwnd = int(self.root.winfo_id())
        except tk.TclError as exc:
            self.notify_error(f"단축키 윈도우 핸들을 가져오지 못했습니다: {exc}")
            return None
        if not hwnd:
            self.notify_error("단축키 윈도우 핸들이 비어 있습니다.")
            return None

        def proc(hwnd_value, message, w_param, l_param) -> int:
            try:
                if message == WM_HOTKEY:
                    hotkey_id = int(w_param)
                    packed = int(l_param) & 0xFFFFFFFF
                    modifiers = packed & 0xFFFF
                    vk = (packed >> 16) & 0xFFFF
                    log_hotkey_event(
                        f"WM_HOTKEY hwnd={int(hwnd_value)} id={hotkey_id} "
                        f"modifiers={format_modifiers(modifiers)} vk={format_vk(vk)}({vk})"
                    )
                    if hotkey_id in self.callbacks:
                        self.pending_hotkeys.put(hotkey_id)
                        log_hotkey_event(f"WM_HOTKEY queued id={hotkey_id}")
                        return 0
            except Exception as exc:
                log_error(f"WM_HOTKEY handling failed: {exc}")

            if self.old_window_proc:
                return int(
                    user32.CallWindowProcW(
                        ctypes.c_void_p(self.old_window_proc),
                        hwnd_value,
                        message,
                        w_param,
                        l_param,
                    )
                )
            return int(user32.DefWindowProcW(hwnd_value, message, w_param, l_param))

        self.window_proc = WindowProc(proc)
        new_proc = ctypes.cast(self.window_proc, ctypes.c_void_p).value
        if not new_proc:
            self.notify_error("단축키 메시지 처리기를 만들지 못했습니다.")
            return None

        old_proc, error_code = self._set_window_proc(hwnd, new_proc)
        if not old_proc and error_code:
            self.window_proc = None
            self.notify_error(f"단축키 메시지 연결 실패: {error_code}")
            return None

        self.hwnd = hwnd
        self.old_window_proc = old_proc
        log_hotkey_process(f"window proc installed hwnd={hwnd} old_proc={old_proc}")
        return hwnd

    def _restore_window_proc(self) -> None:
        if sys.platform != "win32" or not self.hwnd or not self.old_window_proc:
            return
        old_proc = self.old_window_proc
        hwnd = self.hwnd
        restored, error_code = self._set_window_proc(hwnd, old_proc)
        if restored or not error_code:
            log_hotkey_process(f"window proc restored hwnd={hwnd}")
        else:
            log_hotkey_process(f"window proc restore failed hwnd={hwnd} error={error_code}")
        self.hwnd = None
        self.old_window_proc = None
        self.window_proc = None

    def _set_window_proc(self, hwnd: int, proc_pointer: int) -> tuple[int, int]:
        user32 = ctypes.windll.user32
        kernel32 = ctypes.windll.kernel32
        self._configure_windows_api(user32, kernel32)
        kernel32.SetLastError(0)
        if ctypes.sizeof(ctypes.c_void_p) == 8 and hasattr(user32, "SetWindowLongPtrW"):
            result = user32.SetWindowLongPtrW(
                ctypes.wintypes.HWND(hwnd),
                GWLP_WNDPROC,
                ctypes.c_void_p(proc_pointer),
            )
            value = int(result or 0)
        else:
            result = user32.SetWindowLongW(
                ctypes.wintypes.HWND(hwnd),
                GWLP_WNDPROC,
                ctypes.c_long(proc_pointer),
            )
            value = int(result or 0)
        error_code = int(kernel32.GetLastError()) if not value else 0
        return value, error_code

    def _register_hotkeys(
        self,
        hwnd: int,
        hotkeys: dict[int, tuple[str, Callable[[], None]]],
    ) -> None:
        user32 = ctypes.windll.user32
        kernel32 = ctypes.windll.kernel32
        self._configure_windows_api(user32, kernel32)
        for hotkey_id, (text, _) in hotkeys.items():
            spec = self.hotkey_specs.get(hotkey_id)
            if spec is None:
                continue
            modifiers, vk = spec
            kernel32.SetLastError(0)
            if not user32.RegisterHotKey(hwnd, hotkey_id, modifiers | MOD_NOREPEAT, vk):
                error_code = int(kernel32.GetLastError())
                self.notify_status(f"윈도우 단축키 등록 실패, 보조 감지 사용: {text} ({error_code})")
                log_hotkey_process(
                    f"RegisterHotKey failed id={hotkey_id} text={text} hwnd={hwnd} error={error_code}"
                )
                continue
            self.registered_ids.add(hotkey_id)
            log_hotkey_process(f"RegisterHotKey hwnd ok id={hotkey_id} text={text} hwnd={hwnd}")

    def _start_keyboard_hook_thread(self) -> None:
        if not ENABLE_LOW_LEVEL_HOTKEY_HOOK:
            log_hotkey_process("low-level keyboard hook disabled; using RegisterHotKey hwnd mode")
            return
        if LowLevelKeyboardProc is None:
            return
        self._install_keyboard_hook()
        log_hotkey_process(f"low-level keyboard hook active on main thread hook={bool(self.hook_handle)}")

    def _run_hook_loop(self) -> None:
        user32 = ctypes.windll.user32
        kernel32 = ctypes.windll.kernel32
        self._configure_windows_api(user32, kernel32)
        with self.lock:
            self.thread_id = kernel32.GetCurrentThreadId()
        self.pressed_keys = set()
        self._install_keyboard_hook()

        self.ready.set()
        log_hotkey_process(f"hook message loop ready hook={bool(self.hook_handle)}")
        msg = ctypes.wintypes.MSG()
        while True:
            result = user32.GetMessageW(ctypes.byref(msg), None, 0, 0)
            if result == 0:
                break
            if result == -1:
                log_hotkey_process("hook message loop error")
                break

        if self.hook_handle:
            user32.UnhookWindowsHookEx(self.hook_handle)
        with self.lock:
            self.thread_id = None
            self.hook_handle = None
            self.hook_proc = None
            self.pressed_keys = set()
        log_hotkey_process("hook message loop stopped")

    def _install_keyboard_hook(self) -> None:
        if LowLevelKeyboardProc is None:
            return
        user32 = ctypes.windll.user32
        kernel32 = ctypes.windll.kernel32

        def proc(n_code: int, w_param: int, l_param: int) -> int:
            if n_code >= 0:
                event = ctypes.cast(l_param, ctypes.POINTER(KBDLLHOOKSTRUCT)).contents
                vk = int(event.vkCode)
                if w_param in (WM_KEYDOWN, WM_SYSKEYDOWN):
                    first_press = vk not in self.pressed_keys
                    self.pressed_keys.add(vk)
                    if first_press:
                        self._handle_hook_keydown(vk, int(event.flags), int(event.scanCode))
                elif w_param in (WM_KEYUP, WM_SYSKEYUP):
                    self.pressed_keys.discard(vk)
            return user32.CallNextHookEx(self.hook_handle, n_code, w_param, l_param)

        self.hook_proc = LowLevelKeyboardProc(proc)
        module_handle = kernel32.GetModuleHandleW(None)
        attempts = [(module_handle, "module"), (None, "null-module")]
        errors: list[str] = []
        hook = None
        for module, label in attempts:
            kernel32.SetLastError(0)
            hook = user32.SetWindowsHookExW(WH_KEYBOARD_LL, self.hook_proc, module, 0)
            if hook:
                log_hotkey_process(f"SetWindowsHookExW ok mode={label} handle={int(hook)}")
                break
            errors.append(f"{label}:{int(kernel32.GetLastError())}")

        if not hook:
            log_hotkey_process("SetWindowsHookExW failed " + ", ".join(errors))
            return
        with self.lock:
            self.hook_handle = hook

    def _handle_hook_keydown(self, vk: int, flags: int = 0, scan_code: int = 0) -> None:
        modifiers = self._current_modifiers(flags)
        target_vks = {expected_vk for _, expected_vk in self.hotkey_specs.values()}
        modifier_vks = {
            VK_SHIFT,
            VK_CONTROL,
            VK_MENU,
            VK_LWIN,
            VK_RWIN,
            VK_LSHIFT,
            VK_RSHIFT,
            VK_LCONTROL,
            VK_RCONTROL,
            VK_LMENU,
            VK_RMENU,
        }
        if vk in target_vks or vk in modifier_vks:
            log_hotkey_event(
                f"hook keydown vk={format_vk(vk)}({vk}) modifiers={format_modifiers(modifiers)} "
                f"flags={flags} scan={scan_code} pressed={sorted(self.pressed_keys)}"
            )
        for hotkey_id, (expected_modifiers, expected_vk) in self.hotkey_specs.items():
            if vk == expected_vk and modifiers == expected_modifiers:
                log_hotkey_event(
                    f"hook match id={hotkey_id} vk={format_vk(vk)} modifiers={format_modifiers(modifiers)}"
                )
                self.pending_hotkeys.put(hotkey_id)
                log_hotkey_event(f"hook queued id={hotkey_id}")
                return

    def _current_modifiers(self, hook_flags: int = 0) -> int:
        user32 = ctypes.windll.user32

        def down(*vks: int) -> bool:
            return any(
                (vk in self.pressed_keys)
                or (user32.GetAsyncKeyState(vk) & 0x8000)
                or (user32.GetKeyState(vk) & 0x8000)
                for vk in vks
            )

        modifiers = 0
        if down(VK_CONTROL, VK_LCONTROL, VK_RCONTROL):
            modifiers |= MOD_CONTROL
        if (hook_flags & LLKHF_ALTDOWN) or down(VK_MENU, VK_LMENU, VK_RMENU):
            modifiers |= MOD_ALT
        if down(VK_SHIFT, VK_LSHIFT, VK_RSHIFT):
            modifiers |= MOD_SHIFT
        if down(VK_LWIN, VK_RWIN):
            modifiers |= MOD_WIN
        return modifiers


class SelectionOverlay(tk.Toplevel):
    def __init__(
        self,
        master: tk.Tk,
        monitor: dict[str, int],
        on_done: Callable[[tuple[int, int, int, int] | None], None],
    ) -> None:
        super().__init__(master)
        self.monitor = monitor
        self.on_done = on_done
        self.start_x = 0
        self.start_y = 0
        self.rect_id: int | None = None

        self.overrideredirect(True)
        self.attributes("-topmost", True)
        try:
            self.attributes("-alpha", 0.34)
        except tk.TclError:
            pass
        self.geometry(
            f'{monitor["width"]}x{monitor["height"]}+{monitor["left"]}+{monitor["top"]}'
        )
        self.configure(cursor="crosshair")

        self.canvas = tk.Canvas(self, bg="#080711", highlightthickness=0, cursor="crosshair")
        self.canvas.pack(fill="both", expand=True)
        self._draw_background()

        self.canvas.bind("<ButtonPress-1>", self._on_press)
        self.canvas.bind("<B1-Motion>", self._on_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_release)
        self.bind("<Escape>", self._on_cancel)
        self.focus_force()
        self.grab_set()

    def _draw_background(self) -> None:
        self.canvas.create_text(
            24,
            24,
            anchor="nw",
            text="드래그해서 캡쳐할 구역을 선택하세요. 취소: Esc",
            fill="#ffffff",
            font=("Malgun Gothic", 14, "bold"),
        )

    def _on_press(self, event: tk.Event) -> None:
        self.start_x = int(event.x)
        self.start_y = int(event.y)
        self.rect_id = self.canvas.create_rectangle(
            self.start_x,
            self.start_y,
            self.start_x,
            self.start_y,
            outline="#f9d37a",
            width=2,
            fill="",
        )

    def _on_drag(self, event: tk.Event) -> None:
        if self.rect_id is None:
            return
        x = max(0, min(int(event.x), self.monitor["width"]))
        y = max(0, min(int(event.y), self.monitor["height"]))
        self.canvas.coords(self.rect_id, self.start_x, self.start_y, x, y)

    def _on_release(self, event: tk.Event) -> None:
        end_x = max(0, min(int(event.x), self.monitor["width"]))
        end_y = max(0, min(int(event.y), self.monitor["height"]))
        left, right = sorted((self.start_x, end_x))
        top, bottom = sorted((self.start_y, end_y))
        self.grab_release()
        self.destroy()

        if right - left < MIN_CAPTURE_SIZE or bottom - top < MIN_CAPTURE_SIZE:
            self.on_done(None)
            return
        self.on_done(
            (
                self.monitor["left"] + left,
                self.monitor["top"] + top,
                self.monitor["left"] + right,
                self.monitor["top"] + bottom,
            )
        )

    def _on_cancel(self, _event: tk.Event | None = None) -> None:
        self.grab_release()
        self.destroy()
        self.on_done(None)


class HotkeyRecorderDialog(tk.Toplevel):
    MODIFIER_KEYSYMS = {
        "Shift_L",
        "Shift_R",
        "Control_L",
        "Control_R",
        "Alt_L",
        "Alt_R",
        "Meta_L",
        "Meta_R",
        "Super_L",
        "Super_R",
        "Win_L",
        "Win_R",
    }
    KEY_LABELS = {
        "Escape": "Esc",
        "Return": "Enter",
        "Prior": "PageUp",
        "Next": "PageDown",
        "Delete": "Delete",
        "Insert": "Insert",
        "space": "Space",
        "KP_Decimal": "NumDecimal",
        "KP_Delete": "NumDecimal",
        "Decimal": "NumDecimal",
        "decimal": "NumDecimal",
        "period": ".",
    }
    KEYCODE_LABELS = {
        96: "Num0",
        97: "Num1",
        98: "Num2",
        99: "Num3",
        100: "Num4",
        101: "Num5",
        102: "Num6",
        103: "Num7",
        104: "Num8",
        105: "Num9",
        110: "NumDecimal",
    }

    def __init__(
        self,
        master: tk.Tk,
        title: str,
        initial_value: str,
        on_done: Callable[[str | None], None],
    ) -> None:
        super().__init__(master)
        self.on_done = on_done
        self.last_value = initial_value
        self.title(title)
        self.geometry("360x190")
        self.resizable(False, False)
        self.configure(bg="#f7f3ff")
        self.transient(master)
        self.grab_set()
        self.protocol("WM_DELETE_WINDOW", self.cancel)

        frame = tk.Frame(self, bg="#f7f3ff", padx=20, pady=18)
        frame.pack(fill="both", expand=True)
        tk.Label(
            frame,
            text="설정할 단축키를 누르세요",
            bg="#f7f3ff",
            fg="#241a37",
            font=("Malgun Gothic", 14, "bold"),
        ).pack(anchor="w")
        tk.Label(
            frame,
            text="Ctrl, Alt, Shift 조합을 권장합니다. Esc를 누르면 취소됩니다.",
            bg="#f7f3ff",
            fg="#6c607a",
            wraplength=310,
            justify="left",
        ).pack(anchor="w", pady=(6, 14))
        self.value_var = tk.StringVar(value=initial_value)
        tk.Label(
            frame,
            textvariable=self.value_var,
            bg="#ffffff",
            fg="#241a37",
            relief="solid",
            bd=1,
            width=28,
            pady=8,
            font=("Malgun Gothic", 12, "bold"),
        ).pack(anchor="w")

        actions = tk.Frame(frame, bg="#f7f3ff")
        actions.pack(fill="x", pady=(14, 0))
        tk.Button(actions, text="취소", command=self.cancel, width=10).pack(side="right")

        self.bind("<KeyPress>", self.on_key_press)
        self.after(80, self.focus_force)

    def on_key_press(self, event: tk.Event) -> None:
        log_key_input(
            f"dialog={self.title()} raw keysym={event.keysym} keycode={get_event_keycode(event)} "
            f"state={int(event.state)} char={repr(getattr(event, 'char', ''))}"
        )
        if event.keysym == "Escape":
            log_key_input(f"dialog={self.title()} cancel by Escape")
            self.cancel()
            return
        if event.keysym in self.MODIFIER_KEYSYMS:
            preview = self.format_from_event(event, None)
            log_key_input(f"dialog={self.title()} modifier preview={preview}")
            self.value_var.set(preview)
            return

        value = self.format_from_event(event, event.keysym)
        if not value:
            log_key_input(f"dialog={self.title()} ignored empty value")
            return
        try:
            parse_hotkey(value)
        except ValueError:
            log_key_input(f"dialog={self.title()} unsupported value={value}")
            self.value_var.set(f"지원하지 않는 키입니다. ({event.keysym}/{get_event_keycode(event)})")
            return
        self.value_var.set(value)
        log_key_input(f"dialog={self.title()} accepted value={value}")
        self.after(140, lambda: self.finish(value))

    def format_from_event(self, event: tk.Event, key: str | None) -> str:
        parts: list[str] = []
        if sys.platform == "win32":
            if is_windows_key_down(VK_CONTROL, VK_LCONTROL, VK_RCONTROL) or event.keysym in {
                "Control_L",
                "Control_R",
            }:
                parts.append("Ctrl")
            if is_windows_key_down(VK_MENU, VK_LMENU, VK_RMENU) or event.keysym in {
                "Alt_L",
                "Alt_R",
            }:
                parts.append("Alt")
            if is_windows_key_down(VK_SHIFT, VK_LSHIFT, VK_RSHIFT) or event.keysym in {
                "Shift_L",
                "Shift_R",
            }:
                parts.append("Shift")
            if is_windows_key_down(VK_LWIN, VK_RWIN) or event.keysym in {
                "Meta_L",
                "Meta_R",
                "Super_L",
                "Super_R",
                "Win_L",
                "Win_R",
            }:
                parts.append("Win")
        else:
            state = int(event.state)
            if state & 0x0004:
                parts.append("Ctrl")
            if state & 0x0008 or state & 0x0080:
                parts.append("Alt")
            if state & 0x0001:
                parts.append("Shift")
            if state & 0x0040:
                parts.append("Win")
        if key:
            normalized = self.KEYCODE_LABELS.get(get_event_keycode(event), self.KEY_LABELS.get(key, key))
            if len(normalized) == 1:
                normalized = normalized.upper()
            parts.append(normalized)
        value = "+".join(dict.fromkeys(parts))
        log_key_input(
            f"dialog={self.title()} formatted value={value} raw_state={int(event.state)} "
            f"key={key} keycode={get_event_keycode(event)}"
        )
        return value

    def finish(self, value: str) -> None:
        log_key_input(f"dialog={self.title()} finish value={value}")
        self.grab_release()
        self.destroy()
        self.on_done(value)

    def cancel(self) -> None:
        log_key_input(f"dialog={self.title()} cancel")
        self.grab_release()
        self.destroy()
        self.on_done(None)


class RegionCaptureApp:
    def __init__(self) -> None:
        self.config = load_config()
        self.root = tk.Tk()
        self.root.title("Region Capture")
        self.root.geometry("660x660")
        self.root.minsize(600, 630)
        self.root.configure(bg="#f7f3ff")
        self.root.protocol("WM_DELETE_WINDOW", self.close)
        self.root.report_callback_exception = self.report_callback_exception

        self.is_selecting = False
        self.auto_capture_running = False
        self.auto_capture_after_id: str | None = None
        self.auto_capture_count = 0
        self.hotkey_manager = WindowsHotkeyManager(self.root, self._set_hotkey_error)
        self.status_var = tk.StringVar(value="준비됨")
        self.auto_status_var = tk.StringVar(value="자동 캡쳐: 꺼짐")
        self.output_dir_var = tk.StringVar(value=str(self.config.output_dir))
        self.prefix_var = tk.StringVar(value=self.config.filename_prefix)
        self.format_var = tk.StringVar(value=self.config.image_format)
        self.open_folder_var = tk.BooleanVar(value=self.config.open_folder_after_capture)
        self.hotkeys_enabled_var = tk.BooleanVar(value=self.config.hotkeys_enabled)
        self.select_hotkey_var = tk.StringVar(value=self.config.select_hotkey)
        self.quick_hotkey_var = tk.StringVar(value=self.config.quick_capture_hotkey)
        self.auto_hotkey_var = tk.StringVar(value=self.config.auto_capture_hotkey)
        self.auto_interval_var = tk.StringVar(value=self._format_seconds(self.config.auto_capture_interval_seconds))
        self.region_var = tk.StringVar(value=self._format_region(self.config.last_region))
        self.auto_start_button: tk.Button | None = None
        self.auto_stop_button: tk.Button | None = None
        self._build_ui()
        self.root.after(100, self.apply_hotkeys)

    def _build_ui(self) -> None:
        frame = tk.Frame(self.root, bg="#f7f3ff", padx=22, pady=18)
        frame.pack(fill="both", expand=True)

        tk.Label(
            frame,
            text="영역 캡쳐",
            bg="#f7f3ff",
            fg="#241a37",
            font=("Malgun Gothic", 19, "bold"),
        ).pack(anchor="w")

        tk.Label(
            frame,
            text="폴더, 캡쳐 영역, 단축키를 저장해 두고 반복 캡쳐할 수 있습니다.",
            bg="#f7f3ff",
            fg="#5f536f",
            font=("Malgun Gothic", 10),
        ).pack(anchor="w", pady=(4, 16))

        self._build_folder_section(frame)
        self._build_capture_section(frame)
        self._build_hotkey_section(frame)

        tk.Label(
            frame,
            textvariable=self.status_var,
            bg="#f7f3ff",
            fg="#312344",
            anchor="w",
            font=("Malgun Gothic", 10),
        ).pack(fill="x", pady=(14, 0))

    def _build_folder_section(self, parent: tk.Widget) -> None:
        box = tk.LabelFrame(parent, text="저장", bg="#f7f3ff", fg="#312344", padx=12, pady=10)
        box.pack(fill="x", pady=(0, 12))

        row = tk.Frame(box, bg="#f7f3ff")
        row.pack(fill="x")
        tk.Entry(row, textvariable=self.output_dir_var, font=("Malgun Gothic", 10)).pack(
            side="left", fill="x", expand=True
        )
        tk.Button(row, text="폴더 선택", command=self.choose_output_dir, width=10).pack(
            side="left", padx=(8, 0)
        )
        tk.Button(row, text="열기", command=self.open_output_dir, width=7).pack(side="left", padx=(6, 0))

        options = tk.Frame(box, bg="#f7f3ff")
        options.pack(fill="x", pady=(10, 0))
        tk.Label(options, text="파일명", bg="#f7f3ff").pack(side="left")
        tk.Entry(options, textvariable=self.prefix_var, width=16).pack(side="left", padx=(6, 12))
        tk.Label(options, text="형식", bg="#f7f3ff").pack(side="left")
        tk.OptionMenu(options, self.format_var, "png", "jpg", "bmp").pack(side="left", padx=(6, 12))
        tk.Checkbutton(
            options,
            text="캡쳐 후 폴더 열기",
            variable=self.open_folder_var,
            command=self.save_settings_from_ui,
            bg="#f7f3ff",
        ).pack(side="left")

    def _build_capture_section(self, parent: tk.Widget) -> None:
        box = tk.LabelFrame(parent, text="캡쳐", bg="#f7f3ff", fg="#312344", padx=12, pady=10)
        box.pack(fill="x", pady=(0, 12))

        actions = tk.Frame(box, bg="#f7f3ff")
        actions.pack(fill="x")
        tk.Button(
            actions,
            text="영역 선택 후 캡쳐",
            command=self.start_capture_with_selection,
            width=18,
            font=("Malgun Gothic", 10, "bold"),
        ).pack(side="left")
        tk.Button(
            actions,
            text="저장된 영역 바로 캡쳐",
            command=self.capture_saved_region,
            width=20,
        ).pack(side="left", padx=(8, 0))
        tk.Button(actions, text="영역 초기화", command=self.clear_region, width=10).pack(
            side="left", padx=(8, 0)
        )

        auto = tk.Frame(box, bg="#f7f3ff")
        auto.pack(fill="x", pady=(12, 0))
        tk.Label(auto, text="자동 캡쳐 간격", bg="#f7f3ff").pack(side="left")
        tk.Entry(auto, textvariable=self.auto_interval_var, width=7).pack(side="left", padx=(6, 4))
        tk.Label(auto, text="초", bg="#f7f3ff").pack(side="left", padx=(0, 10))
        self.auto_start_button = tk.Button(
            auto,
            text="자동 시작",
            command=self.start_auto_capture,
            width=10,
        )
        self.auto_start_button.pack(side="left")
        self.auto_stop_button = tk.Button(
            auto,
            text="자동 중지",
            command=self.stop_auto_capture,
            width=10,
            state="disabled",
        )
        self.auto_stop_button.pack(side="left", padx=(8, 0))

        tk.Label(
            box,
            textvariable=self.region_var,
            bg="#f7f3ff",
            fg="#5f536f",
            anchor="w",
            font=("Malgun Gothic", 10),
        ).pack(fill="x", pady=(10, 0))
        tk.Label(
            box,
            textvariable=self.auto_status_var,
            bg="#f7f3ff",
            fg="#5f536f",
            anchor="w",
            font=("Malgun Gothic", 10),
        ).pack(fill="x", pady=(4, 0))

    def _build_hotkey_section(self, parent: tk.Widget) -> None:
        box = tk.LabelFrame(parent, text="단축키", bg="#f7f3ff", fg="#312344", padx=12, pady=10)
        box.pack(fill="x")

        tk.Checkbutton(
            box,
            text="전역 단축키 사용",
            variable=self.hotkeys_enabled_var,
            command=self.apply_hotkeys,
            bg="#f7f3ff",
        ).pack(anchor="w")

        grid = tk.Frame(box, bg="#f7f3ff")
        grid.pack(fill="x", pady=(8, 0))
        tk.Label(grid, text="영역 선택", bg="#f7f3ff", width=12, anchor="w").grid(row=0, column=0, sticky="w")
        tk.Label(
            grid,
            textvariable=self.select_hotkey_var,
            bg="#ffffff",
            fg="#241a37",
            relief="solid",
            bd=1,
            width=18,
            anchor="w",
            padx=8,
            pady=4,
        ).grid(row=0, column=1, sticky="w")
        tk.Button(
            grid,
            text="키 입력",
            command=lambda: self.record_hotkey("select"),
            width=9,
        ).grid(row=0, column=2, padx=(8, 0), sticky="w")
        tk.Label(grid, text="저장 영역 캡쳐", bg="#f7f3ff", width=14, anchor="w").grid(
            row=1, column=0, sticky="w", pady=(8, 0)
        )
        tk.Label(
            grid,
            textvariable=self.quick_hotkey_var,
            bg="#ffffff",
            fg="#241a37",
            relief="solid",
            bd=1,
            width=18,
            anchor="w",
            padx=8,
            pady=4,
        ).grid(row=1, column=1, sticky="w", pady=(8, 0))
        tk.Button(
            grid,
            text="키 입력",
            command=lambda: self.record_hotkey("quick"),
            width=9,
        ).grid(row=1, column=2, padx=(8, 0), pady=(8, 0), sticky="w")
        tk.Label(grid, text="자동 시작/중지", bg="#f7f3ff", width=14, anchor="w").grid(
            row=2, column=0, sticky="w", pady=(8, 0)
        )
        tk.Label(
            grid,
            textvariable=self.auto_hotkey_var,
            bg="#ffffff",
            fg="#241a37",
            relief="solid",
            bd=1,
            width=18,
            anchor="w",
            padx=8,
            pady=4,
        ).grid(row=2, column=1, sticky="w", pady=(8, 0))
        tk.Button(
            grid,
            text="키 입력",
            command=lambda: self.record_hotkey("auto"),
            width=9,
        ).grid(row=2, column=2, padx=(8, 0), pady=(8, 0), sticky="w")
        tk.Button(grid, text="적용/저장", command=self.apply_hotkeys, width=10).grid(
            row=0, column=3, rowspan=3, padx=(12, 0)
        )
        grid.columnconfigure(4, weight=1)

        tk.Label(
            box,
            text="키 입력 버튼을 누른 뒤 원하는 조합을 누르세요. 이미 사용 중인 전역 단축키는 등록 실패로 표시됩니다.",
            bg="#f7f3ff",
            fg="#6c607a",
            wraplength=540,
            justify="left",
        ).pack(anchor="w", pady=(10, 0))

    def record_hotkey(self, target: str) -> None:
        log_hotkey_process(f"record_hotkey requested target={target}")
        self.hotkey_manager.stop()
        labels = {
            "select": "영역 선택 단축키",
            "quick": "저장 영역 캡쳐 단축키",
            "auto": "자동 시작/중지 단축키",
        }
        variables = {
            "select": self.select_hotkey_var,
            "quick": self.quick_hotkey_var,
            "auto": self.auto_hotkey_var,
        }
        label = labels[target]
        variable = variables[target]
        initial = variable.get()
        self.status_var.set(f"{label} 입력 대기 중...")

        def on_done(value: str | None) -> None:
            if value:
                variable.set(value)
                self.status_var.set(f"{label} 저장: {value}")
                log_hotkey_process(f"record_hotkey saved target={target} value={value}")
            else:
                self.status_var.set("단축키 입력 취소됨")
                log_hotkey_process(f"record_hotkey canceled target={target}")
            self.apply_hotkeys()

        HotkeyRecorderDialog(self.root, label, initial, on_done)

    def choose_output_dir(self) -> None:
        selected = filedialog.askdirectory(
            title="캡쳐 저장 폴더 선택",
            initialdir=str(self.config.output_dir),
        )
        if not selected:
            return
        self.output_dir_var.set(selected)
        self.save_settings_from_ui()
        self.status_var.set("저장 폴더를 저장했습니다.")

    def save_settings_from_ui(self) -> None:
        self.config.output_dir = Path(os.path.expandvars(self.output_dir_var.get())).expanduser()
        self.config.filename_prefix = self.prefix_var.get().strip() or "capture"
        self.config.image_format = self.format_var.get().strip().lower() or "png"
        self.config.open_folder_after_capture = bool(self.open_folder_var.get())
        self.config.hotkeys_enabled = bool(self.hotkeys_enabled_var.get())
        self.config.select_hotkey = self.select_hotkey_var.get().strip()
        self.config.quick_capture_hotkey = self.quick_hotkey_var.get().strip()
        self.config.auto_capture_hotkey = self.auto_hotkey_var.get().strip()
        self.config.auto_capture_interval_seconds = self.get_auto_interval_seconds()
        save_config(self.config)
        log_hotkey_process(
            "settings saved "
            f"select={self.config.select_hotkey} quick={self.config.quick_capture_hotkey} "
            f"auto={self.config.auto_capture_hotkey} enabled={self.config.hotkeys_enabled}"
        )

    def get_auto_interval_seconds(self) -> float:
        interval = normalize_auto_capture_interval(self.auto_interval_var.get())
        self.auto_interval_var.set(self._format_seconds(interval))
        return interval

    def apply_hotkeys(self) -> None:
        log_hotkey_process("apply_hotkeys begin")
        self.save_settings_from_ui()
        self.hotkey_manager.stop()
        if not self.config.hotkeys_enabled:
            self.status_var.set("전역 단축키 꺼짐")
            log_hotkey_process("apply_hotkeys skipped disabled")
            return
        hotkey_values = [
            self.config.select_hotkey,
            self.config.quick_capture_hotkey,
            self.config.auto_capture_hotkey,
        ]
        if len(set(hotkey_values)) != len(hotkey_values):
            self.status_var.set("세 단축키는 서로 달라야 합니다.")
            log_hotkey_process(f"apply_hotkeys rejected duplicates values={hotkey_values}")
            return
        ok = self.hotkey_manager.start(
            {
                1: (self.config.select_hotkey, self.start_capture_with_selection),
                2: (self.config.quick_capture_hotkey, self.capture_saved_region),
                3: (self.config.auto_capture_hotkey, self.toggle_auto_capture),
            }
        )
        if ok:
            self.status_var.set("단축키 등록 완료")
            log_hotkey_process("apply_hotkeys result ok")
        else:
            self.status_var.set("단축키 등록 실패")
            log_hotkey_process("apply_hotkeys result failed")

    def _set_hotkey_error(self, message: str) -> None:
        log_hotkey_process(f"status message: {message}")
        self.status_var.set(message)

    def report_callback_exception(self, exc_type, exc_value, exc_traceback) -> None:
        detail = "".join(traceback.format_exception(exc_type, exc_value, exc_traceback))
        log_error(detail)
        self.status_var.set("오류가 발생했습니다. 로그를 확인하세요.")
        try:
            messagebox.showerror("오류", f"작업 중 오류가 발생했습니다.\n\n{exc_value}")
        except tk.TclError:
            pass

    def start_capture_with_selection(self) -> None:
        log_hotkey_event("action start_capture_with_selection")
        if self.is_selecting:
            return
        if self.auto_capture_running:
            self.stop_auto_capture(announce=False)
        self.save_settings_from_ui()
        self.is_selecting = True
        self.status_var.set("화면 준비 중...")
        self.root.withdraw()
        self.root.after(160, self._show_overlay)

    def _show_overlay(self) -> None:
        try:
            monitor = get_virtual_monitor()
        except Exception as exc:
            self.is_selecting = False
            self.root.deiconify()
            log_error(f"monitor lookup failed: {exc}")
            messagebox.showerror("캡쳐 실패", f"화면 정보를 가져오지 못했습니다.\n\n{exc}")
            self.status_var.set("캡쳐 실패")
            return

        SelectionOverlay(self.root, monitor, self._finish_selection)

    def _finish_selection(
        self,
        region: tuple[int, int, int, int] | None,
    ) -> None:
        if region is None:
            self.root.deiconify()
            self.is_selecting = False
            self.status_var.set("캡쳐 취소됨")
            return

        self.config.last_region = region
        self.region_var.set(self._format_region(region))
        save_config(self.config)
        self.status_var.set("선택한 영역 저장 중... 자동 캡쳐도 이 영역을 사용합니다.")
        self.root.after(120, lambda: self._capture_selected_region(region))

    def _capture_selected_region(self, region: tuple[int, int, int, int]) -> None:
        try:
            image = crop_region_from_screen(region)
        except Exception as exc:
            log_error(f"selected capture failed: {exc}")
            self.root.deiconify()
            self.is_selecting = False
            messagebox.showerror("캡쳐 실패", f"선택한 영역을 캡쳐하지 못했습니다.\n\n{exc}")
            self.status_var.set("캡쳐 실패")
            return

        self._save_and_report(image)
        self.root.deiconify()
        self.is_selecting = False

    def capture_saved_region(self) -> None:
        log_hotkey_event("action capture_saved_region")
        self.save_settings_from_ui()
        if not self.config.last_region:
            self.status_var.set("저장된 캡쳐 영역이 없습니다.")
            messagebox.showinfo("영역 없음", "먼저 '영역 선택 후 캡쳐'로 영역을 저장하세요.")
            return
        try:
            image = crop_region_from_screen(self.config.last_region)
        except Exception as exc:
            log_error(f"saved-region capture failed: {exc}")
            messagebox.showerror("캡쳐 실패", f"저장된 영역을 캡쳐하지 못했습니다.\n\n{exc}")
            self.status_var.set("캡쳐 실패")
            return
        self._save_and_report(image)

    def start_auto_capture(self) -> None:
        log_hotkey_event("action start_auto_capture")
        self.save_settings_from_ui()
        if not self.config.last_region:
            self.status_var.set("저장된 캡쳐 영역이 없습니다.")
            messagebox.showinfo("영역 없음", "먼저 '영역 선택 후 캡쳐'로 영역을 저장하세요.")
            return
        if self.auto_capture_running:
            return

        self.auto_capture_running = True
        self.auto_capture_count = 0
        self._set_auto_controls()
        self.status_var.set("자동 캡쳐 시작")
        self.auto_status_var.set(
            f"자동 캡쳐: 실행 중 ({self._format_seconds(self.config.auto_capture_interval_seconds)}초)"
        )
        self._schedule_auto_capture(0)

    def toggle_auto_capture(self) -> None:
        log_hotkey_event("action toggle_auto_capture")
        if self.auto_capture_running:
            self.stop_auto_capture()
            return
        self.start_auto_capture()

    def stop_auto_capture(self, announce: bool = True) -> None:
        log_hotkey_event("action stop_auto_capture")
        self.auto_capture_running = False
        if self.auto_capture_after_id is not None:
            try:
                self.root.after_cancel(self.auto_capture_after_id)
            except tk.TclError:
                pass
            self.auto_capture_after_id = None
        self._set_auto_controls()
        self.auto_status_var.set("자동 캡쳐: 꺼짐")
        if announce:
            self.status_var.set("자동 캡쳐 중지")

    def _schedule_auto_capture(self, delay_ms: int | None = None) -> None:
        if not self.auto_capture_running:
            return
        if delay_ms is None:
            delay_ms = max(1, int(self.config.auto_capture_interval_seconds * 1000))
        self.auto_capture_after_id = self.root.after(delay_ms, self._auto_capture_tick)

    def _auto_capture_tick(self) -> None:
        self.auto_capture_after_id = None
        if not self.auto_capture_running:
            return
        region = self.config.last_region
        if not region:
            self.stop_auto_capture(announce=False)
            self.status_var.set("저장된 캡쳐 영역이 없어 자동 캡쳐를 중지했습니다.")
            return

        image: Image.Image | None = None
        try:
            image = crop_region_from_screen(region)
            saved_path = self._save_image(image)
        except Exception as exc:
            log_error(f"auto capture failed: {exc}")
            self.stop_auto_capture(announce=False)
            messagebox.showerror("자동 캡쳐 실패", f"자동 캡쳐를 중지했습니다.\n\n{exc}")
            self.status_var.set("자동 캡쳐 실패")
            return
        finally:
            if image is not None:
                image.close()
            gc.collect(0)

        self.auto_capture_count += 1
        self.status_var.set(f"자동 저장 완료: {saved_path.name}")
        self.auto_status_var.set(
            f"자동 캡쳐: 실행 중 ({self.auto_capture_count}장, "
            f"{self._format_seconds(self.config.auto_capture_interval_seconds)}초)"
        )
        self._schedule_auto_capture()

    def _set_auto_controls(self) -> None:
        if self.auto_start_button is None or self.auto_stop_button is None:
            return
        if self.auto_capture_running:
            self.auto_start_button.configure(state="disabled")
            self.auto_stop_button.configure(state="normal")
        else:
            self.auto_start_button.configure(state="normal")
            self.auto_stop_button.configure(state="disabled")

    def _save_and_report(self, image: Image.Image) -> None:
        saved_path: Path | None = None
        try:
            saved_path = self._save_image(image)
        except Exception as exc:
            log_error(f"save failed: {exc}")
            messagebox.showerror("저장 실패", f"이미지를 저장하지 못했습니다.\n\n{exc}")
            self.status_var.set("저장 실패")
            return
        finally:
            image.close()
            gc.collect(0)

        self.status_var.set(f"저장 완료: {saved_path.name}")
        if self.config.open_folder_after_capture:
            self.open_output_dir()

    def _save_image(self, image: Image.Image) -> Path:
        self.config.output_dir.mkdir(parents=True, exist_ok=True)
        stamp = datetime.now().strftime("%Y%m%d-%H%M%S-%f")[:-3]
        extension = "jpg" if self.config.image_format == "jpeg" else self.config.image_format
        path = self.config.output_dir / f"{self.config.filename_prefix}-{stamp}.{extension}"
        save_format = "JPEG" if extension == "jpg" else extension.upper()
        if save_format == "JPEG":
            image.save(path, format=save_format, quality=92, optimize=True)
        else:
            image.save(path, format=save_format)
        return path

    def clear_region(self) -> None:
        if self.auto_capture_running:
            self.stop_auto_capture(announce=False)
        self.config.last_region = None
        self.region_var.set(self._format_region(None))
        save_config(self.config)
        self.status_var.set("저장된 영역을 초기화했습니다.")

    def open_output_dir(self) -> None:
        self.save_settings_from_ui()
        self.config.output_dir.mkdir(parents=True, exist_ok=True)
        if sys.platform == "win32":
            os.startfile(self.config.output_dir)  # type: ignore[attr-defined]
            return
        subprocess.Popen(["xdg-open", str(self.config.output_dir)])

    def _format_region(self, region: tuple[int, int, int, int] | None) -> str:
        if not region:
            return "저장된 영역: 없음"
        left, top, right, bottom = region
        return f"저장된 영역: x={left}, y={top}, w={right - left}, h={bottom - top}"

    def _format_seconds(self, seconds: float) -> str:
        value = float(seconds)
        if value.is_integer():
            return str(int(value))
        return f"{value:.3f}".rstrip("0").rstrip(".")

    def close(self) -> None:
        self.stop_auto_capture(announce=False)
        self.save_settings_from_ui()
        self.hotkey_manager.dispose()
        self.root.destroy()

    def run(self) -> None:
        self.root.mainloop()


if __name__ == "__main__":
    enable_dpi_awareness()
    if "--smoke" in sys.argv:
        image, monitor = grab_virtual_screen()
        crop_region_from_screen((monitor["left"], monitor["top"], monitor["left"] + 16, monitor["top"] + 16))
        print(f"smoke ok {image.size[0]}x{image.size[1]}")
    else:
        RegionCaptureApp().run()
