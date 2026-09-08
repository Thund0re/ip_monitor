from __future__ import annotations

import csv
import json
import logging
import logging.handlers
import queue
import re
import socket
import ssl
import threading
import time
from collections import OrderedDict, deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Optional

import customtkinter as ctk
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from tkinter import ttk, Toplevel, END, HORIZONTAL, VERTICAL, scrolledtext
import tkinter as tk

from icmplib import ping

# ─── Constants ────────────────────────────────────────────────────────────────
APP_TITLE = "IP Monitor Pro"
DEFAULT_INTERVAL = 15
REFRESH_TIMEOUT = 8
MAX_LOG_LINES = 250
MAX_LOG_FILE_BYTES = 800_000
MAX_GRAPH_POINTS = 40
WAN_FETCH_TIMEOUT = 2.5
PING_COUNT = 2
PING_TIMEOUT_S = 1.5

PUBLIC_IP_SERVICES = [
    "https://api.ipify.org",
    "https://checkip.amazonaws.com",
    "https://ifconfig.me/ip",
]
DEFAULT_SITES = [
    "kite.zerodha.com",
    "signalstrader.com",
    "fyers.in",
    "flattrade.in",
    "zerodha.com",
]

ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("green")


@dataclass
class SiteResult:
    site: str
    dns_ip: str = "-"
    tls_ip: str = "-"
    seen_as: str = "-"
    dns_ms: str = "-"
    connect_ms: str = "-"
    ping_min: str = "-"
    ping_max: str = "-"
    ping_avg: str = "-"
    note: str = "Pending"


def _make_session() -> requests.Session:
    s = requests.Session()
    retry = Retry(total=1, backoff_factor=0.15, status_forcelist=[500, 502, 503, 504])
    adapter = HTTPAdapter(max_retries=retry, pool_connections=6, pool_maxsize=10)
    s.mount("https://", adapter)
    s.mount("http://", adapter)
    return s


class IPMonitorApp(ctk.CTk):
    def __init__(self) -> None:
        super().__init__()
        self.title(APP_TITLE)
        self.geometry("1040x920")
        self.minsize(700, 520)

        self.base_dir = Path(__file__).resolve().parent
        self.config_file = self.base_dir / "sites_config.json"
        self.wan_log_file = self.base_dir / "wan_ip_log.csv"
        self.action_log_file = self.base_dir / "action_log.txt"

        self._raw_cfg: dict = self._load_raw_config()

        self.websites: list[str] = []
        self.results_by_site: OrderedDict[str, SiteResult] = OrderedDict()
        self.ui_queue: queue.SimpleQueue = queue.SimpleQueue()
        self.executor = ThreadPoolExecutor(max_workers=10)
        self.stop_event = threading.Event()
        self.http_session = _make_session()

        self.local_ip = "Fetching..."
        self.wan_ip = "Fetching..."
        self.last_refresh_at = "-"
        self.last_wan_change_at = "-"
        self.wan_change_count = 0
        self.last_logged_ip: Optional[str] = self._raw_cfg.get("last_wan_ip")
        self.total_wan_log_rows = 0
        self.refresh_in_progress = False

        self.auto_refresh_enabled = tk.BooleanVar(value=self._raw_cfg.get("auto_refresh", True))
        self.interval_var = tk.StringVar(value=str(self._raw_cfg.get("interval", DEFAULT_INTERVAL)))
        self.countdown_seconds = self.get_interval_seconds()

        # Lightweight graph state (no matplotlib)
        self._graph_indices: deque[int] = deque(maxlen=MAX_GRAPH_POINTS)
        self._graph_values: deque[float] = deque(maxlen=MAX_GRAPH_POINTS)
        self._ip_index_map: dict[str, int] = {}
        self._graph_entry_counter = 0
        self._graph_dirty = False

        self._setup_file_logger()
        self.websites = self._parse_sites(self._raw_cfg)
        self.build_ui()
        self.configure_tree_style()
        self._load_wan_history_meta_and_prime_graph()
        self.refresh_summary_labels()

        if geo := self._raw_cfg.get("geometry"):
            try:
                self.geometry(geo)
            except Exception:
                pass

        self.protocol("WM_DELETE_WINDOW", self.on_exit)
        self.after(80, self._queue_flush_tick)
        self.after(1000, self.scheduler_tick)
        self.log_action("Application started", "INFO")
        self.refresh_all()

    def _setup_file_logger(self) -> None:
        self._flogger = logging.getLogger("ip_monitor_file")
        self._flogger.setLevel(logging.INFO)
        if not self._flogger.handlers:
            h = logging.handlers.RotatingFileHandler(
                self.action_log_file, maxBytes=MAX_LOG_FILE_BYTES, backupCount=2, encoding="utf-8"
            )
            h.setFormatter(logging.Formatter("%(message)s"))
            self._flogger.addHandler(h)

    def _load_raw_config(self) -> dict:
        if not self.config_file.exists():
            return {}
        try:
            with self.config_file.open("r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}

    def _parse_sites(self, cfg: dict) -> list[str]:
        raw = cfg.get("sites", [])
        if isinstance(raw, list) and raw:
            cleaned = []
            for s in raw:
                n = self.normalize_site(str(s))
                if n and n not in cleaned:
                    cleaned.append(n)
            if cleaned:
                return cleaned
        return list(DEFAULT_SITES)

    def save_config(self) -> None:
        try:
            with self.config_file.open("w", encoding="utf-8") as f:
                json.dump(
                    {
                        "sites": self.websites,
                        "auto_refresh": self.auto_refresh_enabled.get(),
                        "interval": self.get_interval_seconds(),
                        "last_wan_ip": self.last_logged_ip,
                        "geometry": self.geometry(),
                    },
                    f,
                    indent=2,
                )
        except Exception as e:
            self.log_action(f"Config save failed: {e}", "WARN")

    # ─── UI ───────────────────────────────────────────────────────────────────
    def build_ui(self) -> None:
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)

        header = ctk.CTkFrame(self, corner_radius=16, fg_color="#102418")
        header.grid(row=0, column=0, sticky="ew", padx=14, pady=(14, 8))
        header.grid_columnconfigure(0, weight=1)

        title_wrap = ctk.CTkFrame(header, fg_color="transparent")
        title_wrap.grid(row=0, column=0, sticky="w", padx=14, pady=10)
        ctk.CTkLabel(title_wrap, text=APP_TITLE, font=ctk.CTkFont(size=26, weight="bold"), text_color="#e8fff1").pack(anchor="w")
        ctk.CTkLabel(title_wrap, text="dark • green • trader-grade", font=ctk.CTkFont(size=12, slant="italic"), text_color="#9dd6b3").pack(anchor="w")

        header_actions = ctk.CTkFrame(header, fg_color="transparent")
        header_actions.grid(row=0, column=1, sticky="e", padx=14, pady=10)

        self.status_chip = ctk.CTkLabel(
            header_actions, text="Ready", height=30, corner_radius=999, padx=12,
            fg_color="#143a24", text_color="#84f0b1", font=ctk.CTkFont(size=12, weight="bold")
        )
        self.status_chip.pack(side="left", padx=(0, 8))

        ctk.CTkButton(header_actions, text="Refresh", width=100, height=34, command=self.refresh_all,
                      fg_color="#1f8f55", hover_color="#166c40").pack(side="left", padx=4)
        ctk.CTkButton(header_actions, text="Exit", width=80, height=34, command=self.on_exit,
                      fg_color="#7a1f1f", hover_color="#5c1717").pack(side="left")

        body = tk.PanedWindow(self, orient=HORIZONTAL, bg="#0f1511", bd=0, sashwidth=5)
        body.grid(row=1, column=0, sticky="nsew", padx=14, pady=(0, 14))

        self.left_panel = ctk.CTkFrame(body, width=400, corner_radius=14, fg_color="#101712")
        self.right_panel = ctk.CTkFrame(body, corner_radius=14, fg_color="#0f1511")
        body.add(self.left_panel, minsize=280)
        body.add(self.right_panel, minsize=480)

        self.right_panel.grid_columnconfigure(0, weight=1)
        self.right_panel.grid_rowconfigure(2, weight=1)
        self.right_panel.grid_rowconfigure(5, weight=1)
        self.right_panel.grid_rowconfigure(6, weight=2)

        self.build_left_panel()
        self.build_right_panel()

    def build_left_panel(self) -> None:
        cards = ctk.CTkFrame(self.left_panel, corner_radius=14, fg_color="#132019")
        cards.pack(fill="x", padx=12, pady=(12, 8))
        self.local_value = self._metric_block(cards, "Local IP", "Fetching...", "#8cc8ff")
        self.wan_value = self._metric_block(cards, "WAN / Public IP", "Fetching...", "#9dffbf")
        self.seen_value = self._metric_block(cards, "Seen by sites / APIs", "Fetching...", "#b6f59d")

        controls = ctk.CTkFrame(self.left_panel, corner_radius=14, fg_color="#132019")
        controls.pack(fill="x", padx=12, pady=(0, 8))
        ctk.CTkLabel(controls, text="Auto Refresh", font=ctk.CTkFont(size=15, weight="bold")).pack(anchor="w", padx=12, pady=(10, 6))

        switch_row = ctk.CTkFrame(controls, fg_color="transparent")
        switch_row.pack(fill="x", padx=12, pady=(0, 6))
        self.auto_switch = ctk.CTkSwitch(
            switch_row, text="Enable auto + WAN logging", variable=self.auto_refresh_enabled,
            onvalue=True, offvalue=False, command=self.on_auto_toggle, progress_color="#1f8f55"
        )
        self.auto_switch.pack(anchor="w")
        if self.auto_refresh_enabled.get():
            self.auto_switch.select()
        else:
            self.auto_switch.deselect()

        interval_row = ctk.CTkFrame(controls, fg_color="transparent")
        interval_row.pack(fill="x", padx=12, pady=(2, 0))
        ctk.CTkLabel(interval_row, text="Interval", width=65).pack(side="left")
        self.interval_menu = ctk.CTkOptionMenu(
            interval_row, values=["5", "10", "15", "30", "60"], variable=self.interval_var,
            command=self.on_interval_change, fg_color="#17452a", button_color="#1f8f55", button_hover_color="#166c40"
        )
        self.interval_menu.pack(side="left", padx=(0, 6))
        ctk.CTkLabel(interval_row, text="sec", text_color="#99b7a4").pack(side="left")

        self.countdown_label = ctk.CTkLabel(
            controls, text=f"Next in {self.countdown_seconds}s",
            font=ctk.CTkFont(size=13, weight="bold"), text_color="#84f0b1"
        )
        self.countdown_label.pack(anchor="w", padx=12, pady=(6, 4))

        self.refresh_meta_label = ctk.CTkLabel(controls, text="Last refresh: -", anchor="w", text_color="#aac7b3")
        self.wan_change_label = ctk.CTkLabel(controls, text="WAN changes: 0", anchor="w", text_color="#aac7b3")
        self.wan_change_time_label = ctk.CTkLabel(controls, text="Last change: -", anchor="w", text_color="#aac7b3")
        for lbl in (self.refresh_meta_label, self.wan_change_label, self.wan_change_time_label):
            lbl.pack(fill="x", padx=12, pady=1)
        self.wan_change_time_label.pack(pady=(1, 10))

        sites = ctk.CTkFrame(self.left_panel, corner_radius=14, fg_color="#132019")
        sites.pack(fill="both", expand=True, padx=12, pady=(0, 8))

        sites_header = ctk.CTkFrame(sites, fg_color="transparent")
        sites_header.pack(fill="x", padx=12, pady=(10, 2))
        ctk.CTkLabel(sites_header, text="Tracked Sites", font=ctk.CTkFont(size=16, weight="bold")).pack(side="left")
        ctk.CTkButton(sites_header, text="Edit", width=70, height=22, command=self.open_edit_sites_dialog,
                      fg_color="#2a5f3d", hover_color="#1f8f55", font=ctk.CTkFont(size=11)).pack(side="right")

        ctk.CTkLabel(sites, text="Double-click resolve • ↑↓ reorder", text_color="#97b7a2", font=ctk.CTkFont(size=10)).pack(anchor="w", padx=12, pady=(0, 4))

        self.site_listbox = tk.Listbox(
            sites, height=7, font=("Consolas", 11), bg="#0f1511", fg="#dcfce7",
            bd=0, highlightthickness=0, relief="flat", selectbackground="#1f8f55",
            selectforeground="#ffffff", exportselection=False
        )
        self.site_listbox.pack(fill="both", expand=True, padx=12, pady=(0, 4))
        self.site_listbox.bind("<<ListboxSelect>>", self.on_site_select)
        self.site_listbox.bind("<Double-1>", lambda e: self.resolve_selected())
        self.refresh_site_listbox()

        entry_row = ctk.CTkFrame(sites, fg_color="transparent")
        entry_row.pack(fill="x", padx=12, pady=(2, 4))
        self.site_entry = ctk.CTkEntry(entry_row, placeholder_text="Add site (e.g. upstox.com)")
        self.site_entry.pack(side="left", fill="x", expand=True, padx=(0, 6))
        self.site_entry.bind("<Return>", lambda e: self.add_site())
        ctk.CTkButton(entry_row, text="Add", width=60, command=self.add_site, fg_color="#1f8f55", hover_color="#166c40").pack(side="left")

        manage_row = ctk.CTkFrame(sites, fg_color="transparent")
        manage_row.pack(fill="x", padx=12, pady=(0, 8))
        ctk.CTkButton(manage_row, text="Resolve", width=70, command=self.resolve_selected).pack(side="left", padx=(0, 4))
        ctk.CTkButton(manage_row, text="Remove", width=70, fg_color="#6f2b2b", hover_color="#572121",
                      command=self.remove_selected_site).pack(side="left", padx=(4, 0))
        ctk.CTkButton(manage_row, text="↑", width=32, command=lambda: self.move_selected_site(-1)).pack(side="left", padx=(10, 3))
        ctk.CTkButton(manage_row, text="↓", width=32, command=lambda: self.move_selected_site(1)).pack(side="left")

    def _metric_block(self, parent, label: str, value: str, color: str):
        wrap = ctk.CTkFrame(parent, fg_color="transparent")
        wrap.pack(fill="x", padx=12, pady=(10, 0))
        ctk.CTkLabel(wrap, text=label, text_color="#98b7a4", font=ctk.CTkFont(size=12, weight="bold")).pack(anchor="w")
        lbl = ctk.CTkLabel(wrap, text=value, font=ctk.CTkFont(size=18, weight="bold", family="Consolas"),
                           text_color=color, anchor="w", justify="left")
        lbl.pack(anchor="w", pady=(2, 0))
        return lbl

    def _ip_label_font_size(self, value: str) -> int:
        n = len(value)
        if n <= 15:
            return 18
        if n <= 22:
            return 15
        if n <= 32:
            return 12
        return 10

    def build_right_panel(self) -> None:
        top_cards = ctk.CTkFrame(self.right_panel, fg_color="transparent")
        top_cards.grid(row=0, column=0, sticky="ew", padx=10, pady=(10, 4))
        for i in range(4):
            top_cards.grid_columnconfigure(i, weight=1)
        self.total_sites_card = self._small_stat_card(top_cards, 0, "Sites", "0", "#8cc8ff")
        self.ok_sites_card = self._small_stat_card(top_cards, 1, "OK", "0", "#9dffbf")
        self.peer_sites_card = self._small_stat_card(top_cards, 2, "TLS", "0", "#b6f59d")
        self.log_rows_card = self._small_stat_card(top_cards, 3, "Log rows", "0", "#facc7d")

        explain = ctk.CTkFrame(self.right_panel, corner_radius=12, fg_color="#132019")
        explain.grid(row=1, column=0, sticky="ew", padx=10, pady=(2, 6))
        ctk.CTkLabel(explain, text="DNS IP vs TLS IP", font=ctk.CTkFont(size=13, weight="bold")).pack(anchor="w", padx=12, pady=(8, 2))
        self._explain_label = ctk.CTkLabel(
            explain,
            text="DNS = resolver  |  TLS = actual HTTPS peer  |  Seen As = your public IP",
            justify="left", text_color="#c5dfce", font=ctk.CTkFont(size=10), anchor="w"
        )
        self._explain_label.pack(fill="x", anchor="w", padx=12, pady=(0, 8))
        self.right_panel.bind("<Configure>", self._on_right_panel_resize)

        table_wrap = ctk.CTkFrame(self.right_panel, corner_radius=12, fg_color="#132019")
        table_wrap.grid(row=2, column=0, sticky="nsew", padx=10, pady=(0, 4))
        table_wrap.grid_columnconfigure(0, weight=1)
        table_wrap.grid_rowconfigure(0, weight=1)

        columns = ("Site", "DNS_IP", "TLS_IP", "Seen_As", "DNS_ms", "Connect_ms", "Min", "Max", "Avg", "Status")
        self.tree = ttk.Treeview(table_wrap, columns=columns, show="headings", height=5)
        headings = {
            "Site": "Website", "DNS_IP": "DNS IP", "TLS_IP": "TLS IP", "Seen_As": "Server Sees",
            "DNS_ms": "DNS", "Connect_ms": "TLS", "Min": "Min", "Max": "Max", "Avg": "Avg", "Status": "Status"
        }
        widths = {
            "Site": 150, "DNS_IP": 130, "TLS_IP": 120, "Seen_As": 120,
            "DNS_ms": 55, "Connect_ms": 55, "Min": 50, "Max": 50, "Avg": 50, "Status": 140
        }
        for col in columns:
            self.tree.heading(col, text=headings[col], anchor="center")
            self.tree.column(col, width=widths[col], anchor="center", minwidth=45)

        tree_sy = ttk.Scrollbar(table_wrap, orient=VERTICAL, command=self.tree.yview)
        tree_sx = ttk.Scrollbar(table_wrap, orient=HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=tree_sy.set, xscrollcommand=tree_sx.set)
        self.tree.grid(row=0, column=0, sticky="nsew", padx=8, pady=6)
        tree_sy.grid(row=0, column=1, sticky="ns", pady=6)
        tree_sx.grid(row=1, column=0, sticky="ew", padx=8)
        self.tree.bind("<Double-1>", self._on_tree_double_click)

        # Lightweight canvas graph (replaces matplotlib)
        graph_wrap = ctk.CTkFrame(self.right_panel, corner_radius=12, fg_color="#132019")
        graph_wrap.grid(row=5, column=0, sticky="nsew", padx=10, pady=(0, 4))
        graph_wrap.grid_columnconfigure(0, weight=1)
        graph_wrap.grid_rowconfigure(1, weight=1)

        graph_hdr = ctk.CTkFrame(graph_wrap, fg_color="transparent")
        graph_hdr.grid(row=0, column=0, sticky="ew", padx=10, pady=(8, 2))
        ctk.CTkLabel(graph_hdr, text="WAN IP History", font=ctk.CTkFont(size=14, weight="bold")).grid(row=0, column=0, sticky="w")
        self.graph_status_label = ctk.CTkLabel(graph_hdr, text="Waiting…", text_color="#9dd6b3", font=ctk.CTkFont(size=10))
        self.graph_status_label.grid(row=0, column=1, sticky="e", padx=8)

        self._graph_canvas = tk.Canvas(graph_wrap, bg="#0f1511", highlightthickness=0, height=160)
        self._graph_canvas.grid(row=1, column=0, sticky="nsew", padx=8, pady=(0, 8))
        self._graph_canvas.bind("<Configure>", lambda e: self._schedule_graph_redraw())

        log_wrap = ctk.CTkFrame(self.right_panel, corner_radius=12, fg_color="#132019")
        log_wrap.grid(row=6, column=0, sticky="nsew", padx=10, pady=(0, 10))
        log_wrap.grid_columnconfigure(0, weight=1)
        log_wrap.grid_rowconfigure(1, weight=1)

        log_hdr = ctk.CTkFrame(log_wrap, fg_color="transparent")
        log_hdr.grid(row=0, column=0, columnspan=2, sticky="ew", padx=10, pady=(8, 2))
        log_hdr.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(log_hdr, text="Activity Log", font=ctk.CTkFont(size=14, weight="bold")).grid(row=0, column=0, sticky="w")
        ctk.CTkButton(log_hdr, text="Clear", width=70, height=24, command=self.clear_log_view,
                      fg_color="#3a3a3a", hover_color="#4a4a4a", font=ctk.CTkFont(size=10)).grid(row=0, column=1, sticky="e")

        self.log_text = tk.Text(
            log_wrap, font=("Consolas", 9), bg="#0d120f", fg="#e2ffe9",
            insertbackground="#9dffbf", bd=0, padx=10, pady=6, wrap="none",
            relief="flat", highlightthickness=0
        )
        self.log_text.grid(row=1, column=0, sticky="nsew", padx=6, pady=(0, 6))
        log_sy = ttk.Scrollbar(log_wrap, orient=VERTICAL, command=self.log_text.yview)
        log_sx = ttk.Scrollbar(log_wrap, orient=HORIZONTAL, command=self.log_text.xview)
        self.log_text.configure(yscrollcommand=log_sy.set, xscrollcommand=log_sx.set)
        log_sy.grid(row=1, column=1, sticky="ns", pady=(0, 6))
        log_sx.grid(row=2, column=0, sticky="ew", padx=6)

        self.log_text.tag_configure("INFO", foreground="#84f0b1")
        self.log_text.tag_configure("WARN", foreground="#ffd27d")
        self.log_text.tag_configure("ERROR", foreground="#ff9393")
        self.log_text.tag_configure("RESULT", foreground="#b6f59d")
        self.log_text.tag_configure("ts", foreground="#6a8a77")

    def _small_stat_card(self, parent, col: int, label: str, value: str, color: str):
        card = ctk.CTkFrame(parent, corner_radius=12, fg_color="#132019")
        card.grid(row=0, column=col, sticky="ew", padx=4)
        ctk.CTkLabel(card, text=label, text_color="#98b7a4", font=ctk.CTkFont(size=11)).pack(anchor="w", padx=10, pady=(8, 1))
        v_lbl = ctk.CTkLabel(card, text=value, font=ctk.CTkFont(size=20, weight="bold"), text_color=color)
        v_lbl.pack(anchor="w", padx=10, pady=(0, 8))
        return v_lbl

    def configure_tree_style(self) -> None:
        s = ttk.Style()
        try:
            s.theme_use("default")
        except tk.TclError:
            pass
        s.configure("Treeview", rowheight=28, font=("Segoe UI", 9),
                    background="#0d120f", fieldbackground="#0d120f", foreground="#e2ffe9", borderwidth=0)
        s.configure("Treeview.Heading", font=("Segoe UI", 9, "bold"), background="#1b2a20", foreground="#e2ffe9")
        s.map("Treeview", background=[("selected", "#1f8f55")], foreground=[("selected", "#ffffff")])

    def _on_right_panel_resize(self, event) -> None:
        w = max(180, event.width - 50)
        self._explain_label.configure(wraplength=w)

    def _on_tree_double_click(self, event) -> None:
        row = self.tree.identify_row(event.y)
        col = self.tree.identify_column(event.x)
        if row and col:
            idx = int(col.replace("#", "")) - 1
            vals = self.tree.item(row, "values")
            if 0 <= idx < len(vals):
                self.clipboard_clear()
                self.clipboard_append(str(vals[idx]))
                self.set_status(f"Copied: {vals[idx]}", "#b6f59d")

    # ─── Scheduler / queue ────────────────────────────────────────────────────
    def scheduler_tick(self) -> None:
        if self.stop_event.is_set():
            return
        if not self.auto_refresh_enabled.get():
            self.countdown_label.configure(text="Auto paused")
            self.after(1000, self.scheduler_tick)
            return
        if self.refresh_in_progress:
            self.countdown_label.configure(text="Refreshing…")
            self.after(1000, self.scheduler_tick)
            return
        self.countdown_seconds -= 1
        if self.countdown_seconds <= 0:
            self.countdown_seconds = self.get_interval_seconds()
            self.refresh_all()
        else:
            self.countdown_label.configure(text=f"Next in {self.countdown_seconds}s")
        self.after(1000, self.scheduler_tick)

    def on_auto_toggle(self) -> None:
        state = "enabled" if self.auto_refresh_enabled.get() else "disabled"
        self.countdown_seconds = self.get_interval_seconds()
        self.log_action(f"Auto refresh {state}", "INFO")
        self.countdown_label.configure(
            text=f"Next in {self.countdown_seconds}s" if self.auto_refresh_enabled.get() else "Auto paused"
        )

    def on_interval_change(self, _: str) -> None:
        self.countdown_seconds = self.get_interval_seconds()
        self.log_action(f"Interval → {self.countdown_seconds}s", "INFO")
        if self.auto_refresh_enabled.get() and not self.refresh_in_progress:
            self.countdown_label.configure(text=f"Next in {self.countdown_seconds}s")

    def get_interval_seconds(self) -> int:
        try:
            return max(5, int(self.interval_var.get().strip()))
        except Exception:
            return DEFAULT_INTERVAL

    def _queue_flush_tick(self) -> None:
        self._drain_queue()
        if self._graph_dirty:
            self._redraw_graph()
            self._graph_dirty = False
        if not self.stop_event.is_set():
            self.after(80, self._queue_flush_tick)

    def _drain_queue(self) -> None:
        try:
            while True:
                event, payload = self.ui_queue.get_nowait()
                self._handle_ui_event(event, payload)
        except queue.Empty:
            pass

    def _handle_ui_event(self, event: str, payload) -> None:
        if event == "status":
            text, color = payload
            self.set_status(text, color)
        elif event == "header":
            local_ip, wan_ip, ts = payload
            self.local_ip = local_ip
            self.wan_ip = wan_ip
            self.last_refresh_at = ts
            self.refresh_summary_labels()
        elif event == "wan_logged":
            current_ip, changed, ts = payload
            self._on_wan_logged(current_ip, changed, ts)
        elif event == "site_result":
            result: SiteResult = payload
            self.results_by_site[result.site] = result
            self._update_table_row(result)
            self.refresh_stat_cards()
            self.log_action(
                f"{result.site} | DNS={result.dns_ip} | TLS={result.tls_ip} | "
                f"Ping={result.ping_min}/{result.ping_avg}/{result.ping_max} | {result.note}",
                "RESULT",
            )
        elif event == "refresh_done":
            self.refresh_in_progress = False
            self.countdown_seconds = self.get_interval_seconds()
            self.countdown_label.configure(
                text=f"Next in {self.countdown_seconds}s" if self.auto_refresh_enabled.get() else "Auto paused"
            )
            self.set_status("Ready", "#84f0b1")
            self.log_action("Refresh complete", "INFO")
        elif event == "graph_point":
            ip, idx_val = payload
            self._push_graph_point(ip, idx_val)
        elif event == "log":
            message, level = payload
            self.log_action(message, level)
        elif event == "error":
            self.refresh_in_progress = False
            self.set_status(str(payload), "#ff9393")
            self.log_action(str(payload), "ERROR")

    # ─── Core logic ───────────────────────────────────────────────────────────
    def refresh_all(self) -> None:
        if self.refresh_in_progress:
            return
        self.refresh_in_progress = True
        self.countdown_label.configure(text="Refreshing…")
        self.set_status("Refreshing", "#b6f59d")
        self.log_action("Refresh started", "INFO")
        threading.Thread(target=self._refresh_worker, daemon=True).start()

    def _refresh_worker(self) -> None:
        try:
            local_ip = self._get_local_ip()
            wan_ip = self._get_wan_ip_parallel()
            ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            self.ui_queue.put(("header", (local_ip, wan_ip, ts)))

            log_ts, changed = self._append_wan_log(wan_ip)
            self.ui_queue.put(("wan_logged", (wan_ip, changed, log_ts)))

            futures = {
                self.executor.submit(self._resolve_site_parallel, site, wan_ip): site
                for site in self.websites
            }
            for future in as_completed(futures):
                try:
                    result = future.result()
                    self.ui_queue.put(("site_result", result))
                except Exception as exc:
                    site = futures[future]
                    self.ui_queue.put(("error", f"{site}: {exc}"))

            self.ui_queue.put(("refresh_done", None))
        except Exception as exc:
            self.ui_queue.put(("error", f"Refresh failed: {exc}"))

    def resolve_selected(self) -> None:
        sel = self.site_listbox.curselection()
        if not sel:
            self.log_action("No site selected", "WARN")
            return
        site = self.site_listbox.get(sel[0])
        self.log_action(f"Resolving {site}", "INFO")
        threading.Thread(target=self._resolve_single_worker, args=(site,), daemon=True).start()

    def _resolve_single_worker(self, site: str) -> None:
        wan = self.wan_ip if self.wan_ip not in {"Fetching...", "Unavailable"} else self._get_wan_ip_parallel()
        result = self._resolve_site_parallel(site, wan)
        self.ui_queue.put(("site_result", result))
        self.ui_queue.put(("status", ("Updated", "#84f0b1")))

    def _get_local_ip(self) -> str:
        try:
            with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
                s.connect(("8.8.8.8", 80))
                return s.getsockname()[0]
        except Exception:
            try:
                return socket.gethostbyname(socket.gethostname())
            except Exception:
                return "127.0.0.1"

    def _get_wan_ip_parallel(self) -> str:
        result_holder: list[Optional[str]] = [None]
        done = threading.Event()

        def fetch(url: str) -> None:
            if done.is_set():
                return
            try:
                r = self.http_session.get(url, timeout=WAN_FETCH_TIMEOUT)
                if r.ok:
                    val = r.text.strip()
                    if re.match(r"^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$", val) and not done.is_set():
                        result_holder[0] = val
                        done.set()
            except Exception:
                pass

        threads = [threading.Thread(target=fetch, args=(u,), daemon=True) for u in PUBLIC_IP_SERVICES]
        for t in threads:
            t.start()
        done.wait(timeout=WAN_FETCH_TIMEOUT + 0.4)
        return result_holder[0] or "Unavailable"

    def _resolve_site_parallel(self, site: str, seen_as_ip: str) -> SiteResult:
        result = SiteResult(site=site, seen_as=seen_as_ip)

        dns_start = time.perf_counter()
        try:
            addrinfo = socket.getaddrinfo(site, 443, family=socket.AF_INET, type=socket.SOCK_STREAM)
            ipv4s = sorted({item[4][0] for item in addrinfo})
            result.dns_ip = ", ".join(ipv4s[:2]) if ipv4s else "No IPv4"
            result.dns_ms = f"{(time.perf_counter() - dns_start) * 1000:.0f}"
        except Exception as exc:
            result.note = f"DNS: {str(exc)[:35]}"
            return result

        primary_ip = result.dns_ip.split(",")[0].strip() if result.dns_ip not in {"-", "No IPv4"} else ""

        tls_result: list = [("N/A", "-", "Failed")]
        ping_result: list = [None]

        def do_tls():
            tls_result[0] = self._get_tls_peer_ip(site)

        def do_ping():
            if primary_ip:
                ping_result[0] = self._ping_host(primary_ip)

        t1 = threading.Thread(target=do_tls, daemon=True)
        t2 = threading.Thread(target=do_ping, daemon=True)
        t1.start()
        t2.start()
        t1.join(timeout=REFRESH_TIMEOUT)
        t2.join(timeout=REFRESH_TIMEOUT)

        result.tls_ip, result.connect_ms, result.note = tls_result[0]
        if ping_result[0]:
            p = ping_result[0]
            result.ping_min = p["min"]
            result.ping_max = p["max"]
            result.ping_avg = p["avg"]

        return result

    def _get_tls_peer_ip(self, host: str) -> tuple[str, str, str]:
        for port, secure in ((443, True), (80, False)):
            try:
                start = time.perf_counter()
                raw = socket.create_connection((host, port), timeout=REFRESH_TIMEOUT)
                if secure:
                    ctx = ssl.create_default_context()
                    with ctx.wrap_socket(raw, server_hostname=host) as tls:
                        peer_ip = tls.getpeername()[0]
                else:
                    with raw:
                        peer_ip = raw.getpeername()[0]
                elapsed = f"{(time.perf_counter() - start) * 1000:.0f}"
                return peer_ip, elapsed, "OK" if secure else "HTTP"
            except Exception:
                continue
        return "N/A", "-", "Failed"

    def _ping_host(self, host: str) -> Optional[dict[str, str]]:
        try:
            result = ping(host, count=PING_COUNT, timeout=PING_TIMEOUT_S, privileged=False)
            if result.is_alive:
                return {
                    "min": f"{result.min_rtt:.0f}",
                    "max": f"{result.max_rtt:.0f}",
                    "avg": f"{result.avg_rtt:.0f}",
                }
        except Exception:
            pass
        return None

    def _append_wan_log(self, current_ip: str) -> tuple[str, bool]:
        ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        changed = self.last_logged_ip is not None and current_ip != self.last_logged_ip
        exists = self.wan_log_file.exists()
        with self.wan_log_file.open("a", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            if not exists:
                w.writerow(["Timestamp", "WAN_IP", "Changed"])
            w.writerow([ts, current_ip, "Yes" if changed else "No"])
        self.last_logged_ip = current_ip
        self.total_wan_log_rows += 1
        if changed:
            self.last_wan_change_at = ts
            self.wan_change_count += 1
        return ts, changed

    def _on_wan_logged(self, current_ip: str, changed: bool, ts: str) -> None:
        self.wan_ip = current_ip
        self.refresh_summary_labels()
        if changed:
            self.log_action(f"WAN changed → {current_ip} @ {ts}", "WARN")
        else:
            self.log_action(f"WAN logged: {current_ip}", "INFO")
        if current_ip not in self._ip_index_map:
            self._ip_index_map[current_ip] = len(self._ip_index_map) + 1
        ip_val = float(self._ip_index_map[current_ip])
        self._graph_entry_counter += 1
        self.ui_queue.put(("graph_point", (current_ip, ip_val)))

    def _push_graph_point(self, ip: str, y_val: float) -> None:
        if ip:
            self._graph_indices.append(self._graph_entry_counter)
            self._graph_values.append(y_val)
        self._schedule_graph_redraw()

    def _schedule_graph_redraw(self) -> None:
        self._graph_dirty = True

    def _redraw_graph(self) -> None:
        c = self._graph_canvas
        c.delete("all")
        w = c.winfo_width()
        h = c.winfo_height()
        if w < 40 or h < 40 or not self._graph_indices:
            return

        xs = list(self._graph_indices)
        ys = list(self._graph_values)
        n = len(xs)
        pad_l, pad_r, pad_t, pad_b = 70, 12, 12, 22
        plot_w = max(10, w - pad_l - pad_r)
        plot_h = max(10, h - pad_t - pad_b)

        uniq = self._ip_index_map
        y_max = max(uniq.values()) if uniq else 1
        y_min = 0.5
        y_range = max(0.5, y_max - y_min + 0.5)

        # Axes
        c.create_line(pad_l, pad_t, pad_l, h - pad_b, fill="#3a5a4a", width=1)
        c.create_line(pad_l, h - pad_b, w - pad_r, h - pad_b, fill="#3a5a4a", width=1)

        # Y labels (IPs)
        for ip, idx in uniq.items():
            y = pad_t + plot_h - ((idx - y_min) / y_range) * plot_h
            c.create_text(pad_l - 6, y, text=ip, anchor="e", fill="#9dd6b3", font=("Consolas", 7))
            c.create_line(pad_l - 3, y, pad_l, y, fill="#3a5a4a")

        # Points + line
        points = []
        for i, (x_val, y_val) in enumerate(zip(xs, ys)):
            px = pad_l + (i / max(1, n - 1)) * plot_w if n > 1 else pad_l + plot_w / 2
            py = pad_t + plot_h - ((y_val - y_min) / y_range) * plot_h
            points.append((px, py))
            c.create_oval(px - 3, py - 3, px + 3, py + 3, fill="#1f8f55", outline="#9dffbf", width=1)

        if len(points) > 1:
            flat = [coord for pt in points for coord in pt]
            c.create_line(*flat, fill="#1f8f55", width=1.5, smooth=False)

        n_unique = len(uniq)
        self.graph_status_label.configure(
            text=f"{n} pts • {n_unique} IP{'s' if n_unique != 1 else ''}"
        )

    def _load_wan_history_meta_and_prime_graph(self) -> None:
        if not self.wan_log_file.exists():
            return
        try:
            with self.wan_log_file.open("r", encoding="utf-8") as f:
                rows = list(csv.DictReader(f))
            if not rows:
                return

            prev_ip = None
            change_count = 0
            last_change_ts = "-"
            last_ip = None

            for row in rows:
                ip = (row.get("WAN_IP") or "").strip()
                ts = (row.get("Timestamp") or "").strip()
                if not ip:
                    continue
                if prev_ip is not None and ip != prev_ip:
                    change_count += 1
                    last_change_ts = ts
                prev_ip = ip
                last_ip = ip

            self.total_wan_log_rows = len(rows)
            self.wan_change_count = change_count
            self.last_wan_change_at = last_change_ts
            if self.last_logged_ip is None:
                self.last_logged_ip = last_ip

            recent = rows[-MAX_GRAPH_POINTS:]
            for i, row in enumerate(recent, start=1):
                ip = (row.get("WAN_IP") or "").strip()
                if not ip:
                    continue
                if ip not in self._ip_index_map:
                    self._ip_index_map[ip] = len(self._ip_index_map) + 1
                self._graph_indices.append(i)
                self._graph_values.append(float(self._ip_index_map[ip]))
                self._graph_entry_counter = i

            if self._graph_values:
                self.after(300, self._schedule_graph_redraw)
        except Exception as e:
            self.log_action(f"History load: {e}", "WARN")

    def render_table(self) -> None:
        for item in self.tree.get_children():
            self.tree.delete(item)
        for site in self.websites:
            r = self.results_by_site.get(site)
            values, tag = self._row_data(site, r)
            self.tree.insert("", "end", iid=site, values=values, tags=(tag,))
        self._apply_tree_tags()

    def _update_table_row(self, result: SiteResult) -> None:
        values, tag = self._row_data(result.site, result)
        if self.tree.exists(result.site):
            self.tree.item(result.site, values=values, tags=(tag,))
        else:
            self.render_table()
        self._apply_tree_tags()

    def _row_data(self, site: str, r: Optional[SiteResult]) -> tuple[tuple, str]:
        if r is None:
            return (site, "-", "-", self.wan_ip, "-", "-", "-", "-", "-", "Pending"), "pending"
        tag = "ok" if r.note == "OK" else "bad" if any(k in r.note.lower() for k in ("fail", "error", "connect")) else "warn"
        return (
            (r.site, r.dns_ip, r.tls_ip, r.seen_as, r.dns_ms, r.connect_ms, r.ping_min, r.ping_max, r.ping_avg, r.note),
            tag,
        )

    def _apply_tree_tags(self) -> None:
        self.tree.tag_configure("ok", foreground="#d8ffe5")
        self.tree.tag_configure("warn", foreground="#ffe6a3")
        self.tree.tag_configure("bad", foreground="#ffb3b3")
        self.tree.tag_configure("pending", foreground="#aac7b3")

    def refresh_summary_labels(self) -> None:
        fs_local = self._ip_label_font_size(self.local_ip)
        fs_wan = self._ip_label_font_size(self.wan_ip)
        self.local_value.configure(text=self.local_ip, font=ctk.CTkFont(size=fs_local, weight="bold", family="Consolas"))
        self.wan_value.configure(text=self.wan_ip, font=ctk.CTkFont(size=fs_wan, weight="bold", family="Consolas"))
        self.seen_value.configure(text=self.wan_ip, font=ctk.CTkFont(size=fs_wan, weight="bold", family="Consolas"))
        self.refresh_meta_label.configure(text=f"Last: {self.last_refresh_at}")
        self.wan_change_label.configure(text=f"WAN changes: {self.wan_change_count}")
        self.wan_change_time_label.configure(text=f"Last change: {self.last_wan_change_at}")
        self.total_sites_card.configure(text=str(len(self.websites)))
        self.log_rows_card.configure(text=str(self.total_wan_log_rows))

    def refresh_stat_cards(self) -> None:
        ok = sum(1 for r in self.results_by_site.values() if r.note == "OK")
        tls = sum(1 for r in self.results_by_site.values() if r.tls_ip not in {"-", "N/A"})
        self.ok_sites_card.configure(text=str(ok))
        self.peer_sites_card.configure(text=str(tls))
        self.total_sites_card.configure(text=str(len(self.websites)))
        self.log_rows_card.configure(text=str(self.total_wan_log_rows))

    def set_status(self, text: str, color: str) -> None:
        self.status_chip.configure(text=text, text_color=color)

    def log_action(self, message: str, level: str = "INFO") -> None:
        ts = datetime.now().strftime("%H:%M:%S")
        line = f"[{ts}] [{level:<5}] {message}"
        self._flogger.info(line)

        self.log_text.configure(state="normal")
        self.log_text.insert(END, f"[{ts}] ", "ts")
        self.log_text.insert(END, f"[{level:<5}] ", level if level in ("INFO", "WARN", "ERROR", "RESULT") else "INFO")
        self.log_text.insert(END, message + "\n")
        line_count = int(self.log_text.index(END).split(".")[0]) - 1
        if line_count > MAX_LOG_LINES:
            self.log_text.delete("1.0", f"{line_count - MAX_LOG_LINES}.0")
        self.log_text.see(END)
        self.log_text.configure(state="disabled")

    def clear_log_view(self) -> None:
        self.log_text.configure(state="normal")
        self.log_text.delete("1.0", "end")
        self.log_text.configure(state="disabled")
        self.log_action("Log cleared", "INFO")

    def open_edit_sites_dialog(self) -> None:
        dialog = Toplevel(self)
        dialog.title("Edit Sites")
        dialog.geometry("480x380")
        dialog.transient(self)
        dialog.grab_set()
        dialog.configure(bg="#101712")
        dialog.update_idletasks()
        x = self.winfo_x() + (self.winfo_width() - 480) // 2
        y = self.winfo_y() + (self.winfo_height() - 380) // 2
        dialog.geometry(f"+{x}+{y}")

        ctk.CTkLabel(dialog, text="One domain per line  •  # comments ignored", text_color="#9dd6b3").pack(pady=(12, 6))
        tf = ctk.CTkFrame(dialog, fg_color="#0f1511", corner_radius=8)
        tf.pack(fill=tk.BOTH, expand=True, padx=16, pady=4)
        text_w = scrolledtext.ScrolledText(
            tf, font=("Consolas", 10), bg="#0d120f", fg="#dcfce7",
            insertbackground="#9dffbf", bd=0, padx=8, pady=6, wrap="none"
        )
        text_w.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        text_w.insert(END, "\n".join(self.websites))

        btn_f = ctk.CTkFrame(dialog, fg_color="transparent")
        btn_f.pack(fill="x", padx=16, pady=(4, 12))

        def save_and_close():
            lines = [l.strip() for l in text_w.get("1.0", END).split("\n") if l.strip() and not l.strip().startswith("#")]
            cleaned = list(dict.fromkeys(filter(None, (self.normalize_site(l) for l in lines))))
            if cleaned:
                self.websites = cleaned
                self.save_config()
                self.refresh_site_listbox()
                self.render_table()
                self.refresh_stat_cards()
                self.log_action(f"Sites updated ({len(cleaned)})", "INFO")
            dialog.destroy()

        ctk.CTkButton(btn_f, text="Cancel", width=80, command=dialog.destroy, fg_color="#3a3a3a", hover_color="#4a4a4a").pack(side=tk.RIGHT, padx=4)
        ctk.CTkButton(btn_f, text="Save", width=90, command=save_and_close, fg_color="#1f8f55", hover_color="#166c40").pack(side=tk.RIGHT, padx=4)
        text_w.focus_set()

    def on_site_select(self, event=None) -> None:
        sel = self.site_listbox.curselection()
        if sel:
            self.set_status(f"Selected: {self.site_listbox.get(sel[0])}", "#b6f59d")

    def refresh_site_listbox(self) -> None:
        self.site_listbox.delete(0, "end")
        for s in self.websites:
            self.site_listbox.insert("end", s)

    def add_site(self) -> None:
        site = self.normalize_site(self.site_entry.get().strip().lower())
        if not site:
            self.set_status("Enter a valid domain", "#ffd27d")
            return
        if site in self.websites:
            self.set_status("Already tracked", "#ffd27d")
            return
        self.websites.append(site)
        self.save_config()
        self.refresh_site_listbox()
        self.refresh_summary_labels()
        self.site_entry.delete(0, "end")
        self.log_action(f"Added {site}", "INFO")
        threading.Thread(target=self._resolve_single_worker, args=(site,), daemon=True).start()

    def remove_selected_site(self) -> None:
        sel = self.site_listbox.curselection()
        if not sel:
            self.set_status("Select a site first", "#ffd27d")
            return
        site = self.websites.pop(sel[0])
        self.results_by_site.pop(site, None)
        self.save_config()
        self.refresh_site_listbox()
        self.render_table()
        self.refresh_stat_cards()
        self.refresh_summary_labels()
        self.log_action(f"Removed {site}", "INFO")

    def move_selected_site(self, direction: int) -> None:
        sel = self.site_listbox.curselection()
        if not sel:
            return
        idx = sel[0]
        new = idx + direction
        if 0 <= new < len(self.websites):
            self.websites[idx], self.websites[new] = self.websites[new], self.websites[idx]
            self.save_config()
            self.refresh_site_listbox()
            self.site_listbox.selection_set(new)

    def normalize_site(self, value: str) -> str:
        if not value:
            return ""
        v = value.replace("https://", "").replace("http://", "").strip().strip("/")
        return v.split("/")[0].strip()

    def on_exit(self) -> None:
        self.log_action("Exiting", "INFO")
        self.stop_event.set()
        self.save_config()
        self.executor.shutdown(wait=False, cancel_futures=True)
        self.destroy()


def main() -> None:
    app = IPMonitorApp()
    app.mainloop()


if __name__ == "__main__":
    main()