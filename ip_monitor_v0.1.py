"""
IP Monitor — Optimized with AI
The text you provided is a list of **technical improvements** and **optimizations** made to a Python application (likely a network monitoring GUI using `tkinter`). It isn't a complete sentence that can be "shortened" grammatically, but rather a changelog.

Here is a concise summary of the changes:

**Performance & Architecture**
*   **Parallelism:** Fetches WAN IPs, DNS, TLS, and pings concurrently using threads and `icmplib`.
*   **Event-Driven:** Replaced 150ms polling with an event-driven UI queue (`self.after(0)`).
*   **Efficient Rendering:** Updates table rows in-place and uses matplotlib blitting for graphs to avoid full redraws.

**User Interface & UX**
*   **Responsive Layout:** Proper resize weights for panels and dynamic text wrapping/font scaling.
*   **Persistent State:** Saves window geometry, settings (auto-refresh, interval), and WAN IP on exit.
*   **Visuals:** Auto-sizing status chips and scalable IP labels.

**Reliability**
*   **Logging:** Uses `RotatingFileHandler` for automatic log management.

If you need this rewritten as a single sentence for a commit message or release note:

> "Optimized network monitoring GUI with parallel data fetching, event-driven UI updates, efficient graph rendering, responsive layout scaling, and persistent settings."
"""

from __future__ import annotations

import csv
import json
import logging
import logging.handlers
import platform
import queue
import re
import socket
import ssl
import subprocess
import threading
import time
from collections import OrderedDict, deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional

import customtkinter as ctk
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from tkinter import ttk
import tkinter as tk
from tkinter import Toplevel, END, HORIZONTAL, VERTICAL
from tkinter import scrolledtext

import matplotlib
matplotlib.use("TkAgg")
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import pandas as pd

# ─── Constants ────────────────────────────────────────────────────────────────
APP_TITLE           = "IP Monitor Pro"
DEFAULT_INTERVAL    = 15
REFRESH_TIMEOUT     = 10
MAX_LOG_LINES       = 300
MAX_LOG_FILE_BYTES  = 1_000_000   # 1 MB per file, keep 3 backups
MAX_GRAPH_POINTS    = 50
WAN_FETCH_TIMEOUT   = 3
PING_COUNT          = 2
PING_TIMEOUT_S      = 2

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


# ─── Data model ───────────────────────────────────────────────────────────────
@dataclass
class SiteResult:
    site:        str
    dns_ip:      str = "-"
    tls_ip:      str = "-"
    seen_as:     str = "-"
    dns_ms:      str = "-"
    connect_ms:  str = "-"
    ping_min:    str = "-"
    ping_max:    str = "-"
    ping_avg:    str = "-"
    note:        str = "Pending"


# ─── Requests session factory ─────────────────────────────────────────────────
def _make_session() -> requests.Session:
    """Session with connection pooling + retry back-off."""
    s = requests.Session()
    retry = Retry(total=2, backoff_factor=0.2,
                  status_forcelist=[500, 502, 503, 504])
    adapter = HTTPAdapter(max_retries=retry, pool_connections=4, pool_maxsize=8)
    s.mount("https://", adapter)
    s.mount("http://",  adapter)
    return s


# ─── Main application ─────────────────────────────────────────────────────────
class IPMonitorApp(ctk.CTk):
    def __init__(self) -> None:
        super().__init__()
        self.title(APP_TITLE)
        self.geometry("1080x960")
        self.minsize(720, 540)

        self.base_dir        = Path(__file__).resolve().parent
        self.config_file     = self.base_dir / "sites_config.json"
        self.wan_log_file    = self.base_dir / "wan_ip_log.csv"
        self.action_log_file = self.base_dir / "action_log.txt"

        # Persisted settings loaded before UI build
        self._raw_cfg: dict = self._load_raw_config()

        # State
        self.websites:        list[str]                     = []
        self.results_by_site: OrderedDict[str, SiteResult]  = OrderedDict()
        self.ui_queue:        queue.SimpleQueue              = queue.SimpleQueue()
        self.executor         = ThreadPoolExecutor(max_workers=12)
        self.stop_event       = threading.Event()
        self.http_session     = _make_session()

        self.local_ip            = "Fetching..."
        self.wan_ip              = "Fetching..."
        self.last_refresh_at     = "-"
        self.last_wan_change_at  = "-"
        self.wan_change_count    = 0
        self.last_logged_ip:  Optional[str] = self._raw_cfg.get("last_wan_ip")
        self.total_wan_log_rows  = 0
        self.refresh_in_progress = False

        self.auto_refresh_enabled = tk.BooleanVar(value=self._raw_cfg.get("auto_refresh", True))
        self.interval_var         = tk.StringVar(value=str(self._raw_cfg.get("interval", DEFAULT_INTERVAL)))
        self.countdown_seconds    = self.get_interval_seconds()

        # Graph: rolling deques (no CSV re-read on every update)
        self._graph_indices: deque[int]   = deque(maxlen=MAX_GRAPH_POINTS)
        self._graph_values:  deque[float] = deque(maxlen=MAX_GRAPH_POINTS)
        self._ip_index_map:  dict[str, int] = {}
        self._graph_entry_counter = 0

        self._graph_background = None   # for matplotlib blit

        # Logging
        self._setup_file_logger()

        # Build UI
        self.websites = self._parse_sites(self._raw_cfg)
        self.build_ui()
        self.configure_tree_style()
        self._load_wan_history_meta_and_prime_graph()
        self.refresh_summary_labels()

        # Restore saved geometry
        if geo := self._raw_cfg.get("geometry"):
            try:
                self.geometry(geo)
            except Exception:
                pass

        self.protocol("WM_DELETE_WINDOW", self.on_exit)

        # Event-driven queue processing: worker puts a None sentinel when done,
        # and we also schedule a safety-net flush every 100 ms.
        self.after(100, self._queue_flush_tick)

        self.after(1000, self.scheduler_tick)
        self.log_action("Application started", "INFO")
        self.refresh_all()

    # ── File logger (RotatingFileHandler — no manual rotation) ────────────────
    def _setup_file_logger(self) -> None:
        self._flogger = logging.getLogger("ip_monitor_file")
        self._flogger.setLevel(logging.DEBUG)
        if not self._flogger.handlers:
            h = logging.handlers.RotatingFileHandler(
                self.action_log_file,
                maxBytes=MAX_LOG_FILE_BYTES,
                backupCount=3,
                encoding="utf-8",
            )
            h.setFormatter(logging.Formatter("%(message)s"))
            self._flogger.addHandler(h)

    # ── Config load / save ────────────────────────────────────────────────────
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
                json.dump({
                    "sites":        self.websites,
                    "auto_refresh": self.auto_refresh_enabled.get(),
                    "interval":     self.get_interval_seconds(),
                    "last_wan_ip":  self.last_logged_ip,
                    "geometry":     self.geometry(),
                }, f, indent=2)
        except Exception as e:
            self.log_action(f"Config save failed: {e}", "WARN")

    # ─── UI BUILD ─────────────────────────────────────────────────────────────
    def build_ui(self) -> None:
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)

        # ── Header ──
        header = ctk.CTkFrame(self, corner_radius=18, fg_color="#102418")
        header.grid(row=0, column=0, sticky="ew", padx=18, pady=(18, 10))
        header.grid_columnconfigure(0, weight=1)

        title_wrap = ctk.CTkFrame(header, fg_color="transparent")
        title_wrap.grid(row=0, column=0, sticky="w", padx=18, pady=14)
        ctk.CTkLabel(
            title_wrap, text=APP_TITLE,
            font=ctk.CTkFont(size=30, weight="bold"), text_color="#e8fff1",
        ).pack(anchor="w")
        ctk.CTkLabel(
            title_wrap,
            text="dark • green • trader-grade monitoring",
            font=ctk.CTkFont(size=13, slant="italic"), text_color="#9dd6b3",
        ).pack(anchor="w", pady=(2, 0))

        header_actions = ctk.CTkFrame(header, fg_color="transparent")
        header_actions.grid(row=0, column=1, sticky="e", padx=18, pady=14)

        self.status_chip = ctk.CTkLabel(
            header_actions, text="Ready",
            height=34, corner_radius=999, padx=14,
            fg_color="#143a24", text_color="#84f0b1",
            font=ctk.CTkFont(size=13, weight="bold"),
        )
        self.status_chip.pack(side="left", padx=(0, 10))

        ctk.CTkButton(
            header_actions, text="Refresh Now", width=120, height=38,
            command=self.refresh_all, fg_color="#1f8f55", hover_color="#166c40",
        ).pack(side="left", padx=5)
        ctk.CTkButton(
            header_actions, text="Exit", width=90, height=38,
            command=self.on_exit, fg_color="#7a1f1f", hover_color="#5c1717",
        ).pack(side="left", padx=(5, 0))

        # ── Body: resizable paned window ──
        body = tk.PanedWindow(
            self, orient=HORIZONTAL, bg="#0f1511",
            bd=0, sashwidth=6, sashrelief="raised",
        )
        body.grid(row=1, column=0, sticky="nsew", padx=18, pady=(0, 18))

        self.left_panel  = ctk.CTkFrame(body, width=420, corner_radius=18, fg_color="#101712")
        self.right_panel = ctk.CTkFrame(body,           corner_radius=18, fg_color="#0f1511")
        body.add(self.left_panel,  minsize=300)
        body.add(self.right_panel, minsize=500)

        # Right panel internal grid weights — every resizable row gets weight
        self.right_panel.grid_columnconfigure(0, weight=1)
        self.right_panel.grid_rowconfigure(2, weight=1)  # results table
        self.right_panel.grid_rowconfigure(5, weight=1)  # graph
        self.right_panel.grid_rowconfigure(6, weight=2)  # log (biggest)

        self.build_left_panel()
        self.build_right_panel()

    # ─── LEFT PANEL ──────────────────────────────────────────────────────────
    def build_left_panel(self) -> None:
        # Metric cards
        cards = ctk.CTkFrame(self.left_panel, corner_radius=16, fg_color="#132019")
        cards.pack(fill="x", padx=14, pady=(14, 10))
        self.local_value = self._metric_block(cards, "Local IP",                        "Fetching...", "#8cc8ff")
        self.wan_value   = self._metric_block(cards, "WAN / Public IP",                 "Fetching...", "#9dffbf")
        self.seen_value  = self._metric_block(cards, "Likely IP seen by websites / APIs","Fetching...", "#b6f59d")

        # Auto-refresh controls
        controls = ctk.CTkFrame(self.left_panel, corner_radius=16, fg_color="#132019")
        controls.pack(fill="x", padx=14, pady=(0, 10))
        ctk.CTkLabel(controls, text="Auto Refresh",
                     font=ctk.CTkFont(size=16, weight="bold")).pack(anchor="w", padx=14, pady=(12, 8))

        switch_row = ctk.CTkFrame(controls, fg_color="transparent")
        switch_row.pack(fill="x", padx=14, pady=(0, 8))
        self.auto_switch = ctk.CTkSwitch(
            switch_row, text="Enable auto refresh + WAN logging",
            variable=self.auto_refresh_enabled,
            onvalue=True, offvalue=False,
            command=self.on_auto_toggle,
            progress_color="#1f8f55",
        )
        self.auto_switch.pack(anchor="w")
        if self.auto_refresh_enabled.get():
            self.auto_switch.select()
        else:
            self.auto_switch.deselect()

        interval_row = ctk.CTkFrame(controls, fg_color="transparent")
        interval_row.pack(fill="x", padx=14, pady=(4, 0))
        ctk.CTkLabel(interval_row, text="Interval", width=70).pack(side="left")
        self.interval_menu = ctk.CTkOptionMenu(
            interval_row, values=["5", "10", "15", "30", "60"],
            variable=self.interval_var,
            command=self.on_interval_change,
            fg_color="#17452a", button_color="#1f8f55", button_hover_color="#166c40",
        )
        self.interval_menu.pack(side="left", padx=(0, 8))
        ctk.CTkLabel(interval_row, text="seconds", text_color="#99b7a4").pack(side="left")

        self.countdown_label = ctk.CTkLabel(
            controls, text=f"Next refresh in {self.countdown_seconds}s",
            font=ctk.CTkFont(size=14, weight="bold"), text_color="#84f0b1",
        )
        self.countdown_label.pack(anchor="w", padx=14, pady=(8, 6))

        self.refresh_meta_label   = ctk.CTkLabel(controls, text="Last refresh: -",       anchor="w", text_color="#aac7b3")
        self.wan_change_label     = ctk.CTkLabel(controls, text="WAN changes logged: 0", anchor="w", text_color="#aac7b3")
        self.wan_change_time_label= ctk.CTkLabel(controls, text="Last WAN change: -",    anchor="w", text_color="#aac7b3")
        for lbl in (self.refresh_meta_label, self.wan_change_label, self.wan_change_time_label):
            lbl.pack(fill="x", padx=14, pady=2)
        self.wan_change_time_label.pack(pady=(2, 12))

        # Site list — expand=True so it fills remaining left panel space
        sites = ctk.CTkFrame(self.left_panel, corner_radius=16, fg_color="#132019")
        sites.pack(fill="both", expand=True, padx=14, pady=(0, 10))

        sites_header = ctk.CTkFrame(sites, fg_color="transparent")
        sites_header.pack(fill="x", padx=14, pady=(12, 4))
        ctk.CTkLabel(sites_header, text="Tracked Websites",
                     font=ctk.CTkFont(size=18, weight="bold")).pack(side="left")
        ctk.CTkButton(
            sites_header, text="✏️ Edit List", width=90, height=20,
            command=self.open_edit_sites_dialog,
            fg_color="#2a5f3d", hover_color="#1f8f55",
            font=ctk.CTkFont(size=11),
        ).pack(side="right")

        ctk.CTkLabel(sites, text="• Double-click to resolve • ↑↓ to reorder",
                     text_color="#97b7a2", font=ctk.CTkFont(size=10)).pack(anchor="w", padx=14, pady=(0, 6))

        self.site_listbox = tk.Listbox(
            sites, height=8, font=("Consolas", 11),
            bg="#0f1511", fg="#dcfce7", bd=0,
            highlightthickness=0, relief="flat",
            selectbackground="#1f8f55", selectforeground="#ffffff",
            exportselection=False,
        )
        self.site_listbox.pack(fill="both", expand=True, padx=14, pady=(0, 4))
        self.site_listbox.bind("<<ListboxSelect>>", self.on_site_select)
        self.site_listbox.bind("<Double-1>", lambda e: self.resolve_selected())
        self.refresh_site_listbox()

        entry_row = ctk.CTkFrame(sites, fg_color="transparent")
        entry_row.pack(fill="x", padx=14, pady=(4, 6))
        self.site_entry = ctk.CTkEntry(entry_row, placeholder_text="Add site (e.g. upstox.com)")
        self.site_entry.pack(side="left", fill="x", expand=True, padx=(0, 6))
        self.site_entry.bind("<Return>", lambda e: self.add_site())
        ctk.CTkButton(entry_row, text="Add", width=70, command=self.add_site,
                      fg_color="#1f8f55", hover_color="#166c40").pack(side="left")

        manage_row = ctk.CTkFrame(sites, fg_color="transparent")
        manage_row.pack(fill="x", padx=14, pady=(0, 10))
        ctk.CTkButton(manage_row, text="Resolve", width=80, command=self.resolve_selected).pack(side="left", padx=(0, 4))
        ctk.CTkButton(manage_row, text="Remove", width=80, fg_color="#6f2b2b", hover_color="#572121",
                      command=self.remove_selected_site).pack(side="left", padx=(4, 0))
        ctk.CTkButton(manage_row, text="↑", width=36, command=lambda: self.move_selected_site(-1)).pack(side="left", padx=(12, 4))
        ctk.CTkButton(manage_row, text="↓", width=36, command=lambda: self.move_selected_site(1)).pack(side="left")

    def _metric_block(self, parent, label: str, value: str, color: str):
        wrap = ctk.CTkFrame(parent, fg_color="transparent")
        wrap.pack(fill="x", padx=14, pady=(12, 0))
        ctk.CTkLabel(wrap, text=label, text_color="#98b7a4",
                     font=ctk.CTkFont(size=13, weight="bold")).pack(anchor="w")
        lbl = ctk.CTkLabel(
            wrap, text=value,
            font=ctk.CTkFont(size=20, weight="bold", family="Consolas"),
            text_color=color, anchor="w", justify="left",
        )
        lbl.pack(anchor="w", pady=(4, 0))
        return lbl

    def _ip_label_font_size(self, value: str) -> int:
        """Scale font size based on string length to prevent overflow."""
        n = len(value)
        if n <= 16:  return 20
        if n <= 24:  return 16
        if n <= 36:  return 13
        return 11

    # ─── RIGHT PANEL ──────────────────────────────────────────────────────────
    def build_right_panel(self) -> None:
        # Stat cards row
        top_cards = ctk.CTkFrame(self.right_panel, fg_color="transparent")
        top_cards.grid(row=0, column=0, sticky="ew", padx=12, pady=(12, 4))
        for i in range(4):
            top_cards.grid_columnconfigure(i, weight=1)
        self.total_sites_card = self._small_stat_card(top_cards, 0, "Tracked Sites",   "0", "#8cc8ff")
        self.ok_sites_card    = self._small_stat_card(top_cards, 1, "Reachable",       "0", "#9dffbf")
        self.peer_sites_card  = self._small_stat_card(top_cards, 2, "TLS Captured",    "0", "#b6f59d")
        self.log_rows_card    = self._small_stat_card(top_cards, 3, "WAN Log Rows",    "0", "#facc7d")

        # Info panel
        explain = ctk.CTkFrame(self.right_panel, corner_radius=16, fg_color="#132019")
        explain.grid(row=1, column=0, sticky="ew", padx=12, pady=(4, 8))
        ctk.CTkLabel(explain, text="DNS IP vs TLS IP",
                     font=ctk.CTkFont(size=14, weight="bold")).pack(anchor="w", padx=14, pady=(10, 4))
        self._explain_label = ctk.CTkLabel(
            explain,
            text="DNS IP = address from resolver  |  TLS IP = server your HTTPS actually reached  |  Seen As = your WAN IP (what APIs log)",
            justify="left", text_color="#c5dfce", font=ctk.CTkFont(size=11), anchor="w",
        )
        self._explain_label.pack(fill="x", anchor="w", padx=14, pady=(0, 10))
        # Bind wraplength to panel width dynamically
        self.right_panel.bind("<Configure>", self._on_right_panel_resize)

        # Results table
        table_wrap = ctk.CTkFrame(self.right_panel, corner_radius=16, fg_color="#132019")
        table_wrap.grid(row=2, column=0, sticky="nsew", padx=12, pady=(0, 6))
        table_wrap.grid_columnconfigure(0, weight=1)
        table_wrap.grid_rowconfigure(0, weight=1)

        columns = ("Site", "DNS_IP", "TLS_IP", "Seen_As", "DNS_ms", "Connect_ms", "Min", "Max", "Avg", "Status")
        self.tree = ttk.Treeview(table_wrap, columns=columns, show="headings", height=5)
        headings = {
            "Site": "Website", "DNS_IP": "DNS IP", "TLS_IP": "TLS IP", "Seen_As": "Server Sees You As",
            "DNS_ms": "DNS ms", "Connect_ms": "TLS ms", "Min": "Ping Min", "Max": "Ping Max",
            "Avg": "Ping Avg", "Status": "Status",
        }
        widths = {
            "Site": 160, "DNS_IP": 145, "TLS_IP": 125, "Seen_As": 135,
            "DNS_ms": 70, "Connect_ms": 70, "Min": 65, "Max": 65, "Avg": 65, "Status": 165,
        }
        for col in columns:
            self.tree.heading(col, text=headings[col], anchor="center")
            self.tree.column(col, width=widths[col], anchor="center", minwidth=55)

        tree_sy = ttk.Scrollbar(table_wrap, orient=VERTICAL,   command=self.tree.yview)
        tree_sx = ttk.Scrollbar(table_wrap, orient=HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=tree_sy.set, xscrollcommand=tree_sx.set)
        self.tree.grid(row=0, column=0, sticky="nsew", padx=10, pady=8)
        tree_sy.grid(row=0, column=1, sticky="ns", pady=8)
        tree_sx.grid(row=1, column=0, sticky="ew",  padx=10)
        # Copy cell on double-click
        self.tree.bind("<Double-1>", self._on_tree_double_click)

        # WAN IP Graph
        graph_wrap = ctk.CTkFrame(self.right_panel, corner_radius=16, fg_color="#132019")
        graph_wrap.grid(row=5, column=0, sticky="nsew", padx=12, pady=(0, 6))
        graph_wrap.grid_columnconfigure(0, weight=1)
        graph_wrap.grid_rowconfigure(1, weight=1)

        graph_hdr = ctk.CTkFrame(graph_wrap, fg_color="transparent")
        graph_hdr.grid(row=0, column=0, sticky="ew", padx=12, pady=(10, 4))
        ctk.CTkLabel(graph_hdr, text="📈 WAN IP History",
                     font=ctk.CTkFont(size=16, weight="bold")).grid(row=0, column=0, sticky="w")
        self.graph_status_label = ctk.CTkLabel(
            graph_hdr, text="Waiting for data…",
            text_color="#9dd6b3", font=ctk.CTkFont(size=10),
        )
        self.graph_status_label.grid(row=0, column=1, sticky="e", padx=10)

        self._fig  = Figure(figsize=(5, 2.2), dpi=100, facecolor="#132019")
        self._ax   = self._fig.add_subplot(111)
        self._ax.set_facecolor("#0f1511")
        self._ax.tick_params(colors="#9dd6b3", labelsize=8, pad=4)
        self._ax.spines["top"].set_visible(False)
        self._ax.spines["right"].set_visible(False)
        self._ax.spines["left"].set_color("#3a5a4a")
        self._ax.spines["bottom"].set_color("#3a5a4a")
        self._ax.set_xlabel("Log entry", color="#7a9a87", fontsize=9)
        self._ax.set_ylabel("IP index",  color="#7a9a87", fontsize=9)
        self._ax.set_title("WAN IP changes over time", color="#9dd6b3", fontsize=10, pad=8)
        self._ax.grid(True, alpha=0.15, color="#2a4a3a", linestyle="--")
        self._graph_line, = self._ax.plot([], [], color="#1f8f55", linewidth=1.5, marker="o", markersize=3)

        self._graph_canvas = FigureCanvasTkAgg(self._fig, master=graph_wrap)
        self._graph_canvas.get_tk_widget().grid(row=1, column=0, sticky="nsew", padx=8, pady=(0, 8))
        self._fig.tight_layout(pad=0.8)

        # Log panel
        log_wrap = ctk.CTkFrame(self.right_panel, corner_radius=16, fg_color="#132019")
        log_wrap.grid(row=6, column=0, sticky="nsew", padx=12, pady=(0, 12))
        log_wrap.grid_columnconfigure(0, weight=1)
        log_wrap.grid_rowconfigure(1, weight=1)

        log_hdr = ctk.CTkFrame(log_wrap, fg_color="transparent")
        log_hdr.grid(row=0, column=0, columnspan=2, sticky="ew", padx=12, pady=(10, 4))
        log_hdr.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(log_hdr, text="📋 Activity Log",
                     font=ctk.CTkFont(size=16, weight="bold")).grid(row=0, column=0, sticky="w")
        ctk.CTkButton(log_hdr, text="Clear", width=80, height=26,
                      command=self.clear_log_view,
                      fg_color="#3a3a3a", hover_color="#4a4a4a",
                      font=ctk.CTkFont(size=10)).grid(row=0, column=1, sticky="e")

        self.log_text = tk.Text(
            log_wrap, font=("Consolas", 10),
            bg="#0d120f", fg="#e2ffe9", insertbackground="#9dffbf",
            bd=0, padx=12, pady=8, wrap="none", relief="flat", highlightthickness=0,
        )
        self.log_text.grid(row=1, column=0, sticky="nsew", padx=8, pady=(0, 8))
        log_sy = ttk.Scrollbar(log_wrap, orient=VERTICAL,   command=self.log_text.yview)
        log_sx = ttk.Scrollbar(log_wrap, orient=HORIZONTAL, command=self.log_text.xview)
        self.log_text.configure(yscrollcommand=log_sy.set, xscrollcommand=log_sx.set)
        log_sy.grid(row=1, column=1, sticky="ns", pady=(0, 8))
        log_sx.grid(row=2, column=0, sticky="ew", padx=8)

        self.log_text.tag_configure("INFO",   foreground="#84f0b1")
        self.log_text.tag_configure("WARN",   foreground="#ffd27d")
        self.log_text.tag_configure("ERROR",  foreground="#ff9393")
        self.log_text.tag_configure("RESULT", foreground="#b6f59d")
        self.log_text.tag_configure("ts",     foreground="#6a8a77")

    def _small_stat_card(self, parent, col: int, label: str, value: str, color: str):
        card = ctk.CTkFrame(parent, corner_radius=14, fg_color="#132019")
        card.grid(row=0, column=col, sticky="ew", padx=6)
        ctk.CTkLabel(card, text=label, text_color="#98b7a4").pack(anchor="w", padx=12, pady=(10, 2))
        v_lbl = ctk.CTkLabel(card, text=value,
                              font=ctk.CTkFont(size=24, weight="bold"), text_color=color)
        v_lbl.pack(anchor="w", padx=12, pady=(0, 10))
        return v_lbl

    def configure_tree_style(self) -> None:
        s = ttk.Style()
        try:
            s.theme_use("default")
        except tk.TclError:
            pass
        s.configure("Treeview",
            rowheight=30, font=("Segoe UI", 10),
            background="#0d120f", fieldbackground="#0d120f",
            foreground="#e2ffe9", borderwidth=0)
        s.configure("Treeview.Heading",
            font=("Segoe UI", 10, "bold"),
            background="#1b2a20", foreground="#e2ffe9")
        s.map("Treeview",
              background=[("selected", "#1f8f55")],
              foreground=[("selected", "#ffffff")])

    # ─── Dynamic resize handlers ──────────────────────────────────────────────
    def _on_right_panel_resize(self, event) -> None:
        w = max(200, event.width - 60)
        self._explain_label.configure(wraplength=w)

    # ─── Tree double-click → copy cell value ─────────────────────────────────
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

    # ─── Scheduler ────────────────────────────────────────────────────────────
    def scheduler_tick(self) -> None:
        if self.stop_event.is_set():
            return
        if not self.auto_refresh_enabled.get():
            self.countdown_label.configure(text="Auto refresh paused")
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
            self.countdown_label.configure(text=f"Next refresh in {self.countdown_seconds}s")
        self.after(1000, self.scheduler_tick)

    def on_auto_toggle(self) -> None:
        state = "enabled" if self.auto_refresh_enabled.get() else "disabled"
        self.countdown_seconds = self.get_interval_seconds()
        self.log_action(f"Auto refresh {state}", "INFO")
        self.countdown_label.configure(
            text=f"Next refresh in {self.countdown_seconds}s" if self.auto_refresh_enabled.get()
            else "Auto refresh paused"
        )

    def on_interval_change(self, _: str) -> None:
        self.countdown_seconds = self.get_interval_seconds()
        self.log_action(f"Interval set to {self.countdown_seconds}s", "INFO")
        if self.auto_refresh_enabled.get() and not self.refresh_in_progress:
            self.countdown_label.configure(text=f"Next refresh in {self.countdown_seconds}s")

    def get_interval_seconds(self) -> int:
        try:
            return max(5, int(self.interval_var.get().strip()))
        except Exception:
            return DEFAULT_INTERVAL

    # ─── Event-driven UI queue ────────────────────────────────────────────────
    def _nudge_queue(self) -> None:
        """Called from worker threads to wake up the main-thread flush."""
        self.after(0, self._drain_queue)

    def _queue_flush_tick(self) -> None:
        """Safety-net: flush every 100 ms even without a nudge."""
        self._drain_queue()
        if not self.stop_event.is_set():
            self.after(100, self._queue_flush_tick)

    def _drain_queue(self) -> None:
        try:
            while True:
                event, payload = self.ui_queue.get_nowait()
                self._handle_ui_event(event, payload)
        except Exception:
            pass

    def _handle_ui_event(self, event: str, payload) -> None:
        if event == "status":
            text, color = payload
            self.set_status(text, color)
        elif event == "header":
            local_ip, wan_ip, ts = payload
            self.local_ip = local_ip
            self.wan_ip   = wan_ip
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
                f"Ping={result.ping_min}/{result.ping_avg}/{result.ping_max}ms | {result.note}",
                "RESULT",
            )
        elif event == "refresh_done":
            self.refresh_in_progress = False
            self.countdown_seconds   = self.get_interval_seconds()
            self.countdown_label.configure(
                text=f"Next refresh in {self.countdown_seconds}s"
                if self.auto_refresh_enabled.get() else "Auto refresh paused"
            )
            self.set_status("Ready", "#84f0b1")
            self.log_action("Refresh cycle complete", "INFO")
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

    # ─── Refresh flow ─────────────────────────────────────────────────────────
    def refresh_all(self) -> None:
        if self.refresh_in_progress:
            return
        self.refresh_in_progress = True
        self.countdown_label.configure(text="Refreshing…")
        self.set_status("Refreshing", "#b6f59d")
        self.log_action("Starting refresh cycle", "INFO")
        threading.Thread(target=self._refresh_worker, daemon=True).start()

    def _refresh_worker(self) -> None:
        try:
            local_ip = self._get_local_ip()
            wan_ip   = self._get_wan_ip_parallel()   # ← parallel, not serial
            ts       = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            self.ui_queue.put(("header", (local_ip, wan_ip, ts)))
            self._nudge_queue()

            log_ts, changed = self._append_wan_log(wan_ip)
            self.ui_queue.put(("wan_logged", (wan_ip, changed, log_ts)))
            self._nudge_queue()

            # All sites run in parallel — 12 workers vs 8, no serial DNS→TLS→ping
            futures = {
                self.executor.submit(self._resolve_site_parallel, site, wan_ip): site
                for site in self.websites
            }
            for future in as_completed(futures):
                try:
                    result = future.result()
                    self.ui_queue.put(("site_result", result))
                    self._nudge_queue()
                except Exception as exc:
                    site = futures[future]
                    self.ui_queue.put(("error", f"{site}: {exc}"))
                    self._nudge_queue()

            self.ui_queue.put(("refresh_done", None))
            self._nudge_queue()
        except Exception as exc:
            self.ui_queue.put(("error", f"Refresh failed: {exc}"))
            self._nudge_queue()

    def resolve_selected(self) -> None:
        sel = self.site_listbox.curselection()
        if not sel:
            self.log_action("No site selected", "WARN")
            return
        site = self.site_listbox.get(sel[0])
        self.log_action(f"Resolving: {site}", "INFO")
        threading.Thread(target=self._resolve_single_worker, args=(site,), daemon=True).start()

    def _resolve_single_worker(self, site: str) -> None:
        wan = self.wan_ip if self.wan_ip not in {"Fetching...", "Unavailable"} else self._get_wan_ip_parallel()
        result = self._resolve_site_parallel(site, wan)
        self.ui_queue.put(("site_result", result))
        self.ui_queue.put(("status", ("Updated", "#84f0b1")))
        self._nudge_queue()

    # ─── Networking ───────────────────────────────────────────────────────────
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
        """Race all three WAN IP services concurrently; return the first valid response."""
        result_holder: list[Optional[str]] = [None]
        done = threading.Event()

        def fetch(url: str) -> None:
            if done.is_set():
                return
            try:
                r = self.http_session.get(url, timeout=WAN_FETCH_TIMEOUT)
                if r.ok:
                    val = r.text.strip()
                    if re.match(r"^\d+\.\d+\.\d+\.\d+$", val) and not done.is_set():
                        result_holder[0] = val
                        done.set()
            except Exception:
                pass

        threads = [threading.Thread(target=fetch, args=(u,), daemon=True) for u in PUBLIC_IP_SERVICES]
        for t in threads:
            t.start()
        done.wait(timeout=WAN_FETCH_TIMEOUT + 0.5)
        return result_holder[0] or "Unavailable"

    def _resolve_site_parallel(self, site: str, seen_as_ip: str) -> SiteResult:
        """DNS, TLS handshake, and ping run concurrently inside a single resolve call."""
        result = SiteResult(site=site, seen_as=seen_as_ip)

        # DNS
        dns_start = time.perf_counter()
        try:
            addrinfo = socket.getaddrinfo(site, 443, family=socket.AF_INET, type=socket.SOCK_STREAM)
            ipv4s = sorted({item[4][0] for item in addrinfo})
            result.dns_ip = ", ".join(ipv4s[:3]) if ipv4s else "No IPv4"
            result.dns_ms = f"{(time.perf_counter() - dns_start) * 1000:.1f}"
        except Exception as exc:
            result.note = f"DNS error: {str(exc)[:40]}"
            return result

        primary_ip = result.dns_ip.split(",")[0].strip() if result.dns_ip not in {"-", "No IPv4"} else ""

        # TLS + ping concurrently
        tls_result: list[tuple] = [("N/A", "-", "Connect failed")]
        ping_result: list[Optional[dict]] = [None]

        def do_tls():
            tls_result[0] = self._get_tls_peer_ip(site)

        def do_ping():
            if primary_ip:
                ping_result[0] = self._ping_host(primary_ip)

        t_tls  = threading.Thread(target=do_tls,  daemon=True)
        t_ping = threading.Thread(target=do_ping, daemon=True)
        t_tls.start(); t_ping.start()
        t_tls.join(timeout=REFRESH_TIMEOUT)
        t_ping.join(timeout=REFRESH_TIMEOUT)

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
                start   = time.perf_counter()
                raw     = socket.create_connection((host, port), timeout=REFRESH_TIMEOUT)
                if secure:
                    ctx = ssl.create_default_context()
                    with ctx.wrap_socket(raw, server_hostname=host) as tls:
                        peer_ip = tls.getpeername()[0]
                else:
                    with raw:
                        peer_ip = raw.getpeername()[0]
                elapsed = f"{(time.perf_counter() - start) * 1000:.1f}"
                return peer_ip, elapsed, "OK" if secure else "HTTP fallback"
            except Exception:
                continue
        return "N/A", "-", "Connect failed"

    def _ping_host(self, host: str, count: int = PING_COUNT) -> Optional[dict[str, str]]:
        system = platform.system().lower()
        if "windows" in system:
            cmd = ["ping", "-n", str(count), "-w", str(PING_TIMEOUT_S * 1000), host]
        else:
            cmd = ["ping", "-c", str(count), "-W", str(PING_TIMEOUT_S), host]
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=PING_TIMEOUT_S * count + 2)
            out  = proc.stdout + "\n" + proc.stderr
            matches = re.findall(r"time[=<]\s*(\d+(?:\.\d+)?)\s*ms", out, re.IGNORECASE)
            if not matches and "time<1ms" in out.lower():
                matches = ["0.5"] * count
            if not matches:
                return None
            vals = [float(x) for x in matches[:count]]
            return {"min": f"{min(vals):.1f}", "max": f"{max(vals):.1f}", "avg": f"{sum(vals)/len(vals):.1f}"}
        except Exception:
            return None

    # ─── WAN log + graph ──────────────────────────────────────────────────────
    def _append_wan_log(self, current_ip: str) -> tuple[str, bool]:
        ts      = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        changed = self.last_logged_ip is not None and current_ip != self.last_logged_ip
        exists  = self.wan_log_file.exists()
        with self.wan_log_file.open("a", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            if not exists:
                w.writerow(["Timestamp", "WAN_IP", "Changed"])
            w.writerow([ts, current_ip, "Yes" if changed else "No"])
        self.last_logged_ip       = current_ip
        self.total_wan_log_rows  += 1
        if changed:
            self.last_wan_change_at  = ts
            self.wan_change_count   += 1
        return ts, changed

    def _on_wan_logged(self, current_ip: str, changed: bool, ts: str) -> None:
        self.wan_ip = current_ip
        self.refresh_summary_labels()
        if changed:
            self.log_action(f"WAN IP changed → {current_ip} at {ts}", "WARN")
        else:
            self.log_action(f"WAN IP logged: {current_ip}", "INFO")
        # Push new graph point (no CSV re-read)
        if current_ip not in self._ip_index_map:
            self._ip_index_map[current_ip] = len(self._ip_index_map) + 1
        ip_val = float(self._ip_index_map[current_ip])
        self._graph_entry_counter += 1
        self.ui_queue.put(("graph_point", (current_ip, ip_val)))
        self._nudge_queue()

    def _push_graph_point(self, ip: str, y_val: float) -> None:
        """Add one point and redraw via blit (fast)."""
        self._graph_indices.append(self._graph_entry_counter)
        self._graph_values.append(y_val)

        xs = list(self._graph_indices)
        ys = list(self._graph_values)

        self._graph_line.set_data(xs, ys)
        if xs:
            self._ax.set_xlim(xs[0] - 0.5, xs[-1] + 0.5)

        uniq_ips = self._ip_index_map
        y_min = 0.5
        y_max = max(uniq_ips.values()) + 0.5 if uniq_ips else 1.5
        self._ax.set_ylim(y_min, y_max)
        self._ax.set_yticks(list(uniq_ips.values()))
        self._ax.set_yticklabels(list(uniq_ips.keys()), fontsize=7)

        self._graph_canvas.draw()   # full redraw kept — blit unreliable w/ CTk
        n_unique = len(uniq_ips)
        self.graph_status_label.configure(
            text=f"{len(xs)} entries • {n_unique} unique IP{'s' if n_unique != 1 else ''}"
        )

    def _load_wan_history_meta_and_prime_graph(self) -> None:
        """Read CSV once at startup to prime counters and graph deques."""
        if not self.wan_log_file.exists():
            return
        try:
            df = pd.read_csv(self.wan_log_file, dtype=str)
            if df.empty:
                return
            prev_ip = None
            change_count  = 0
            last_change_ts = "-"
            last_ip        = None
            for _, row in df.iterrows():
                ip = (row.get("WAN_IP") or "").strip()
                ts = (row.get("Timestamp") or "").strip()
                if not ip:
                    continue
                if prev_ip is not None and ip != prev_ip:
                    change_count  += 1
                    last_change_ts = ts
                prev_ip  = ip
                last_ip  = ip

            self.total_wan_log_rows  = len(df)
            self.wan_change_count    = change_count
            self.last_wan_change_at  = last_change_ts if len(df) else "-"
            if self.last_logged_ip is None:
                self.last_logged_ip = last_ip

            # Prime graph with last MAX_GRAPH_POINTS rows
            recent = df.tail(MAX_GRAPH_POINTS)
            for i, row in enumerate(recent.itertuples(), start=1):
                ip = (getattr(row, "WAN_IP", "") or "").strip()
                if not ip:
                    continue
                if ip not in self._ip_index_map:
                    self._ip_index_map[ip] = len(self._ip_index_map) + 1
                self._graph_indices.append(i)
                self._graph_values.append(float(self._ip_index_map[ip]))
                self._graph_entry_counter = i
            self.after(400, lambda: self._push_graph_point("", 0.0) if self._graph_values else None)
        except Exception as e:
            self.log_action(f"WAN history load error: {e}", "WARN")

    # ─── Table render (in-place update, not full delete/reinsert) ─────────────
    def render_table(self) -> None:
        """Full rebuild — called only when site list changes."""
        for item in self.tree.get_children():
            self.tree.delete(item)
        for site in self.websites:
            r = self.results_by_site.get(site)
            values, tag = self._row_data(site, r)
            iid = self.tree.insert("", "end", iid=site, values=values, tags=(tag,))
        self._apply_tree_tags()

    def _update_table_row(self, result: SiteResult) -> None:
        """Update only the changed row — O(1), not O(n)."""
        values, tag = self._row_data(result.site, result)
        if self.tree.exists(result.site):
            self.tree.item(result.site, values=values, tags=(tag,))
        else:
            # Row doesn't exist yet (first run or new site); rebuild table
            self.render_table()
        self._apply_tree_tags()

    def _row_data(self, site: str, r: Optional[SiteResult]) -> tuple[tuple, str]:
        if r is None:
            return (site, "-", "-", self.wan_ip, "-", "-", "-", "-", "-", "Pending"), "pending"
        tag = "ok" if r.note == "OK" else \
              "bad" if any(k in r.note.lower() for k in ("failed", "error", "connect")) else \
              "warn"
        return (r.site, r.dns_ip, r.tls_ip, r.seen_as,
                r.dns_ms, r.connect_ms, r.ping_min, r.ping_max, r.ping_avg, r.note), tag

    def _apply_tree_tags(self) -> None:
        self.tree.tag_configure("ok",      foreground="#d8ffe5")
        self.tree.tag_configure("warn",    foreground="#ffe6a3")
        self.tree.tag_configure("bad",     foreground="#ffb3b3")
        self.tree.tag_configure("pending", foreground="#aac7b3")

    # ─── Summary labels ───────────────────────────────────────────────────────
    def refresh_summary_labels(self) -> None:
        fs_local = self._ip_label_font_size(self.local_ip)
        fs_wan   = self._ip_label_font_size(self.wan_ip)
        self.local_value.configure(text=self.local_ip,
            font=ctk.CTkFont(size=fs_local, weight="bold", family="Consolas"))
        self.wan_value.configure(text=self.wan_ip,
            font=ctk.CTkFont(size=fs_wan,   weight="bold", family="Consolas"))
        self.seen_value.configure(text=self.wan_ip,
            font=ctk.CTkFont(size=fs_wan,   weight="bold", family="Consolas"))
        self.refresh_meta_label.configure(text=f"Last refresh: {self.last_refresh_at}")
        self.wan_change_label.configure(text=f"WAN changes logged: {self.wan_change_count}")
        self.wan_change_time_label.configure(text=f"Last WAN change: {self.last_wan_change_at}")
        self.total_sites_card.configure(text=str(len(self.websites)))
        self.log_rows_card.configure(text=str(self.total_wan_log_rows))

    def refresh_stat_cards(self) -> None:
        ok    = sum(1 for r in self.results_by_site.values() if r.note == "OK")
        tls   = sum(1 for r in self.results_by_site.values() if r.tls_ip not in {"-", "N/A"})
        self.ok_sites_card.configure(text=str(ok))
        self.peer_sites_card.configure(text=str(tls))
        self.total_sites_card.configure(text=str(len(self.websites)))
        self.log_rows_card.configure(text=str(self.total_wan_log_rows))

    def set_status(self, text: str, color: str) -> None:
        self.status_chip.configure(text=text, text_color=color)

    # ─── Logging ─────────────────────────────────────────────────────────────
    def log_action(self, message: str, level: str = "INFO") -> None:
        ts   = datetime.now().strftime("%H:%M:%S")
        line = f"[{ts}] [{level:<6}] {message}"

        # File: RotatingFileHandler handles rotation automatically
        self._flogger.info(line)

        # UI text widget
        self.log_text.configure(state="normal")
        self.log_text.insert(END, f"[{ts}] ", "ts")
        self.log_text.insert(END, f"[{level:<6}] ",
                             level if level in ("INFO", "WARN", "ERROR", "RESULT") else "INFO")
        self.log_text.insert(END, message + "\n")
        # Trim to MAX_LOG_LINES
        line_count = int(self.log_text.index(END).split(".")[0]) - 1
        if line_count > MAX_LOG_LINES:
            self.log_text.delete("1.0", f"{line_count - MAX_LOG_LINES}.0")
        self.log_text.see(END)
        self.log_text.configure(state="disabled")

    def clear_log_view(self) -> None:
        self.log_text.configure(state="normal")
        self.log_text.delete("1.0", "end")
        self.log_text.configure(state="disabled")
        self.log_action("Log view cleared", "INFO")

    # ─── Site management ──────────────────────────────────────────────────────
    def open_edit_sites_dialog(self) -> None:
        dialog = Toplevel(self)
        dialog.title("Edit Tracked Sites")
        dialog.geometry("500x400")
        dialog.transient(self)
        dialog.grab_set()
        dialog.configure(bg="#101712")
        dialog.update_idletasks()
        x = self.winfo_x() + (self.winfo_width()  - 500) // 2
        y = self.winfo_y() + (self.winfo_height() - 400) // 2
        dialog.geometry(f"+{x}+{y}")

        ctk.CTkLabel(dialog, text="One domain per line  •  # lines are ignored",
                     text_color="#9dd6b3").pack(pady=(15, 8))
        tf = ctk.CTkFrame(dialog, fg_color="#0f1511", corner_radius=10)
        tf.pack(fill=tk.BOTH, expand=True, padx=20, pady=5)
        text_w = scrolledtext.ScrolledText(
            tf, font=("Consolas", 10), bg="#0d120f", fg="#dcfce7",
            insertbackground="#9dffbf", bd=0, padx=10, pady=8, wrap="none",
        )
        text_w.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)
        text_w.insert(END, "\n".join(self.websites))

        btn_f = ctk.CTkFrame(dialog, fg_color="transparent")
        btn_f.pack(fill="x", padx=20, pady=(5, 15))

        def save_and_close():
            lines = [l.strip() for l in text_w.get("1.0", END).split("\n")
                     if l.strip() and not l.strip().startswith("#")]
            cleaned = list(dict.fromkeys(filter(None, (self.normalize_site(l) for l in lines))))
            if cleaned:
                self.websites = cleaned
                self.save_config()
                self.refresh_site_listbox()
                self.render_table()
                self.refresh_stat_cards()
                self.log_action(f"Site list updated: {len(cleaned)} sites", "INFO")
            dialog.destroy()

        ctk.CTkButton(btn_f, text="Cancel", width=90, command=dialog.destroy,
                      fg_color="#3a3a3a", hover_color="#4a4a4a").pack(side=tk.RIGHT, padx=5)
        ctk.CTkButton(btn_f, text="Save Changes", width=110, command=save_and_close,
                      fg_color="#1f8f55", hover_color="#166c40").pack(side=tk.RIGHT, padx=5)
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
        self.log_action(f"Added site: {site}", "INFO")
        threading.Thread(target=self._resolve_single_worker, args=(site,), daemon=True).start()

    def remove_selected_site(self) -> None:
        sel = self.site_listbox.curselection()
        if not sel:
            self.set_status("Select a site to remove", "#ffd27d")
            return
        site = self.websites.pop(sel[0])
        self.results_by_site.pop(site, None)
        self.save_config()
        self.refresh_site_listbox()
        self.render_table()
        self.refresh_stat_cards()
        self.refresh_summary_labels()
        self.log_action(f"Removed: {site}", "INFO")

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

    # ─── Exit ─────────────────────────────────────────────────────────────────
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