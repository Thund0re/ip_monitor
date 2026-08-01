from __future__ import annotations

import csv
import json
import platform
import queue
import re
import socket
import ssl
import subprocess
import threading
import time
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Optional

import customtkinter as ctk
import requests
from tkinter import ttk
import tkinter as tk
from tkinter import Toplevel, END, HORIZONTAL, VERTICAL
from tkinter import scrolledtext

# Graph imports
import matplotlib
matplotlib.use('TkAgg')
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import pandas as pd


APP_TITLE = "IP Monitor Pro"
DEFAULT_INTERVAL_SECONDS = 15
REFRESH_TIMEOUT = 15
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
MAX_LOG_LINES = 250


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


class IPMonitorApp(ctk.CTk):
    def __init__(self) -> None:
        super().__init__()
        self.title(APP_TITLE)
        self.geometry("1080x960")
        self.minsize(640, 480)

        self.base_dir = Path(__file__).resolve().parent
        self.config_file = self.base_dir / "sites_config.json"
        self.wan_log_file = self.base_dir / "wan_ip_log.csv"
        self.action_log_file = self.base_dir / "action_log.txt"

        self.websites = self.load_sites()
        self.results_by_site: OrderedDict[str, SiteResult] = OrderedDict()
        self.ui_queue: queue.Queue[tuple[str, object]] = queue.Queue()
        self.executor = ThreadPoolExecutor(max_workers=8)
        self.stop_event = threading.Event()

        self.local_ip = "Fetching..."
        self.wan_ip = "Fetching..."
        self.last_refresh_at = "-"
        self.last_wan_change_at = "-"
        self.wan_change_count = 0
        self.last_logged_ip: Optional[str] = None
        self.total_wan_log_rows = 0
        self.refresh_in_progress = False
        self.auto_refresh_enabled = tk.BooleanVar(value=True)
        self.interval_var = tk.StringVar(value=str(DEFAULT_INTERVAL_SECONDS))
        self.countdown_seconds = DEFAULT_INTERVAL_SECONDS
        self.log_lines: list[str] = []

        # Graph data
        self.wan_graph_fig: Optional[Figure] = None
        self.wan_graph_ax = None
        self.wan_graph_canvas = None
        self.wan_graph_line = None
        self.graph_status_label = None

        self.build_ui()
        self.configure_tree_style()
        self.load_existing_wan_history_meta()
        self.refresh_summary_labels()

        self.protocol("WM_DELETE_WINDOW", self.on_exit)
        self.after(150, self.process_ui_queue)
        self.after(1000, self.scheduler_tick)

        self.log_action("Application started", "INFO")
        self.refresh_all()

    # -------------------- UI --------------------

    def build_ui(self) -> None:
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(1, weight=1)

        header = ctk.CTkFrame(self, corner_radius=18, fg_color="#102418")
        header.grid(row=0, column=0, sticky="ew", padx=18, pady=(18, 10))
        header.grid_columnconfigure(0, weight=1)

        title_wrap = ctk.CTkFrame(header, fg_color="transparent")
        title_wrap.grid(row=0, column=0, sticky="w", padx=18, pady=14)
        ctk.CTkLabel(
            title_wrap,
            text=APP_TITLE,
            font=ctk.CTkFont(size=30, weight="bold"),
            text_color="#e8fff1",
        ).pack(anchor="w")
        ctk.CTkLabel(
            title_wrap,
            text="Dark mode • green theme • fast refresh • trader-focused monitoring",
            font=ctk.CTkFont(size=14, slant="italic"),
            text_color="#9dd6b3",
        ).pack(anchor="w", pady=(3, 0))

        header_actions = ctk.CTkFrame(header, fg_color="transparent")
        header_actions.grid(row=0, column=1, sticky="e", padx=18, pady=14)

        self.status_chip = ctk.CTkLabel(
            header_actions,
            text="Ready",
            width=150,
            height=34,
            corner_radius=999,
            fg_color="#143a24",
            text_color="#84f0b1",
            font=ctk.CTkFont(size=13, weight="bold"),
        )
        self.status_chip.pack(side="left", padx=(0, 10))

        ctk.CTkButton(
            header_actions,
            text="Refresh Now",
            width=120,
            height=38,
            command=self.refresh_all,
            fg_color="#1f8f55",
            hover_color="#166c40",
        ).pack(side="left", padx=5)

        ctk.CTkButton(
            header_actions,
            text="Exit",
            width=100,
            height=38,
            command=self.on_exit,
            fg_color="#7a1f1f",
            hover_color="#5c1717",
        ).pack(side="left", padx=(5, 0))

        # === RESIZABLE PANED WINDOW (FIXED) ===
        body = tk.PanedWindow(self, orient=HORIZONTAL, bg="#0f1511", bd=0, sashwidth=6, sashrelief="raised")
        body.grid(row=1, column=0, sticky="nsew", padx=18, pady=(0, 18))

        # Left panel (fixed min width, resizable via sash)
        self.left_panel = ctk.CTkFrame(body, width=420, corner_radius=18, fg_color="#101712")
        body.add(self.left_panel, minsize=300)  # ✅ No 'weight' param

        # Right panel (takes remaining space)
        self.right_panel = ctk.CTkFrame(body, corner_radius=18, fg_color="#0f1511")
        body.add(self.right_panel, minsize=500)  # ✅ No 'weight' param

        # Configure right panel internal grid for resizable children
        self.right_panel.grid_columnconfigure(0, weight=1)
        self.right_panel.grid_rowconfigure(3, weight=1)  # Graph area
        self.right_panel.grid_rowconfigure(4, weight=1)  # Log area

        self.build_left_panel()
        self.build_right_panel()

    def build_left_panel(self) -> None:
        cards = ctk.CTkFrame(self.left_panel, corner_radius=16, fg_color="#132019")
        cards.pack(fill="x", padx=14, pady=(14, 10))

        self.local_value = self.metric_block(cards, "Local IP", "Fetching...", "#8cc8ff")
        self.wan_value = self.metric_block(cards, "WAN / Public IP", "Fetching...", "#9dffbf")
        self.seen_value = self.metric_block(cards, "Likely IP seen by websites / APIs", "Fetching...", "#b6f59d")

        controls = ctk.CTkFrame(self.left_panel, corner_radius=16, fg_color="#132019")
        controls.pack(fill="x", padx=14, pady=(0, 10))
        ctk.CTkLabel(controls, text="Auto Refresh", font=ctk.CTkFont(size=16, weight="bold")).pack(anchor="w", padx=14, pady=(12, 10))

        switch_row = ctk.CTkFrame(controls, fg_color="transparent")
        switch_row.pack(fill="x", padx=14, pady=(0, 8))
        self.auto_switch = ctk.CTkSwitch(
            switch_row,
            text="Enable auto refresh + WAN logging",
            variable=self.auto_refresh_enabled,
            onvalue=True,
            offvalue=False,
            command=self.on_auto_toggle,
            progress_color="#1f8f55",
        )
        self.auto_switch.pack(anchor="w")
        self.auto_switch.select()

        interval_row = ctk.CTkFrame(controls, fg_color="transparent")
        interval_row.pack(fill="x", padx=14, pady=(4, 0))
        ctk.CTkLabel(interval_row, text="Interval", width=70).pack(side="left")
        self.interval_menu = ctk.CTkOptionMenu(
            interval_row,
            values=["5", "10", "15", "30", "60"],
            variable=self.interval_var,
            command=self.on_interval_change,
            fg_color="#17452a",
            button_color="#1f8f55",
            button_hover_color="#166c40",
        )
        self.interval_menu.pack(side="left", padx=(0, 8))
        ctk.CTkLabel(interval_row, text="seconds", text_color="#99b7a4").pack(side="left")

        self.countdown_label = ctk.CTkLabel(
            controls,
            text="Next refresh in 5s",
            font=ctk.CTkFont(size=14, weight="bold"),
            text_color="#84f0b1",
        )
        self.countdown_label.pack(anchor="w", padx=14, pady=(8, 6))

        self.refresh_meta_label = ctk.CTkLabel(controls, text="Last refresh: -", anchor="w", text_color="#aac7b3")
        self.refresh_meta_label.pack(fill="x", padx=14, pady=2)
        self.wan_change_label = ctk.CTkLabel(controls, text="WAN changes logged: 0", anchor="w", text_color="#aac7b3")
        self.wan_change_label.pack(fill="x", padx=14, pady=2)
        self.wan_change_time_label = ctk.CTkLabel(controls, text="Last WAN change: -", anchor="w", text_color="#aac7b3")
        self.wan_change_time_label.pack(fill="x", padx=14, pady=(2, 12))

        # === IMPROVED SITE MANAGEMENT ===
        sites = ctk.CTkFrame(self.left_panel, corner_radius=16, fg_color="#132019")
        sites.pack(fill="both", expand=True, padx=14, pady=(0, 10))

        sites_header = ctk.CTkFrame(sites, fg_color="transparent")
        sites_header.pack(fill="x", padx=14, pady=(12, 4))
        ctk.CTkLabel(sites_header, text="Tracked Websites", font=ctk.CTkFont(size=18, weight="bold")).pack(side="left")

        # Edit button for bulk management
        ctk.CTkButton(
            sites_header,
            text="✏️ Edit List",
            width=90,
            height=20,
            command=self.open_edit_sites_dialog,
            fg_color="#2a5f3d",
            hover_color="#1f8f55",
            font=ctk.CTkFont(size=11)
        ).pack(side="right")

        ctk.CTkLabel(sites, text="• Click to select • Double-click to resolve • Drag to reorder",
                    text_color="#97b7a2", font=ctk.CTkFont(size=10)).pack(anchor="w", padx=14, pady=(0, 6))

        self.site_listbox = tk.Listbox(
            sites,
            height=8,
            font=("Consolas", 11),
            bg="#0f1511",
            fg="#dcfce7",
            bd=0,
            highlightthickness=0,
            relief="flat",
            selectbackground="#1f8f55",
            selectforeground="#ffffff",
            exportselection=False,
        )
        self.site_listbox.pack(fill="both", expand=True, padx=14, pady=(0, 4))
        self.site_listbox.bind("<<ListboxSelect>>", self.on_site_select)
        self.site_listbox.bind("<Double-1>", lambda e: self.resolve_selected())
        self.refresh_site_listbox()

        entry_row = ctk.CTkFrame(sites, fg_color="transparent")
        entry_row.pack(fill="x", padx=14, pady=(4, 6))
        self.site_entry = ctk.CTkEntry(entry_row, placeholder_text="Add site (e.g. upstox.com) • Press Enter")
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

    def open_edit_sites_dialog(self):
        """Open dialog for bulk site management"""
        dialog = Toplevel(self)
        dialog.title("Edit Tracked Sites")
        dialog.geometry("500x400")
        dialog.transient(self)
        dialog.grab_set()
        dialog.configure(bg="#101712")

        # Center dialog
        dialog.update_idletasks()
        x = self.winfo_x() + (self.winfo_width() - 500) // 2
        y = self.winfo_y() + (self.winfo_height() - 400) // 2
        dialog.geometry(f"+{x}+{y}")

        ctk.CTkLabel(dialog, text="One domain per line • Comments start with #",
                    text_color="#9dd6b3").pack(pady=(15, 8))

        text_frame = ctk.CTkFrame(dialog, fg_color="#0f1511", corner_radius=10)
        text_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=5)

        text_widget = scrolledtext.ScrolledText(
            text_frame,
            font=("Consolas", 10),
            bg="#0d120f",
            fg="#dcfce7",
            insertbackground="#9dffbf",
            bd=0,
            padx=10,
            pady=8,
            wrap="none",  # Enable horizontal scroll
        )
        text_widget.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)

        # Load current sites
        current_text = "\n".join(self.websites)
        text_widget.insert(END, current_text)

        btn_frame = ctk.CTkFrame(dialog, fg_color="transparent")
        btn_frame.pack(fill="x", padx=20, pady=(5, 15))

        def save_and_close():
            content = text_widget.get("1.0", END).strip()
            lines = [line.strip() for line in content.split("\n") if line.strip() and not line.strip().startswith("#")]
            cleaned = [self.normalize_site(line) for line in lines]
            cleaned = [s for s in cleaned if s]  # Remove empty

            if cleaned:
                self.websites = list(dict.fromkeys(cleaned))  # Preserve order, remove dupes
                self.save_sites()
                self.refresh_site_listbox()
                self.render_table()
                self.refresh_stat_cards()
                self.log_action(f"Updated site list: {len(self.websites)} sites", "INFO")
            dialog.destroy()

        ctk.CTkButton(btn_frame, text="Cancel", width=90, command=dialog.destroy,
                     fg_color="#3a3a3a", hover_color="#4a4a4a").pack(side=tk.RIGHT, padx=5)
        ctk.CTkButton(btn_frame, text="Save Changes", width=110, command=save_and_close,
                     fg_color="#1f8f55", hover_color="#166c40").pack(side=tk.RIGHT, padx=5)

        # Focus text widget
        text_widget.focus_set()

    def on_site_select(self, event=None):
        """Handle site selection - just visual feedback for now"""
        selection = self.site_listbox.curselection()
        if selection:
            site = self.site_listbox.get(selection[0])
            self.set_status(f"Selected: {site}", "#b6f59d")

    def build_right_panel(self) -> None:
        # Top stat cards
        top_cards = ctk.CTkFrame(self.right_panel, fg_color="transparent")
        top_cards.grid(row=0, column=0, sticky="ew", padx=12, pady=(12, 4))
        for idx in range(4):
            top_cards.grid_columnconfigure(idx, weight=1)

        self.total_sites_card = self.small_stat_card(top_cards, 0, "Tracked Sites", "0", "#8cc8ff")
        self.ok_sites_card = self.small_stat_card(top_cards, 1, "Reachable", "0", "#9dffbf")
        self.peer_sites_card = self.small_stat_card(top_cards, 2, "TLS IP Captured", "0", "#b6f59d")
        self.log_rows_card = self.small_stat_card(top_cards, 3, "WAN Log Rows", "0", "#facc7d")

        # Info panel
        explain = ctk.CTkFrame(self.right_panel, corner_radius=16, fg_color="#132019")
        explain.grid(row=1, column=0, sticky="ew", padx=12, pady=(4, 8))
        ctk.CTkLabel(explain, text="What DNS IP and TLS IP mean", font=ctk.CTkFont(size=14, weight="bold")).pack(anchor="w", padx=14, pady=(10, 4))
        ctk.CTkLabel(
            explain,
            text=(
                "DNS IP = address returned by DNS resolver | TLS IP = actual server your HTTPS connected to | "
                "Server Sees You As = your public/WAN IP (what APIs log)"
            ),
            justify="left",
            text_color="#c5dfce",
            wraplength=900,
            font=ctk.CTkFont(size=11)
        ).pack(anchor="w", padx=14, pady=(0, 10))

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
        widths = {"Site": 170, "DNS_IP": 150, "TLS_IP": 130, "Seen_As": 140, "DNS_ms": 75,
                 "Connect_ms": 75, "Min": 70, "Max": 70, "Avg": 70, "Status": 170}
        for col in columns:
            self.tree.heading(col, text=headings[col])
            self.tree.column(col, width=widths[col], anchor="center", minwidth=60)

        # Add scrollbars to tree
        tree_scroll_y = ttk.Scrollbar(table_wrap, orient=VERTICAL, command=self.tree.yview)
        tree_scroll_x = ttk.Scrollbar(table_wrap, orient=HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=tree_scroll_y.set, xscrollcommand=tree_scroll_x.set)

        self.tree.grid(row=0, column=0, sticky="nsew", padx=10, pady=8)
        tree_scroll_y.grid(row=0, column=1, sticky="ns", pady=8)
        tree_scroll_x.grid(row=1, column=0, sticky="ew", padx=10)

        # === WAN IP GRAPH (NEW) ===
        graph_wrap = ctk.CTkFrame(self.right_panel, corner_radius=16, fg_color="#132019")
        graph_wrap.grid(row=5, column=0, sticky="nsew", padx=12, pady=(0, 6))
        graph_wrap.grid_columnconfigure(0, weight=1)
        graph_wrap.grid_rowconfigure(1, weight=1)

        graph_header = ctk.CTkFrame(graph_wrap, fg_color="transparent")
        graph_header.grid(row=0, column=0, sticky="ew", padx=12, pady=(10, 4))
        ctk.CTkLabel(graph_header, text="📈 WAN IP History (Last 50 Logs)",
                    font=ctk.CTkFont(size=16, weight="bold")).grid(row=0, column=0, sticky="w")
        self.graph_status_label = ctk.CTkLabel(graph_header, text="Loading...",
                                        text_color="#9dd6b3", font=ctk.CTkFont(size=10))
        self.graph_status_label.grid(row=0, column=1, sticky="e", padx=10)

        # Create matplotlib figure
        self.wan_graph_fig = Figure(figsize=(5, 2.5), dpi=100, facecolor="#132019", edgecolor="none")
        self.wan_graph_ax = self.wan_graph_fig.add_subplot(111)
        self.wan_graph_ax.set_facecolor("#0f1511")
        self.wan_graph_ax.tick_params(colors="#9dd6b3", labelsize=8)
        self.wan_graph_ax.spines['top'].set_visible(False)
        self.wan_graph_ax.spines['right'].set_visible(False)
        self.wan_graph_ax.spines['left'].set_color('#3a5a4a')
        self.wan_graph_ax.spines['bottom'].set_color('#3a5a4a')

        self.wan_graph_canvas = FigureCanvasTkAgg(self.wan_graph_fig, master=graph_wrap)
        self.wan_graph_canvas.get_tk_widget().grid(row=1, column=0, sticky="nsew", padx=8, pady=(0, 8))

        # Initialize empty graph
        self.wan_graph_line, = self.wan_graph_ax.plot([], [], color='#1f8f55', linewidth=1.5, marker='o', markersize=3)
        self.wan_graph_ax.set_xlabel("Log Entry", color="#7a9a87", fontsize=9)
        self.wan_graph_ax.set_ylabel("IP Index", color="#7a9a87", fontsize=9)
        self.wan_graph_ax.set_title("WAN IP Changes Over Time", color="#9dd6b3", fontsize=10, pad=10)
        self.wan_graph_ax.grid(True, alpha=0.15, color='#2a4a3a', linestyle='--')

        # Load initial graph data
        self.after(500, self.update_wan_graph)

        # === IMPROVED LOG PANEL ===
        log_wrap = ctk.CTkFrame(self.right_panel, corner_radius=16, fg_color="#132019")
        log_wrap.grid(row=6, column=0, sticky="nsew", padx=12, pady=(0, 12))
        log_wrap.grid_columnconfigure(0, weight=1)
        log_wrap.grid_rowconfigure(1, weight=1)

        log_head = ctk.CTkFrame(log_wrap, fg_color="transparent")
        log_head.grid(row=0, column=0, sticky="ew", padx=12, pady=(10, 4))
        log_head.grid_columnconfigure(0, weight=1)
        ctk.CTkLabel(log_head, text="📋 Activity Log", font=ctk.CTkFont(size=16, weight="bold")).grid(row=0, column=0, sticky="w")
        ctk.CTkButton(log_head, text="Clear", width=80, height=26, command=self.clear_log_view,
                     fg_color="#3a3a3a", hover_color="#4a4a4a", font=ctk.CTkFont(size=10)).grid(row=0, column=1, sticky="e")

        # === COLOR-CODED, MONOSPACE, SCROLLABLE LOG ===
        self.log_text = tk.Text(
            log_wrap,
            font=("Consolas", 10),
            bg="#0d120f",
            fg="#e2ffe9",
            insertbackground="#9dffbf",
            bd=0,
            padx=12,
            pady=8,
            wrap="none",  # Horizontal scroll enabled
            relief="flat",
            highlightthickness=0,
        )
        self.log_text.grid(row=1, column=0, sticky="nsew", padx=8, pady=(0, 8))

        # Add scrollbars
        log_scroll_y = ttk.Scrollbar(log_wrap, orient=VERTICAL, command=self.log_text.yview)
        log_scroll_x = ttk.Scrollbar(log_wrap, orient=HORIZONTAL, command=self.log_text.xview)
        self.log_text.configure(yscrollcommand=log_scroll_y.set, xscrollcommand=log_scroll_x.set)

        log_scroll_y.grid(row=1, column=1, sticky="ns", pady=(0, 8))
        log_scroll_x.grid(row=2, column=0, sticky="ew", padx=8)

        # Configure color tags for log levels
        self.log_text.tag_configure("INFO", foreground="#84f0b1")
        self.log_text.tag_configure("WARN", foreground="#ffd27d")
        self.log_text.tag_configure("ERROR", foreground="#ff9393")
        self.log_text.tag_configure("RESULT", foreground="#b6f59d")
        self.log_text.tag_configure("timestamp", foreground="#6a8a77")

    def metric_block(self, parent, label: str, value: str, color: str):
        wrap = ctk.CTkFrame(parent, fg_color="transparent")
        wrap.pack(fill="x", padx=14, pady=(12, 0))
        ctk.CTkLabel(wrap, text=label, text_color="#98b7a4", font=ctk.CTkFont(size=14, weight="bold")).pack(anchor="w")
        value_label = ctk.CTkLabel(
            wrap,
            text=value,
            font=ctk.CTkFont(size=20, weight="bold", family="Consolas"),
            text_color=color,
            anchor="w",
            justify="left",
        )
        value_label.pack(anchor="w", pady=(4, 0))
        return value_label

    def small_stat_card(self, parent, col: int, label: str, value: str, color: str):
        card = ctk.CTkFrame(parent, corner_radius=14, fg_color="#132019")
        card.grid(row=0, column=col, sticky="ew", padx=6)
        ctk.CTkLabel(card, text=label, text_color="#98b7a4").pack(anchor="w", padx=12, pady=(10, 2))
        value_label = ctk.CTkLabel(card, text=value, font=ctk.CTkFont(size=24, weight="bold"), text_color=color)
        value_label.pack(anchor="w", padx=12, pady=(0, 10))
        return value_label

    def configure_tree_style(self) -> None:
        style = ttk.Style()
        try:
            style.theme_use("default")
        except tk.TclError:
            pass
        style.configure(
            "Treeview",
            rowheight=31,
            font=("Segoe UI", 10),
            background="#0d120f",
            fieldbackground="#0d120f",
            foreground="#e2ffe9",
            borderwidth=0,
        )
        style.configure(
            "Treeview.Heading",
            font=("Segoe UI", 10, "bold"),
            background="#1b2a20",
            foreground="#e2ffe9",
        )
        style.map("Treeview", background=[("selected", "#1f8f55")], foreground=[("selected", "#ffffff")])

    # -------------------- Scheduler and UI events --------------------

    def scheduler_tick(self) -> None:
        if self.stop_event.is_set():
            return

        interval = self.get_interval_seconds()
        if not self.auto_refresh_enabled.get():
            self.countdown_label.configure(text="Auto refresh paused")
            self.after(1000, self.scheduler_tick)
            return

        if self.refresh_in_progress:
            self.countdown_label.configure(text="Refreshing...")
            self.after(1000, self.scheduler_tick)
            return

        self.countdown_seconds -= 1
        if self.countdown_seconds <= 0:
            self.countdown_seconds = interval
            self.refresh_all()
        else:
            self.countdown_label.configure(text=f"Next refresh in {self.countdown_seconds}s")

        self.after(1000, self.scheduler_tick)

    def on_auto_toggle(self) -> None:
        state = "enabled" if self.auto_refresh_enabled.get() else "disabled"
        self.countdown_seconds = self.get_interval_seconds()
        self.log_action(f"Auto refresh {state}", "INFO")
        if self.auto_refresh_enabled.get():
            self.countdown_label.configure(text=f"Next refresh in {self.countdown_seconds}s")
        else:
            self.countdown_label.configure(text="Auto refresh paused")

    def on_interval_change(self, _value: str) -> None:
        self.countdown_seconds = self.get_interval_seconds()
        self.log_action(f"Interval set to {self.countdown_seconds} seconds", "INFO")
        if self.auto_refresh_enabled.get() and not self.refresh_in_progress:
            self.countdown_label.configure(text=f"Next refresh in {self.countdown_seconds}s")

    def get_interval_seconds(self) -> int:
        try:
            value = int(self.interval_var.get().strip())
            return max(5, value)
        except Exception:
            return DEFAULT_INTERVAL_SECONDS

    def process_ui_queue(self) -> None:
        try:
            while True:
                event, payload = self.ui_queue.get_nowait()
                if event == "status":
                    text, color = payload
                    self.set_status(text, color)
                elif event == "header":
                    local_ip, wan_ip, refreshed_at = payload
                    self.local_ip = local_ip
                    self.wan_ip = wan_ip
                    self.last_refresh_at = refreshed_at
                    self.refresh_summary_labels()
                elif event == "wan_logged":
                    current_ip, changed, timestamp = payload
                    self.on_wan_logged(current_ip, changed, timestamp)
                elif event == "site_result":
                    result: SiteResult = payload
                    self.results_by_site[result.site] = result
                    self.render_table()
                    self.refresh_stat_cards()
                    self.log_action(
                        f"{result.site} | DNS={result.dns_ip} | TLS={result.tls_ip} | SeenAs={result.seen_as} | Ping={result.ping_min}/{result.ping_avg}/{result.ping_max} ms | {result.note}",
                        "RESULT",
                    )
                elif event == "refresh_done":
                    self.refresh_in_progress = False
                    self.countdown_seconds = self.get_interval_seconds()
                    self.countdown_label.configure(text=f"Next refresh in {self.countdown_seconds}s" if self.auto_refresh_enabled.get() else "Auto refresh paused")
                    self.set_status("Ready", "#84f0b1")
                    self.log_action("Refresh cycle completed", "INFO")
                elif event == "log":
                    message, level = payload
                    self.log_action(message, level)
                elif event == "error":
                    self.refresh_in_progress = False
                    self.set_status(str(payload), "#ff9393")
                    self.log_action(str(payload), "ERROR")
        except queue.Empty:
            pass
        finally:
            if not self.stop_event.is_set():
                self.after(150, self.process_ui_queue)

    def refresh_all(self) -> None:
        if self.refresh_in_progress:
            return
        self.refresh_in_progress = True
        self.countdown_label.configure(text="Refreshing...")
        self.set_status("Refreshing", "#b6f59d")
        self.log_action("Starting refresh cycle", "INFO")
        threading.Thread(target=self.refresh_worker, daemon=True).start()

    def refresh_worker(self) -> None:
        try:
            local_ip = self.get_local_ip()
            wan_ip = self.get_wan_ip()
            refreshed_at = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            self.ui_queue.put(("header", (local_ip, wan_ip, refreshed_at)))

            timestamp, changed = self.append_wan_log(wan_ip)
            self.ui_queue.put(("wan_logged", (wan_ip, changed, timestamp)))

            futures = [self.executor.submit(self.resolve_site, site, wan_ip) for site in self.websites]
            for future in futures:
                try:
                    result = future.result()
                    self.ui_queue.put(("site_result", result))
                except Exception as exc:
                    self.ui_queue.put(("error", f"Resolve error: {exc}"))
            self.ui_queue.put(("refresh_done", None))
        except Exception as exc:
            self.ui_queue.put(("error", f"Refresh failed: {exc}"))

    def resolve_selected(self) -> None:
        selection = self.site_listbox.curselection()
        if not selection:
            self.log_action("No site selected", "WARN")
            self.set_status("Select a site first", "#ffd27d")
            return
        site = self.site_listbox.get(selection[0])
        self.log_action(f"Resolving selected site: {site}", "INFO")
        threading.Thread(target=self.resolve_selected_worker, args=(site,), daemon=True).start()

    def resolve_selected_worker(self, site: str) -> None:
        try:
            wan_ip = self.wan_ip if self.wan_ip not in {"Fetching...", "Unavailable"} else self.get_wan_ip()
            result = self.resolve_site(site, wan_ip)
            self.ui_queue.put(("site_result", result))
            self.ui_queue.put(("status", ("Selected site updated", "#84f0b1")))
        except Exception as exc:
            self.ui_queue.put(("error", f"Selected resolve failed: {exc}"))

    # -------------------- Networking --------------------

    def get_local_ip(self) -> str:
        try:
            with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
                sock.connect(("8.8.8.8", 80))
                return sock.getsockname()[0]
        except Exception:
            try:
                return socket.gethostbyname(socket.gethostname())
            except Exception:
                return "127.0.0.1"

    def get_wan_ip(self) -> str:
        for url in PUBLIC_IP_SERVICES:
            try:
                response = requests.get(url, timeout=3)
                if response.ok:
                    value = response.text.strip()
                    if re.match(r"^\d+\.\d+\.\d+\.\d+$", value):
                        return value
            except requests.RequestException:
                continue
        return "Unavailable"

    def resolve_site(self, site: str, seen_as_ip: str) -> SiteResult:
        result = SiteResult(site=site, seen_as=seen_as_ip)

        dns_start = time.perf_counter()
        try:
            addrinfo = socket.getaddrinfo(site, 443, family=socket.AF_INET, type=socket.SOCK_STREAM)
            ipv4s = sorted({item[4][0] for item in addrinfo})
            result.dns_ip = ", ".join(ipv4s[:3]) if ipv4s else "No IPv4"
            result.dns_ms = f"{(time.perf_counter() - dns_start) * 1000:.1f}"
        except socket.gaierror as exc:
            result.note = f"DNS error: {exc}"
            return result
        except Exception as exc:
            result.note = f"DNS failed: {str(exc)[:40]}"
            return result

        primary_ip = result.dns_ip.split(",")[0].strip() if result.dns_ip not in {"No IPv4", "-"} else ""
        tls_ip, connect_ms, note = self.get_tls_peer_ip(site)
        result.tls_ip = tls_ip
        result.connect_ms = connect_ms
        result.note = note

        if primary_ip:
            ping_stats = self.ping_host(primary_ip, count=2)
            if ping_stats:
                result.ping_min = ping_stats["min"]
                result.ping_max = ping_stats["max"]
                result.ping_avg = ping_stats["avg"]

        return result

    def get_tls_peer_ip(self, host: str) -> tuple[str, str, str]:
        for port, secure in ((443, True), (80, False)):
            try:
                start = time.perf_counter()
                raw_sock = socket.create_connection((host, port), timeout=REFRESH_TIMEOUT)
                if secure:
                    context = ssl.create_default_context()
                    with context.wrap_socket(raw_sock, server_hostname=host) as tls_sock:
                        peer_ip = tls_sock.getpeername()[0]
                else:
                    with raw_sock:
                        peer_ip = raw_sock.getpeername()[0]
                elapsed = f"{(time.perf_counter() - start) * 1000:.1f}"
                return peer_ip, elapsed, "OK" if secure else "HTTP fallback"
            except Exception:
                continue
        return "N/A", "-", "Connect failed"

    def ping_host(self, host: str, count: int = 2) -> Optional[dict[str, str]]:
        system_name = platform.system().lower()
        if "windows" in system_name:
            command = ["ping", "-n", str(count), "-w", "1500", host]
        else:
            command = ["ping", "-c", str(count), "-W", "2", host]

        try:
            completed = subprocess.run(command, capture_output=True, text=True, timeout=8)
            output = (completed.stdout or "") + "\n" + (completed.stderr or "")
            matches = re.findall(r"time[=<]\s*(\d+(?:\.\d+)?)\s*ms", output, re.IGNORECASE)
            if not matches and "time<1ms" in output.lower():
                matches = ["0.5"] * count
            if not matches:
                return None
            values = [float(x) for x in matches[:count]]
            return {
                "min": f"{min(values):.1f}",
                "max": f"{max(values):.1f}",
                "avg": f"{sum(values) / len(values):.1f}",
            }
        except Exception:
            return None

    # -------------------- Logging and persistence --------------------

    def append_wan_log(self, current_ip: str) -> tuple[str, bool]:
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        file_exists = self.wan_log_file.exists()
        changed = self.last_logged_ip is not None and current_ip != self.last_logged_ip

        with self.wan_log_file.open("a", newline="", encoding="utf-8") as file:
            writer = csv.writer(file)
            if not file_exists:
                writer.writerow(["Timestamp", "WAN_IP", "Changed"])
            writer.writerow([timestamp, current_ip, "Yes" if changed else "No"])

        self.last_logged_ip = current_ip
        self.total_wan_log_rows += 1
        if changed:
            self.last_wan_change_at = timestamp
            self.wan_change_count += 1
        return timestamp, changed

    def on_wan_logged(self, current_ip: str, changed: bool, timestamp: str) -> None:
        self.wan_ip = current_ip
        self.refresh_summary_labels()
        if changed:
            self.log_action(f"WAN IP changed to {current_ip} at {timestamp}", "WARN")
        else:
            self.log_action(f"WAN IP logged: {current_ip}", "INFO")

        # Update graph after a short delay (let CSV write complete)
        self.after(200, self.update_wan_graph)

    def load_existing_wan_history_meta(self) -> None:
        if not self.wan_log_file.exists():
            self.total_wan_log_rows = 0
            self.wan_change_count = 0
            self.last_wan_change_at = "-"
            self.last_logged_ip = None
            return

        previous_ip = None
        last_change_time = "-"
        total_rows = 0
        change_count = 0
        last_ip = None
        try:
            with self.wan_log_file.open("r", newline="", encoding="utf-8") as file:
                reader = csv.DictReader(file)
                for row in reader:
                    ip = (row.get("WAN_IP") or "").strip()
                    ts = (row.get("Timestamp") or "").strip()
                    if not ip:
                        continue
                    total_rows += 1
                    if previous_ip is not None and ip != previous_ip:
                        change_count += 1
                        last_change_time = ts or last_change_time
                    previous_ip = ip
                    last_ip = ip
            self.total_wan_log_rows = total_rows
            self.wan_change_count = change_count
            self.last_wan_change_at = last_change_time if total_rows else "-"
            self.last_logged_ip = last_ip
        except Exception:
            self.total_wan_log_rows = 0
            self.wan_change_count = 0
            self.last_wan_change_at = "-"
            self.last_logged_ip = None

    def log_action(self, message: str, level: str = "INFO") -> None:
        timestamp = datetime.now().strftime("%H:%M:%S")
        line = f"[{timestamp}] [{level:<6}] {message}"
        self.log_lines.append(line)
        self.log_lines = self.log_lines[-MAX_LOG_LINES:]

        # Update UI with color coding
        self.log_text.configure(state="normal")

        # Insert with tags
        self.log_text.insert(END, f"[", "timestamp")
        self.log_text.insert(END, timestamp, "timestamp")
        self.log_text.insert(END, f"] [{level:<6}] ", level if level in ["INFO", "WARN", "ERROR", "RESULT"] else "INFO")
        self.log_text.insert(END, message + "\n")

        # Auto-scroll to bottom
        self.log_text.see(END)
        self.log_text.configure(state="disabled")

        # Also write to file (unchanged)
        try:
            with self.action_log_file.open("a", encoding="utf-8") as file:
                file.write(line + "\n")
        except Exception:
            pass

    def clear_log_view(self) -> None:
        self.log_lines.clear()
        self.log_text.configure(state="normal")
        self.log_text.delete("1.0", "end")
        self.log_text.configure(state="disabled")
        self.log_action("Cleared on-screen log view", "INFO")

    def load_sites(self) -> list[str]:
        if not self.config_file.exists():
            return list(DEFAULT_SITES)
        try:
            with self.config_file.open("r", encoding="utf-8") as file:
                data = json.load(file)
            sites = data.get("sites", [])
            if isinstance(sites, list):
                cleaned = []
                for site in sites:
                    normalized = self.normalize_site(str(site))
                    if normalized and normalized not in cleaned:
                        cleaned.append(normalized)
                if cleaned:
                    return cleaned
        except Exception:
            pass
        return list(DEFAULT_SITES)

    def save_sites(self) -> None:
        with self.config_file.open("w", encoding="utf-8") as file:
            json.dump({"sites": self.websites}, file, indent=2)

    def refresh_site_listbox(self) -> None:
        self.site_listbox.delete(0, "end")
        for site in self.websites:
            self.site_listbox.insert("end", site)

    def add_site(self) -> None:
        raw = self.site_entry.get().strip().lower()
        site = self.normalize_site(raw)
        if not site:
            self.set_status("Enter a valid domain", "#ffd27d")
            self.log_action("Rejected empty or invalid domain", "WARN")
            return
        if site in self.websites:
            self.set_status("Site already exists", "#ffd27d")
            self.log_action(f"Site already tracked: {site}", "WARN")
            return
        self.websites.append(site)
        self.save_sites()
        self.refresh_site_listbox()
        self.refresh_summary_labels()
        self.site_entry.delete(0, "end")
        self.log_action(f"Added site: {site}", "INFO")
        threading.Thread(target=self.resolve_selected_worker, args=(site,), daemon=True).start()

    def remove_selected_site(self) -> None:
        selection = self.site_listbox.curselection()
        if not selection:
            self.set_status("Select a site to remove", "#ffd27d")
            self.log_action("Remove requested without selection", "WARN")
            return
        index = selection[0]
        site = self.websites.pop(index)
        self.results_by_site.pop(site, None)
        self.save_sites()
        self.refresh_site_listbox()
        self.render_table()
        self.refresh_stat_cards()
        self.refresh_summary_labels()
        self.log_action(f"Removed site: {site}", "INFO")

    def move_selected_site(self, direction: int) -> None:
        selection = self.site_listbox.curselection()
        if not selection:
            self.set_status("Select a site to move", "#ffd27d")
            self.log_action("Move requested without selection", "WARN")
            return
        index = selection[0]
        new_index = index + direction
        if new_index < 0 or new_index >= len(self.websites):
            return
        self.websites[index], self.websites[new_index] = self.websites[new_index], self.websites[index]
        self.save_sites()
        self.refresh_site_listbox()
        self.site_listbox.selection_set(new_index)
        self.log_action(f"Moved site to position {new_index + 1}: {self.websites[new_index]}", "INFO")

    def normalize_site(self, value: str) -> str:
        if not value:
            return ""
        value = value.replace("https://", "").replace("http://", "").strip().strip("/")
        value = value.split("/")[0].strip()
        return value

    # -------------------- Rendering --------------------

    def render_table(self) -> None:
        for item in self.tree.get_children():
            self.tree.delete(item)
        for site in self.websites:
            result = self.results_by_site.get(site)
            if result is None:
                values = (site, "-", "-", self.wan_ip, "-", "-", "-", "-", "-", "Pending")
                tag = "pending"
            else:
                values = (
                    result.site,
                    result.dns_ip,
                    result.tls_ip,
                    result.seen_as,
                    result.dns_ms,
                    result.connect_ms,
                    result.ping_min,
                    result.ping_max,
                    result.ping_avg,
                    result.note,
                )
                if result.note == "OK":
                    tag = "ok"
                elif "failed" in result.note.lower() or "error" in result.note.lower() or "connect" in result.note.lower():
                    tag = "bad"
                else:
                    tag = "warn"
            self.tree.insert("", "end", values=values, tags=(tag,))

        self.tree.tag_configure("ok", foreground="#d8ffe5")
        self.tree.tag_configure("warn", foreground="#ffe6a3")
        self.tree.tag_configure("bad", foreground="#ffb3b3")
        self.tree.tag_configure("pending", foreground="#aac7b3")

    def refresh_summary_labels(self) -> None:
        self.local_value.configure(text=self.local_ip)
        self.wan_value.configure(text=self.wan_ip)
        self.seen_value.configure(text=self.wan_ip)
        self.refresh_meta_label.configure(text=f"Last refresh: {self.last_refresh_at}")
        self.wan_change_label.configure(text=f"WAN changes logged: {self.wan_change_count}")
        self.wan_change_time_label.configure(text=f"Last WAN change: {self.last_wan_change_at}")
        self.total_sites_card.configure(text=str(len(self.websites)))
        self.log_rows_card.configure(text=str(self.total_wan_log_rows))

    def refresh_stat_cards(self) -> None:
        ok_count = sum(1 for item in self.results_by_site.values() if item.note == "OK")
        tls_count = sum(1 for item in self.results_by_site.values() if item.tls_ip not in {"-", "N/A"})
        self.ok_sites_card.configure(text=str(ok_count))
        self.peer_sites_card.configure(text=str(tls_count))
        self.total_sites_card.configure(text=str(len(self.websites)))
        self.log_rows_card.configure(text=str(self.total_wan_log_rows))

    def set_status(self, text: str, text_color: str) -> None:
        self.status_chip.configure(text=text, text_color=text_color)

    # -------------------- WAN IP Graph --------------------

    def update_wan_graph(self):
        """Update the WAN IP history graph with last 50 log entries"""
        try:
            if not self.wan_log_file.exists() or self.wan_graph_ax is None:
                if self.graph_status_label:
                    self.graph_status_label.configure(text="No log data yet")
                return

            # Read last 50 entries from CSV
            df = pd.read_csv(self.wan_log_file)
            if len(df) == 0:
                if self.graph_status_label:
                    self.graph_status_label.configure(text="Empty log file")
                return

            # Get last 50 rows
            recent = df.tail(50).reset_index(drop=True)

            # Create numeric index for Y-axis (unique IP = unique value)
            ip_map = {}
            ip_values = []
            for ip in recent["WAN_IP"]:
                if ip not in ip_map:
                    ip_map[ip] = len(ip_map) + 1
                ip_values.append(ip_map[ip])

            # Update plot
            if self.wan_graph_line:
                self.wan_graph_line.set_data(range(len(ip_values)), ip_values)

            # Auto-scale axes
            if len(ip_values) > 0:
                self.wan_graph_ax.set_xlim(-0.5, len(ip_values) - 0.5)
                self.wan_graph_ax.set_ylim(0.5, max(ip_values) + 0.5 if ip_values else 1.5)

                # Add IP labels on right side
                self.wan_graph_ax.set_yticks(list(ip_map.values()))
                self.wan_graph_ax.set_yticklabels(list(ip_map.keys()), fontsize=7, ha="left")

                # Highlight changes with vertical lines
                changes = recent["Changed"] == "Yes"
                change_indices = [i for i, c in enumerate(changes) if c]
                for idx in change_indices:
                    self.wan_graph_ax.axvline(x=idx, color='#ffd27d', alpha=0.3, linestyle=':', linewidth=0.5)

            if self.wan_graph_canvas:
                self.wan_graph_canvas.draw()
            if self.graph_status_label:
                self.graph_status_label.configure(text=f"Showing {len(recent)} entries • {len(ip_map)} unique IPs")

        except Exception as e:
            if self.graph_status_label:
                self.graph_status_label.configure(text=f"Graph error: {str(e)[:30]}")

    # -------------------- Shutdown --------------------

    def on_exit(self) -> None:
        self.log_action("Exiting application", "INFO")
        self.stop_event.set()
        self.executor.shutdown(wait=False, cancel_futures=True)
        self.destroy()


def main() -> None:
    app = IPMonitorApp()
    app.mainloop()


if __name__ == "__main__":
    main()
