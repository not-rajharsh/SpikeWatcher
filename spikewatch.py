#!/usr/bin/env python3
"""
spikewatch - a real-time system monitor that tells you WHO caused each spike.

Every sample (default 1s) it records CPU, memory growth, disk read/write and
network up/down, along with a per-process breakdown taken at that same instant.
When a metric jumps well above its own rolling baseline, the spike is logged
together with the processes responsible at the moment it peaked.

    pip install psutil rich
    python spikewatch.py                 # live dashboard
    python spikewatch.py --plain         # scrolling text log (good for SSH/tmux)
    python spikewatch.py --report spikewatch_events.jsonl   # summarise a past run

Run with sudo/admin for complete per-process disk and network attribution.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from collections import Counter, defaultdict, deque
from dataclasses import dataclass, field
from datetime import datetime
from statistics import median

try:
    import psutil
    from rich.console import Console
    from rich.live import Live
    from rich.panel import Panel
    from rich.table import Table
    from rich.text import Text
    from rich.console import Group
except ImportError:
    sys.exit("Missing dependencies. Run:  pip install psutil rich")

MB = 1024 * 1024
NCPU = psutil.cpu_count() or 1
HAS_PROC_IO = hasattr(psutil.Process, "io_counters")  # not available on macOS
USE_SS = sys.platform.startswith("linux") and shutil.which("ss") is not None
console = Console()


# --------------------------------------------------------------------------- #
# Metric definitions
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class Spec:
    key: str        # key in Sample.m
    label: str
    kind: str       # "pct" or "bps"
    attr: str       # matching attribute on ProcSample
    abs_min: float  # never flag below this absolute value
    min_delta: float  # must exceed baseline by at least this much
    k: float        # ...and by k robust standard deviations


SPECS = [
    Spec("cpu", "CPU", "pct", "cpu", 25, 15, 3.5),
    Spec("mem_growth", "Memory growth", "bps", "rss_growth", 60 * MB, 40 * MB, 4),
    Spec("disk_read", "Disk read", "bps", "read_bps", 25 * MB, 15 * MB, 4),
    Spec("disk_write", "Disk write", "bps", "write_bps", 25 * MB, 15 * MB, 4),
    Spec("net_down", "Net download", "bps", "net_down", 1.5 * MB, 1 * MB, 4),
    Spec("net_up", "Net upload", "bps", "net_up", 1 * MB, 0.75 * MB, 4),
]
BY_LABEL = {s.label: s for s in SPECS}


def fmt_bytes(n: float) -> str:
    for unit in ("B", "KB", "MB", "GB"):
        if abs(n) < 1024:
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.1f} TB"


def fmt(spec: Spec, v: float) -> str:
    return f"{v:.0f}%" if spec.kind == "pct" else fmt_bytes(max(v, 0)) + "/s"


# --------------------------------------------------------------------------- #
# Sampling
# --------------------------------------------------------------------------- #
@dataclass
class ProcSample:
    pid: int
    name: str
    cpu: float          # % of the WHOLE machine (so it sums to system CPU)
    rss: int
    read_bps: float = 0.0
    write_bps: float = 0.0
    rss_growth: float = 0.0   # bytes/s of resident-memory growth
    net_down: float = 0.0
    net_up: float = 0.0


@dataclass
class Sample:
    ts: float
    m: dict
    procs: list
    mem_pct: float
    swap_pct: float
    net_attr: bool      # True if per-process network numbers are real


_USERS_RE = re.compile(r'users:\(\("([^"]*)",pid=(\d+)')


def _is_loop(addr: str) -> bool:
    return addr.startswith(("127.", "[::1]")) or "::ffff:127." in addr


def read_ss():
    """Per-socket TCP byte counters from `ss`: {(pid, local, peer): (sent, recv)}."""
    try:
        out = subprocess.run(["ss", "-tinp"], capture_output=True, text=True, timeout=3).stdout
    except (OSError, subprocess.SubprocessError):
        return None
    sockets, lines, i = {}, out.splitlines(), 0
    while i < len(lines):
        head = lines[i]
        if not head.strip() or head[0].isspace() or head.startswith("State"):
            i += 1
            continue
        info = ""
        if i + 1 < len(lines) and lines[i + 1][:1].isspace():
            info = lines[i + 1]
            i += 1
        i += 1
        cols = head.split()
        m = _USERS_RE.search(head)
        if len(cols) < 5 or not m or _is_loop(cols[3]) or _is_loop(cols[4]):
            continue
        sent = re.search(r"bytes_sent:(\d+)", info)
        recv = re.search(r"bytes_received:(\d+)", info)
        sockets[(int(m.group(2)), cols[3], cols[4])] = (
            int(sent.group(1)) if sent else 0,
            int(recv.group(1)) if recv else 0,
        )
    return sockets


def connection_estimate(top: int = 3) -> list:
    """Fallback when real per-process network counters are unavailable:
    rank processes by number of established, non-loopback connections."""
    counts: Counter = Counter()
    try:
        for c in psutil.net_connections(kind="inet"):
            if c.status == psutil.CONN_ESTABLISHED and c.pid and c.raddr and not _is_loop(c.raddr.ip):
                counts[c.pid] += 1
    except (psutil.Error, OSError):
        return []
    named: Counter = Counter()
    for pid, n in counts.items():
        try:
            named[psutil.Process(pid).name()] += n
        except psutil.Error:
            pass
    return [{"name": n, "value": c, "share": 0, "procs": 0, "pid": 0, "estimated": True}
            for n, c in named.most_common(top)]


class Sampler:
    def __init__(self):
        self.t = time.monotonic()
        self.disk = psutil.disk_io_counters()
        self.nic = self._nic_totals()
        self.used = psutil.virtual_memory().used
        self.proc_io: dict = {}
        self.proc_rss: dict = {}
        self.socks: dict = {}

    @staticmethod
    def _nic_totals():
        rx = tx = 0
        for name, n in psutil.net_io_counters(pernic=True).items():
            if not name.lower().startswith(("lo", "loopback")):
                rx += n.bytes_recv
                tx += n.bytes_sent
        return rx, tx

    def sample(self) -> Sample:
        now = time.monotonic()
        dt = max(now - self.t, 1e-3)
        self.t = now
        m = {"cpu": psutil.cpu_percent(None)}

        vm = psutil.virtual_memory()
        m["mem_growth"] = (vm.used - self.used) / dt
        self.used = vm.used

        d = psutil.disk_io_counters()
        if d and self.disk:
            m["disk_read"] = (d.read_bytes - self.disk.read_bytes) / dt
            m["disk_write"] = (d.write_bytes - self.disk.write_bytes) / dt
        else:
            m["disk_read"] = m["disk_write"] = 0.0
        self.disk = d

        rx, tx = self._nic_totals()
        m["net_down"] = max(rx - self.nic[0], 0) / dt
        m["net_up"] = max(tx - self.nic[1], 0) / dt
        self.nic = (rx, tx)

        procs, cur_io, cur_rss = [], {}, {}
        for p in psutil.process_iter(["pid", "name", "cpu_percent", "memory_info"]):
            info = p.info
            mi = info.get("memory_info")
            pid = info["pid"]
            name = info.get("name") or "?"
            if mi is None or pid == 0 or name == "System Idle Process":
                continue
            ps = ProcSample(pid, name, (info.get("cpu_percent") or 0.0) / NCPU, mi.rss)
            if pid in self.proc_rss:
                ps.rss_growth = max(mi.rss - self.proc_rss[pid], 0) / dt
            cur_rss[pid] = mi.rss
            if HAS_PROC_IO:
                try:
                    io = p.io_counters()
                    cur_io[pid] = (io.read_bytes, io.write_bytes)
                    if pid in self.proc_io:
                        ps.read_bps = max(io.read_bytes - self.proc_io[pid][0], 0) / dt
                        ps.write_bps = max(io.write_bytes - self.proc_io[pid][1], 0) / dt
                except (psutil.Error, OSError):
                    pass
            procs.append(ps)
        self.proc_io, self.proc_rss = cur_io, cur_rss

        net_attr = False
        if USE_SS:
            cur = read_ss()
            if cur is not None:
                net_attr = True
                by_pid = {p.pid: p for p in procs}
                for key, (sent, recv) in cur.items():
                    ps_, pr_ = self.socks.get(key, (0, 0))   # new socket starts at 0
                    p = by_pid.get(key[0])
                    if p:
                        p.net_up += max(sent - ps_, 0) / dt
                        p.net_down += max(recv - pr_, 0) / dt
                self.socks = cur

        return Sample(time.time(), m, procs, vm.percent, psutil.swap_memory().percent, net_attr)


# --------------------------------------------------------------------------- #
# Attribution + spike detection
# --------------------------------------------------------------------------- #
def aggregate(procs, attr: str) -> list:
    """Group processes by name (so 14 chrome helpers count as one 'chrome')."""
    groups: dict = {}
    for p in procs:
        v = getattr(p, attr)
        if v <= 0:
            continue
        g = groups.setdefault(p.name, {"name": p.name, "value": 0.0, "procs": 0, "pid": p.pid, "best": 0.0})
        g["value"] += v
        g["procs"] += 1
        if v > g["best"]:
            g["best"], g["pid"] = v, p.pid
    return sorted(groups.values(), key=lambda g: -g["value"])


def attribute(spec: Spec, s: Sample, top: int = 3) -> list:
    if spec.key.startswith("net") and not s.net_attr:
        return connection_estimate(top)
    total = s.m[spec.key]
    return [
        {"name": g["name"], "value": round(g["value"], 1),
         "share": round(g["value"] / total, 3) if total > 0 else 0.0,
         "procs": g["procs"], "pid": g["pid"]}
        for g in aggregate(s.procs, spec.attr)[:top]
    ]


def running_now(s: Sample, top: int = 5) -> list:
    """Context snapshot: the busiest applications at this instant."""
    return [{"name": g["name"], "cpu": round(g["value"], 1)} for g in aggregate(s.procs, "cpu")[:top]]


@dataclass
class Event:
    spec: Spec
    start: float
    baseline: float
    peak: float = 0.0
    peak_ts: float = 0.0
    last: float = 0.0
    quiet: int = 0
    culprits: list = field(default_factory=list)
    running: list = field(default_factory=list)

    def duration(self, interval: float) -> float:
        return self.last - self.start + interval


WARMUP, QUIET = 10, 3


class Detector:
    """Flags a sample when it exceeds a robust (median/MAD) rolling baseline."""

    def __init__(self, sensitivity: float = 1.0, window: int = 90):
        self.sens = sensitivity
        self.hist = {s.key: deque(maxlen=window) for s in SPECS}
        self.open: dict = {}

    def update(self, s: Sample):
        opened, closed = [], []
        for sp in SPECS:
            v, h, base, spike = s.m[sp.key], self.hist[sp.key], 0.0, False
            if len(h) >= WARMUP:
                base = median(h)
                mad = median(abs(x - base) for x in h) * 1.4826
                thr = max(base + max(sp.k * mad, sp.min_delta / self.sens), sp.abs_min / self.sens)
                spike = v > thr
            h.append(v)
            ev = self.open.get(sp.key)
            if spike:
                if ev is None:
                    ev = self.open[sp.key] = Event(sp, s.ts, base)
                    opened.append(ev)
                ev.quiet, ev.last = 0, s.ts
                if v > ev.peak:
                    ev.peak, ev.peak_ts = v, s.ts
                    ev.culprits, ev.running = attribute(sp, s), running_now(s)
            elif ev:
                ev.quiet += 1
                if ev.quiet >= QUIET:
                    closed.append(self.open.pop(sp.key))
        return opened, closed


# --------------------------------------------------------------------------- #
# Presentation
# --------------------------------------------------------------------------- #
SPARK = "▁▂▃▄▅▆▇█"


def spark(vals, hi: float, width: int = 48) -> str:
    vals = list(vals)[-width:]
    hi = max(hi, max(vals, default=0), 1e-9)
    return "".join(SPARK[min(7, int(max(v, 0) / hi * 7.999))] for v in vals)


def culprit_text(ev_spec: Spec, culprits: list) -> str:
    if not culprits:
        return "no per-process data (try running with sudo / as admin)"
    parts = []
    for c in culprits:
        if c.get("estimated"):
            parts.append(f"{c['name']} ({c['value']} open conns, est.)")
        else:
            parts.append(f"{c['name']} {fmt(ev_spec, c['value'])} ({min(c['share'], 1) * 100:.0f}%)")
    covered = min(sum(c.get("share", 0) for c in culprits), 1)
    if culprits and not culprits[0].get("estimated") and covered < 0.5:
        parts.append(f"{(1 - covered) * 100:.0f}% unattributed")
    return " · ".join(parts)


def clock(ts: float) -> str:
    return datetime.fromtimestamp(ts).strftime("%H:%M:%S")


def event_record(ev: Event, interval: float) -> dict:
    return {
        "time": datetime.fromtimestamp(ev.start).isoformat(timespec="seconds"),
        "peak_time": datetime.fromtimestamp(ev.peak_ts).isoformat(timespec="seconds"),
        "metric": ev.spec.key, "label": ev.spec.label,
        "duration_s": round(ev.duration(interval), 1),
        "baseline": round(ev.baseline, 1), "peak": round(ev.peak, 1),
        "culprits": ev.culprits, "running_at_peak": ev.running,
    }


class App:
    def __init__(self, interval: float, sens: float, log_path: str | None):
        self.interval, self.log_path = interval, log_path
        self.sampler, self.det = Sampler(), Detector(sens)
        self.hist = {s.key: deque(maxlen=60) for s in SPECS}
        self.hist["mem_pct"] = deque(maxlen=60)
        self.recent: deque = deque(maxlen=8)
        self.last: Sample | None = None
        self.sampler.sample()          # warm-up: primes counters, result discarded
        time.sleep(0.5)

    def tick(self, plain: bool = False) -> None:
        s = self.last = self.sampler.sample()
        for k, h in self.hist.items():
            h.append(s.mem_pct if k == "mem_pct" else s.m[k])
        opened, closed = self.det.update(s)
        for ev in opened:
            if plain:
                console.print(f"[{clock(ev.start)}] [bold red]▲ {ev.spec.label} spike[/] "
                              f"{fmt(ev.spec, ev.peak)} (baseline {fmt(ev.spec, ev.baseline)}) "
                              f"← {culprit_text(ev.spec, ev.culprits)}", highlight=False)
        for ev in closed:
            self._finish(ev, plain)

    def _finish(self, ev: Event, plain: bool) -> None:
        self.recent.appendleft(ev)
        if self.log_path:
            with open(self.log_path, "a") as f:
                f.write(json.dumps(event_record(ev, self.interval)) + "\n")
        if plain:
            console.print(f"[{clock(ev.last)}] [green]▼ {ev.spec.label} back to normal[/] after "
                          f"{ev.duration(self.interval):.0f}s, peak {fmt(ev.spec, ev.peak)} "
                          f"← {culprit_text(ev.spec, ev.culprits)}", highlight=False)

    def close_all(self, plain: bool = False) -> None:
        for ev in list(self.det.open.values()):
            self._finish(ev, plain)
        self.det.open.clear()


def top_groups(procs, n: int = 8) -> list:
    groups: dict = {}
    for p in procs:
        g = groups.setdefault(p.name, dict(name=p.name, n=0, cpu=0.0, rss=0, rd=0.0, wr=0.0, dn=0.0, up=0.0))
        g["n"] += 1
        g["cpu"] += p.cpu
        g["rss"] += p.rss
        g["rd"] += p.read_bps
        g["wr"] += p.write_bps
        g["dn"] += p.net_down
        g["up"] += p.net_up

    def score(g):
        return (g["cpu"] / 25 + (g["rd"] + g["wr"]) / (20 * MB) + (g["dn"] + g["up"]) / (2 * MB)
                + g["rss"] / (1 << 42))
    return sorted(groups.values(), key=score, reverse=True)[:n]


def render(app: App):
    s = app.last
    capabilities = (
        f"per-process: CPU ✓  memory ✓  disk {'✓' if HAS_PROC_IO else '✗ (unsupported on this OS)'}  "
        f"network {'✓ (ss)' if USE_SS else '≈ connection-count estimate only'}"
    )
    sys_t = Table(box=None, expand=True, pad_edge=False)
    sys_t.add_column("Metric", no_wrap=True)
    sys_t.add_column("Now", justify="right", no_wrap=True)
    sys_t.add_column("Last 60s", no_wrap=True)
    sys_t.add_row("Memory used", f"{s.mem_pct:.0f}%", Text(spark(app.hist["mem_pct"], 100), style="cyan"))
    for sp in SPECS:
        active = sp.key in app.det.open
        hi = 100 if sp.kind == "pct" else sp.abs_min * 2
        sys_t.add_row(
            Text(sp.label, style="bold red" if active else ""),
            Text(fmt(sp, s.m[sp.key]), style="bold red" if active else ""),
            Text(spark(app.hist[sp.key], hi), style="red" if active else "green"),
        )

    proc_t = Table(box=None, expand=True, pad_edge=False)
    for col, right in (("Application", False), ("CPU", True), ("RAM", True), ("Disk R", True),
                       ("Disk W", True), ("Net ↓", True), ("Net ↑", True)):
        proc_t.add_column(col, justify="right" if right else "left", no_wrap=True)
    for g in top_groups(s.procs):
        label = g["name"] + (f" ×{g['n']}" if g["n"] > 1 else "")
        proc_t.add_row(label, f"{g['cpu']:.1f}%", fmt_bytes(g["rss"]), fmt_bytes(g["rd"]), fmt_bytes(g["wr"]),
                       fmt_bytes(g["dn"]), fmt_bytes(g["up"]))

    log = Text()
    for ev in app.det.open.values():
        log.append(f"{clock(ev.start)} ● ACTIVE {ev.spec.label} {fmt(ev.spec, ev.peak)} ", style="bold red")
        log.append(f"← {culprit_text(ev.spec, ev.culprits)}\n")
    for ev in app.recent:
        log.append(f"{clock(ev.start)} ○ {ev.spec.label} peaked {fmt(ev.spec, ev.peak)} "
                   f"for {ev.duration(app.interval):.0f}s ", style="yellow")
        log.append(f"← {culprit_text(ev.spec, ev.culprits)}\n")
    if not log.plain:
        log = Text("No spikes yet. Baselines are still learning the first ~10 seconds.", style="dim")

    return Group(
        Text(f" {capabilities}   (Ctrl-C to quit)", style="dim"),
        Panel(sys_t, title="System", border_style="blue"),
        Panel(proc_t, title="Busiest applications right now", border_style="blue"),
        Panel(log, title="Spike log (who was responsible at the peak)", border_style="red"),
    )


# --------------------------------------------------------------------------- #
# Report mode
# --------------------------------------------------------------------------- #
def report(path: str) -> None:
    try:
        rows = [json.loads(line) for line in open(path) if line.strip()]
    except FileNotFoundError:
        sys.exit(f"No such log: {path}")
    if not rows:
        sys.exit("Log is empty.")
    by_label = defaultdict(list)
    for r in rows:
        by_label[r["label"]].append(r)
    t = Table(title=f"{len(rows)} spike events in {path}")
    for c in ("Metric", "Events", "Total time", "Worst peak", "Most-blamed (events)"):
        t.add_column(c)
    for label, evs in by_label.items():
        spec = BY_LABEL.get(label)
        blame = Counter(e["culprits"][0]["name"] for e in evs if e["culprits"])
        worst = max(evs, key=lambda e: e["peak"])
        t.add_row(label, str(len(evs)), f"{sum(e['duration_s'] for e in evs):.0f}s",
                  fmt(spec, worst["peak"]) if spec else str(worst["peak"]),
                  ", ".join(f"{n} ({c})" for n, c in blame.most_common(3)) or "-")
    console.print(t)


# --------------------------------------------------------------------------- #
def main() -> None:
    ap = argparse.ArgumentParser(description="Real-time system monitor that attributes spikes to applications.")
    ap.add_argument("--interval", type=float, default=1.0, help="seconds between samples (default 1)")
    ap.add_argument("--sensitivity", type=float, default=1.0,
                    help="higher = flags smaller spikes (default 1.0; try 2 for twitchy, 0.5 for calm)")
    ap.add_argument("--log", default="spikewatch_events.jsonl", help="JSONL file for spike events ('' to disable)")
    ap.add_argument("--plain", action="store_true", help="scrolling text output instead of the live dashboard")
    ap.add_argument("--duration", type=float, default=0, help="stop after N seconds (0 = run until Ctrl-C)")
    ap.add_argument("--report", metavar="LOG", help="summarise a JSONL log and exit")
    args = ap.parse_args()

    if args.report:
        return report(args.report)

    app = App(args.interval, args.sensitivity, args.log or None)
    end = time.time() + args.duration if args.duration else None
    try:
        if args.plain:
            console.print(f"spikewatch running — logging to {args.log or '(nowhere)'}. Ctrl-C to stop.")
            while end is None or time.time() < end:
                t0 = time.time()
                app.tick(plain=True)
                time.sleep(max(0, args.interval - (time.time() - t0)))
        else:
            app.tick()
            with Live(render(app), console=console, screen=True, refresh_per_second=4) as live:
                while end is None or time.time() < end:
                    t0 = time.time()
                    app.tick()
                    live.update(render(app))
                    time.sleep(max(0, args.interval - (time.time() - t0)))
    except KeyboardInterrupt:
        pass
    finally:
        app.close_all(plain=args.plain)


if __name__ == "__main__":
    main()
