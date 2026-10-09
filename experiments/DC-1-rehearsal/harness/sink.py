#!/usr/bin/env python3
"""DC-1 single-host rehearsal: the effect sink (preregistration prereg/DC1-REHEARSAL-SINGLEHOST.md).

A single-threaded, append-only record store. Workers connect to the effect socket and send one JSON line per effect:
    {"w": worker, "s": seq, "e": epoch held by the worker, "ti": worker CLOCK_MONOTONIC ns at initiation}
The sink stamps every effect with its OWN CLOCK_MONOTONIC (time.monotonic_ns) when it processes the line (the landing
time) and decides, with the rule of `DistributedHalt.accepts`:

    accept  iff  fencing is off  or  epoch >= current epoch

(the model's third disjunct, landing time < t0 + eps, is implicit: before the bump the current epoch is e0, which
every worker holds). The controller's socket carries MARK (t0, stamped by the sink), BUMP <epoch> (the fence, stamped
by the sink when it takes effect) and STOP. Effects and control commands are processed one at a time in one loop, so
an effect processed after the BUMP is checked against the new epoch.

Self-contained (runs with python -I -S). Benign: it only reads its two Unix sockets and appends to one file.
Self-exits after --lifetime seconds.
"""
import argparse
import json
import os
import selectors
import socket
import sys
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--effects", required=True, help="Unix socket path for worker effects")
    ap.add_argument("--ctl", required=True, help="Unix socket path for the controller")
    ap.add_argument("--fence", choices=["on", "off"], required=True)
    ap.add_argument("--epoch", type=int, required=True, help="initial epoch e0")
    ap.add_argument("--log", required=True, help="append-only JSONL log of every effect and control event")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    fence = a.fence == "on"
    cur = a.epoch
    t_end = time.monotonic() + a.lifetime
    logf = open(a.log, "a", buffering=1 << 20)
    counts = {"effects": 0, "accepted": 0, "rejected": 0, "bad": 0}

    def rec(obj):
        logf.write(json.dumps(obj, separators=(",", ":")) + "\n")

    sel = selectors.DefaultSelector()
    lis = {}
    for name, path in (("effects", a.effects), ("ctl", a.ctl)):
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.bind(path)
        os.chmod(path, 0o600)
        s.listen(64)
        s.setblocking(False)
        sel.register(s, selectors.EVENT_READ, ("listen", name))
        lis[name] = s
    bufs = {}
    rec({"ctl": "START", "t": time.monotonic_ns(), "fence": fence, "epoch": cur, "pid": os.getpid()})
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid()}) + "\n")
    sys.stdout.flush()

    def effect_line(line):
        nonlocal cur
        t = time.monotonic_ns()
        try:
            m = json.loads(line)
            w, sq, ep, ti = int(m["w"]), int(m["s"]), int(m["e"]), int(m["ti"])
        except (ValueError, KeyError, TypeError):
            counts["bad"] += 1
            rec({"bad": line[:200].decode("utf-8", "replace"), "t": t})
            return
        acc = (not fence) or ep >= cur
        counts["effects"] += 1
        counts["accepted" if acc else "rejected"] += 1
        rec({"t": t, "w": w, "s": sq, "e": ep, "ti": ti, "acc": acc, "cur": cur})

    def drain_effects():
        """STOP: read everything already buffered on effect connections before closing the log."""
        for key in list(sel.get_map().values()):
            kind, name = key.data
            if kind != "conn" or name != "effects":
                continue
            conn = key.fileobj
            while True:
                try:
                    chunk = conn.recv(65536)
                except (BlockingIOError, InterruptedError):
                    break
                except OSError:
                    break
                if not chunk:
                    break
                bufs[conn] += chunk
                while b"\n" in bufs[conn]:
                    line, bufs[conn] = bufs[conn].split(b"\n", 1)
                    effect_line(line)

    def ctl_line(conn, line):
        nonlocal cur
        parts = line.decode().split()
        t = time.monotonic_ns()
        if not parts:
            return False
        if parts[0] == "MARK":
            rec({"ctl": "MARK", "t": t})
            reply = {"ok": True, "t": t}
        elif parts[0] == "BUMP":
            cur = int(parts[1])
            t = time.monotonic_ns()
            rec({"ctl": "BUMP", "t": t, "epoch": cur, "fence": fence})
            reply = {"ok": True, "t": t, "epoch": cur}
        elif parts[0] == "STOP":
            drain_effects()
            t = time.monotonic_ns()
            rec({"ctl": "STOP", "t": t, "counts": counts})
            logf.flush()
            os.fsync(logf.fileno())
            reply = {"ok": True, "t": t, "counts": counts}
            conn.sendall((json.dumps(reply) + "\n").encode())
            return True
        else:
            reply = {"ok": False, "error": "unknown command"}
        conn.sendall((json.dumps(reply) + "\n").encode())
        return False

    stop = False
    try:
        while not stop:
            rem = t_end - time.monotonic()
            if rem <= 0:
                rec({"ctl": "LIFETIME", "t": time.monotonic_ns(), "counts": counts})
                break
            for key, _ in sel.select(timeout=min(rem, 0.5)):
                kind, name = key.data
                if kind == "listen":
                    try:
                        conn, _ = key.fileobj.accept()
                    except (BlockingIOError, InterruptedError):
                        continue
                    conn.setblocking(name == "ctl")
                    bufs[conn] = b""
                    sel.register(conn, selectors.EVENT_READ, ("conn", name))
                    continue
                conn = key.fileobj
                try:
                    chunk = conn.recv(65536)
                except (BlockingIOError, InterruptedError):
                    continue
                except OSError:
                    chunk = b""
                if not chunk:
                    sel.unregister(conn)
                    conn.close()
                    if bufs.get(conn):
                        rec({"bad": "partial line at close", "t": time.monotonic_ns(),
                             "n": len(bufs[conn])})
                    bufs.pop(conn, None)
                    continue
                bufs[conn] += chunk
                while b"\n" in bufs[conn]:
                    line, bufs[conn] = bufs[conn].split(b"\n", 1)
                    if name == "effects":
                        effect_line(line)
                    elif ctl_line(conn, line):
                        stop = True
                        break
                if stop:
                    break
    finally:
        logf.flush()
        logf.close()
        for s in lis.values():
            s.close()
        for p in (a.effects, a.ctl):
            try:
                os.unlink(p)
            except OSError:
                pass


if __name__ == "__main__":
    main()
