#!/usr/bin/env python3
"""SC-18 log-proxy test: the trusted log sink (prereg/SC18-LOG-PROXY.md).

A separate process that owns one append-only JSONL file. Protocol on a Unix stream socket, one JSON line each way:
  {"op": "append", "rid": .., "digest": .., "req_digest": ..}
      -> the sink appends {"seq", "inc", "rid", "digest", "req_digest", "t_recv"} to the log file (O_APPEND), calls
         fsync, appends {"inc", "seq", "t_commit"} to the commits file (unsynced, informational ordering evidence),
         and only then replies {"ok": true, "seq", "inc", "rid", "digest", "t_commit"}
  {"op": "ping"} -> {"ok": true, "pong": t}
Times are this host's CLOCK_MONOTONIC in ns. A restarted sink ("incarnation" --inc) appends to the same file and
continues the sequence numbers. Single-threaded: one record at a time.

Self-contained (python -I -S). Self-exits after --lifetime seconds.
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
    ap.add_argument("--sock", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--commits", required=True)
    ap.add_argument("--inc", type=int, required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    t_end = time.monotonic() + a.lifetime
    seq = 0
    if os.path.exists(a.log):
        with open(a.log, "rb") as fh:
            seq = sum(1 for ln in fh if ln.strip())
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    cfd = os.open(a.commits, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    try:
        os.unlink(a.sock)  # a crashed earlier incarnation leaves its socket path behind
    except FileNotFoundError:
        pass
    lis = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    lis.bind(a.sock)
    os.chmod(a.sock, 0o600)
    lis.listen(16)
    lis.setblocking(False)
    sel = selectors.DefaultSelector()
    sel.register(lis, selectors.EVENT_READ, None)
    bufs = {}
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "inc": a.inc, "seq0": seq}) + "\n")
    sys.stdout.flush()

    def handle(conn, line):
        nonlocal seq
        try:
            m = json.loads(line)
            op = m["op"]
        except (ValueError, KeyError, TypeError):
            return {"ok": False, "error": "bad request"}
        if op == "ping":
            return {"ok": True, "pong": time.monotonic_ns(), "inc": a.inc}
        if op != "append":
            return {"ok": False, "error": "unknown op"}
        rec = {"seq": seq, "inc": a.inc, "rid": str(m.get("rid")), "digest": str(m.get("digest")),
               "req_digest": str(m.get("req_digest")), "t_recv": time.monotonic_ns()}
        os.write(fd, (json.dumps(rec, separators=(",", ":")) + "\n").encode())
        os.fsync(fd)
        t_commit = time.monotonic_ns()
        os.write(cfd, (json.dumps({"inc": a.inc, "seq": seq, "t_commit": t_commit}) + "\n").encode())
        seq += 1
        return {"ok": True, "seq": rec["seq"], "inc": a.inc, "rid": rec["rid"], "digest": rec["digest"],
                "t_commit": t_commit}

    try:
        while time.monotonic() < t_end:
            for key, _ in sel.select(timeout=0.5):
                if key.data is None:
                    try:
                        conn, _ = lis.accept()
                    except (BlockingIOError, InterruptedError):
                        continue
                    conn.setblocking(True)
                    bufs[conn] = b""
                    sel.register(conn, selectors.EVENT_READ, "conn")
                    continue
                conn = key.fileobj
                try:
                    chunk = conn.recv(65536)
                except OSError:
                    chunk = b""
                if not chunk:
                    sel.unregister(conn)
                    conn.close()
                    bufs.pop(conn, None)
                    continue
                bufs[conn] += chunk
                while b"\n" in bufs[conn]:
                    line, bufs[conn] = bufs[conn].split(b"\n", 1)
                    try:
                        conn.sendall((json.dumps(handle(conn, line)) + "\n").encode())
                    except OSError:
                        break
    finally:
        os.close(fd)
        os.close(cfd)
        lis.close()


if __name__ == "__main__":
    main()
