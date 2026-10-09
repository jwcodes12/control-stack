#!/usr/bin/env python3
"""SC-07 benign job client. Runs unprivileged (numeric UID) inside the job namespace.

  upload : generate --bytes of random data, connect over plain TCP to --dst:--port, send it (optionally paced at
           --rate bytes/s), half-close, and wait for the sink's "OK <bytes> <sha256>" line. Gives up when connect
           takes longer than --connect-timeout, when a send makes no progress for --stall-timeout, or when the ack
           does not arrive within --ack-timeout. Prints one JSON result line. The socket uses SO_LINGER 0, so
           closing it aborts the connection and frees it at once.
  hold   : print "READY {pid}" and wait until stdin closes (used for the H5 credential/namespace inspection).

No evasion, retries, tunnelling or alternative paths: one TCP connection to one address. Every mode exits by itself
after --lifetime seconds. Stdlib only; Python 3.9 compatible.
"""
import argparse
import hashlib
import json
import os
import select
import signal
import socket
import struct
import sys
import time


def upload(a):
    data = os.urandom(a.bytes)
    sha = hashlib.sha256(data).hexdigest()
    res = {"mode": "upload", "pid": os.getpid(), "uid": os.getuid(), "dst": "%s:%d" % (a.dst, a.port),
           "bytes": a.bytes, "sha256": sha, "rate": a.rate, "connected": False, "connect_error": None,
           "sent": 0, "send_end": None, "ack": None, "completed": False}
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
    s.settimeout(a.connect_timeout)
    t0 = time.monotonic()
    res["t_connect_start"] = t0
    try:
        s.connect((a.dst, a.port))
        res["connected"] = True
    except (socket.timeout, OSError) as e:
        res["connect_error"] = "%s: %s" % (e.__class__.__name__, e)
    res["t_connect_end"] = time.monotonic()
    if res["connected"]:
        s.settimeout(a.stall_timeout)
        mv = memoryview(data)
        sent, t_send = 0, time.monotonic()
        end = "complete"
        while sent < a.bytes:
            if time.monotonic() - t0 > a.deadline:
                end = "deadline"
                break
            try:
                sent += s.send(mv[sent:sent + a.chunk])
            except socket.timeout:
                end = "stalled"
                break
            except OSError as e:
                end = "error:%s" % e.__class__.__name__
                break
            if a.rate:
                ahead = t_send + sent / float(a.rate) - time.monotonic()
                if ahead > 0:
                    time.sleep(ahead)
        res["sent"], res["send_end"], res["t_send_end"] = sent, end, time.monotonic()
        if end == "complete":
            try:
                s.shutdown(socket.SHUT_WR)
                s.settimeout(a.ack_timeout)
                buf = b""
                while b"\n" not in buf and len(buf) < 256:
                    chunk = s.recv(256)
                    if not chunk:
                        break
                    buf += chunk
                res["ack"] = buf.decode("ascii", "replace").strip() or None
            except (socket.timeout, OSError) as e:
                res["ack_error"] = "%s: %s" % (e.__class__.__name__, e)
            res["completed"] = res["ack"] == "OK %d %s" % (a.bytes, sha)
    s.close()
    res["t_end"] = time.monotonic()
    print(json.dumps(res), flush=True)
    return 0


def hold(a):
    print("READY " + json.dumps({"pid": os.getpid(), "uid": os.getuid()}), flush=True)
    select.select([sys.stdin], [], [], a.lifetime)
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["upload", "hold"])
    ap.add_argument("--dst")
    ap.add_argument("--port", type=int, default=8080)
    ap.add_argument("--bytes", type=int, default=0)
    ap.add_argument("--rate", type=int, default=0, help="bytes/s; 0 = unpaced")
    ap.add_argument("--chunk", type=int, default=65536)
    ap.add_argument("--connect-timeout", type=float, default=1.0)
    ap.add_argument("--stall-timeout", type=float, default=1.0)
    ap.add_argument("--ack-timeout", type=float, default=3.0)
    ap.add_argument("--deadline", type=float, default=8.0)
    ap.add_argument("--lifetime", type=float, default=10.0)
    a = ap.parse_args()
    signal.signal(signal.SIGALRM, lambda s, f: os._exit(3))
    signal.alarm(int(a.lifetime) + 1)
    return upload(a) if a.mode == "upload" else hold(a)


if __name__ == "__main__":
    sys.exit(main())
