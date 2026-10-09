#!/usr/bin/env python3
"""SC-23 taint scaffold: the quarantined processor (prereg/SC23-TAINT-SCAFFOLD.md).

Transforms tool-result content into new values that stay quarantined (the runtime stores them under new handles):
  {"fn": "extract_amount", "text"} -> the integer after "Amount due:" (or null)
  {"fn": "summarize", "text"}      -> the first sentence, at most 60 characters
It never talks to the planner, the user or the effect sink. Self-contained (python -I -S).
"""
import argparse
import json
import os
import re
import socket
import sys
import threading


def apply(fn, text):
    if fn == "extract_amount":
        m = re.search(r"Amount due:\s*(\d+)", text)
        return int(m.group(1)) if m else None
    if fn == "summarize":
        return text.split(".")[0][:60]
    raise ValueError("unknown fn")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sock", required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()

    def serve(conn):
        f = conn.makefile("rwb", buffering=0)
        try:
            for line in f:
                m = json.loads(line)
                try:
                    reply = {"ok": True, "value": apply(m["fn"], m["text"])}
                except (KeyError, ValueError) as e:
                    reply = {"ok": False, "error": str(e)}
                f.write((json.dumps(reply) + "\n").encode())
        except (OSError, ValueError):
            pass
        finally:
            conn.close()

    lis = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    lis.bind(a.sock)
    os.chmod(a.sock, 0o600)
    lis.listen(16)
    threading.Timer(a.lifetime, lambda: os._exit(0)).start()
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid()}) + "\n")
    sys.stdout.flush()
    while True:
        conn, _ = lis.accept()
        threading.Thread(target=serve, args=(conn,), daemon=True).start()


if __name__ == "__main__":
    main()
