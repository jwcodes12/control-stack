#!/usr/bin/env python3
"""SC-18 log-proxy test: a model server stub (prereg/SC18-LOG-PROXY.md).

Returns canned completions; no model, no network beyond 127.0.0.1. POST /v1/complete with a JSON body
{"prompt": str} returns {"text": <one of a few canned strings chosen by the prompt's hash>, "model": "stub"}.
Prints "READY {"port": p}" once listening. Self-contained (python -I -S); self-exits after --lifetime seconds.
"""
import argparse
import hashlib
import json
import os
import sys
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

CANNED = [
    "The capital of France is Paris.",
    "Water boils at 100 degrees Celsius at sea level.",
    "A haiku has three lines of five, seven and five syllables.",
    "Photosynthesis converts light energy into chemical energy.",
    "The quick brown fox jumps over the lazy dog.",
]


class H(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *a):
        pass

    def do_POST(self):
        n = int(self.headers.get("Content-Length") or 0)
        try:
            prompt = json.loads(self.rfile.read(n) or b"{}").get("prompt", "")
        except ValueError:
            prompt = ""
        i = int(hashlib.sha256(prompt.encode()).hexdigest(), 16) % len(CANNED)
        body = json.dumps({"text": CANNED[i], "model": "stub"}).encode()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    srv = ThreadingHTTPServer(("127.0.0.1", 0), H)
    srv.daemon_threads = True
    threading.Timer(a.lifetime, lambda: os._exit(0)).start()
    sys.stdout.write("READY " + json.dumps({"port": srv.server_address[1], "pid": os.getpid()}) + "\n")
    sys.stdout.flush()
    srv.serve_forever()


if __name__ == "__main__":
    main()
