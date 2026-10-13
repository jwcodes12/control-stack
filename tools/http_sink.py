#!/usr/bin/env python3
"""Loopback-only HTTP destination for the outbox relay demo and tests. Not a product: it exists so the relay can be exercised
against a destination that is not a third party. It honours Idempotency-Key (one stored copy per key) and can inject the
faults the relay must survive: a lost acknowledgement after the bytes were stored, a 500 before storing, a wrong echoed hash,
a redirect."""
import hashlib
import json
import sys
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer


class Sink:
    def __init__(self):
        self.stored = {}      # idempotency key -> bytes (the effect: exactly one copy per key)
        self.requests = []    # (key, sha256) for every POST received, duplicates included
        self.faults = []      # consumed front to back, one per request: None | drop_ack | http500 | wrong_echo | redirect
        self.lock = threading.Lock()

    def server(self, port=0):
        sink = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def log_message(self, *args):
                pass

            def do_POST(self):
                body = self.rfile.read(int(self.headers.get("Content-Length", "0")))
                key = self.headers.get("Idempotency-Key", "")
                digest = hashlib.sha256(body).hexdigest()
                with sink.lock:
                    fault = sink.faults.pop(0) if sink.faults else None
                    sink.requests.append((key, digest))
                    if fault == "http500":
                        return self._reply(500, b"{}")
                    if fault == "redirect":
                        self.send_response(302)
                        self.send_header("Location", "http://127.0.0.1:1/elsewhere")
                        self.send_header("Content-Length", "0")
                        self.end_headers()
                        return
                    sink.stored.setdefault(key, body)  # the idempotent effect
                    if fault == "drop_ack":
                        self.close_connection = True
                        self.connection.close()
                        return
                    echoed = "0" * 64 if fault == "wrong_echo" else digest
                self._reply(200, json.dumps({"sha256": echoed, "stored": len(sink.stored)}).encode())

            def _reply(self, status, data):
                self.send_response(status)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(data)))
                self.end_headers()
                self.wfile.write(data)

        return ThreadingHTTPServer(("127.0.0.1", port), Handler)


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    srv = Sink().server(port)
    print("listening on 127.0.0.1:%d" % srv.server_address[1], flush=True)
    srv.serve_forever()


if __name__ == "__main__":
    main()
