#!/usr/bin/env python3
"""SC-18 log-proxy test: the trusted log-before-release proxy (prereg/SC18-LOG-PROXY.md).

Sits between clients and the model stub, on 127.0.0.1. For POST /v1/complete with header X-Request-Id:
  1. if the watchdog has stopped serving: refuse (503, X-Refuse: watchdog) without contacting the model;
  2. a request id seen before is refused (409, X-Refuse: duplicate)  [model: no request released twice];
  3. forward to the model stub, read the response body, digest = sha256(body);
  4. send {"op": "append", rid, digest, req_digest} to the log sink and wait up to --ack-timeout for an ack that
     names the same rid and digest  [model: logWrite, then `release` requires id in acked];
  5. ack received -> release (200) with X-Log-Seq / X-Log-Inc; no ack -> refuse (503, X-Refuse: no-ack).
     With --fail-open (NEGATIVE_CONTROL configuration only) a response is released WITHOUT an ack when the sink
     fails  [model: `failOpen`].
Watchdog [model: `watchdog`]: a thread checks every 20 ms; if nothing has been acked for > T seconds, it stops serving
(fail closed). A separate heartbeat thread pings the sink when the last ack is older than --hb (so a hung sink never
delays the halt check); a successful ping after a stop resumes serving (the model's
watchdog halt is absorbing; resumption is an operational extension, see the prereg).
GET /status returns the serving state and the watchdog's halt/resume events. Times are CLOCK_MONOTONIC ns.

Self-contained (python -I -S); self-exits after --lifetime seconds.
"""
import argparse
import hashlib
import http.client
import json
import os
import socket
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer


class Proxy:
    def __init__(self, a):
        self.a = a
        self.T_ns = int(a.T * 1e9)
        self.hb_ns = int(a.hb * 1e9)
        self.conn_lock = threading.Lock()
        self.lock = threading.Lock()
        self.conn = None
        self.rbuf = b""
        self.last_ack = time.monotonic_ns()
        self.serving = True
        self.events = []
        self.seen = set()
        self.counts = {"released_logged": 0, "released_unlogged": 0, "refused_watchdog": 0, "refused_no_ack": 0,
                       "refused_duplicate": 0, "model_error": 0}
        self.journal = open(a.journal, "a", buffering=1)

    # ------------------------------------------------------------ sink connection (caller holds conn_lock)
    def _close(self):
        if self.conn is not None:
            try:
                self.conn.close()
            except OSError:
                pass
        self.conn, self.rbuf = None, b""

    def _call(self, obj):
        """one request/response on the sink connection; raises on any failure or timeout"""
        if self.conn is None:
            s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            s.settimeout(self.a.ack_timeout)
            s.connect(self.a.sink)
            self.conn, self.rbuf = s, b""
        deadline = time.monotonic() + self.a.ack_timeout
        self.conn.settimeout(self.a.ack_timeout)
        self.conn.sendall((json.dumps(obj) + "\n").encode())
        while b"\n" not in self.rbuf:
            rem = deadline - time.monotonic()
            if rem <= 0:
                raise socket.timeout("ack timeout")
            self.conn.settimeout(rem)
            chunk = self.conn.recv(65536)
            if not chunk:
                raise ConnectionError("sink closed")
            self.rbuf += chunk
        line, self.rbuf = self.rbuf.split(b"\n", 1)
        return json.loads(line)

    def log_record(self, rid, digest, req_digest):
        if not self.conn_lock.acquire(timeout=self.a.ack_timeout):
            return False, "no-ack", None
        try:
            if not self.serving:
                return False, "watchdog", None
            try:
                ack = self._call({"op": "append", "rid": rid, "digest": digest, "req_digest": req_digest})
            except (OSError, ValueError):
                self._close()
                return False, "no-ack", None
            if not (ack.get("ok") and ack.get("rid") == rid and ack.get("digest") == digest):
                self._close()
                return False, "no-ack", ack
            with self.lock:
                self.last_ack = time.monotonic_ns()
            return True, None, ack
        finally:
            self.conn_lock.release()

    # ------------------------------------------------------------ watchdog
    def watchdog(self):
        """the halt check only; never blocks on the sink (pings run in their own thread)"""
        while True:
            time.sleep(0.02)
            now = time.monotonic_ns()
            with self.lock:
                if self.serving and now - self.last_ack > self.T_ns:
                    self.serving = False
                    self.events.append({"ev": "halt", "t": now, "last_ack": self.last_ack})

    def heartbeat(self):
        """ping the sink when the last ack is older than hb; a successful ping after a halt resumes serving"""
        while True:
            time.sleep(0.02)
            with self.lock:
                stale = time.monotonic_ns() - self.last_ack > self.hb_ns
            if stale and self.conn_lock.acquire(blocking=False):
                try:
                    ok = False
                    try:
                        ok = bool(self._call({"op": "ping"}).get("ok"))
                    except (OSError, ValueError):
                        self._close()
                    if ok:
                        t = time.monotonic_ns()
                        with self.lock:
                            self.last_ack = t
                            if not self.serving:
                                self.serving = True
                                self.events.append({"ev": "resume", "t": t})
                finally:
                    self.conn_lock.release()

    def note(self, obj):
        with self.lock:
            self.journal.write(json.dumps(obj, separators=(",", ":")) + "\n")


def make_handler(P):
    class H(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def log_message(self, *a):
            pass

        def reply(self, code, body, headers):
            self.send_response(code)
            for k, v in headers.items():
                self.send_header(k, str(v))
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Connection", "close")
            self.end_headers()
            self.wfile.write(body)

        def do_GET(self):
            if self.path != "/status":
                return self.reply(404, b"", {})
            with P.lock:
                st = {"serving": P.serving, "last_ack_age_s": (time.monotonic_ns() - P.last_ack) / 1e9,
                      "events": list(P.events), "counts": dict(P.counts), "fail_open": P.a.fail_open}
            self.reply(200, json.dumps(st).encode(), {"Content-Type": "application/json"})

        def do_POST(self):
            t_in = time.monotonic_ns()
            n = int(self.headers.get("Content-Length") or 0)
            req = self.rfile.read(n)
            rid = self.headers.get("X-Request-Id")

            def refuse(code, why):
                with P.lock:
                    P.counts["refused_" + why.replace("-", "_")] = P.counts.get(
                        "refused_" + why.replace("-", "_"), 0) + 1
                P.note({"rid": rid, "decision": "refuse", "why": why, "t_in": t_in, "t_out": time.monotonic_ns()})
                self.reply(code, json.dumps({"refused": why}).encode(), {"X-Refuse": why})

            if self.path != "/v1/complete" or not rid:
                return self.reply(400, b"", {})
            if not P.serving:
                return refuse(503, "watchdog")
            with P.lock:
                dup = rid in P.seen
                P.seen.add(rid)
            if dup:
                return refuse(409, "duplicate")
            try:
                mc = http.client.HTTPConnection("127.0.0.1", P.a.model_port, timeout=2.0)
                mc.request("POST", "/v1/complete", body=req, headers={"Content-Type": "application/json"})
                mr = mc.getresponse()
                body = mr.read()
                mc.close()
                if mr.status != 200:
                    raise OSError("model status %d" % mr.status)
            except (OSError, http.client.HTTPException):
                with P.lock:
                    P.counts["model_error"] += 1
                return refuse(502, "model")
            digest = hashlib.sha256(body).hexdigest()
            req_digest = hashlib.sha256(req).hexdigest()
            ok, why, ack = P.log_record(rid, digest, req_digest)
            if ok:
                with P.lock:
                    P.counts["released_logged"] += 1
                P.note({"rid": rid, "decision": "release", "logged": True, "seq": ack["seq"], "inc": ack["inc"],
                        "t_in": t_in, "t_out": time.monotonic_ns()})
                return self.reply(200, body, {"Content-Type": "application/json", "X-Log-Seq": ack["seq"],
                                              "X-Log-Inc": ack["inc"], "X-Response-Digest": digest})
            if P.a.fail_open and why == "no-ack":
                with P.lock:
                    P.counts["released_unlogged"] += 1
                P.note({"rid": rid, "decision": "release", "logged": False, "t_in": t_in,
                        "t_out": time.monotonic_ns()})
                return self.reply(200, body, {"Content-Type": "application/json", "X-Unlogged": 1,
                                              "X-Response-Digest": digest})
            return refuse(503, why)

    return H


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sink", required=True)
    ap.add_argument("--model-port", type=int, required=True)
    ap.add_argument("--T", type=float, required=True, help="watchdog: stop serving after T s without an ack")
    ap.add_argument("--ack-timeout", type=float, required=True)
    ap.add_argument("--hb", type=float, required=True, help="ping the sink when the last ack is older than this")
    ap.add_argument("--journal", required=True)
    ap.add_argument("--fail-open", action="store_true", help="NEGATIVE_CONTROL: release without an ack")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    P = Proxy(a)
    # start only once the sink has answered a ping
    t_end = time.monotonic() + 5.0
    while True:
        try:
            with P.conn_lock:
                if P._call({"op": "ping"}).get("ok"):
                    P.last_ack = time.monotonic_ns()
                    break
        except (OSError, ValueError):
            with P.conn_lock:
                P._close()
        if time.monotonic() > t_end:
            sys.exit("sink not answering")
        time.sleep(0.05)
    threading.Thread(target=P.watchdog, daemon=True).start()
    threading.Thread(target=P.heartbeat, daemon=True).start()
    srv = ThreadingHTTPServer(("127.0.0.1", 0), make_handler(P))
    srv.daemon_threads = True
    threading.Timer(a.lifetime, lambda: os._exit(0)).start()
    sys.stdout.write("READY " + json.dumps({"port": srv.server_address[1], "pid": os.getpid(),
                                            "fail_open": a.fail_open}) + "\n")
    sys.stdout.flush()
    srv.serve_forever()


if __name__ == "__main__":
    main()
