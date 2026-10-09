#!/usr/bin/env python3
"""SC-09: a requester process (prereg/SC09-ELEVATION-BROKER.md). A persistent process with a stable pid (which the
broker maps to a requester name). It reads one JSON request per stdin line, forwards it to the broker, and prints
"REPLY {...}". It never opens the protected file; it can only ask the broker. Self-contained."""
import json
import os
import socket
import sys

sock = sys.argv[1]
sys.stdout.write("READY " + json.dumps({"pid": os.getpid()}) + "\n")
sys.stdout.flush()
for line in sys.stdin:
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(10)
    try:
        s.connect(sock)
        f = s.makefile("rwb")
        f.write((line.strip() + "\n").encode())
        f.flush()
        reply = f.readline().decode().strip()
    finally:
        s.close()
    sys.stdout.write("REPLY " + reply + "\n")
    sys.stdout.flush()
