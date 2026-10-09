#!/usr/bin/env python3
"""SC-10/11: a one-shot client process (prereg/SC10-POLICY-STORE.md). Sends one JSON request to a Unix socket and
prints the reply. Used for the AGENT's policy-write attempts, so they come from a process other than the admin (the
store identifies writers by the kernel-reported pid). Self-contained."""
import json
import socket
import sys

s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
s.settimeout(10)
s.connect(sys.argv[1])
f = s.makefile("rwb")
f.write((sys.argv[2] + "\n").encode())
f.flush()
sys.stdout.write(f.readline().decode())
