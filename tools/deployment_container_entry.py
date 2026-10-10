#!/usr/bin/env python3
"""Offline experiment image entry point. Protocol implementation stays in trusted_stack."""
import os
import subprocess
import sys
import time
from pathlib import Path
role = os.environ['SLICE_ROLE']
if role == 'broker':
    os.execv(sys.executable, [sys.executable, '-m', 'trusted_stack.server', '--db', '/private/gate.db', '--socket', '/channel/broker.sock', '--agents', '23701,23702', '--reviewers', '23703', '--approvers', '23704', '--admins', '23700', '--bootstrap-cap', '1'])
# Receiver stays ready; the harness invokes its real deliver_record function
# after two independent agent contenders have released against the shared cap.
while True:
    time.sleep(1)
