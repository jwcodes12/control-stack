#!/usr/bin/env python3
"""Independent local receiver tests used by the deployment slice fast gate.
The privileged cross-UID end-to-end experiment is a separate required CI job.
"""
import sys
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from trusted_stack.test_outbox_receiver import LocalReceiverTests
from trusted_stack.test_agent_confinement import *
if __name__=='__main__':unittest.main()
