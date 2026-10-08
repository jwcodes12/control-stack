"""Validate this namespace, then start the untrusted adapter and task."""
import json
from pathlib import Path
import socket
import subprocess
import sys
import time
from validator import validate

config = json.loads(Path('/suite-config.json').read_text())
found = validate(config)
if sys.argv[1]=='--inspect':
    print(json.dumps(found)); sys.exit()
Path('/tmp/config.json').write_text(json.dumps(config))
relay = subprocess.Popen([sys.executable,'/suite/relay.py'])
try:
    for _ in range(100):
        try:
            with socket.create_connection(('127.0.0.1',3128),timeout=.1): break
        except OSError: time.sleep(.02)
    else: raise RuntimeError('sandbox relay unavailable')
    if sys.argv[1] in ('honest-http','honest-connect','honest-dependency-task'):
        config['adapter'] = True; Path('/tmp/config.json').write_text(json.dumps(config))
    subprocess.run([sys.executable,'/suite/attacks.py',sys.argv[1],'/tmp/config.json'],check=True)
finally:
    relay.terminate(); relay.wait(timeout=5)
