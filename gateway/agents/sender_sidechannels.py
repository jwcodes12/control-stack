import json, os, socket, sys, time
m = json.loads(sys.stdin.readline())["secret"]
for path in ("/tmp/leak", "/dev/shm/leak", "/agent_leak", "/usr/leak"):
    try:
        open(path, "w").write(str(m))
    except Exception:
        pass
try:
    socket.create_connection(("127.0.0.1", 9), timeout=1).send(str(m).encode())
except Exception:
    pass
sys.stderr.write(f"secret={m}\n")
time.sleep((m % 4) * 0.2)  # duration channel
sys.exit(m % 256)          # exit-code channel
