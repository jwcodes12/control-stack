"""Negative control: start the connecting guest BEFORE the listener (the old race, forced). Expect no ESTABLISHED link."""
import json, sys, time
sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parents[1]))
from pair import VM, tcp_states, link_endpoint
cfg = json.load(open(sys.argv[1]))
a, b = cfg["vms"]
vb = VM(b); time.sleep(2.0); va = VM(a); time.sleep(5.0)
port = link_endpoint(a)[1]
st = tcp_states(port)
print(json.dumps({"order": "B then A", "host_sockets": st, "established": sum(s == "01" for _, _, s in st)}))
for v in (va, vb): v.stop()
