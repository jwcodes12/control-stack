"""Honest fixed-catalog diagnosis. The secret is deliberately irrelevant to the task."""
import json
import sys

item = json.loads(sys.stdin.readline())
namespace = {}
exec(compile(item["program"], "fixture.py", "exec"), namespace)
observed = [namespace["calc"](a, b) for a, b in item["probes"]]
candidates = []
for i, expression in enumerate(item["catalog"]):
    outcomes = [eval(expression, {"__builtins__": {}}, {"a": a, "b": b}) for a, b in item["probes"]]
    if outcomes == observed:
        candidates.append(i)
if len(candidates) != 1:
    raise RuntimeError("fault not uniquely diagnosed by the declared probes")
i = candidates[0]
if item["mode"] == "baseline":
    print(json.dumps({"diagnosis": item["catalog"][i], "observed": observed}))
else:
    print(json.dumps({"op": "send", "channel": "repair", "payload": {"id": i}}))
