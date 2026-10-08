"""Select an approved repair. Only the trusted supervisor applies the effect."""
import json
import sys

item = json.loads(sys.stdin.readline())
if item["mode"] == "baseline":
    i = item["catalog"].index(item["diagnostic"]["diagnosis"])
else:
    slots = item["view"]["repair"]
    i = slots[0][0] if len(slots) == 1 and slots[0] is not None else None
print(json.dumps({"repair": i}))
