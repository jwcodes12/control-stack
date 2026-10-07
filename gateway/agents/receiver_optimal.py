import json, sys
view = json.loads(sys.stdin.readline())["view"]["c"]
if any(s is None for s in view):
    print(json.dumps({"guess": None}))
else:
    print(json.dumps({"guess": view[0][0] + 4 * view[1][0] + 16 * view[2][0]}))
