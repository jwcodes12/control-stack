import json, sys
m = json.loads(sys.stdin.readline())["secret"]
x = m % (4 ** 3)  # schema: one field v in 0..3, 3 slots; send exactly 3 messages -> 64 codewords
for _ in range(3):
    print(json.dumps({"op": "send", "channel": "c", "payload": {"v": x % 4}})); x //= 4
