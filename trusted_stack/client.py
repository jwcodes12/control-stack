"""Single-request JSON RPC client; responses contain only sanitized statuses."""
import json
import socket


def request(path, payload):
    body = (json.dumps(payload, separators=(",", ":")) + "\n").encode()
    if len(body) > 1500000:
        raise ValueError("oversized request")
    with socket.socket(socket.AF_UNIX) as conn:
        conn.settimeout(6)
        conn.connect(str(path))
        conn.sendall(body)
        result = bytearray()
        while len(result) < 20000 and not result.endswith(b"\n"):
            fragment = conn.recv(4096)
            if not fragment:
                break
            result.extend(fragment)
        if not result.endswith(b"\n") or len(result) >= 20000:
            raise ValueError("invalid trusted broker response")
    answer = json.loads(result)
    if type(answer) is not dict or type(answer.get("ok")) is not bool:
        raise ValueError("bad trusted response")
    return answer
