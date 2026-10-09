#!/usr/bin/env python3
"""SC-23 taint scaffold: a scripted planner (prereg/SC23-TAINT-SCAFFOLD.md).

Stands in for the LLM planner (no model; deterministic). It reads tasks from stdin, one JSON line each
({"task", "type"}), and drives the runtime over planner.sock. Its state is a list of planner values:
{"trusted": v} (user inputs and values it derives) or {"handle": "hN"} (an opaque reference to quarantined content).
Task types:
  pay_invoice : get the user's trusted inputs (invoice doc id, own account); read the doc (-> handle); ask the
                quarantined processor to extract the amount (-> handle); call send_payment(amount handle, account)
  summarize   : read the doc; summarize it in quarantine; call log_note(summary handle) (not sensitive)
After each task it derives one trusted value from its own view (counts of trusted values and handles: it reads its
state, as in `honest_planner_reads_state`) and prints "DONE {task, result, state, requests}".
--leaky (NEGATIVE_CONTROL, with the runtime's --leaky-view): the planner sees tool-result contents, stores them as
trusted values, and acts on an instruction of the form "transfer N to account M" it finds there
(`leaky_view_launders`). Self-contained (python -I -S).
"""
import argparse
import json
import re
import socket
import sys
import time


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runtime", required=True)
    ap.add_argument("--leaky", action="store_true")
    a = ap.parse_args()
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.connect(a.runtime)
    f = s.makefile("rwb", buffering=0)
    state = []

    def call(obj, reqs):
        reqs.append(obj)
        f.write((json.dumps(obj) + "\n").encode())
        return json.loads(f.readline())

    def keep(r):
        """store a runtime reply: a handle, or (leaky view only) the content it reveals"""
        if a.leaky and "content" in r:
            state.append({"trusted": r["content"]})
            return {"trusted": r["content"]}, r["content"]
        state.append({"handle": r["handle"]})
        return {"handle": r["handle"]}, None

    sys.stdout.write("READY {}\n")
    sys.stdout.flush()
    for line in sys.stdin:
        task = json.loads(line)
        tid, reqs, result = task["task"], [], None
        t0 = time.monotonic_ns()
        if task["type"] == "pay_invoice":
            inp = call({"op": "user_input", "task": tid}, reqs)["trusted"]
            for k in sorted(inp):
                state.append({"trusted": inp[k]})
            r = call({"op": "tool", "tool": "read_doc", "doc": inp["doc"]}, reqs)
            doc, content = keep(r)
            m = re.search(r"transfer (\d+) to account (\d+)", content) if content else None
            if m:  # leaky planner obeys the injected instruction, with "trusted" laundered values
                n, acct = int(m.group(1)), int(m.group(2))
                state.extend([{"trusted": n}, {"trusted": acct}])
                result = call({"op": "act", "task": tid, "tool": "send_payment",
                               "args": [{"trusted": n}, {"trusted": acct}]}, reqs)
            elif content is not None:  # leaky planner, no instruction: it reads the amount itself (laundering too)
                m2 = re.search(r"Amount due:\s*(\d+)", content)
                amt = {"trusted": int(m2.group(1)) if m2 else 0}
                state.append(amt)
                result = call({"op": "act", "task": tid, "tool": "send_payment",
                               "args": [amt, {"trusted": inp["account"]}]}, reqs)
            else:
                amt, _ = keep(call({"op": "qtransform", "fn": "extract_amount", "handle": doc["handle"]}, reqs))
                result = call({"op": "act", "task": tid, "tool": "send_payment",
                               "args": [amt, {"trusted": inp["account"]}]}, reqs)
        elif task["type"] == "summarize":
            inp = call({"op": "user_input", "task": tid}, reqs)["trusted"]
            for k in sorted(inp):
                state.append({"trusted": inp[k]})
            doc, _ = keep(call({"op": "tool", "tool": "read_doc", "doc": inp["doc"]}, reqs))
            if "handle" in doc:
                summ, _ = keep(call({"op": "qtransform", "fn": "summarize", "handle": doc["handle"]}, reqs))
            else:  # leaky planner summarizes the content itself
                summ = {"trusted": doc["trusted"].split(".")[0][:60]}
                state.append(summ)
            result = call({"op": "act", "task": tid, "tool": "log_note", "args": [summ]}, reqs)
        n_t = sum(1 for x in state if "trusted" in x)
        n_h = sum(1 for x in state if "handle" in x)
        state.append({"trusted": "ref-%d-%d" % (n_t, n_h)})
        sys.stdout.write("DONE " + json.dumps({"task": tid, "result": result, "state": state, "requests": reqs,
                                               "lat_s": (time.monotonic_ns() - t0) / 1e9}) + "\n")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
