#!/usr/bin/env python3
"""Generate scenario status from the four independent axes, without promotion."""
import argparse
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
HEADER="# Control Stack scenario status (derived from scenario manifests)\n\nThis is the single scenario-level status entry point, **not** a replacement for the detailed theory and research history in ROADMAP.md and STACK.md. No scenario is deployment assured.\n\n| ID | Scenario | Proof | Evidence | Applicability | Usefulness |\n|---|---|---|---|---|---|\n"
TAIL="\n**Drafts:** {count} other scenarios have only proposed narrow claims, falsifiers, and correspondence obligations. There is no new checked proof or runtime evidence for them.\n\n**Priority blocking facts:** SC-01 failed its unchanged 0.25-second QEMU TCG VM usefulness gate (0/64 baseline and 0/64 mediated lifetimes); a measured single-host side channel refuted the sole-gateway-view assumption in that harness. SC-03 does not establish confidentiality or universal process attribution. SC-13 protects dispatch audit ordering, not all effects or external completion. SC-27 lacks an independent attestation root.\n"
def generate():
    cases=[json.loads(p.read_text()) for p in sorted((ROOT/"scenarios").glob("SC-*/scenario.json"))]
    active=[c for c in cases if c["lifecycle"]=="active"]
    rows=""
    for c in active:
        row=[c["id"],c["title"]]+[c["axes"][a]["status"] for a in ("proof","evidence","applicability","usefulness")]
        rows+="| "+" | ".join(row)+" |\n"
    return HEADER+rows+TAIL.format(count=len(cases)-len(active))
if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--check",action="store_true");args=p.parse_args()
    path=ROOT/"scenarios/STATUS.md";value=generate()
    if args.check:
        if path.read_text()!=value:raise SystemExit("status drift: run python3 tools/build_status.py")
        print("status current")
    else:
        path.write_text(value);print("status generated")
