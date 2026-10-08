#!/usr/bin/env python3
"""Generate an explicit, non-certifying inventory of local Lean declarations.

Reads source and scenario manifests only. No Lean or other process is invoked.
Unknown model/adversary/premises are marked UNCLASSIFIED, never inferred from a name.
This is a declaration inventory, NOT a kernel proof checker or assurance decision.
"""
import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DECL = re.compile(r"^\s*(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma)\s+([A-Za-z_][\w']*)\b", re.M)
LEDGER = re.compile(r"^\s*def\s+(Claim|Witness)\b", re.M)
MODELS = {
    "ControlStack/SafetyCaseSC01.lean": ("shared seed, side-observing lifetime", "fixed finite views; bounded side kernel; independent useful lifetimes", "SC-01"),
    "ControlStack/CovertChannel.lean": ("shared-seed encoder/decoder", "uniform secret; complete bounded observation", "SC-01"),
    "ControlStack/GatewayCore.lean": ("adaptive agent actions", "typed slots, closing/blanking and fixed budget", "SC-01"),
    "ControlStack/EgressGate.lean": ("agent tool/socket traces", "safe topology; trusted policy; no bypass/deputy", "SC-03"),
    "ControlStack/AuditDispatch.lean": ("app operations and trusted dispatch", "effect only via dispatcher and atomic audit-before-effect", "SC-13"),
}


def inventory(root):
    linked = {}
    for mf in sorted((root / "scenarios").glob("SC-*/manifest.json")):
        m = json.loads(mf.read_text())
        for t in m.get("theorems", []):
            linked.setdefault((t["path"], t["name"].split(".")[-1]), []).append(
                (m["id"], ",".join(m["families"]), t["recorded_status"]))
    out = []
    # Limit traversal to tracked source families; do not descend into .lake/Mathlib caches.
    candidates = [root / "ControlStack.lean"]
    for folder in ("ControlStack", "ledger", "proofs", "core", "numerics"):
        if (root / folder).exists():
            candidates.extend((root / folder).rglob("*.lean"))
    for file in sorted(f for f in candidates if f.is_file()):
        rel = file.relative_to(root).as_posix()
        if any(part.startswith(".") for part in file.relative_to(root).parts):
            continue
        if rel.startswith(("ledger-check/", "ci/")):
            continue
        src = file.read_text(encoding="utf-8")
        decls = [(m.group(1), m.group(2)) for m in DECL.finditer(src)]
        if rel.startswith("ledger/"):
            decls.extend(("ledger-definition", m.group(1)) for m in LEDGER.finditer(src))
        for kind, name in decls:
            links = linked.get((rel, name), [])
            model = MODELS.get(rel)
            out.append({
                "source": f"{rel}:{name}",
                "kind": kind,
                "families": ",".join(sorted({f for _, fam, _ in links for f in fam.split(",")})) if links else "UNCLASSIFIED",
                "scenarios": ",".join(sorted({sid for sid, _, _ in links})) if links else (model[2] if model else "UNCLASSIFIED"),
                "adversary": model[0] if model else "UNCLASSIFIED",
                "premises": model[1] if model else "UNCLASSIFIED",
                "status": "RECORDED_NOT_RECHECKED" if links else "NOT_INDEPENDENTLY_CLASSIFIED",
                "necessity_witness": "PRESENT_AS_LEDGER_DEFINITION" if rel.startswith("ledger/") and name == "Witness" else "UNCLASSIFIED"
            })
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--require-complete", action="store_true")
    args = ap.parse_args()
    rows = inventory(ROOT)
    if args.json:
        print(json.dumps(rows, indent=2))
    else:
        print("# Lean declaration inventory (generated; NOT a proof check)\n")
        print("Unknown classifications are deliberately explicit. Review statements and"
              " necessity witnesses before composing claims.\n")
        print("| Declaration | Kind | Family | Scenarios | Adversary | Premises | Recorded status | Necessity witness |")
        print("|---|---|---|---|---|---|---|---|")
        for r in rows:
            values = [r[k] for k in ("source", "kind", "families", "scenarios",
                                    "adversary", "premises", "status", "necessity_witness")]
            print("| " + " | ".join(str(v).replace("|", "/").replace("\n", " ") for v in values) + " |")
    if not rows:
        return 1
    if args.require_complete and any("UNCLASSIFIED" in str(v) for r in rows for v in r.values()):
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
