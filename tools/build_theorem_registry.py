#!/usr/bin/env python3
"""Regenerate a conservative theorem inventory from the root axiom report and frozen manifests.
This reads source metadata and NEVER runs Lean or treats a manifest as deployment assurance.
"""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CIDS = "UMHSF1 UMSURVF1 UMPROTF1 UMSTRATF1 UMNOGOF1 UMLOWERF1 UMADAPTF1 UMUSEF1 UMDEFERF1 UMCERTF1 TMCERTF1 TMGACF1 UMADAPTF2 TMCERTUSF1 TMLIPF1 CANONF1 SANDBOXF1 SANDBOX2F1".split()

def family(name):
    if re.search("SANDBOX|Egress",name): return "F1"
    if re.search("CANON|Covert|GatewayModel|SideChannel|ScenarioARepair|ScenarioASide",name): return "F2"
    if re.search("Audit|LifetimeLedger|GatewayCore|SafetyCaseSC01",name): return "F3"
    if "Compose" in name: return "F8"
    if re.search("UM|TM|Spike|Bridge|Refine|Outcome|Soft|Stratified|Defer|UseQ|Adaptive",name): return "F6"
    return "UNMAPPED"

def inventory():
    rows = {}
    def add(name, source, status, ids=()):
        row = rows.setdefault(name, {"name":name,"source":source,"verdicts":[],"families":[],"scenarios":[],
                                      "adversary_class":"unspecified",
                                      "premises":"Read source declaration and DESIGN.md; not mechanically extracted",
                                      "witness":"No necessity witness indexed"})
        if status not in row["verdicts"]: row["verdicts"].append(status)
        f = family(name)
        if f not in row["families"]: row["families"].append(f)
        for sid in ids:
            if sid not in row["scenarios"]: row["scenarios"].append(sid)
    for cid in CIDS:
        for kind in ("Claim","Witness"):
            add(f"PL_{cid}.{kind}",f"proofs/{cid}.lean","REPORTED_LEDGER_VERIFIED")
    src = (ROOT / "ControlStack.lean").read_text()
    for name in re.findall(r"^#print axioms\s+(ControlStack\.[A-Za-z0-9_.']+)",src,re.M):
        add(name,"ControlStack.lean","AXIOM_QUERY_IN_SOURCE")
    m = json.loads((ROOT/"assurance/sc01-safety-case.json").read_text())
    for entry in m["lean"]:
        for name in entry["theorems"]:
            add(entry["namespace"]+"."+name,entry["file"],"LEGACY_MANIFEST_REPORTED_PASSED",("SC-01",))
    m = json.loads((ROOT/"assurance/egress-boundary-v1.json").read_text())
    for name in m["theorem"]["ids"]:
        add("ControlStack."+name,"ControlStack/EgressGate.lean","LEGACY_MANIFEST_REPORTED_PASSED",("SC-03",))
    m = json.loads((ROOT/"assurance/monitoring-integrity-auditgate-v1.json").read_text())
    for name in m["theorem"]["ids"]:
        add("ControlStack."+name,"ControlStack/AuditDispatch.lean" if "AuditDispatch" in name else "ControlStack/AuditGate.lean","LEGACY_MANIFEST_REPORTED_PASSED",("SC-13",))
    cases = {sid:json.loads((ROOT/"scenarios"/sid/"scenario.json").read_text()) for sid in ("SC-01","SC-03","SC-13")}
    for row in rows.values():
        name=row["name"]
        for sid,needles in (("SC-01",("Covert","GatewayModel","LifetimeLedger","SafetyCaseSC01","GatewayCore")),
                            ("SC-03",("EgressGate",)),("SC-13",("AuditDispatch","AuditGate"))):
            if any(n in name for n in needles) and sid not in row["scenarios"]:row["scenarios"].append(sid)
        if name.startswith("PL_"):
            row["witness"]="Ledger witness is the separate "+name.replace(".Claim",".Witness")+"; inspect frozen source"
        for sid in ("SC-01","SC-03","SC-13"):
            if sid in row["scenarios"]:
                case=cases[sid]
                row["adversary_class"]=case["formal"]["adversary_class"]
                row["premises"]=case["formal"]["premises"]
                row["witness"]=case["falsification"][0]
                break
        row["scenarios"].sort()
    return [rows[k] for k in sorted(rows)]

def esc(s):
    return str(s).replace("|",r"\|").replace("\n"," ")

def markdown(items):
    output = "# Theorem inventory (generated metadata, not a proof check)\n\n"
    output += "**Status:** This table indexes frozen ledger claim/witness names, root-module axiom query targets and the three current scenario-specific historical manifests. **It is not an exhaustive parse of private/helper lemmas** and is not proof of runtime applicability. Legacy checked statuses are assertions in older files, not checks run by this generator. For a full declaration inventory use source/Lean tooling; statement-fidelity review is still required.\n\n"
    output += "| Named declaration / claim | Family | Scenario(s) | Adversary class | Premises (pointer/summary) | Reported status | Necessity witness / refuter |\n"
    output += "|---|---|---|---|---|---|---|\n"
    for r in items:
        output += f'| {chr(96)}{esc(r["name"])}{chr(96)} ({chr(96)}{r["source"]}{chr(96)}) | {", ".join(r["families"])} | {", ".join(r["scenarios"]) or "not mapped"} | {esc(r["adversary_class"])} | {esc(r["premises"])} | {", ".join(r["verdicts"])} | {esc(r["witness"])} |\n'
    return output

if __name__=="__main__":
    import argparse
    p=argparse.ArgumentParser();p.add_argument("--check",action="store_true");args=p.parse_args()
    data=inventory();md=markdown(data)
    file=ROOT/"scenarios/THEOREM-REGISTRY.md"
    if args.check:
        if file.read_text()!=md:
            raise SystemExit("Theorem registry drift: run python3 tools/build_theorem_registry.py")
        print(f"registry current ({len(data)} rows)")
    else:
        file.write_text(md)
        (ROOT/"scenarios/theorem-registry.json").write_text(json.dumps(data,indent=2)+"\n")
        print(f"wrote {len(data)} theorem entries")
