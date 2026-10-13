"""Save structural, pointwise comparisons from the already frozen back files.

Original types are copied from their declaration signatures, never obtained by
proving two closed true propositions. Shape conjuncts tie each conclusion to its
complete declaration. The only proof of equivalence is definitional reduction.
"""
from pathlib import Path
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[3]
names = [
    "runtime_exclusive", "agent_call_legal", "protocol_safe", "one_use",
    "gate_contract", "broker_contract", "deployment_safe",
    "accepted_path_safety_monotone", "path_edge_subset",
    "requested_monotonicity_counterexample",
]
configs = [
    ("(d : IR) (e : Edge)", "d e", "e.source = d.receiver",
     "∀ (d : IR) (actual : List Edge) (e : Edge), Accepted d → Faithful d actual → e ∈ actual → e.authority = true → e.target = d.sink →"),
    ("(d : IR) (r a : Node) (approvers admins : List Nat) (key : Nat) (tx : SC26.Tx)", "d r a approvers admins key tx",
     "SC26.legal (roles d r.uid approvers admins)\n      (SC26.Op.bankCall a.uid key tx)",
     "∀ (d : IR) (r a : Node) (approvers admins : List Nat) (key : Nat) (tx : SC26.Tx), Accepted d → r ∈ d.nodes → r.id = d.receiver → a ∈ d.nodes → a.agent = true →"),
    ("(R : SC26.Roles) (cap : Nat) (ops : List SC26.Op)", "R cap ops",
     "SC26.Good R cap (SC26.run R cap SC26.full SC26.init ops)",
     "∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op), (∀ o ∈ ops, SC26.legal R o) →"),
    ("(R : SC26.Roles) (cap : Nat) (ops : List SC26.Op)", "R cap ops",
     "(SC26.run R cap SC26.full SC26.init ops).reserved.Nodup",
     "∀ (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op),"),
    ("(R : SC26.Roles) (cap : Nat) (ops : List {o : SC26.Op // SC26.legal R o})", "R cap ops", "let G := SC26.sys R cap",
     "∀ (R : SC26.Roles) (cap : Nat) (ops : List {o : SC26.Op // SC26.legal R o}),"),
    ("(R : TrustedBroker.Roles) (cap : Nat) (t : TrustedBroker.State)", "R cap t", "TrustedBroker.Safe t",
     "∀ (R : TrustedBroker.Roles) (cap : Nat) (t : TrustedBroker.State), TrustedBroker.Trace R (TrustedBroker.initial cap) t →"),
    ("(d : IR) (r : Node) (actualEdges : List Edge) (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) (sinkEffects : List (Nat × SC26.Tx))",
     "d r actualEdges R cap ops sinkEffects", "let s := SC26.run R cap SC26.full SC26.init ops",
     "∀ (d : IR) (r : Node) (actualEdges : List Edge) (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) (sinkEffects : List (Nat × SC26.Tx)), Accepted d → ExtractionFaithful d r actualEdges → ProtocolRefinement d r R cap ops sinkEffects →"),
    ("(d : IR) (a : Node)", "d a", "¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database",
     "∀ (d larger : IR) (a : Node), (∀ e ∈ d.edges, e ∈ larger.edges) → d.nodes = larger.nodes → d.broker = larger.broker → d.receiver = larger.receiver → d.sink = larger.sink → d.database = larger.database → Accepted larger → a ∈ d.nodes → a.agent = true →"),
    ("(larger : IR) (start target : Nat)", "larger start target", "AvoidedPath larger start target",
     "∀ (d larger : IR) (start target : Nat), (∀ e ∈ d.edges, e ∈ larger.edges) → d.broker = larger.broker → d.receiver = larger.receiver → AvoidedPath d start target →"),
]

W = "ControlStack.Deployment.Witnesses"
witnesses = [
    (f"Accepted clean ∧ Faithful clean clean.edges ∧ ({W}.receiverNode ∈ clean.nodes) ∧ ∃ e ∈ clean.edges, e.authority = true ∧ e.target = clean.sink",
     f"exact ⟨clean_accepted, {W}.extracted.authority, {W}.extracted.receiverNode, ⟨⟨3,4,true,false,true⟩, by decide, rfl, rfl⟩⟩"),
    (f"Accepted clean ∧ {W}.receiverNode ∈ clean.nodes ∧ {W}.receiverNode.id = clean.receiver ∧ {W}.agentA ∈ clean.nodes ∧ {W}.agentA.agent = true ∧ SC26.legal (roles clean {W}.receiverNode.uid [23703] [23704]) (.bankCall {W}.agentA.uid 0 payload)",
     f"exact ⟨clean_accepted, by decide, rfl, by decide, rfl, {W}.legal_call_positive⟩"),
    (f"(∀ o ∈ {W}.modelOps, SC26.legal twoRoles o) ∧ (SC26.run twoRoles 1 SC26.full SC26.init {W}.modelOps).bank = [(0,payload)]",
     f"exact ⟨{W}.model_ops_legal, by decide⟩"),
    (f"(SC26.run twoRoles 1 SC26.full SC26.init {W}.modelOps).reserved = [0] ∧ (SC26.run twoRoles 1 SC26.full SC26.init {W}.modelOps).spent = 1", "unfold Witness\n  decide"),
    ("∃ ops : List {o : SC26.Op // SC26.legal twoRoles o}, ops.length = 5 ∧ (SC26.sys twoRoles 1).effects ((SC26.sys twoRoles 1).run SC26.init ops) = [(0,payload)]",
     "refine ⟨[⟨.request 23701 payload, by trivial⟩, ⟨.approve 23703 0 payload, by trivial⟩, ⟨.execute 23701 0, by trivial⟩, ⟨.deliver 0, by trivial⟩, ⟨.arrive 0, by trivial⟩], rfl, ?_⟩\n  decide"),
    (f"TrustedBroker.Trace {W}.R (TrustedBroker.initial 1) {W}.s5 ∧ {W}.s5.spent = 1 ∧ {W}.s5.releases = 1 ∧ {W}.s5.consumed = [7]",
     f"exact ⟨{W}.useful_broker_trace, {W}.useful_broker_state⟩"),
    (f"Accepted clean ∧ ExtractionFaithful clean {W}.receiverNode clean.edges ∧ ProtocolRefinement clean {W}.receiverNode twoRoles 1 {W}.modelOps [(0,payload)] ∧ ([(0,payload)] : List (Nat × SC26.Tx)).length = 1",
     f"exact ⟨clean_accepted, {W}.extracted, {W}.sc26_refined, rfl⟩"),
    (f"(∀ e ∈ sinkOnly.edges, e ∈ clean.edges) ∧ sinkOnly.nodes = clean.nodes ∧ sinkOnly.broker = clean.broker ∧ sinkOnly.receiver = clean.receiver ∧ sinkOnly.sink = clean.sink ∧ sinkOnly.database = clean.database ∧ Accepted clean ∧ {W}.agentA ∈ sinkOnly.nodes ∧ {W}.agentA.agent = true ∧ ¬ Accepted sinkOnly ∧ sinkOnly.edges ≠ clean.edges", "unfold Witness\n  decide"),
    ("(∀ e ∈ sinkOnly.edges, e ∈ clean.edges) ∧ sinkOnly.broker = clean.broker ∧ sinkOnly.receiver = clean.receiver ∧ AvoidedPath sinkOnly 3 4 ∧ 3 ≠ (4 : Nat) ∧ sinkOnly.edges ≠ clean.edges",
     "refine ⟨by decide, rfl, rfl, ?_, by decide, by decide⟩\n  exact .step ⟨3,4,true,false,true⟩ (by decide) (by decide) (by decide) .refl"),
    ("sinkOnly.edges ≠ clean.edges ∧ sinkOnly.nodes.length = 6 ∧ Accepted clean ∧ ¬ Accepted sinkOnly", "unfold Witness\n  decide"),
]


def signature(source, name):
    start = source.index("theorem " + name)
    end = source.index(":=", start)
    sig = source[start + len("theorem " + name):end].strip()
    depth = 0
    for i, ch in enumerate(sig):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0:
            binders, conclusion = sig[:i].strip(), sig[i+1:].strip()
            prop = ("∀ " + binders + ",\n    " if binders else "") + conclusion
            return prop, conclusion, source[start:end+2], source[:start].count("\n") + 1
    raise ValueError(name)


records = []
for n, name in enumerate(names, 1):
    backpath = next((OUT / "typed").glob(f"{n}-*.lean"))
    backsrc = backpath.read_text()
    back = backsrc.split(f"def Back_{name} : Prop :=", 1)[1].split("\nend ControlStack.Deployment", 1)[0].strip()
    origpath = ROOT / "ControlStack/Deployment" / ("Contracts.lean" if n <= 7 else "R2Contracts.lean")
    orig, origconclusion, origsignature, line = signature(origpath.read_text(), name)
    if n <= 9:
        params, args, marker, prefix = configs[n-1]
        idx = back.rindex(marker)
        backconclusion = back[idx:]
        backshape = back[:idx] + "BackConclusion " + args
        # The original calls the key k; all other names are shared.
        origargs = args.replace(" key ", " k ") if n == 2 else args
        origshape = orig[:-len(origconclusion)] + "OrigConclusion " + origargs
        origconclusion = re.sub(r"\bk\b", "key", origconclusion) if n == 2 else origconclusion
        pointwise = prefix + f"\n    (BackConclusion {args} ↔ OrigConclusion {args})"
    else:
        params, args = "(small large : IR)", "sinkOnly clean"
        backconclusion = re.sub(r"\bsinkOnly\b", "small", re.sub(r"\bclean\b", "large", back))
        origconclusion = re.sub(r"\bsinkOnly\b", "small", re.sub(r"\bclean\b", "large", origconclusion))
        backshape, origshape = "BackConclusion " + args, "OrigConclusion " + args
        pointwise = "∀ (small large : IR), BackConclusion small large ↔ OrigConclusion small large"
    # Moving a let block out of a quantified body must preserve its relative
    # indentation: its body starts at the same column as the let keyword.
    embedded_backconclusion = backconclusion
    if n in (5, 7):
        embedded_backconclusion = backconclusion.replace("\n    ", "\n  ")
    statement = f"""namespace PL_bg0n1_{n}
open ControlStack ControlStack.Deployment

def Back : Prop :=
  {back}

def Orig : Prop :=
  {orig}

def BackConclusion {params} : Prop :=
  {embedded_backconclusion}

def OrigConclusion {params} : Prop :=
  {origconclusion}

def Claim : Prop :=
  (Back ↔ ({backshape})) ∧
  (Orig ↔ ({origshape})) ∧
  ({pointwise})

def Witness : Prop :=
  {witnesses[n-1][0]}

end PL_bg0n1_{n}
"""
    proof = f"""open ControlStack ControlStack.Deployment

theorem original_signature : Orig := @{name}

theorem claim : Claim := by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  {witnesses[n-1][1]}
"""
    (OUT / f"bg0n1_{n}.statement.lean").write_text(statement)
    (OUT / f"bg0n1_{n}.proof.lean").write_text(proof)
    (OUT / f"bg0n1_{n}.original-signature.txt").write_text(f"{origpath.relative_to(ROOT)}:{line}\n" + origsignature + "\n")
    records.append({"claim": n, "original": name, "source": str(origpath.relative_to(ROOT)), "line": line,
                    "source_sha256": hashlib.sha256(origpath.read_bytes()).hexdigest(),
                    "typed_sha256": hashlib.sha256(backpath.read_bytes()).hexdigest()})
(OUT / "COMPARISONS.json").write_text(json.dumps(records, indent=2) + "\n")
