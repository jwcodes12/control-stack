#!/usr/bin/env python3
"""Portfolio-wide typed assumption ledger: generates ASSURANCE-LEDGER.md.

Reads every scenarios/SC-*/manifest.json assumption and NORMALISES premise identities across scenarios with the curated
table PREMISES below (credential separation appears in most manifests under the same id; exclusive effect paths appear
under a dozen different ids). Each normalised premise has a kind (the `PremiseKind` of ControlStack/Core/Cert.lean),
its member scenarios, the best evidence across them, and the practical test that would discharge it, taken from
stack/components.json.

Ranking: leverage = (number of scenarios depending on the premise) × (2 if no member has runtime evidence, else 1).

Fail-closed: every manifest assumption must be covered by exactly one normalised premise; every referenced stack
premise must exist in stack/components.json. Unmapped or doubly-mapped assumptions are errors.

The Lean side: with lake available, the stack certificate's typed ledger (`ControlStack.Cert.stackLedger`, via
tools/cert_ledger.py) is mapped onto the normalised premises in a final section. `--no-lean` omits that section,
and `--check` then compares only the part before it.

Usage: portfolio_ledger.py [--check] [--json] [--no-lean]. Exit 0 = ok / no drift; 1 = error or drift.
"""
import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "ASSURANCE-LEDGER.md"
LEAN_MARKER = "<!-- lean-section -->"
KINDS = ("proof_obligation", "correspondence", "measurement", "environment", "organisational")

# normalised premise -> kind, title, members ("*:id" = every manifest assumption with that id; "SC-XX:id"),
# stack refs ("component.premise" in stack/components.json)
PREMISES = {
    "credential_separation": dict(
        kind="environment", title="No agent-reachable process can act with a trusted role's identity",
        members=["*:credential_separation"],
        stack=["secrets_kms.credential_separation", "cloud_control_plane.credential_separation",
               "human_approval.approval_channel_integrity"]),
    "honest_usefulness": dict(
        kind="measurement", title="The restricted path still completes representative honest tasks",
        members=["*:honest_usefulness", "SC-01:vm_usefulness", "SC-03:usefulness_population"],
        stack=[]),
    "exclusive_effect_path": dict(
        kind="environment", title="The gate is the only path to the effect (complete mediation; no bypass, deputy or "
        "out-of-band writer)",
        members=["SC-03:exclusive_mediation", "SC-05:action_gate_complete", "SC-07:single_route",
                 "SC-08:complete_exec_mediation", "SC-10:single_evaluator", "SC-12:registry_complete",
                 "SC-13:exclusive_dispatcher", "SC-16:exclusive_deploy_path", "SC-17:single_apply_path",
                 "SC-18:single_release_path", "SC-25:exclusive_executor"],
        stack=["agent_sandbox.complete_mediation", "network_egress.all_routes_through_proxy",
               "logging_pipeline.effects_only_via_dispatcher", "cloud_control_plane.no_unmediated_deputy"]),
    "observation_complete": dict(
        kind="measurement", title="Every receiver- or monitor-visible observation (timing, side channels, residue) is "
        "inside the certified view, with a measured certificate",
        members=["SC-01:complete_receiver_observations", "SC-01:side_kernel", "SC-02:episode_certificates",
                 "SC-04:timing_in_view", "SC-05:zero_dependence_measured", "SC-07:adversarial_channels",
                 "SC-24:complete_mediated_view"],
        stack=["agent_sandbox.co_tenant_side_channels", "gpu_multitenancy.partition_observation_boundary",
               "gpu_physical_side_channels.physical_channel_measured",
               "network_egress.allowed_destination_not_a_channel"]),
    "semantic_judgement": dict(
        kind="measurement", title="Reviewers, classifiers and replication detect what they are trusted to detect "
        "(per-history recall, not population averages)",
        members=["SC-15:review_adequacy", "SC-17:ceiling_correct", "SC-20:source_allowlist_trustworthy",
                 "SC-22:replication_detects", "SC-25:trusted_classifier"],
        stack=["human_approval.approver_competence", "code_review_cicd.review_semantics",
               "trusted_monitor_audit.per_history_recall"]),
    "policy_integrity": dict(
        kind="environment", title="Policy, toolchain and trust roots cannot be edited by the agent; one evaluator",
        members=["SC-03:policy_integrity", "SC-10:store_trusted", "SC-11:pinned_location_protected"],
        stack=["agent_sandbox.policy_integrity", "agent_sandbox.mount_policy", "network_egress.policy_integrity"]),
    "model_runtime_correspondence": dict(
        kind="correspondence", title="The runtime implements the Lean model's transitions (records match effects)",
        members=["SC-26:model_runtime_correspondence", "SC-01:ledger_correspondence", "SC-13:effect_vs_record"],
        stack=["logging_pipeline.audit_before_effect"]),
    "role_separation": dict(
        kind="organisational", title="Agent and approver/reviewer/admin identity sets are disjoint",
        members=["SC-16:role_disjointness", "SC-26:role_disjointness", "SC-09:admin_separation"],
        stack=["code_review_cicd.distinct_reviewer"]),
    "trusted_meter": dict(
        kind="environment", title="Resource use is measured by a trusted meter covering every descendant, robust to "
        "evasion",
        members=["SC-14:trusted_meter", "SC-28:trusted_meter", "SC-28:adversarial_workloads"],
        stack=["job_scheduler.kernel_enforced_hierarchical_cap", "gpu_telemetry_meter.meter_upper_bounds_usage",
               "cloud_control_plane.trusted_spend_meter"]),
    "anti_rollback": dict(
        kind="environment", title="Ledgers, counters and nonce history cannot be rolled back",
        members=["SC-14:anti_rollback", "SC-28:anti_rollback"],
        stack=["secrets_kms.anti_rollback", "job_scheduler.anti_rollback"]),
    "hidden_sample": dict(
        kind="correspondence", title="Audit/replication samples and phases stay hidden from the agent until after it "
        "commits",
        members=["SC-21:sample_hidden", "SC-22:sample_hidden", "SC-24:phase_rerandomised"],
        stack=["trusted_monitor_audit.schedule_not_observable"]),
    "canonicaliser_complete": dict(
        kind="correspondence", title="Every cross-agent or receiver-visible artifact passes the trusted canonicaliser",
        members=["SC-04:canonicaliser_complete", "SC-06:canonicaliser_complete"],
        stack=["logging_pipeline.log_records_canonicalised"]),
    "collision_resistance": dict(
        kind="environment", title="Content hashes are injective on the contents of a run",
        members=["SC-16:hash_injective", "SC-27:hash_injective_on_run"],
        stack=[]),
    "independent_anchor": dict(
        kind="organisational", title="An independently administered witness anchors logs and evidence, often enough",
        members=["SC-27:independent_anchor", "SC-27:anchor_frequency"],
        stack=["researcher_workstation.independent_attestation", "logging_pipeline.log_anchor_external"]),
    "receiver_idempotency": dict(
        kind="correspondence", title="Effect sinks are idempotent per key, authenticate the gate, never reuse keys",
        members=["SC-26:receiver_idempotency"],
        stack=["cloud_control_plane.idempotent_external_api"]),
    "consume_by_digest": dict(
        kind="correspondence", title="The bytes checked are the bytes loaded or deployed",
        members=["SC-08:fd_pinned_hash"],
        stack=["code_review_cicd.consume_by_digest"]),
    "honeypot_indistinguishable": dict(
        kind="measurement", title="Honeypot and real view laws are close (TV bounded and estimated)",
        members=["SC-24:tv_estimated"],
        stack=["trusted_monitor_audit.honeypots_indistinguishable"]),
    "exact_payload_display": dict(
        kind="correspondence", title="Confirmation shows the exact payload, and only users can confirm",
        members=["SC-23:confirmation_ui_exact"],
        stack=["human_approval.approver_sees_exact_payload"]),
    "taint_propagation": dict(
        kind="correspondence", title="Provenance labels are truthful; untrusted data reaches the planner only labelled",
        members=["SC-23:provenance_truthful"],
        stack=["agent_sandbox.taint_propagation"]),
    "revocation_effective": dict(
        kind="environment", title="Revocation stops running work, not only new admissions",
        members=["SC-12:revocation_effective"],
        stack=["job_scheduler.revocation_reaches_running_work", "incident_halt.kill_completeness"]),
    "os_kernel_enforcement": dict(
        kind="environment", title="The OS kernel enforces the capability model as specified",
        members=["SC-09:kernel_enforces_caps"],
        stack=["agent_sandbox.privilege_lattice"]),
    "durable_ack": dict(
        kind="environment", title="A sink acknowledgement means a durable commit",
        members=["SC-18:ack_durable"],
        stack=["logging_pipeline.serving_logging_invariant"]),
    "versioned_writes": dict(
        kind="correspondence", title="Every write bumps a version; restore verification is trusted",
        members=["SC-19:versioned_targets", "SC-19:trusted_verifier"],
        stack=[]),
    "deterministic_reexecution": dict(
        kind="measurement", title="Re-execution is deterministic or has a specified tolerance",
        members=["SC-21:deterministic_reexecution"],
        stack=[]),
    "rekey_independence": dict(
        kind="correspondence", title="Rounds outside an epoch carry no information about that epoch's secret",
        members=["SC-02:rekey_independence"],
        stack=[]),
    "source_attribution": dict(
        kind="correspondence", title="All destinations and processes have trustworthy source attribution",
        members=["SC-03:general_attribution"],
        stack=[]),
    "finite_transcript": dict(
        kind="correspondence", title="The receiver's lifetime transcript has the stated finite cardinality",
        members=["SC-01:finite_lifetime_transcript"],
        stack=[]),
    "statistical_independence": dict(
        kind="measurement", title="The usefulness statistics model (independent lifetimes) applies to the environment",
        members=["SC-01:independent_lifetimes"],
        stack=[]),
    "independent_review": dict(
        kind="organisational", title="Independent human review of statement fidelity and premises",
        members=["SC-26:independent_review"],
        stack=["researcher_workstation.statement_fidelity"]),
}

# Lean stack-certificate premise id (before ':') -> normalised premise
LEAN_MAP = {
    "SC26.legal": "credential_separation",
    "SC26.legal_realized": "credential_separation",
    "SC26.sound_config": "model_runtime_correspondence",
    "F6.recall": "semantic_judgement",
    "F6.strategy": "observation_complete",
    "F3.rate": "trusted_meter",
}

EVIDENCE_RANK = {"RUNTIME_VALIDATED": 4, "TESTED_NOT_PROVED": 3, "OBSERVED_FAILURE": 2, "NOT_RUN": 1,
                 "NOT_APPLICABLE": 0}
PROOF_RANK = {"THEOREM_VERIFIED": 2, "NOT_PROVED": 1, "NOT_APPLICABLE": 0}
TESTED = {"RUNTIME_VALIDATED", "TESTED_NOT_PROVED"}


class LedgerError(Exception):
    pass


def load_manifests(root=ROOT):
    out = {}
    for f in sorted((root / "scenarios").glob("SC-*/manifest.json")):
        m = json.loads(f.read_text())
        if not re.fullmatch(r"SC-\d\d", str(m.get("id"))) or not isinstance(m.get("assumptions"), list):
            raise LedgerError(f"malformed manifest {f}")
        out[m["id"]] = m
    if not out:
        raise LedgerError("no scenario manifests found")
    return out


def load_stack(root=ROOT):
    data = json.loads((root / "stack/components.json").read_text())
    comps = {c["id"]: c for c in data["components"]}
    prem = {f"{c['id']}.{p['id']}": (c, p) for c in data["components"] for p in c["premises"]}
    return comps, prem


def run_dirs(m):
    """evidence runs cited with PASS in a manifest (e.g. 'run-2')"""
    runs = set()
    for e in m.get("evidence", []):
        mt = re.search(r"/evidence/(run-[^/]+)/", e.get("path", ""))
        if mt and e.get("outcome") == "PASS":
            runs.add(mt.group(1))
    return sorted(runs)


def normalise(manifests, stack_prem, premises):
    """map every manifest assumption to exactly one normalised premise (fail closed)"""
    owner = {}
    for pid, spec in premises.items():
        if spec["kind"] not in KINDS:
            raise LedgerError(f"{pid}: unknown kind {spec['kind']}")
        for ref in spec["stack"]:
            if ref not in stack_prem:
                raise LedgerError(f"{pid}: stack premise {ref} not in stack/components.json")
        for mem in spec["members"]:
            sid, aid = mem.split(":", 1)
            targets = [(s, aid) for s in manifests if sid in ("*", s)
                       and any(a["id"] == aid for a in manifests[s]["assumptions"])]
            if not targets and sid != "*":
                raise LedgerError(f"{pid}: member {mem} not found in any manifest")
            for t in targets:
                if t in owner and owner[t] != pid:
                    raise LedgerError(f"{t[0]}:{t[1]} mapped to both {owner[t]} and {pid}")
                owner[t] = pid
    unmapped = [f"{s}:{a['id']}" for s, m in manifests.items() for a in m["assumptions"] if (s, a["id"]) not in owner]
    if unmapped:
        raise LedgerError("unmapped manifest assumptions: " + ", ".join(unmapped))
    return owner


def build(root=ROOT, premises=None):
    premises = PREMISES if premises is None else premises
    manifests = load_manifests(root)
    comps, stack_prem = load_stack(root)
    owner = normalise(manifests, stack_prem, premises)
    rows = []
    for pid, spec in premises.items():
        members = sorted((s, a) for (s, a), p in owner.items() if p == pid)
        scen = sorted({s for s, _ in members})
        ev, pr, runs = "NOT_APPLICABLE", "NOT_APPLICABLE", []
        for s, aid in members:
            a = next(x for x in manifests[s]["assumptions"] if x["id"] == aid)
            if EVIDENCE_RANK.get(a.get("evidence"), -1) > EVIDENCE_RANK[ev]:
                ev = a["evidence"]
            if PROOF_RANK.get(a.get("proof"), -1) > PROOF_RANK[pr]:
                pr = a["proof"]
            if a.get("evidence") in TESTED:
                runs += [f"{s} {r}" for r in run_dirs(manifests[s])] or [f"{s} (harness)"]
        status = {(s, a): next(x for x in manifests[s]["assumptions"] if x["id"] == a).get("evidence")
                  for s, a in members}
        tested_in = sorted({s for (s, a), e in status.items() if e in TESTED})
        failures = sorted({s for (s, a), e in status.items() if e == "OBSERVED_FAILURE"})
        tested = bool(tested_in)
        practical = []
        for ref in spec["stack"]:
            c, p = stack_prem[ref]
            com = (c.get("practical") or {}).get("commodity") or ""
            practical.append({"ref": ref, "premise": p["text"], "stack_evidence": len(p.get("evidence", [])),
                              "commodity_test": com if len(com) <= 300 else com[:297].rsplit(" ", 1)[0] + " …"})
        rows.append(dict(id=pid, kind=spec["kind"], title=spec["title"], scenarios=scen,
                         members=[f"{s}:{a}" for s, a in members], best_evidence=ev, best_proof=pr,
                         runs=sorted(set(runs)), tested=tested, tested_in=tested_in, failures=failures,
                         leverage=len(scen) * (1 if tested else 2), practical=practical))
    rows.sort(key=lambda r: (-r["leverage"], r["tested"], r["id"]))
    return rows


def lean_section(rows, lean_entries):
    by = {r["id"]: r for r in rows}
    lines = ["## Lean stack certificate premises (ControlStack.Cert.stackLedger)", "",
             "| Lean premise | kind | normalised premise | leverage |", "|---|---|---|---|"]
    seen = set()
    for e in lean_entries:
        lid = e["name"].split(":", 1)[0].strip()
        if (lid, e["kind"]) in seen:
            continue
        seen.add((lid, e["kind"]))
        norm = LEAN_MAP.get(lid)
        if e["kind"] == "proof_obligation":
            target = f"discharged by `{e['theorem']}`"
            lev = "—"
        elif norm:
            target, lev = f"`{norm}`", str(by[norm]["leverage"])
        else:
            target, lev = "(stack-level; no scenario manifest)", "—"
        lines.append(f"| `{lid}` | {e['kind']} | {target} | {lev} |")
    return "\n".join(lines) + "\n"


def render(rows, lean_entries=None):
    def cell(s):
        return s.replace("|", "\\|").replace("\n", " ")
    lines = ["# Assurance ledger (generated)", "",
             "Generated by `tools/portfolio_ledger.py` from `scenarios/SC-*/manifest.json`, `stack/components.json`",
             "and (last section) the Lean stack certificate. Do not edit by hand; regenerate and check with",
             "`--check`. Premise identities are normalised across scenarios by the curated table in the tool.",
             "Leverage = scenarios depending on the premise × (2 if no member has runtime evidence).", "",
             "Evidence is the best status across member assumptions (`TESTED_NOT_PROVED` is runtime evidence from a",
             "preregistered run or harness; nothing is `RUNTIME_VALIDATED` without an independent runner). Kinds",
             "follow `ControlStack.Cert.PremiseKind`.", "",
             "| # | premise | kind | leverage | scenarios | best evidence | tested in | best proof | runs | "
             "practical test |",
             "|---|---|---|---|---|---|---|---|---|---|"]
    for i, r in enumerate(rows, 1):
        prac = "; ".join(f"`{p['ref']}`: {p['commodity_test']}" for p in r["practical"][:1]) or "—"
        if len(r["practical"]) > 1:
            prac += " (also: " + ", ".join(f"`{p['ref']}`" for p in r["practical"][1:]) + ")"
        ev = r["best_evidence"] + (f" (observed failure: {', '.join(r['failures'])})" if r["failures"] else "")
        tin = f"{len(r['tested_in'])}/{len(r['scenarios'])}"
        lines.append(f"| {i} | **{r['id']}**: {cell(r['title'])} | {r['kind']} | {r['leverage']} | "
                     f"{', '.join(r['scenarios'])} | {ev} | {tin} | {r['best_proof']} | "
                     f"{', '.join(r['runs']) or '—'} | {cell(prac)} |")
    lines += ["", "## By kind", ""]
    for k in KINDS:
        ids = [r["id"] for r in rows if r["kind"] == k]
        lines.append(f"- **{k}** ({len(ids)}): " + (", ".join(f"`{x}`" for x in ids) or "—"))
    lines += ["", "## Member assumptions", ""]
    for r in rows:
        lines.append(f"- `{r['id']}`: " + ", ".join(r["members"]))
    text = "\n".join(lines) + "\n\n" + LEAN_MARKER + "\n"
    if lean_entries is not None:
        text += "\n" + lean_section(rows, lean_entries)
    return text


def main(argv=None, root=ROOT, out=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true", help="fail if ASSURANCE-LEDGER.md is out of date")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--no-lean", action="store_true", help="omit the Lean section (no lake needed)")
    args = ap.parse_args(argv)
    out = Path(out) if out else root / "ASSURANCE-LEDGER.md"
    try:
        rows = build(root)
        lean_entries = None
        if not args.no_lean:
            sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
            from tools.cert_ledger import lean_ledger, LedgerError as CertError
            try:
                lean_entries = lean_ledger(root=root)
            except CertError as e:
                raise LedgerError(f"Lean ledger unavailable ({e}); use --no-lean") from e
    except (LedgerError, OSError, ValueError, KeyError) as e:
        print(f"FAIL: {e}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps({"premises": rows, "lean": lean_entries}, indent=2, ensure_ascii=False))
        return 0
    text = render(rows, lean_entries)
    if args.check:
        old = out.read_text() if out.exists() else ""
        if args.no_lean:
            old, new = old.split(LEAN_MARKER)[0], text.split(LEAN_MARKER)[0]
        else:
            new = text
        if old != new:
            print(f"FAIL: {out.name} is out of date; regenerate with tools/portfolio_ledger.py", file=sys.stderr)
            return 1
        print(f"OK: {out.name} up to date ({len(rows)} normalised premises)")
        return 0
    out.write_text(text)
    print(f"wrote {out.name}: {len(rows)} normalised premises")
    return 0


if __name__ == "__main__":
    sys.exit(main())
