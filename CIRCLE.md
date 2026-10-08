# Circle effort: pickup notes (2026-10-08)

Start with [ROADMAP.md](ROADMAP.md) ("Status at a glance"), then:
- [PRIMITIVES-AND-SCENARIOS.md](PRIMITIVES-AND-SCENARIOS.md): status of F1–F8 and of all 28 scenarios;
- [STRUCTURE-PLAN.md](STRUCTURE-PLAN.md): work that needs no testing. Read its "check first" note about the three
  scenario branches;
- [NECESSITY.md](NECESSITY.md): what each necessity witness does and does not show.

## What was added

| file | content |
|---|---|
| `ControlStack/Leakage.lean` | leakage transfer, one-shot and sequential with hidden state and feedback. Instances: stateful side channels (`covert_seq`, `covert_side_bound`, `sc01_adaptive_target`, `covert_seq_seed`) and leakage-sensitive adaptive auditing (`audit_leak_bound`, `audit_adaptive_hidden`) |
| `ControlStack/LeakWitness.lean` | a real-leak instance of the audit bound (BSC(ε) leak; survival ≤ 1 − ε) |
| `ControlStack/Necessity.lean` | necessity witnesses, plus a policy comparison and an illustration (labelled) |
| `ControlStack/Gate.lean`, `GateClients.lean` | shared reference-monitor interface with an absorbing-halt combinator. Clients: AuditDispatch, AuditGate, EgressGate; F4 content-addressed artefact gate; F7 exact-payload approval |
| `ControlStack/Lease.lean` | F5 leases: per-lease budgets across forks, unit-count bound, global cap, absorbing revocation |
| `tools/check_sc01_case.py` | reports proofs / bindings / evidence / applicability separately; exit 3 when a hypothesis is refuted |
| `tools/ctrlcert.py` | researcher CLI: `channel`, `probe`, `audit`, `hazard`, `samples`, `diagnose`; `--lean` emits checked instantiations |
| `reviews/circle-consult-2026-10-08/` | adversarial consultation (Astra, Fable): don't build a general calculus; the value is accounting, refutation and experiment design |
| `reviews/adversarial-2026-10-08/` | Gemini 3.1 Pro + Opus 5.5 review of the new Lean, with the disposition |

Status:
- Everything above is proved with standard axioms only, and has been adversarially reviewed.
- It is NOT ledger-verified (no proofledger foreign-family red team yet).
- None of the mathematics is new: the circle consultation and the adversarial reviews (`reviews/`) found every
  result classical.

## Verify

```
lake build ControlStack                 # all modules
python3 tools/check_sc01_case.py        # expected: exit 3, VERDICT HYPOTHESIS_REFUTED (side certificate refuted)
python3 tools/test_ctrlcert.py
python3 tools/ctrlcert.py audit --rounds 100 --budget 10 --steps 5 --fpr 0.2
```
