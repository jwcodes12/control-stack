# Lean track handoff — 2026-10-08 (branch `claude/lean-track`, worktree <repo root>)

Built in a separate worktree so it does not collide with the concurrent SC-01 isolation work on `master`.
Not merged, not pushed. To merge: `git -C ~/research/control-stack merge claude/lean-track` (new files only,
except ROADMAP.md/STACK.md, which may conflict with master's edits).

All Lean files below are "proved" (`lake env lean` + `#print axioms`: only propext/Classical.choice/Quot.sound);
none is ledger-gated or red-teamed by two families yet.

| file | result |
|---|---|
| ControlStack/SideChannel.lean | receiver also sees a side observation from a fixed kernel: P ≤ \|V\|·Σc/\|M\| for any domination certificate c; uninfluenced side obs costs nothing; certificates multiply over episodes |
| ControlStack/ScenarioASide.lean | SC-01: target 2^-16 holds if side mass ≤ 65536/59049 ≈ 1.11; ONE clean side bit is attained at 2·59049/2^32 > 2^-16; per-episode noisy bits need crossover ≥ ~0.49 |
| ControlStack/ScenarioAUsefulness.lean | usefulness gate passes only at 63/64 or 64/64; false pass ≤ 1/80 for p ≤ 0.9 (monotone tail); Python grid endpoints valid and maximal |
| ControlStack/LifetimeLedger.lean | ledger transition model: restore-free traces keep every lineage ≤ cap; one older-snapshot restore breaks it (no-rollback is necessary); lifetime secret bound |
| ControlStack/GatewayCore.lean | multi-channel gateway core matching gateway.py incl. close/after-close: refusal blanks, close freezes, exact reachable count (= view_space_size), end-to-end bound |
| gateway/difftest_core.py | Python vs Lean core on 2000 random multi-channel traces: 0 mismatches |
| ControlStack/SafetyCaseSC01.lean | the case in one theorem (`sc01_case`), ledger admits ≤ 5 nine-view episodes, `bit_refutes` (measured bit recovery p ⇒ certificate mass ≥ 2p) |
| tools/check_sc01_case.py + assurance/sc01-safety-case.json | one-command checker; current verdict HYPOTHESIS_REFUTED for the single-host harness (cache bit 64/64, lower 0.954 ⇒ mass ≥ 1.909 > 1.11) |
| ControlStack/ComposeCoverage.lean | coverage (K, ε): Red's trusted miss ≤ K·τ̄ + ε, tight in K and ε; composed protocol bound under coverage (positive counterpart to ComposeBlindSpot) |
| ControlStack/MultiStep.lean | k-step attacks: uniform conditional catch rate c ⇒ survival ≤ (1−c)^k; marginal rate c with correlated misses gives 1−c for every k (no-go); posterior-hazard bound for seeded monitors |
| ControlStack/ScenarioACore.lean | SC-01's 9-view carrier derived from GatewayCore; end-to-end five-episode bound over raw traces; a visible variable episode count attains 66430/2^32 > 2^-16 |
| ControlStack/AuditBudget.lean | shared fixed audit budget B over N rounds vs a k-step attack: a hidden uniformly random audit set gives survival C(N−k,B)/C(N,B) ≤ (1−B/N)^k; a schedule Red can observe gives survival 1 whenever N−B ≥ k (e.g. N=100, B=10, k=5: 0.584 vs 1) |
| REVIEW-PACKET.md | packet for one human control researcher: claim, threat model, theorem chain, assumptions, 12 questions, reproduction |
| reviews/codex-lean-audit-2026-10-08.md | independent statement audit of ScenarioARepair / EgressGate / GatewayModel |

Open from the audit (for whoever owns those files): EgressGate assumes policy integrity by definition (FIDELITY.md
overclaims); fixed-five-episode premise undocumented in README/manifest; egress README vs manifest CI claim;
CORRESPONDENCE.md timing row marked validated despite the cache finding.

Checker coverage: `tools/check_sc01_case.py` now also checks ScenarioACore (case chain) and ComposeCoverage, MultiStep, AuditBudget (supporting results).

Next: once the VM-pair isolation lands, re-run the side-channel probe there and re-run `python3 tools/check_sc01_case.py`;
the safety conjunct applies only if the measured evidence no longer refutes the side certificate.
