You are a HOSTILE REVIEWER of two proposed formal statements in a Lean-verified AI-control programme: TMCERT v1 (core
certificate checker for finite-horizon stateful control games) and TMGAC v0 (the Games-for-AI-Control trusted-monitoring
instance, arXiv 2409.07985). Do not praise; find errors. Use web search if available. Nothing is proved yet; this review
decides what is frozen. For each issue: severity (FATAL / MAJOR / MINOR), the exact definition or conjunct, why it is
wrong / unfaithful / vacuous / overclaimed, and a concrete fix (Lean text if possible).

PROGRAMME. Lean-verified, CAPABILITY-FREE control guarantees conditional on explicit trust hypotheses. Classical lemmas
are welcome as infrastructure (report triviality; do not reject for it); vacuity, falsity and unfaithfulness are not.

HISTORY. TMCERT v0 got MAJOR from both reviewers (no false conjunct). Their fixes, applied in v1 / TMGAC v0:
- horizon-bounded certificates (`RiskCertUpTo`) and a computable list-based rational checker with a soundness bridge
  (`checkRiskQ`, `checkLawfulQ`, `gameOfQ`, `valOfQ`), so instances are checked by `decide`;
- row-local admissibility `adm n s a θ` with nature choosing rows per cell (rectangular), a separate fixed-model
  corollary (Fx), and an exact example (FxGap: 3/4 vs 1/2) that rectangular is strictly more conservative;
- an observation interface (`liftObs`); single-model and robust tightness with time-dependent Markov attainment;
- usefulness of the SAME controller (honest action a0, nature's selector, sub-solution certificate);
- a vertex lemma for polytope uncertainty; a deployment theorem through an abstraction (Abs): if every concrete row
  (catastrophe, and continuation pushed forward by α) EQUALS an admissible abstract row, every concrete history-
  dependent Red policy is bounded by the abstract certificate;
- TMGAC: the GAC game, the threshold adapter (n + 1 indexing; c = 0 convention qa m 0 = 0, f 0 = 0), exact bridges
  to GAC's safety recurrence (Prop. 4.1 / App. C) and usefulness recurrence, `constRed` (renamed from `memoryless`;
  no "exactly"), a Lipschitz lemma for constant rates, WLOG at C = 0, and the corrected separation instance (three
  problems, one coin, defer threshold kept at c = 0: sup over constant rates 13/50 vs a round-index-only Red 11/32 =
  full-information value), framed as a sensitivity result against GAC's explicit null-observation assumption, with
  the prior art (Greenblatt 2312.06942, Mallen 2412.12480, Korbak 2501.17315, Ctrl-Z 2504.10374 App. L).
Exact-rational checks (numerics/tmgac_check.py): the safety bridge and usefulness bridge on 300 random instances, 0
mismatches; exG3 numbers; the exV3 certificate table; WLOG at C = 0.

CHECK IN PARTICULAR
1. TRUTH of every conjunct and both Witnesses (edge cases: N = 0, n > N, empty adm, m = 0 or t = 0 tables, k = 0, the
   checker's Fin.castSucc / Fin.succ indexing, `gameOfQ` beyond the horizon, `valOfQ` at n = N, `pushK` with empty
   fibres, Covered at n ≥ N, `honestER` with nature, `Vrob` with Nonempty Θ, the Lipschitz constant N, WLOG with
   TA > 0 at c = 0, the zGAC bridge when f(qd) < f(qa)).
2. Is (Abs) the right deployment statement? Is "EQUALS an admissible row" too strong (should it be "is dominated by")?
   Does it really cover "every policy the untrusted model could follow" once the concrete state includes the model's
   private information? What must a lab actually establish to use it?
3. Does (Q) really make instances kernel-checkable (`decide` on ℚ with List.foldl / List.finRange / Fin.castSucc)? Any
   reason `decide` will fail or be too slow, and what to change?
4. Is the TMGAC usefulness bridge faithful to GAC (does GAC count audited safe solutions as used? deferred ones?),
   and the safety bridge faithful to Prop. 4.1's λ-form?
5. Is anything still overclaimed in the docstrings? Is anything important missing for a lab to certify a real
   trusted-monitoring configuration (interval ROC from finite samples, discretised score thresholds, Blue optimisation)?

End with an overall verdict per statement (accept / minor / major / reject), the fixes in priority order, and the final
conjunct lists you would freeze.

