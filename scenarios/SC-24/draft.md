# SC-24 — scenario design draft (SPECIFIED ONLY)

**Bad event:** Untrusted monitor colludes with generator or learns honeypot phase

**Proposed thin enforcement claim (not Lean checked):**

```text
∀ attackStrategy, scopedWorstCaseRecall ∧ freshIndependentPhase → risk ≤ certifiedBound
```

**Reusable families:** F2+F6+F8. These names identify candidate lemmas, not a proof or measured security guarantee.

**Adversarial falsifier:** A monitor chooses a honeypot-specific behavior, exploits feedback or hides in a population-average blind spot.

**Scope to freeze before formalization:** concrete agent action alphabet, complete authority paths and external effects, meaningful honest task, horizon/rollback policy, adversary class and observation/feedback model. Any uncertain semantic property must be isolated as an assumption, not inferred from a hash or allowlist.

**Evidence needed before promotion:** a reviewed actual bad-event correspondence, Lean statement and kernel proof with explicit axioms, pinned reference-monitor policy, adversarial bypass tests, human/independent scrutiny, and baseline vs restricted usefulness. No experiment or runtime enforcement exists *from this draft*.

**Catalog source:** [SCENARIO-CATALOG.md](../../SCENARIO-CATALOG.md) §4.
