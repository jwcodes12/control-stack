# SC-23 — scenario design draft (SPECIFIED ONLY)

**Bad event:** Prompt-injected document/tool result causes an unauthorized tool action

**Proposed thin enforcement claim (not Lean checked):**

```text
∀ toolEffect, trustedAuthorization toolEffect ∧ untrustedTextCannotGrantAuthority toolEffect
```

**Reusable families:** F1+F3+F7. These names identify candidate lemmas, not a proof or measured security guarantee.

**Adversarial falsifier:** A prompt injection changes a tool parameter, identity, or capability despite separate auth.

**Scope to freeze before formalization:** concrete agent action alphabet, complete authority paths and external effects, meaningful honest task, horizon/rollback policy, adversary class and observation/feedback model. Any uncertain semantic property must be isolated as an assumption, not inferred from a hash or allowlist.

**Evidence needed before promotion:** a reviewed actual bad-event correspondence, Lean statement and kernel proof with explicit axioms, pinned reference-monitor policy, adversarial bypass tests, human/independent scrutiny, and baseline vs restricted usefulness. No experiment or runtime enforcement exists *from this draft*.

**Catalog source:** [SCENARIO-CATALOG.md](../../SCENARIO-CATALOG.md) §4.
