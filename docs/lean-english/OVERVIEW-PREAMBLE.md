# What the Lean claims, in plain English

Generated overview of {TOTAL} headline Lean claims (the deployment verifier stack plus the headline theorems of scenarios SC-01 to SC-28). Each row is the first sentence of a full block
(the statement, its hypotheses, what it does **not** say, its kind, and whether its hypotheses are shown satisfiable) in `docs/lean-english/part-g0.md` .. `part-g7.md`.
The blocks were written by Sonnet from the Lean source (not from the scenario descriptions) and are **not yet verified one-to-one against the Lean**; that check is the next step
(`docs/lean-english/ONE-TO-ONE.md`). Treat every sentence as a claim to be checked, not as a result.

**One-to-one freshness as of draft PR #56:** G0 had 26 historical gate-checked comparisons, but the exercise was not strictly blind; revised G0 blocks (including `runtime_trace` and the earlier `Accepted` correction) need a new blind evaluation. **G1–G7 (161 claims) have never been checked one-to-one.** This is model-written, model-reviewed work; no independent human review has occurred.

**How to read the "Kind" column.** *general theorem*: a statement quantified over arbitrary instances. *finite computation*: checked by `decide` on one concrete case. *witness / non-vacuity example*: shows hypotheses can hold together. *negative control*: shows a weakened model fails. *refinement/bridge*: links a concrete machine to the abstract model. *definitional/trivial*: a projection or a restatement of a hypothesis.

**What a Lean theorem can and cannot give you.** Every claim is about a *model* (a list of operations and a state machine, or a finite graph). The runtime link (the real code does what the model does), extraction faithfulness (the model lists every real authority edge), and the trusted base (kernel, Docker, SQLite, Python, the hash function) are premises, never conclusions of these theorems.

## Claims the translators flagged as most likely to be overstated

These are the translators' own judgement, to be confirmed or refuted in the verification step.

1. **`Deployment.deployment_broker_safe` / `broker_contract`.** The harm is "reviewed, exactly approved, once-consumed release". The conclusion only says each published nonce has an approval marked *used* (plus no duplicates, count within the cap). It does not say who signed it, that the digest matched, or that a review happened; those are guards of the model's `release` step, not facts proved about reachable states. `Safe` is only counting and uniqueness. (A reachable-state provenance invariant was drafted but not built; see the verification task.)
2. **`Deployment.exclusive_sink`, `runtime_exclusive`, `accepted_no_avoided_path`.** Hold only over the edges the IR lists; edges into the broker or receiver are cut by definition; `exclusive_sink` covers only edges flagged `authority`.
3. **`TranscriptReplay.runtime_trace`, `final_safe`.** "Runtime" is a hand-mapped, trusted log shown to be a valid model chain; a truncated log also passes (`omitted_tail_is_accepted`).
4. **SC-26 `sc26_once`, `halt_freezes`.** Only each request id is reserved once (approvals are not consumed; the same payload under a new id can be paid again); in-flight messages can still land after HALT.
5. **SC-25 `sc25_safe`.** A later FAIL on the same digest does not block execution; role lists are unconstrained.
6. **SC-06 `sc06_safe`.** "Confirmed by a user" only means a confirm operation carrying a user id; typed fields are unbounded numbers, so an instruction can still ride in one.
7. **SC-07 `sc07_mixed`, `concrete_safe`.** Bounds each window, not the run total; the bound is on "never caught and capped total ≥ S", not "S bits before the first catch".
8. **SC-15 `sc15_safe`, SC-16 `sc16_safe`, SC-17 `sc17_safe`.** Hash match is not content identity without injectivity; "live equals desired" holds by construction; the diff in the operation is treated as trusted.
9. **SC-18 `concrete_safe`, SC-19 `sc19_safe`, SC-20 `sc20_safe`.** The conclusion drops part of what the guard enforces (promoter ≠ writer; allowlist); "verified snapshot" is a flag, not a restore test.
10. **SC-21 `sc21_safe`, `sc21_undetected_prob`; SC-24 `collusion_uniform`.** Escape probabilities, not detection guarantees; the bound is one-shot with a 50/50 prior and is vacuous at TV=1.
11. **SC-23 `sc23_safe`, isolation theorems.** "Untrusted" is the model's own provenance bit; a confirmation can back the same action repeatedly.
12. **SC-27 `sc27_safe`, `sc27_ext_safe`.** Truncation back to an earlier anchor is accepted; entries fabricated before the next anchoring get anchored.
13. **SC-28 `sc28_safe`, `exclusive_placement_safe`.** The meter charging at least real consumption is built into the model; escape from a cgroup is not expressible.
14. **SC-08..SC-14 (`exclusive_dispatcher`, `anti_rollback`, SC-10/11/12 policy theorems).** Several are true by construction of the model (the application is defined as everything except dispatch; no mounts or filesystem in the SC-11 model; unregistered creation is a no-op when `registryOnly` is on).
15. **`*_safe_authenticated` family.** The adversary is not constrained to issue only from the stated set; "not in U" follows from the hypothesis on U, so authentication adds little beyond the unauthenticated theorem on a filtered trace.

---
