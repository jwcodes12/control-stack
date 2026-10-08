# Theory work queue — not yet proved

These are concrete proof goals and countermodels for future work. No item here is represented as an established theorem, verified deployment invariant, or completed Lean check.

## 1. Policy integrity / explicit tampering model
State consists of a trusted policy root, untrusted mutable state and attempted actions. Define a policy update step available only to a distinct authenticated principal. Goal: assuming complete mediation and atomic checks against the current trusted root, traces of untrusted actions preserve the policy. Counterexamples to model: mutable config/symlink alias, inherited FD, supervisor deputy, rollback, TOCTOU, and a direct trusted-root write. The theorem must not assume integrity merely by defining untrusted actions to leave policy alone without a deployment correspondence obligation.

## 2. Gate composition / confused deputy
Goal: the conjunction of two inductive gate invariants persists under joint state transitions if every effect is mediated and each gate's trusted transition preserves the other's invariant. Formalize the required rely/guarantee and atomicity premises. Countermodel: gate A trusts a staging path after copying an attacker artifact; gate B trusts that path without binding artifact bytes. Individually local checks pass; composition executes attacker-controlled content. Remedy: content address/hash at review and at use, plus globally mediated effects.

## 3. Halt liveness / fairness
Separate absorbing halt safety (no further effects after halt) from eventual halt liveness. Under a scheduler fairness hypothesis and interruptible trusted operations, a requested halt is eventually serviced. Give an infinite unfair trace showing unconditional liveness fails. Distinguish an effect already in flight and external delayed completion.

## 4. Audit truncation
Formalize first k attack attempts which were genuinely unaudited, not merely first k action proposals. Preserve distinction between refused, deferred, admitted and externally effected actions. Prove a risk bound on that prefix only and show a later-step counterexample if the horizon condition is silently dropped.

## 5. Approximate witness attainment
For each positive epsilon, construct a valid encoder/decoder within the same shared seed, horizon, finite view and lifetime constraints whose exact-recovery probability approaches the claimed supremum from below. Do not generalize a recovery-tightness witness into a no-collusion guarantee (a one-bit command may still coordinate a harm).

## 6. Positive audit policy despite false positives
Design a paced or randomized reservation mechanism preserving nonzero honest-task opportunity while bounding dangerous admissions under explicitly defined false-positive and adversarial schedules. Prove both nonvacuous usefulness and control bounds and show a counterexample when false positives can be arbitrary and persistent.

## Deferred structural moves
Do not move the approximately 45 flat ControlStack modules until the theorem inventory has been extended to declarations beyond root axiom queries, then re-export original module paths and run the full Lake build and axiom check. Do not archive ROADMAP, STACK, SESSION or HANDOFF before checking that their experimental provenance, failed gates, decisions and known counterexamples survive in the generated status/history model.
