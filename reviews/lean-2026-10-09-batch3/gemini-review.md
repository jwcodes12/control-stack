### File ControlStack/Scenarios/LabStack.lean
Verdict: 
The file presents a joint state model intended to show component integration, but its safety properties are largely tautological or rely on extremely weak arithmetic assumptions. The integration between components is superficial, and the "deputy" provides no actual autonomous authorization.

Defects:
1. Location: `deputyOp` and `deputy_admissible`.
Problem: The deputy is claimed to be an automated bridge that triggers a vendor payment upon deployment. However, it merely issues an `.execute` command for the payment. Since SC-26 strictly requires a prior explicit human `.approve` for any executed payment, the deputy cannot actually authorize the payment itself.
Instance: A deployment occurs, `deputyOp` issues `.execute`, but SC-26 rejects it because no human approver has approved it. The payment bridge is essentially a no-op.
Fix: The deputy should issue `.request` and `.approve` (using a dedicated deputy role) or SC-26 must be modified to allow the deputy to bypass human approval for deploy-triggered payments.

2. Location: `lab_safe` theorem and `hU16r`, `hU16a`, `hU28`, `hU26` premises.
Problem: The authenticated provenance claims (e.g., reviewers are outside the adversary set `U`) are vacuous tautologies. The theorem assumes as a premise that `U` is disjoint from all trusted roles (e.g., `∀ u ∈ U, u ∉ P.R16.reviewers`). It then "proves" that any reviewer is not in `U`. This merely proves `A ∩ B = ∅ → a ∈ A → a ∉ B`.
Instance: The `issued_trusted` tactic directly applies `hU16r` to conclude `c ∉ U`, which is a simple set disjointness fact rather than a meaningful security property.
Fix: Model compromised credentials or actual cryptographic authentication checks rather than hardcoding perfect role disjointness as a premise.

3. Location: `payStep` global budget check.
Problem: The budget check `s.money + (p.spent - s.pay.spent) ≤ P.G` is evaluated on natural numbers (`ℕ`). If `SC26.step` allows `p.spent` to be smaller than `s.pay.spent` (e.g., via a bug or a refund), the subtraction truncates to zero. This allows an arbitrary budget increase to bypass the check entirely.
Instance: If `s.pay.spent = 10` and the next state `p.spent = 5`, `5 - 10 = 0`, allowing the step regardless of how large `s.money` is.
Fix: Use integer arithmetic (`ℤ`) for budget diffs or explicitly mandate and prove strict monotonicity (`s.pay.spent ≤ p.spent`) before executing the subtraction.

4. Location: `lab_halt_freezes` and `isArrive` handling in `labStep`.
Problem: The theorem claims that after a shared halt, the payment gate's messages are "frozen" and the bank gains only messages already in flight. This is just a deceptive restatement of the definition of `.arrive`. The halt explicitly allows `.arrive` operations, which actively move messages from `net` to `bank`.
Instance: The system is halted. The adversary calls `.pay (.arrive k)`. `labStep` allows it because `isArrive o` is true, actively changing the bank state.
Fix: Do not frame an active state transition between the network and the bank as a "frozen" state.

Overclaims: 
The "global budget" result implies complex cross-gate coordination, but it trivially holds because `compStep` enforces `spentT ≤ G`, which mathematically dominates the actual usage `usedT ≤ G`. The deputy is claimed to be a functional bridge, but it lacks the authority to autonomously approve the payments it triggers.

### File ControlStack/Scenarios/SC26Liveness.lean
Verdict: 
The liveness guarantees are built on fixed adversarial schedules and highly unrealistic network assumptions. The properties structurally exclude the exact interleavings and failures that would actually threaten liveness in a distributed system.

Defects:
1. Location: `crash_tolerant_progress` adversarial trace definition.
Problem: The adversary's interleaving is fixed to the exact sequence `pre ++ [.recover] ++ mid ++ [.bankProcess k] ++ post`. The adversary is structurally prevented from acting between `recover` and `bankProcess k` in a way that drops the message, and is explicitly forbidden from halting the system before `recover` (via the `hh` premise). 
Instance: If the adversary maliciously schedules a network drop or a halt inside `pre`, the property simply doesn't apply, ignoring realistic liveness failures.
Fix: Formulate liveness using temporal logic (e.g., `Eventually paid`) under fairness constraints instead of hardcoding a highly favorable execution trace.

2. Location: `CMono` definition and `crash` semantics.
Problem: The concrete monotonicity constraint `s.wire <+: t.wire` strictly enforces that the network wire only grows, and the `.crash` step is defined to preserve the wire perfectly (`List.prefix_refl _`). This mathematically eliminates the possibility of message loss entirely.
Instance: A node crashes, but `s.wire` is perfectly retained in `t.wire` without any data loss.
Fix: Model the wire as a volatile queue where crashes can drop unacknowledged messages, forcing `.recover` to actually perform meaningful retransmission.

3. Location: `progress_interleaved` cap exhaustion condition.
Problem: The theorem concludes that either the payment is made, the gate halts, or `cap < s.spent + r.tx.amount`. This is a trivial disjunction of the gate's predefined blocking conditions. 
Instance: The adversary simply exhausts the cap during the arbitrary `a0` trace, making the honest execute a no-op, which satisfies the `∨ cap < ...` branch trivially.
Fix: A true progress theorem should prove that the honest trace can successfully secure its prerequisites (like reserving cap space) before the adversary exhausts them.

Overclaims: 
Claims "crash-tolerant progress", but the model completely redefines a crash to perfectly preserve the network wire state (`s.wire <+: t.wire`). True crash tolerance requires demonstrating recovery from lost volatile state, which this file mathematically prohibits.

### File ControlStack/Scenarios/SC27ExtensionOnly.lean
Verdict: 
The extension-only witness avoids laundering tampered logs by permanently bricking the anchor mechanism upon any fork. The safety proofs rely on tautologies and push the core security requirement entirely into an injectivity premise.

Defects:
1. Location: `step` for `.anchor` and `honest_liveness`.
Problem: If the storage ever fails to extend `last` (e.g., via an adversarial `.rewrite`), `extendsLast` becomes false and an alarm is raised. Because the `last` anchor is never updated again, every subsequent honest `.append` will also fail to extend `last`, triggering alarms forever. The single fork permanently bricks the witness's anchoring capability.
Instance: Adversary issues `.rewrite [7]`. `extendsLast` evaluates to false. User issues honest `.append 8`. Storage is `[7, 8]`. `extendsLast` remains false forever.
Fix: Implement a recovery state or witness reset mechanism to resume anchoring after a fork is acknowledged and mitigated.

2. Location: `sc27_ext_safe` injectivity premise.
Problem: The injectivity premise `Set.InjOn` is applied exactly to the set of manifests and logs that appear in the *current* trace. This pushes the burden of safety onto a dynamic execution property, meaning safety holds only if the adversary conditionally decides not to generate a hash collision in this specific run.
Instance: If the adversary actively finds a collision, the premise becomes false, and the theorem vacuously holds `False → True`.
Fix: Require collision resistance as a global cryptographic assumption over all possible strings, rather than a trace-dependent property.

3. Location: `alarm_iff`.
Problem: The theorem proves that an alarm is raised *if and only if* `extendsLast s = false`. This is completely vacuous because `step` is literally defined as `if extendsLast s then ... else { s with alarms := ... }`.
Instance: The proof is just unpacking the `if/else` statement logic.
Fix: Remove tautological restatements of code logic from the theorems; they provide no independent verification.

Overclaims: 
The "strengthened safety" (`sc27_ext_safe`) relies heavily on a trace-dependent injectivity assumption, meaning it doesn't actually prove the system is safe; it only proves that *if* no collisions happen to occur in this specific run, the system is safe.

### File ControlStack/Scenarios/SC25Refinement.lean
Verdict: 
The refinement is an illusion that maps an atomic concrete operation into a sequence of abstract steps, completely bypassing the concurrency issues (TOCTOU) the abstract model is supposed to analyze. The proofs are largely trivial mappings.

Defects:
1. Location: `stepC` for `.fire` and `opsOf`.
Problem: In the concrete machine, `.fire` is a monolithic, atomic step that recalculates the digest and applies the effect all at once. The abstraction function `opsOf` artificially splits this single step into `[.check id, .fire id]`. Because the concrete machine is single-threaded and executes `.fire` atomically, this mapping deceptively bypasses the Time-of-Check-to-Time-of-Use (TOCTOU) vulnerability that the split abstract model was built to analyze.
Instance: The runtime simply does not have interleavings between check and fire. The abstraction model hardcodes this atomicity.
Fix: If the concrete system is atomic, the abstract model must also use an atomic fire operation to accurately reflect the architecture. Defining a two-step abstract model and then mapping an atomic concrete step to it hides architectural flaws.

2. Location: `stepC` for `.check` and `CSt.checked`.
Problem: The `.check` operation adds `id` to the `s.checked` list. However, the concrete `.fire` operation never reads or requires `id ∈ s.checked` to succeed. The `.check` operation is a useless ghost step injected solely to satisfy the abstract model's simulation relation.
Instance: Calling `.fire id` without ever calling `.check id` succeeds perfectly in the concrete machine, rendering `.check` completely fake.
Fix: Remove the dummy `checked` state and `.check` operation from the concrete machine, or force `.fire` to actually consume it.

3. Location: `concrete_content_safe` proof logic.
Problem: The theorem proves that the executed content matches the audited content by relying entirely on the injectivity of the hash function (`Set.InjOn h`). Since the audit log stores `h(content)` and the fire step checks `h(current_content) == logged_hash`, the proof is a trivial application of injectivity (`h(A) = h(B) → A = B`) rather than a deep state machine invariant.
Instance: The proof merely applies the mathematical definition of injectivity to the hashes stored in the audit log and effect log.
Fix: Frame this as a standard cryptographic hash guarantee rather than presenting it as a complex state machine safety refinement.

Overclaims: 
Claims a "forward simulation" into the Lean model, but the concrete machine is built with ghost variables and forced atomicity specifically tailored to make the simulation trivially succeed, masking the real-world concurrency gaps.

### Cross-cutting
- **Tautological Proofs**: Core theorems repeatedly restate `if/else` branching logic directly from the step definitions (e.g., `alarm_iff`, `lab_halt_freezes`) or rely on vacuous set disjointness to "prove" properties (e.g., authenticated provenance).
- **Adversary Neutering**: Adversarial environments are structurally constrained to prevent meaningful attacks. Network wires are append-only and immune to crashes, and adversarial event schedules are hardcoded to ensure honest actions succeed (e.g., `pre ++ recover ++ mid`).
- **Ghost Logic for Simulation**: Concrete refinements include fake state variables (like `checked` in SC-25) and map atomic implementations onto non-atomic abstractions. This intentionally bypasses the vulnerability classes (like TOCTOU) the models are meant to evaluate, providing a false sense of security.
- **Trace-Dependent Assumptions**: Cryptographic properties like collision resistance are scoped to the exact strings present in a single execution trace, meaning safety is only proven conditionally on the adversary failing to exploit the system in that specific run.
