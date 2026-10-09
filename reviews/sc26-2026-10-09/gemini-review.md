### Verdict
The formal model successfully captures the basic sequential state machine logic of the SC-26 gate, proving that internal invariants hold under idealized, synchronous conditions. However, the model artificially synchronizes external bank interactions and fails to constrain the adversary's ability to forge unauthenticated operations in the trace. Consequently, the safety property (`Good`) relies heavily on unmodeled environmental assumptions rather than the transition system itself enforcing the physical constraints.

### Defects
1. **Location:** `Op.deliver` and `bankAppend` in `SC26Transaction.lean`.
**Problem:** The transition system models network delivery as an atomic, synchronous update to the external bank ledger (`s.bank`). This assumes zero network latency and no in-flight packets, which invalidates the proof that HALT instantly freezes all external effects.
**Concrete trace:** The gate executes a transaction and sends the network packet. An admin issues `.halt` before the bank receives it. The gate's formal model incorrectly asserts the bank is completely frozen (`halt_freezes`), but the real external bank will asynchronously receive and process the in-flight packet.
**Fix:** Model the network explicitly as an asynchronous message queue, allowing the bank to process in-flight messages independently of the gate's `halted` flag.

2. **Location:** `Op.approve` and the `legal` premise.
**Problem:** The `legal` predicate restricts only `.bankCall`, leaving `.approve` completely unconstrained. The model allows the adversary (who supplies the `ops` trace) to trivially synthesize approvals with arbitrary caller IDs, meaning the formal system does not computationally enforce authentication.
**Concrete trace:** The adversary submits `ops = [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0]`, simply forging the caller ID `2` (a valid approver) during the `.approve` step. The model accepts this as a valid legal trace and `sc26_safe` holds.
**Fix:** Constrain the generation of `ops` to explicitly model authentication, ensuring `.approve c ...` can only be appended to the trace if principal `c` authentically authorized it.

3. **Location:** `Op.execute` and the Cap logic (`s.spent + r.tx.amount ≤ cap`).
**Problem:** The cap implementation only bounds the total numerical sum, allowing an infinite number of zero-amount transactions to be executed and delivered to the bank even after the cap is fully exhausted.
**Concrete trace:** An agent requests a transaction for the full `cap` amount, which is approved and executed. The agent then requests infinite transactions with amount `0`. All are approved, executed (`cap + 0 ≤ cap`), and delivered, creating unauthorized external side effects despite a frozen budget.
**Fix:** Require `r.tx.amount > 0` in the `.request` or `.execute` transitions.

### Prose overclaims
- The claim "HALT freezes effects" is physically false for a distributed system; it only freezes the gate's ability to initiate *new* deliveries, not the external bank's execution of already-sent, in-flight packets.
- The claim "an agent never causes an irreversible external transaction... without an exact... approval" implies the gate's logic prevents forgery, but the formal model simply assumes the environment prevents the adversary from forging `.approve` caller IDs.
- The documentation claims "withHalt adds a trusted HALT to any gate" implying architectural reuse, but the SC-26 gate manually implements its own inline `halt` logic rather than actually utilizing the `Gate.withHalt` functor.

### Missing premises to document
- **Multiple Gate Instances:** If multiple deployed gates share the same bank credential, they must use strictly disjoint ID spaces. Otherwise, ID collisions will cause the bank's `bankDedup` to silently drop valid transactions.
- **Rollback and Replay:** Crash recovery must never roll back the `next` counter independently of the bank. If `next` rolls back, new requests will reuse old IDs and be silently dropped by the bank's deduplication.
- **External Bank Authentication:** The external bank must actually enforce its own authentication (`C.bankAuth`) and strictly reject direct network calls from any credential other than `R.gate` for arbitrary payloads.
- **UI and Intent Binding:** The approver's UI must prevent deception by perfectly binding their human consent to the exact `id` and payload actually transmitted over the network.

### Triviality and novelty (honest)
The formalization contains no new mathematics; it is a straightforward induction over a highly simplified, fully synchronous state machine. The `reqOf` first-match semantics, ID uniqueness, exact `id` binding preventing one approval from authorizing two effects, and `execute` approval matching are mathematically sound and free of encoding traps. The necessity witnesses are trivial demonstrations of removing boolean flags, though `nonce_protects_budget_only` is correctly characterized as an honest nuance showing that removing the nonce double-charges the internal budget while the idempotent bank safely prevents double-execution.
