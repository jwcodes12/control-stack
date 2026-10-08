### Verdict
The proofs correctly mechanize classical maximal leakage and predictable-process optional stopping. However, critical encoding traps undermine the applied gate specs: the Artifact theorem is vacuously true for real hashes, and the Lease manager permanently shadows new quotas. Furthermore, one Necessity witness is mathematically trivial and fails to instantiate any system. While the core theorems are sound, the interface bindings to the control architecture require immediate revision.

### Defects

**1. `ControlStack/GateClients.lean` : `Artifact.deployed_is_reviewed` (VACUITY / ENCODING TRAP)**
* **Problem:** The theorem assumes `(hinj : Function.Injective hash)`, which requires the hash function to be injective over the *entire* type `C`. For any standard hash function (which compresses a large/infinite space `C` into a finite digest `H`), global injectivity is mathematically impossible. This renders the hypothesis unconditionally false and the theorem vacuously true. 
* **Instance/Counterexample:** Let `C = String` and `H = Fin (2^256)`. By the Pigeonhole Principle, no such injective function exists, making the bound vacuous for real-world content stores.
* **Fix:** Restrict the injectivity assumption to the exact contents present in the trace: `∀ c ∈ s.store, ∀ c' ∈ s.reviewedContent, hash c = hash c' → c = c'`.

**2. `ControlStack/Lease.lean` : `leaseOf` and `fork` (ENCODING TRAP)**
* **Problem:** `leaseOf` uses `s.holder.find? (fun p => p.1 = w)`. When the trusted controller issues a new lease to an existing worker, or an agent forks over an existing worker, `holder := holder ++ [(w, id)]` appends the new assignment to the *end* of the list. Because `find?` returns the first match, the worker will permanently resolve to their oldest lease. New quotas are effectively swallowed.
* **Instance/Counterexample:** Execute `issue leaseA worker1`, then `issue leaseB worker1`. Any subsequent `.work worker1 cost` will exclusively debit `leaseA`.
* **Fix:** Prepend new leases (`[(w, id)] ++ s.holder`) so `find?` hits the newest entry, or redefine `holder` as an associative map with strict override semantics.

**3. `ControlStack/Necessity.lean` : `shared_score_product_unsound` (TRIVIALITY / FIDELITY)**
* **Problem:** The module header claims each witness shows that "dropping the premise outright breaks the bound [that used it]". However, this theorem never invokes a `ControlStack` bound or transition system. It merely evaluates trivial boolean probability (`P(A ∩ A) = P(A) ≠ P(A)²`) to show perfectly correlated events don't multiply.
* **Instance/Counterexample:** The theorem is formulated entirely in isolation using `scoreLaw`, proving `1/10 ≠ 1/100`, rather than instantiating a multi-layer system trace.
* **Fix:** Instantiate a real trace using two gate clients (e.g., `AuditGate` and `EgressGate`) triggered by the same agent-controlled boolean flag, state the independent pass-probability bound, and show the trace violates it.

*(Note on other checked items: `N - k` subtraction evaluates to 0 safely bounding `0 ≤ 0` when `k > N`; `survInd` strictly locks in failure upon a catch because `Disjoint` cannot be recovered; quantifier orders in `transfer` correctly bind the blind value.)*

### Overclaims in Prose

* **(e) Artifact `deployed_is_reviewed`:** The prose claims "if the hash is injective on the contents involved", but the Lean code demands global injectivity over `C`. This is a massive overclaim because it hides the theorem's vacuity.
* **(g) Lease "a fork inherits its parent's LEASE":** False if the target worker already holds a lease, because the first-match append bug forces the target to retain their original lease rather than inheriting the parent's.
* **(h) every Necessity witness shows dropping the premise breaks the bound:** False. `shared_score_product_unsound` breaks no bound; it only demonstrates basic non-independence.

*(Claims a, b, c, d, and f correctly describe the Lean statements without overclaiming.)*

### Harness Question

Putting these results through the proofledger harness is **not ceremony**; it would add immense value. The foreign-family spec red team is designed to catch exactly the first-match append bug in `Lease.lean` by attempting to execute valid operational traces that fail. 

More critically, the **mandatory `Witness` of non-vacuity** would have immediately blocked `Artifact.deployed_is_reviewed`. The verifier would have demanded a concrete instantiation of an injective hash function for a non-trivial domain, immediately exposing the global injectivity trap. `Leakage.audit_leak_bound` also heavily needs the Witness obligation to prove that a strict bounding certificate `cl` can actually be constructed for a realistic, non-degenerate side-channel kernel `K`.

### Triviality / Novelty

The mathematics are completely classical. `seq_transfer` packages the maximal leakage chain rule (Issa–Wagner–Kamath 2020) for reactive environments. `audit_adaptive_hidden` and `cval_live` are standard predictable-process / optional stopping arguments (an attacker stopping when caught gains no advantage, as their total attack count locks below $k$). The novelty is entirely in the operational packaging (tying transfer bounds directly to an interactive transition system with catch feedback), not the underlying probability theory.

### Missing Results

1. **Damage Bounds:** `audit_leak_bound` bounds the probability of executing $k$ steps unseen, but lacks a connection to *expected catastrophic harm*. A skeptical researcher needs a bound proving the gate halts the agent *before* cumulative damage exceeds a threshold.
2. **Policy Tampering Resistance:** `EgressGate` relies on policy integrity by definition. The framework lacks a theorem showing the agent cannot use its allowed actions (e.g., standard workflow steps) to overwrite the `EgressGate.Policy` map itself.
3. **End-to-End Mediation:** The files lack a theorem proving that the abstract gates actually mediate the concrete agent execution model (i.e., proving the agent has no out-of-band actions that bypass `System.step`).
