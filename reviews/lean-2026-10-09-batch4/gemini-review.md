### File ControlStack/Families/F5/EscrowBudget.lean

**Verdict:** Flawed model that relies on shared-memory semantics for a distributed protocol, with vacuous liveness proofs and unrealistic clock properties.

**Defects:**
1. **Location:** `step` (cases `.reclaim` and `.reconcile`).
   **Problem:** Instantaneous shared-memory reads in a supposedly high-latency distributed model.
   **Instance:** The coordinator evaluates `(s.g i).spent` directly from the global state `ESt` as long as `host ∉ s.cut`. There is no modeling of in-flight settlement messages or network delay; the coordinator instantly and perfectly reads remote local state merely due to the absence of a network partition.
   **Fix:** Introduce explicit message passing where hosts send `settle_msg i spent` to the coordinator, and modify `reclaim`/`reconcile` to only process received messages rather than probing global state.
2. **Location:** `step` (case `.crash`).
   **Problem:** Crashed nodes remain perfectly reachable and do not halt.
   **Instance:** The `.crash` operator is a complete no-op (`| .crash _ => s`) and does not add the host to `s.cut` or track its crashed status. Consequently, in `starveTrace` (used in `no_expiry_starves`), the coordinator perfectly reclaims the exact unused budget of a crashed host as if it successfully communicated with it, bypassing the real-world consequence that a dead node cannot report its spend.
   **Fix:** Ensure `.crash` adds the host to `s.cut` or a dedicated `crashed` set, forcing the coordinator to conservatively reclaim `amt` unless the host explicitly heals and reports.
3. **Location:** `datacenter_example`.
   **Problem:** Vacuous liveness claim via an arithmetic tautology.
   **Instance:** The theorem states that unused escrow is settleable 64 ticks after the grant. However, the formal proof executes no system traces; it literally only proves the arithmetic statement `60 + 2 * 2 = 64` using `by norm_num`. 
   **Fix:** State and prove a formal temporal liveness property over trace suffixes (e.g., proving that a legal `reclaim` operation is always eventually possible in the trace model) instead of merely verifying integer addition.
4. **Location:** `legal`.
   **Problem:** Host clocks are neither monotonic nor bounded from above.
   **Instance:** The bounded skew premise `s.now ≤ h + C.σ` permits the host clock `h` to lead true time indefinitely (e.g., `h = 1000000` when `s.now = 0`) and allows `h` to arbitrarily jump backwards during subsequent `.spend` steps as long as the loose inequality holds. This creates a physically unrealistic adversary model.
   **Fix:** Store the host's current clock reading in `ESt` and enforce monotonicity (`h ≥ last_h`) as well as a strict upper bound (`h ≤ s.now + C.σ`) in the `legal` check.

**Overclaims:**
- Claims "latency is high" and "hosts are partitioned" across a datacenter, yet the formalism models state settlement as an instantaneous shared-memory read.
- Claims `datacenter_example` demonstrates when escrow is "settleable" on legal traces, but the proof is exclusively an arithmetic identity (`60 + 4 = 64`) disconnected from the trace semantics.
- Claims `crash` models durable state, but implements it as a global no-op that leaves the host fully online, contactable, and capable of immediately spending again.

### File ControlStack/Families/F6/MonitorEnsemble.lean

**Verdict:** Tautological probability theory lacking axiomatic bounds, with a completely unformalized ensemble composition.

**Defects:**
1. **Location:** `indep_escape` and `mixture_escape_eq`.
   **Problem:** Independence is asserted tautologically rather than formalized as a statistical property of random variables.
   **Instance:** The definition `indepW` explicitly hardcodes the joint distribution as the algebraic product of the marginal rates. The theorem then trivially evaluates this product definition to show that the resulting probability equals the product. This proves nothing about the statistical independence of distinct monitor variables.
   **Fix:** Define a formal probability space, define monitors as independent random variables, and prove that their joint distribution factorizes into the product of marginals.
2. **Location:** `ensemble_adaptive`.
   **Problem:** Vacuous ensemble composition.
   **Instance:** The theorem claims to model an ensemble acting as ONE monitor, but the formalized theorem entirely omits the $m$ individual monitors. It instead takes a generic single monitor `K` (with single-monitor output type `Y × AOut Unit`) and manually assumes its miss rate is $e$. The actual aggregation of $m$ monitors into $K$ is unformalized.
   **Fix:** Define an ensemble aggregator that explicitly maps the joint outputs of $m$ monitors to a single `AOut Unit` and formally prove that this constructed $K$ satisfies the $e$ bound based on `mixture_escape_eq`.
3. **Location:** `ensemble_example`.
   **Problem:** Vacuous execution claim.
   **Instance:** The theorem asserts expected attack rounds for a 3-monitor ensemble against an adaptive attacker, but the formal proof merely evaluates real arithmetic (e.g., `1/20 + (1 - 3/5)^3 = 57/500`) and standard geometric bounds. It applies no adaptive adversary traces to an ensemble protocol.
   **Fix:** Construct an explicit instantiation of the $m$-monitor ensemble protocol and apply `ensemble_adaptive` to prove trace bounds on its actual execution.
4. **Location:** `indepW_nonneg`, `indep_escape`, and `blind_spot_escape`.
   **Problem:** Missing probability space axioms allow unphysical, meaningless evaluations.
   **Instance:** The function `P` and the mixture distributions entirely omit domain restrictions. Variables like $q_j$ (miss rates), $r_j$ (recalls), and $b$ (blind spot weight) are never bounded within $[0, 1]$. The formalism will happily compute negative "probabilities" or probabilities exceeding $1$ without contradiction.
   **Fix:** Add explicit boundary hypotheses (e.g., `0 ≤ q j ≤ 1`, `0 ≤ b ≤ 1`, `0 ≤ r j ≤ 1`) to ensure the weight functions constitute mathematically valid probability distributions.

**Overclaims:**
- Claims the file establishes an "independence premise" and "indep_escape" properties, but it merely evaluates a explicitly defined product formula.
- Claims `ensemble_adaptive` proves that "an ensemble ... acts as ONE monitor", when it literally just restates the single-monitor theorem for an arbitrary black-box $K$ without ever modeling an ensemble.
- Claims `ensemble_example` proves adaptive bounds on an ensemble, but it only solves a static arithmetic equation.

### Cross-cutting

- **Vacuous Arithmetic as Proof:** Both files severely abuse Lean's arithmetic tactics to "prove" system behaviors that are actually just algebraic identities. File 1 proves system liveness by asserting `60 + 2 * 2 = 64`; File 2 proves expected attack bounds on a system by asserting `1/20 + (1 - 3/5)^3 = 57/500`. In both cases, the formal systems and trace models are entirely bypassed.
- **Skipping Composition Hardships:** Both models sidestep the core complexity of their respective domains by oversimplifying state boundaries. File 1 ignores network messaging and latency, treating distributed escrow settlement as a shared-memory read. File 2 ignores the statistical aggregation of $m$ distinct agents, modeling the "ensemble" as an unformalized black-box single monitor $K$ that is presumed to magically satisfy the required bounds.
