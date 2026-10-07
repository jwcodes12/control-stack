**Verdict: MAJOR. Do not freeze v0.** I find no false displayed mathematical conjunct. The defects concern what those conjuncts certify, the missing connection to deployment, and the claim that this is already a finite certificate checker.

I checked the snippet using Lean 4.35.0-rc3 and mathlib, and kernel-checked `Witness`, the toy risk identities, `IsPolicy clocked`, the quadratic bound, and `Vstar exG 2 1 = 5/8`. I did not prove the entire `Claim`.

**1. FATAL to the deployment interpretation — Boolean policies do not cover arbitrary code-generating policies without an abstraction hypothesis.**

Exact location: the programme’s “for every policy the untrusted model could follow,” instantiated through `gac`’s action space `Bool` and fixed `TA/TD/FA`.

T1 quantifies over every policy **of the supplied abstract game**. It does not establish that every actual model policy induces such a game. In particular, an empirical suspicion-score distribution conditional on “backdoored” need not remain valid when an adversary chooses the task, vulnerability, obfuscation, or attack timing.

Allowing arbitrary Boolean attack schedules removes a restriction on **when** to attack. It does not remove restrictions on **how effectively** the adversary can evade monitoring.

Concrete fix: make a uniform conditional abstraction hypothesis explicit. For every reachable concrete history, every concrete output, and every relevant private-information condition, the probabilities of catastrophe and continuation into each abstract state must belong to the admissible row set. Also require that concrete catastrophes are represented by the abstract catastrophe event.

The resulting deployment theorem should have the shape

\[
\text{ConditionalRowsCovered}
\land \text{CatastropheRepresented}
\land \text{CertificateAccepted}
\Longrightarrow
\forall\text{ concrete Red policies},\quad
\Pr(\text{catastrophe within }N)\le V_N(s_0).
\]

This is compatible with a capability-free programme: the conditional hypotheses concern trusted components and the abstraction. A fitted ROC alone does not establish them.

**2. MAJOR — `RiskCert` is neither finite nor computably checkable as defined.**

Exact definition:

```lean
∀ th, adm th → ∀ n s a, ...
```

There are two independent problems:

- `n : ℕ` is unbounded.
- `Θ` is unrestricted; admissible models can form an infinite continuum.

Even finite quantification over arbitrary real-valued functions is not an executable rational checker.

Concrete fix: retain the global predicate as infrastructure, but make the campaign theorem use a horizon-bounded predicate:

```lean
def RiskCertUpTo {S A Θ : Type} [Fintype S] (N : ℕ)
    (G : Θ → Game S A) (adm : Θ → Prop)
    (V : ℕ → S → ℝ) : Prop :=
  (∀ s, 0 ≤ V 0 s) ∧
  ∀ th, adm th → ∀ n, n < N → ∀ s a,
    (G th).cat n s a +
      ∑ s', (G th).K n s a s' * V n s'
      ≤ V (n + 1) s
```

Use a corresponding `LawfulUpTo`; a finite checker cannot establish your current all-horizons `Lawful` from a finite input table.

For finitely many rational models, an executable core can look like this:

```lean
def checkRiskQ (N m k t : ℕ)
    (cat : Fin t → Fin N → Fin m → Fin k → ℚ)
    (K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ)
    (V : Fin (N + 1) → Fin m → ℚ) : Bool :=
  decide (
    (∀ s, 0 ≤ V 0 s) ∧
    ∀ th i s a,
      cat th i s a +
        ∑ s', K th i s a s' * V i.castSucc s'
        ≤ V i.succ s)
```

Both fragments above compile locally. The second still needs a lawfulness checker and a proved rational-to-real soundness bridge.

For \(N=100,C=2\), the value table has 303 entries and a single model requires 600 Bellman inequalities, plus base checks. That is a concrete finite checking task.

**3. MAJOR — nature models adaptive switching, which can be strictly stronger than a fixed unknown model.**

Exact definition:

```lean
θ : Ω → RHist S A → S → A → Θ
```

Nature knows the seed and the realized action, then selects a possibly different model after every history. Thus the theorem covers the rectangular closure of the admissible conditional rows. It preserves no requirement that one parameter or ROC law governs the entire episode.

This is sound conservatism, but it is not interchangeable with fixed-model uncertainty.

A two-round, one-state, one-action example demonstrates the difference:

| Model | First-round `(cat, K)` | Last-round `(cat, K)` | Fixed-model risk |
|---|---:|---:|---:|
| A | `(1/2, 1/2)` | `(0, 1)` | `1/2` |
| B | `(0, 1)` | `(1/2, 1/2)` | `1/2` |

Switching from A to B gives risk \(1/2+(1/2)(1/2)=3/4\). This distinction is standard in robust dynamic programming; rectangularity is a substantive uncertainty assumption. [Iyengar, *Robust Dynamic Programming*](https://pubsonline.informs.org/doi/abs/10.1287/moor.1040.0129).

Concrete fixes:

- Name T1 “soundness for adaptive admissible conditional rows.”
- Prefer row-local admissibility, such as `adm n s a th`, for conditional transition uncertainty.
- Add a separate fixed-model corollary using

```lean
risk (fun _ : Unit => G th) (fun _ _ _ => ()) σ N s₀ []
```

For useful fixed-model certificates, allow `V th` and prove every admissible model’s initial bound is at most `U`. A shared supersolution can otherwise introduce unnecessary switching conservatism.

Nature’s dependence on the seed does **not** falsify T1: the bound holds pointwise for every seed before averaging.

**4. MAJOR — “every observation-restricted Red is a special case” needs an explicit information interface.**

Exact location: the `RHist` documentation and T1’s prose.

This holds for observations determined by the encoded history and current state. It does not automatically cover additional signals about hidden monitor state, task difficulty, future randomness, or omitted environment state.

A precise observation restriction can be expressed through a lift:

```lean
def liftObs {S A O : Type}
    (obs : RHist S A → S → O)
    (π : O → A → ℝ) : RHist S A → S → A → ℝ :=
  fun h s a => π (obs h s) a
```

Here `O` can encode an entire observation history. Prove the policy and risk-bound preservation lemmas. Signals outside this interface require state augmentation or conditional-row coverage under those signals.

Seeding itself is not the problem:

- At a fixed finite horizon, finite states and actions give finitely many deterministic contingent plans. Finite seeds can represent arbitrary mixtures over those plans.
- This realization argument is currently absent.
- A continuously sampled `β` is not literally covered by the finite-`Ω` T4 conjunct. Add an integration corollary if that wording is retained.
- Mixed and behavioral strategies cannot be identified indiscriminately under imperfect recall.

Also correct “ignores history” to **“ignores history conditional on the seed.”** An episode-level mixture over `β` can induce history-dependent posterior action probabilities after conditioning on survival or previous actions.

**5. MAJOR — T4 proves no “exactly when” result, and its scalar bound is not a `RiskCert`.**

Exact conjunct:

```lean
(∀ b, 0 ≤ b → b ≤ 1 → risk ... (memoryless b) ... ≤ U) →
  ∑ ω, ρ ω * risk ... (memoryless (β ω)) ... ≤ U
```

This is weighted averaging. It establishes neither a necessity direction nor a characterization of when fixed-rate policies are without loss.

Calling `sup_beta` a Bellman certificate is especially misleading. In the toy, its value is `49/160`; no T1 certificate can have that initial bound because the clocked policy attains `5/8`.

Concrete fix: rename this a **fixed-rate risk bound** and remove “exactly.”

A genuine per-instance “without loss” theorem could characterize stationary fixed-rate optimality through Bellman slack:

\[
d(n,s,a)=V^\star_{n+1}(s)
-\left(\mathrm{cat}(n,s,a)+\sum_{s'}K(n,s,a,s')V^\star_n(s')\right).
\]

A fixed rate is full-information optimal exactly when its supported actions have zero slack at every state/time reached with positive continuation probability. Prove this using a performance-difference identity.

Useful sufficient conditions are possible—for example, one action simultaneously maximizes every relevant Bellman expression. **Stationarity of the transition laws alone is insufficient: `exG` already ignores `n`.**

“No informative observations” also needs a stationary policy interface and appropriate fresh-randomness assumptions; marginal independence of observations from time is not enough.

**6. MAJOR — T2 is lossless only for the full-information relaxation.**

Exact prose: “the certificate method loses nothing.”

The conjunct is true, but the unrestricted wording is false for observation-restricted adversaries. T5 itself demonstrates conservatism relative to fixed-rate Reds.

Concrete fix:

> `Vstar` is the least supersolution and the exact adversarial value of the fully observed, finite-horizon game. It upper-bounds observation-restricted values.

The attaining policy is deterministic and **time-dependent Markov**, not necessarily stationary. Your length-invariance conjunct correctly permits this.

There is no `Finset.sup'` obstruction. Mathlib provides:

```lean
Finset.exists_mem_eq_sup'
Finset.le_sup'
Finset.sup'_le
```

Choose an action maximizing the expression at continuation horizon `n`. For an episode of length `N`, use:

```lean
fun h s a =>
  if a = argmaxAction G (N - (h.length + 1)) s then 1 else 0
```

with `classical` for action equality. Prove attainment using the invariant

```lean
h.length + remaining = N
```

Histories beyond the episode can receive arbitrary normalized actions. `[Nonempty A]` supplies an action even at unused histories.

**7. MAJOR — `gac` lawfulness does not establish fidelity to GAC.**

Exact conjunct: the first T4 conjunct proves only `Lawful (gac ...)`.

Calculating directly from the draft, the transition table is:

| Action/state | Catastrophe | Continuation | Safe termination |
|---|---:|---|---:|
| Backdoor, `c > 0` | `1 − TD` | `TD − TA` at `c` | `TA` |
| Backdoor, `c = 0` | `1 − TD + TA` | `TD − TA` at `0` | `0` |
| Safe, `c > 0` | `0` | `FA` at `c−1`, `1−FA` at `c` | `0` |
| Safe, `c = 0` | `0` | `1` at `0` | `0` |

Thus the draft handles safe audits consuming coins, deferral continuing, caught backdoors terminating safely, and attempted audits without coins running the code.

The restricted adapter corresponds to GAC’s perfect-auditor, memoryless-threshold case. GAC’s thresholds depend on `(m,c)`; its zero-coin threshold convention assumes no attempted audit. Pin the cited version and specialization. [GAC §4 and Appendix C](https://arxiv.org/html/2409.07985v2).

Concrete fixes:

- Define threshold parameters `qa`, `qd`, with `0 ≤ qa ≤ qd ≤ 1`.
- For the shared ROC `f`, set

\[
TA(n,c)=f(qa(n+1,c)),\quad
TD(n,c)=f(qd(n+1,c)),\quad
FA(n,c)=qa(n+1,c).
\]

- Prove the actual zone probabilities, including score-boundary conventions for discrete laws.
- Prove contraction of the paper’s state/initial phase into your per-problem transition.
- Prove `risk = 1 − safetyRecurrence`, including the zero-coin boundary.

Your indexing is correct **if those definitions use `n+1`**: `risk ... (n+1)` describes a problem with `m=n+1` remaining. Using `qa n c` would introduce an off-by-one error.

For example, defining `z_m(c)=1-risk_m(c)`, the draft entails, for `c>0`,

\[
z_{n+1}(c)=
\beta TA+
[\beta(TD-TA)+(1-\beta)(1-FA)]z_n(c)
+(1-\beta)FAz_n(c-1).
\]

At `c=0`,

\[
z_{n+1}(0)=[1-\beta+\beta(TD-TA)]z_n(0).
\]

These are the identities the bridge should prove. Neither is stated in `Claim`.

**8. MAJOR — T3 permits non-probabilistic kernels, and GAC usefulness cannot be recovered from `TA/TD/FA`.**

Exact hypothesis:

```lean
∀ n s s', 0 ≤ Kh n s s'
```

T3 is a true monotone-recursion lemma. Calling `ER` an expected reward of an honest Markov chain additionally requires row normalization or substochastic rows with zero-reward termination.

Counterexample to the probabilistic interpretation: a singleton state, `Kh = 2`, and `rew = 1` gives `ER 2 = 3`, although two rounds of unit reward cannot total three.

Concrete fix: add

```lean
∀ n s, ∑ s', Kh n s s' ≤ 1
```

and an explicit reward interpretation.

For GAC, introduce the missing safe audit-or-defer probability `FD`, satisfying `FA ≤ FD ≤ 1`. With a perfect auditor:

```lean
Kh n c c' := (gac C TA TD FA).K n c false c'
rew n c := 1 - FD n c.val + FA n c.val
```

This counts accepted U solutions: run and successful audit retain U’s solution; defer does not. Under the usual zero-coin convention, `FA n 0 = 0`.

Tie this chain and reward to the **same Blue controller** used in the risk theorem. Otherwise unrelated safety and usefulness certificates can be combined without describing any one protocol. Normalize by `M` only with an explicit `M > 0` condition, or define a separate zero-task convention.

**9. MINOR — the Witness comment misidentifies the certificate; bare `exV` is false as an all-horizons certificate.**

Exact definition:

```lean
| _, c => if c.val = 0 then 1 else 5/8
```

At `n=2`, `c=1`, safe action:

\[
\sum_{c'}K(2,1,\mathrm{false},c')\,exV(2,c')
=\tfrac12+\tfrac12\cdot\tfrac58
=\tfrac{13}{16}>\tfrac58=exV(3,1).
\]

Therefore:

```lean
¬ RiskCert (fun _ : Unit => exG) (fun _ => True) exV
```

The actual `Witness` avoids the error by using `1` beyond horizon two. It is true. The padded function is not `Vstar`; indeed `Vstar exG 3 1 = 13/16`.

Concrete fix: name the padded function and describe it as a two-round certificate extended by the trivial bound `1`. Alternatively use `RiskCertUpTo 2 ... exV`.

The memoryless maximum is exact:

\[
\frac{49}{160}
-\left(\frac78b-\frac58b^2\right)
=\frac58\left(b-\frac7{10}\right)^2.
\]

The polynomial bound even holds for all real `b`; `[0,1]` is needed for its policy interpretation.

**10. MINOR — the numerical comparisons reproduce, but “best fixed beta” is not certified.**

Exact location: `numerics/gac_realistic.py`, the 2,001-point search and midpoint CDF approximation.

For the highlighted parameters, the supplied script returns:

| Class | Computed risk | Parameter |
|---|---:|---|
| Fixed-rate grid maximum | `0.3575223` | `β = 0.065` |
| Last-`j` schedule maximum | `0.6687791` | `j = 13` |
| Full information | `0.7089530` | — |

The schedule indexing is correct: the backward recursion makes attacks occur during the last 13 problems.

These are approximate results. The fixed-rate grid maximum is a lower bound on the continuous maximum of the approximated game, and the CDF table has no rigorous enclosure. Increasing the CDF resolution changes the results slightly while preserving the reported two-decimal comparison.

Concrete fixes:

- Say “fixed-rate grid maximum.”
- Use certified polynomial maximization or an interval upper bound before calling it a fixed-rate certificate.
- Use rational enclosing zone probabilities and check an outward-rounded rational value table.
- Replace “at GAC’s scale” with “a 100-task, two-coin instance using GAC’s fitted score laws.” Its main APPS setting has 1,000 tasks and a 2% audit budget. [GAC v1 §2](https://arxiv.org/html/2409.07985v1).

The two other numerical files were not supplied, so “gaps at every tested instance” remains unaudited. It implies no universal gap: `N=1`, `C=0`, or ineffective auditing give immediate equality cases.

**11. MAJOR — the decision recommendation and novelty framing need revision.**

Exact prose:

> “either hide the round index (and every other clock) … or certify …”

Hiding clocks is not by itself sufficient to justify fixed `β`. One must also control external memory, informative task ordering, changing contexts, shared state, sampler behavior, and any other input that changes conditional action or transition laws.

A clocked attack is a fair counterexample to **extending** the fixed-rate guarantee. It is not a refutation of GAC’s stated adversary class: GAC explicitly restricts Red to a memoryless policy with a null observation. [GAC §3–4](https://arxiv.org/html/2409.07985v1).

The relevant prior art is substantial:

| Work, verified identifier | What it establishes for this review |
|---|---|
| [Mallen et al., *Subversion Strategy Eval*, `2412.12480`](https://arxiv.org/html/2412.12480v4) | Its upfront-auditing game explicitly withholds memory and the current round number. The information restriction is deliberate. |
| [Korbak et al., *A sketch of an AI control safety case*, `2501.17315`](https://arxiv.org/html/2501.17315v1#S7.SS5) | Explicitly discusses nonconstant attack rates, codebase messages, coordinated dates, timestamps, and shared environmental signals. This directly anticipates the clock concern. |
| [Bhatt et al., *Ctrl-Z*, `2504.10374`](https://arxiv.org/html/2504.10374v1#A12) | Appendix L analyzes time-dependent auditing and optimizing a constant attack rate. It does not establish fixed-rate optimality against clocked Reds. |
| [Järviniemi, *Subversion via Focal Points*, `2507.03010`](https://arxiv.org/html/2507.03010v1) | Studies independently designed collusion strategies and shared signals. Relevant to coordination without private memory, rather than this specific trusted-monitor timing gap. |
| [Korbak et al., *How to evaluate control measures…*, `2504.05259`](https://arxiv.org/html/2504.05259v1) | Connects evaluation permissions to deployment context, consistency, and situational awareness. It is a capability-sensitive framework, distinct from your capability-free objective. |

“Bhatt et al.” and the named Ctrl-Z paper are the same reference here.

Timestamps and codebase state are documented concerns. Sequential task identifiers can expose order when the deployment provides them, but whether they reveal the relevant remaining horizon is deployment-specific. Fresh contexts do not remove such observations.

Concrete fix: frame T5 as an exact illustration of audit-budget depletion under a richer information interface. The general warning about clocks and statelessness is established prior art. T1–T3 are classical infrastructure; novelty must reside in the checked artifact, abstraction bridge, uncertainty treatment, and useful instantiated guarantees.

The requested edge cases do not falsify the displayed formulas:

| Edge case | Assessment |
|---|---|
| `N = 0` | `risk = 0`; the certificate base condition suffices. |
| Lawful mass `< 1` | Valid: missing mass is safe termination, provided the concrete abstraction justifies that interpretation. |
| Empty `Θ` or no admissible model | Transition certification can be vacuous. An admissible selector cannot exist in a nonempty playable instance. Require an admissible witness in checker acceptance. |
| Empty `Ω` | Weight normalization is impossible. |
| Singleton `A` | T1/T2 remain true; policy optimization disappears. |
| Negative `V` | T1 needs no extra global nonnegativity assumption. With a lawful admissible model and nonempty actions, certification forces nonnegative values inductively. Empty admissibility permits meaningless negative later values. |
| Nature sees the seed | Covered by the pointwise proof; stronger than some intended uncertainty models. |
| `C = 0` | `gac` correctly runs attempted audits. In this game, always backdooring is optimal because there is no catching sink. |

**Overall verdict: major. Fix in this priority order:**

1. State the concrete conditional-row and catastrophe abstraction hypotheses.
2. Implement the finite rational checker and prove its real-valued soundness bridge.
3. Specify observations, seed semantics, and adaptive versus fixed-model uncertainty.
4. Prove the GAC safety adapter and add usefulness for the same controller.
5. Remove “exactly,” qualify tightness, and correct the Witness and numerical wording.

**The conjuncts I would freeze are:**

1. Finite-horizon lawfulness implies `0 ≤ risk ≤ 1`, with a finite trajectory-probability interpretation.
2. `RiskCertUpTo` bounds every seeded history-dependent policy against adaptive admissible conditional rows.
3. Explicit observation-policy lifting and finite-horizon mixed-policy realization.
4. A separate fixed-unknown-model corollary, optionally using model-indexed certificates.
5. Single-model Bellman leastness and attainment by a deterministic time-dependent Markov policy.
6. Honest substochastic-chain subsolution soundness with explicit reward semantics.
7. Rational checker acceptance implies the real certificate predicate; finite vertex checks cover specified continuous uncertainty polytopes.
8. GAC zone-law lawfulness **and** equality to the specialized safety recurrence, including indexing and zero coins.
9. Fixed-rate bounds are preserved by episode-level mixtures—without “exactly” or a `RiskCert` claim.
10. The exact T5 separation and the correctly named padded Witness.
11. A GAC usefulness certificate tied to the same Blue controller, including `FD` and normalization.
12. A deployment corollary conditional on the explicit abstraction hypotheses.