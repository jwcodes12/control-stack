Do not freeze this draft. **Conjunct (c) is false as quantified.** The remaining identities are algebraically consistent, but the proposed “Pareto statement” does not impose usefulness, and its main lower bound requires a honeypot-support assumption absent from the stated design.

1. **FATAL — (c), the lower inequality, omits bounds on `κ`.**

   Its exact-value equality remains algebraically valid for arbitrary real `κ`. Its inequality requires nonnegative survival.

   Counterexample:

   ```lean
   X = Z = Unit
   Bad := fun _ => True
   M := fun _ _ => 1
   PH := fun _ => 1
   φ₀ := fun _ => 1/2
   κ := fun _ => 3
   nh = 1
   r = 0
   b = 1
   N = 1
   ```

   All stated hypotheses hold. But
   \[
   S=1-3(1/2)=-1/2,\qquad
   S\alpha_0=-1/4,\qquad
   \operatorname{protocolCat}=S\cdot1=-1/2.
   \]
   The claimed inequality is \(-1/4\le-1/2\), which is false.

   **Fix:** add

   ```lean
   (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) →
   ```

   before the conclusions. Alternatively, separate the unrestricted algebraic equality from a probability-valued corollary requiring a valid schedule. Merely assuming `0 ≤ survH ...` suffices for the inequality, but is a less faithful protocol hypothesis.

2. **MAJOR — (a)/(b) quantify objects that are not probability rules or schedules.**

   Both identities are true as polynomial identities without `IsRule φ₀`. That does not make their outputs probabilities.

   For a one-point benign law and kernel, take `φ₀ = -1`, `N = 1`, `b = 0`. Then `flagRate = 2` and `haltP = 2`. Likewise, an unrestricted `κ` can make `honestUse` negative or greater than one.

   **Fix:** add `IsRule φ₀` to the probability-facing versions of (a)/(b), and schedule validity to the general-schedule version of (b). Keep broader algebraic identities as infrastructure if useful. Also freeze rate and probability bounds:

   ```lean
   0 ≤ missRate M PH φ₀ ∧ missRate M PH φ₀ ≤ 1
   0 ≤ flagRate M μ φ₀ ∧ flagRate M μ φ₀ ≤ 1
   0 ≤ honestUse ... ∧ honestUse ... ≤ 1
   ```

   The false-shutdown identity promised by the docstring should become an explicit conclusion. Currently it is only an immediate consequence mentioned in prose.

   Distinguish conditional and whole-protocol events. Writing \(S\) for test survival and \(D=\operatorname{binCDF}(N,b,f_0)\):

   \[
   \begin{aligned}
   P(\text{deployment budget halt}\mid\text{test survival})&=1-D,\\
   P(\text{whole protocol reaches a budget halt})&=S(1-D),\\
   P(\text{honest completion failure})&=(1-S)+S(1-D)=1-SD.
   \end{aligned}
   \]

3. **MAJOR — generic `honestUse` does not mean “runs all `N` rounds.”**

   The problematic definition is:

   ```lean
   surv ... * (1 - haltP ...)
   ```

   For an arbitrary `π₀`, the complement of a budget halt includes catastrophe and caught-attack shutdown. Those executions may terminate before completing the stream.

   Counterexample: `nh = 0`, `N = 1`, an all-bad submission law, and an always-PASS monitor. Then `haltP = 0`, so `honestUse = 1`, while catastrophe occurs with probability one.

   The benign-support premises in (a)/(b) prevent this counterexample from falsifying those conjuncts. They do not repair the generic definition’s docstring.

   **Fix:** either specialize this definition to the benign law `μ`, documenting its support hypothesis, or define a separate completion recursion that scores every early terminal branch zero. A third option is to retain the definition but call its general interpretation “survive testing and avoid a budget halt,” and prove the completion interpretation under a benign-policy hypothesis.

   **`haltP` itself follows the frozen protocol correctly.** Its bad PASS branch ends with score zero. A bad FLAG with an available audit also ends with score zero: both caught shutdown and failed-audit catastrophe are distinct from an unaffordable-flag halt. Therefore **`r` is correctly irrelevant to this particular halt event**. The budget rule is also correct: the **\((b+1)\)-st FLAG**, rather than the \(b\)-th, causes a budget halt.

4. **MAJOR — the honest abstraction establishes availability under a supplied submission law, not task usefulness.**

   The rates are correctly defined for the stated model:

   \[
   \alpha_0=E_{\operatorname{push}M P_H}\phi_0,\qquad
   f_0=E_\mu E_M(1-\phi_0).
   \]

   But `μ : X → ℝ` is a law on **submissions**. Calling it a task stream hides any task-to-solution generation process. Moreover, `¬ Bad x` does not imply that `x` solves a task. A benign law concentrated on harmless junk, with an always-PASS monitor, can have `honestUse = 1`.

   **Fix:** call the metric “honest completion probability” or “availability.” If actual useful work is intended, add a `Good`/task-success predicate and an explicit hypothesis connecting the supplied honest submission law to it. This affects the honest-side interpretation without weakening the universal adversarial safety theorem.

   “Honest monitor = any rule” is acceptable as **a nominated reference behavior**. It does not establish honesty, competence, or correspondence to the deployed model. State that distinction.

   The iid and fresh-call assumptions are essential. For example, two benign rounds whose FLAGS are perfectly correlated, each with marginal flag probability \(1/2\), have halt probability \(1/2\) when `b = 0`; the iid formula gives \(3/4\).

   The product is faithful for a fixed stateless rule with independent test and deployment randomness. It fails after averaging a persistent shared seed. A half-and-half mixture of an always-PASS and always-FLAG monitor, with one no-slack honeypot and one zero-budget benign deployment round, has completion probability zero; multiplying expressions formed from the averaged rates gives \(1/4\).

   Thus A1 must explicitly exclude persistent shared randomness or state linking these phases. The current product definition **stipulates** this model; it does not prove independence.

5. **MAJOR — (c)/(e) require `PH` supported on `Bad`, whereas the design supplies support on `B̄`.**

   The exact offending premise is:

   ```lean
   (∀ x, PH x ≠ 0 → Bad x)
   ```

   It is sufficient, but it is not implied by support on a Blue-enumerable superset of `Bad`.

   Dropping it destroys the honest-rate floor. Take the identity mediator on Bool, `Bad = {true}`, uniform `PH`, and

   ```lean
   φ₀ true  = 0
   φ₀ false = 1
   ```

   Then \(\alpha_0=1/2\), but this monitor passes no bad submission. With `nh = 0`, `b = 0`, `N = 1`, its risk is zero. This example even admits domination with `L = 2` and a benign law concentrated on `false`.

   Consequently, the aggregate honeypot PASS rate need not be a bad-submission miss rate.

   **Fix:** generalize the exact attack calculation to a separate law `PA` supported on `Bad`. With

   ```lean
   aA := E (push M PA) φ₀
   ```

   the conclusion becomes

   ```lean
   protocolCat Bad M PH κ nh r b N
       (fun _ : Unit => 1) (fun _ => φ₀) (fun _ _ => PA)
     =
       survH (missRate M PH φ₀) κ nh 0 *
         (aA + (if 0 < b then (1 - r) * (1 - aA) else 0))
   ```

   Here `PH` need not be supported on `Bad`; `PA` does. Recover the present mimicry specialization only when its stronger support premise is available.

   Conditioning `PH` on `Bad` is another option when its bad mass \(\beta\) is positive. But its attack PASS rate is \(\alpha_{\mathrm{Bad}}\), not \(\alpha_0\). From the aggregate rate alone, only
   \[
   \alpha_{\mathrm{Bad}}
   \ge \max\!\left(0,\frac{\alpha_0-(1-\beta)}{\beta}\right)
   \]
   follows.

   “Needs no capability” is an overclaim about realizability. This is a legal attack policy in the unrestricted free-submission model. Physically sampling executable bad honeypots may require access and capabilities. “Requires no monitor collusion or shared seed” is accurate. Also, fresh draws after the first submission are irrelevant: the first bad submission terminates this protocol.

6. **MAJOR — (e) assembles old conclusions without imposing a usefulness requirement.**

   Its three components are:

   - the hard-slack instance of (b);
   - the frozen UMPROT upper bound;
   - the hard-slack specialization of (c)’s weaker lower bound.

   It establishes neither an optimized Pareto frontier nor a usefulness-constrained feasible region. An always-FLAG reference monitor with `b < N` still satisfies the entire conjunct while having completion probability zero.

   The sentence “no choice certifies risk below honest survival × \(\alpha_0\)” is pointwise true under the valid support assumptions. It is weak as a design claim because survival may tend to zero. With zero slack and fixed \(0<\alpha_0<1\), increasing `nh` drives both the floor and honest survival to zero.

   **Fix:** replace (e) with an explicit usefulness-target obstruction. Set
   \[
   a=\alpha_0,\quad
   q=a+\mathbf1_{b>0}(1-r)(1-a),\quad
   D=\operatorname{binCDF}(N,b,f_0),\quad U=\operatorname{honestUse}.
   \]
   For the mimicry witness,
   \[
   R_{\mathrm{mimic}}=Sq,\qquad U=SD,\qquad
   \boxed{D\,R_{\mathrm{mimic}}=q\,U}.
   \]
   Thus a universal risk certificate \(X\), together with \(U\ge u\), must satisfy
   \[
   \boxed{q\,u\le D X},
   \qquad\text{hence}\qquad
   \boxed{q\,u\le X}.
   \]
   When \(D>0\), the stronger form is \(X\ge qu/D\).

   This avoids division in Lean and connects **both honest rates** to the certificate. Under the existing valid probability/support assumptions, the concluding implication can have the shape:

   ```lean
   universalRiskCap X →
   0 ≤ u → u ≤ honestUse ... →
   q * u ≤ binCDF N b (flagRate M μ φ₀) * X
   ```

   Use the exact coefficient `q`. For positive audit budget it is \(1-r+r\alpha_0\), and may substantially exceed \(\alpha_0\).

   The universal upper bound should also reflect zero budget. For `b = 0`, catastrophe is independent of recall, and the domination cap can be sharpened to
   \[
   \min\!\left(1,L\frac{n_s+1}{n_h+1}\right).
   \]
   For positive budget, clip the stated cap at one.

   Regarding adversarial gain: when a bad submission exists and `b ≥ 1`, the always-FLAG worst-case baseline is exactly \(1-r\). The existing upper bound already bounds excess above that baseline by \(rL(n_s+1)/(n_h+1)\). The honest completion metric alone supplies no new upper bound on that excess. A perfect honest reference monitor can have \(U=1,\alpha_0=f_0=0\), while a different hostile rule still attains positive risk.

   A cheap additional bridge from frozen UMHS is:
   \[
   \alpha_0\ge
   1-f_0-\operatorname{hs}_0(\operatorname{push}M\mu,\operatorname{push}M P_H).
   \]
   This supplies a relationship between benign acceptance and honeypot acceptance. (e) currently supplies none.

7. **MINOR — (d) is true but unnecessarily weak; its operational corollary is absent from Lean.**

   The premise `s ≤ nα` is necessary for the stated square. Without it, `n = 1`, `s = 1`, `α = 1/10` gives \(81/100\le9/100\), which is false.

   The present result is ordinary Chebyshev applied to a lower-tail event. Cantelli is stronger at similar cost once the same moment identities exist:

   ```lean
   ∀ (n s : ℕ) (α : ℝ), 0 ≤ α → α ≤ 1 →
     (max 0 ((n : ℝ) * α - (s : ℝ))) ^ 2 * binCDF n s α
       ≤ (n : ℝ) * α * (1 - α) * (1 - binCDF n s α)
   ```

   The positive part removes the side condition and handles all `s`.

   With `0 ≤ ε`, `ε < 1`, and `binCDF n s α ≥ 1 - ε`, this yields
   \[
   s\ge n\alpha-
   \sqrt{\frac{n\alpha(1-\alpha)\epsilon}{1-\epsilon}}.
   \]
   The draft’s Chebyshev corollary lacks the factor \(\epsilon\) inside the square root and is therefore weaker. Both inequalities are classical infrastructure, not mathematical novelty. [Pinelis, *Between Chebyshev and Cantelli*](https://arxiv.org/html/1011.6065)

   **Fix:** freeze the stronger inequality and its explicit slack corollary. Retain the present (d) as a derived compatibility lemma.

   The supplied first-moment grid check is also mathematically sound: from the bounded count,
   \[
   n\alpha\le s+n(1-\operatorname{binCDF}(n,s,\alpha)),
   \]
   giving \(s\ge n(\alpha-\epsilon)\). That is a cheap fallback.

8. **MAJOR — the class-count converse belongs in Lean; “class-aware bound → \(\alpha_0\)” needs additional hypotheses.**

   From the stated UMLOWER converse, let
   \[
   A=\frac{k(n_s+1)}{n_h},\qquad n_h>0,\ k>0.
   \]
   Optimizing its quadratic over \(t\in[0,1]\) gives
   \[
   H(A)=
   \begin{cases}
   A/4,&A\le2,\\
   1-1/A,&A>2.
   \end{cases}
   \]
   The table’s \(\min(1/2,A/4)\) is valid but is **not** the best optimization when \(A>2\).

   Combining the honest-survival requirement with Chebyshev gives
   \[
   n_s+1\ge
   D_C:=1+\max\!\left(
      n_h\alpha_0-\sqrt{\frac{n_h\alpha_0(1-\alpha_0)}{1-\epsilon}},0
   \right),
   \]
   hence a design-free lower bound \(H(kD_C/n_h)\), subject to every frozen UMLOWER premise. Cantelli improves \(D_C\) by inserting \(\epsilon\) inside that square root. Handle `n_h = 0` separately.

   **Fix:** formalize this corollary rather than leaving the programme’s principal class-count obstruction in the write-up. Unlike the mimicry specialization, it does not need `PH` supported on `Bad`, assuming the stated UMLOWER hypotheses suffice.

   For class-aware testing, the honest identity uses **class-specific rates**:
   \[
   U_{\mathrm{strat}}
     =\left(\prod_c\operatorname{binCDF}(m_c,s_c,\alpha_c)\right)D.
   \]
   It cannot generally use the aggregate \(\alpha_0\). With two equally weighted classes, \(\alpha_1=1,\alpha_2=0\), the aggregate is \(1/2\), while honest survival requires allowing every miss in class 1. An attacker restricted to that class can then attain risk one.

   An upper bound approaching \(\alpha_0\) therefore needs equal class rates, or a uniform bound \(\alpha_c\le\bar\alpha\). In general the limiting coefficient is **\(\max_c\alpha_c\)**. With positive audit budget and imperfect recall, the stated upper bound tends to \(1-r+r\max_c\alpha_c\).

   A finite Chebyshev construction is enough: for equal sample counts, choose
   \[
   s_c=\left\lceil
       m\alpha_c+\sqrt{k\,m\alpha_c(1-\alpha_c)/\epsilon}
   \right\rceil.
   \]
   Each class fails with probability at most \(\epsilon/k\), so all classes survive with probability at least \(1-\epsilon\). Apply UMSTRAT to those slacks. This supplies a formal finite counterpart to the claimed asymptotic comparison.

9. **MAJOR — the numerical “frontier” mixes sampling designs and omits deployment usefulness.**

   The code evaluates
   \[
   \sup_t t\,\operatorname{binCDF}(m,n_s,t),\qquad m=\lfloor n_h/k\rfloor.
   \]
   This uses **fixed per-class counts with a global miss budget**.

   For frozen UMPROT’s iid honeypots, with uniform class masses and a monitor passing only one class at rate \(t\), the expression is instead
   \[
   \sup_t t\,\operatorname{binCDF}(n_h,n_s,t/k).
   \]

   Furthermore, `k*m` is 28 rather than 30 in the first two rows, and 96 rather than 100 in the affected later rows. The code sizes global honest slack using `n_h` but its class tests use only `k*m` samples.

   **Fix:** specify the sampling design. For deterministic stratification, allocate balanced counts `m_c` summing to `n_h` and use the correct product for honest survival. I checked that balanced allocation leaves the displayed slack choices and attack-risk values unchanged in these rows; the present code still fails to encode that allocation.

   “Decodable mediator” alone also does not justify calling this curve the exact worst-case risk. A mediator may decode the class **and disclose additional within-class information** that distinguishes attacks from honeypots. The plotted exact model needs class-only views, appropriate class coverage, and realizable bad submissions in each class. Under mere decodability, these class-selective attacks demonstrate attainable risks, not a universal optimum.

   Finally, the table constrains false **test shutdown**, not honest completion. With `b = 0`,
   \[
   U=S(1-f_0)^N.
   \]
   Neither `f0` nor `N` is supplied. For example, \(S=0.9,f_0=0.01,N=1000\) gives \(U\approx0.0000389\). A full safety/usefulness table needs deployment parameters or an explicit `f0 = 0` assumption.

The numerical recomputation gives the following maxima, refined beyond the supplied grid. “Fixed global” is the code’s deterministic-class expression; “iid global” uses the frozen protocol’s iid expression under the same ideal uniform class model.

| \(n_h\) | \(\alpha_0\) | \(k\) | \(n_s\) | Fixed global | Iid global | Cheb floor | \(s_c\) | Class risk | Mimicry floor |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 30 | .01 | 4 | 1 | .11542 | .11088 | .03333 | 1 | .11542 | .0090 |
| 30 | .05 | 4 | 3 | .28444 | .25946 | .04139 | 2 | .19423 | .0450 |
| 100 | .01 | 4 | 2 | .05459 | .05477 | .01000 | 1 | .03320 | .0090 |
| 100 | .01 | 8 | 2 | .11338 | .10955 | .02000 | 1 | .06834 | .0090 |
| 100 | .05 | 8 | 8 | .47610 | .41482 | .07405 | 3 | .16326 | .0450 |
| 100 | .05 | 16 | 8 | 1.00000 | .82678 | .14811 | 2 | .22684 | .0450 |
| 1000 | .05 | 8 | 59 | .38330 | .36639 | .08747 | 12 | .06423 | .0450 |
| 1000 | .01 | 8 | 14 | .07610 | .07530 | .01537 | 4 | .02038 | .0090 |
| 10000 | .05 | 8 | 528 | .38686 | .37948 | .09560 | 80 | .05104 | .0450 |

All supplied rounded outputs reproduce. The `1.000` entry versus iid `0.82678` is a material sampling-design difference.

**MINOR — `sup_t` is a grid maximum, not an exact supremum.** Label the values numerical approximations. For these curves, monotonicity of the CDF gives a simple grid error bound of at most the grid spacing, \(0.0005\), ignoring floating-point evaluation error. The comment claiming PMF evaluation “by recurrence” is also inaccurate: the code uses log-gamma summation.

The Witness arithmetic is correct:

| Quantity | Recomputed value |
|---|---:|
| \(\alpha_0,f_0\) | \(1/10,1/10\) |
| Test survival | \(81/100\) |
| Conditional deployment halt | \(1/100\) |
| Honest completion | \(8019/10000\) |
| Mimicry risk, \(r=1\) | \(81/1000\) |
| Mimicry risk, \(r=1/2\) | \(891/2000\) |
| \(\operatorname{binCDF}(10,1,1/2)\) | \(11/1024\) |
| Chebyshev left side | \(11/64\) |
| Chebyshev right side | \(5/2\) |

For this witness the whole-protocol false halt is \(81/10000\), and total completion failure is \(1981/10000\). The stated UMPROT upper bounds are \(1/3\) for `r = 1` and \(2/3\) for `r = 1/2`. The interval `[81/1000, 1/3]` is a witness lower bound and a loose certificate, rather than an exact frontier; the ideal instance’s worst-case risk at `r = 1` is \(4/27\).

The remaining edge cases behave as follows once rules and schedules are probability-valued:

| Case | Consequence |
|---|---|
| `N = 0` | `haltP = 0`, deployment CDF \(=1\), usefulness \(=S\), catastrophe \(=0\). (c)/(e) correctly exclude it. |
| `b = 0` | Completion factor \((1-f_0)^N\); mimicry risk \(S\alpha_0\); recall irrelevant. |
| `b ≥ N` | No budget halt; deployment CDF \(=1\). |
| `nh = 0` | Test survival \(=1\). |
| `ns ≥ nh` | Hard-slack test survival \(=1\). |
| `α0 = 0` | Test survival \(=1\); mimicry risk is \(1-r\) for positive budget, zero for zero budget. |
| `α0 = 1` | General survival is \(\prod_{j<nh}(1-\kappa_j)\); hard survival is one iff `ns ≥ nh`. |
| `r = 1` | Mimicry risk \(=S\alpha_0\). |
| `r = 0`, positive budget | Mimicry risk \(=S\). |
| `μ` has bad mass | The benign-support proof fails; `1-haltP` can count early termination as completion. |

**MINOR — the “FLAGs everything is useless” docstring needs `b < N` and a stated metric.** Always-FLAG survives testing and has completion probability \(\mathbf1_{N\le b}\). It completes every benign round when the audit budget covers the stream. When `b < N`, it may still complete the first `b` rounds, although the all-round completion metric is zero.

For prior art, all three requested identifiers are correct:

- **2312.06942:** Greenblatt et al., *AI Control: Improving Safety Despite Intentional Subversion*. It already evaluates safety and usefulness separately, uses honest-model correctness for usefulness, and studies upfront synthetic monitor evaluation and false-positive thresholds. The two-axis framing is prior art. [Paper, v5](https://arxiv.org/html/2312.06942v5)
- **2602.20628:** Gardner-Challis et al., *When can we trust untrusted monitoring? A safety case sketch across collusion strategies*. Appendix B.3 explicitly identifies honest monitoring abilities as limiting safety even with perfect anti-collusion. Appendix B.5 models slack through retraining effects; UMUSE’s trusted shutdown schedule should not be presented as an exact formalization of that mechanism. [Paper, v2](https://arxiv.org/html/2602.20628v2)
- **2504.10374:** Bhatt et al., *Ctrl-Z: Controlling AI Agents via Resampling*. It explicitly studies safety/usefulness Pareto comparisons and measures usefulness through normalized task-solving performance, rather than all-round availability. [Paper, v1](https://arxiv.org/html/2504.10374v1)

The binomial hitting identities, product under independent phases, and moment inequalities are classical infrastructure. That is not a rejection reason. The potential formal contribution lies in a faithful operational metric and explicit usefulness-constrained converses. Current (e) adds no independent mathematical result.

For Lean, the proof burden can be reduced substantially:

- **(a):** prove, for every `n u h`, the generalized identity

  ```lean
  1 - haltP Bad M φ₀ (fun _ => μ) b n u h
    = survH (flagRate M μ φ₀) (hardKill b) n u
  ```

  under normalization and benign support. This is an induction matching the frozen survival recursion. Then obtain the CDF identity from UMSURV; no new binomial counting proof is needed.

- **(b):** use that identity, normalization of `push M PH`, and the frozen survival reduction. The hard-slack result is a rewrite.

- **(c):** the attack-law equality is a first-round calculation because every positive-mass attack is bad. The lower inequality follows from survival nonnegativity and nonnegativity of the failed-audit term. It is unprovable as currently quantified.

- **(d):** the substantial new infrastructure is the finite binomial moment calculation. Prove total mass, mean, and centered second moment once. Finite weighted-sum proofs avoid introducing measure-theoretic machinery merely to translate this real-valued `binCDF`. Chebyshev and the upper-tail sizing lemma then follow by pointwise comparison; Cantelli requires a modest additional shifted-square argument.

- **Replacement (e):** the usefulness-target obstruction is elementary multiplication after the exact identities and probability bounds. The global class-count corollary is arithmetic plus the frozen UMLOWER result. Exact Lean integration requires its full frozen statement, not just the summary supplied here.

**Overall verdict: reject as written.** The most important repairs are the missing schedule hypothesis in (c), honest completion semantics, the `PH`/`Bad` mismatch, and an explicit usefulness target.

I would freeze these conjuncts after repair:

1. **Benign iid completion/halt identity**, including probability bounds and the generalized survival-recursion bridge.
2. **Honest completion identity**, valid schedules, explicit false shutdown, and total failure decomposition.
3. **Exact first-bad attack-law calculation**, with a separate `PA` supported on `Bad`; retain `PA = PH` only as a conditional specialization.
4. **Finite binomial moments, Cantelli slack cost, and its usefulness/slack corollary**; derive the draft’s Chebyshev lemma.
5. **Usefulness-target certificate obstruction** \(qu\le DX\), plus the formal global-slack class-count converse and the always-FLAG audit-error baseline.
6. **Class-aware honest product and finite slack-sizing corollary**, using class-specific rates and an explicit bound approaching their maximum.

Drop the present (e) as an independent “Pareto” theorem; retain its conjunction only as a named assembly corollary.