**Verdict: major revisions before freezing.** I found no false formal conjunct in `Claim`, and no failure of the displayed Witness. The principal defects are overclaims in the docstring: general envelope certificates are not exact, the stated trusted-input list omits `Bad`, and the AOQL identification needs additional restrictions.

I checked the supplied definitions and proved the grid and numerical lower inequality with Lean’s `norm_num`. I did **not** prove `Claim`. `DESIGN.md` and `numerics/umcert_check.py` were unavailable, so I cannot verify the reported random-test counts or correspondence with the DESIGN tables.

1. **MAJOR — blanket exactness overclaims (C) and (G).**

   Exact text: “replaces the Markov step by a one-dimensional certificate … and shows the certificate is EXACT.”

   Three different claims are being conflated:

   - (R) preserves the set of universal upper bounds exactly.
   - (C) replaces attainable bad-view pass rates with an envelope, which can introduce slack.
   - (G) replaces a continuous curve with rectangle bounds, which introduce further slack.

   Even a **sharp** domination constant need not produce an exact scalar envelope optimum. Take one bad submission with view law
   \[
   P=(1/2,1/2),
   \]
   and mediated honeypot law
   \[
   Q=(1/4,3/4).
   \]
   These can arise from two submissions: the bad one has law \(P\), the benign one has law \((0,1)\), and `PH` mixes them equally. The least domination constant is \(L=2\).

   With one honeypot, no slack, `r = b = N = 1`, the envelope optimum is
   \[
   \max_t(1-t)\min(1,2t)=1/2.
   \]
   The actual optimum is
   \[
   \max_{u,v\in[0,1]}
   \left(1-\frac{u+3v}{4}\right)\frac{u+v}{2}
   =3/8.
   \]
   Thus even minimal \(L\)-domination does not make (C) necessary.

   **Fix:** replace the sentence with:

   > This campaign proves an exact one-shot reduction and sound scalar upper certificates. The scalar certificate is necessary and sufficient under the hypotheses of (X) or (S2). Grid certificates provide sufficient numerical upper bounds.

   Keep (C) as an implication.

2. **MAJOR — (R)’s claimed trusted-input list is incomplete.**

   Exact text: “the worst case is a function of the trusted components `(M, PH, κ, n_h, r, b)` only.”

   It also depends on **`Bad` and the admissible submission space**.

   Counterexample: fix the identity mediator on `Bool`, honeypots concentrated on `true`, one honeypot with no slack, and `r = b = N = 1`.

   - With `Bad = {true}`, the optimum is \(\max_t t(1-t)=1/4\).
   - With `Bad = {false}`, PASS only `false`. Honeypot survival and attack success are both 1.

   Every listed component is identical.

   **Fix:** include the trusted catastrophe specification:

   > For fixed submission/view spaces and `Bad`, the worst-case value depends only on `M, PH, κ, nh, r` and whether `b` is zero, once `N ≥ 1`.

   The disappearance of the positive horizon and the distinction between different positive budgets is a consequence of this particular first-bad-decides model.

3. **MAJOR — “history dependence … do not help” needs an explicit subject and model restriction.**

   Exact text: “shared randomness, history dependence and waiting do not help the colluders.”

   The theorem permits history dependence of the **generator**. It excludes history dependence of the monitor. It also relies on free submission choice, a fixed monitor rule throughout testing and deployment, constant audit recall, and absorbing outcomes.

   A phase-aware monitor can FLAG every honeypot and PASS every deployment attack. That produces risk 1 even where the displayed stateless Witness has risk below `3/40`. This is outside the formal model, but the unqualified sentence obscures precisely that exclusion.

   The one-shot attainment construction also need not be feasible under an exogenous task stream: the chosen bad submission may become available only later.

   **Fix:**

   > Within the finite free-submission model, with a fixed stateless monitor and the protocol’s conditional independence assumptions, arbitrary generator histories and finite shared-seed mixtures do not increase the worst-case value above an immediate fixed attack.

   For the programme’s capability-free interpretation, statelessness must be a trusted interface restriction. Merely assuming that an unrestricted untrusted monitor behaves statelessly does not establish the programme’s advertised quantification.

4. **MAJOR — the AOQL identification is too broad.**

   Exact labels: “(F) Honest-free floor (acceptance-sampling AOQL)” and the motivating assertion that the \(L=1\) curve is “the AOQL … Dodge-Romig.”

   For hard slack, the classical large-lot AOQ curve is
   \[
   t\,\operatorname{binCDF}(n,s,t).
   \]
   Its maximum is the corresponding AOQL. Finite-lot rectifying inspection includes a factor \((Q-n)/Q\), where \(Q\) is the lot size. This is documented in [NIST’s acceptance-sampling treatment](https://www.itl.nist.gov/div898/handbook/pmc/section2/pmc243.htm).

   Your factor equals \(t\) when `r = 1` **or** `b = 0`. For positive budget and `r < 1`, it is `1 - r + r*t`. For arbitrary `κ`, survival is not the OC curve of the stated hard-threshold single-sampling plan.

   For example, `r = 0`, positive budget gives maximum 1, rather than approximately 0.068.

   **Fix:** retain (F), but describe it as a view-blind attainable floor. Restrict the classical AOQL identification to hard slack with `capB r b t = t`, using the large-lot convention. Call the positive-budget, imperfect-recall curve **AOQL-type** or audit-adjusted.

   NIST also verifies the historical Dodge–Romig connection; do not present the underlying acceptance-sampling calculation as new mathematics. [NIST historical overview](https://www.itl.nist.gov/div898/handbook/pmc/section2/pmc21.htm)

5. **MAJOR — (S1)’s “no coverage” wording hides an essential hypothesis.**

   Exact text: “No coverage or domination constant is needed beyond content-only views and tested bad classes.”

   Exact conjunct:
   ```lean
   (∀ x, Bad x → c x ∈ Es)
   ```

   This **is** a coverage hypothesis: qualitative coverage of every bad class. What is unnecessary is a lower bound on honeypot probability mass.

   Without that conjunct, take `Es = ∅`, a nonempty bad set and an always-PASS monitor. Risk is 1, while the `3/40` scalar certificate remains valid for `m = 12`, `sc = r = b = 1`.

   **Fix:**

   > Every bad class must be tested. No quantitative class-mass coverage or domination constant is required.

   Keep the conjunct.

6. **MAJOR — (S2)’s kernel/class independence claim needs its conditioning and cost held fixed.**

   Exact text: “independent of the kernel `K` and of the number of classes.”

   This is mathematically correct **within exactly decodable, covered instances, with fixed per-class `m`**. It is misleading as a general design comparison.

   Without decoding, overlapping class laws can force simultaneous misses in several tested classes. For example, two identical tested class laws give survival \(B(t)^2\), rather than \(B(t)\), when their common pass rate is \(t\). The worst-case value can therefore be strictly smaller.

   Also, testing more classes at fixed per-class `m` increases total honeypot cost to
   ```lean
   m * Es.card
   ```
   At a fixed total testing budget, increasing the number of classes generally reduces `m` and changes the bound.

   **Fix:**

   > Conditional on exact class decoding and complete bad-class coverage, the optimum depends on the per-class sampling parameters, rather than the detailed kernel or class count. Total testing cost remains proportional to the number of tested classes.

7. **MINOR — (G) is sound, but its advertised composition with arbitrary (C) is incomplete.**

   Exact text: “With (G0) and (C) this turns a sup over `t` into finitely many rational inequalities.”

   (C) permits arbitrary, non-monotone `g`. Applying (G) additionally requires
   ```lean
   F t = capB r b (min 1 (g t))
   ```
   to be monotone and nonnegative. Neither follows from arbitrary envelopehood.

   Moreover, arbitrary real schedules and `Real.exp η` do not yield rational inequalities automatically.

   **Fix:** qualify this workflow for monotone envelopes with rational evaluation data. For hockey-stick certificates, prove a rational upper bound on `exp η`, or use an exactly reducible choice such as `η = Real.log 2`.

   `GridCert` itself is an analytic proposition, not an executable checker. Keep it, and either promise proof-carrying `norm_num` certificates or add a rational checker with a soundness bridge. This definition compiles:

   ```lean
   def checkGridQ (S F : ℚ → ℚ) (U : ℚ) (ts : List ℚ) : Bool :=
     decide (ts.head? = some 0) &&
     decide (ts.getLast? = some 1) &&
     (ts.zip ts.tail).all (fun p =>
       decide (p.1 ≤ p.2 ∧ S p.1 * F p.2 ≤ U))
   ```

   The missing theorem would transport a successful check to `GridCert` after proving that the rational evaluations equal the relevant real evaluations. Bernstein coefficients are an alternative certificate format, not a prerequisite for this milestone.

8. **MINOR — (S2) unnecessarily excludes zero budget and requires decoding outside the tested set.**

   Exact hypotheses:
   ```lean
   1 ≤ b →
   (∀ e z, K e z ≠ 0 → g z = e) →
   ```

   Its conclusion already uses `capB`. The same exactness argument works for `b = 0`; the attack’s value becomes its PASS probability.

   For necessity, decoding is needed only on tested classes. The upper implication needs no decoder.

   **Fix:** delete `1 ≤ b`, and optionally weaken decoding to:

   ```lean
   (∀ e ∈ Es, ∀ z, K e z ≠ 0 → g z = e)
   ```

   This requires generalising the dependency’s attainment helper, but (R) already needs the zero-budget version.

The following are **not defects in the displayed formal statements**.

| Conjunct | Mathematical assessment |
|---|---|
| **(R)** | The two expectations are correctly placed. Honeypot survival uses `E (push M PH) ψ`; attack success uses `E (M x) ψ`. |
| **(C)** | True with arbitrary `g`, including non-monotone `g`. Its `0 ≤ U` guard handles empty `Bad`. |
| **(E), domination** | True by multiplying pointwise domination by nonnegative `ψ` and summing. No additional distribution or sign hypotheses are needed for this algebraic implication. |
| **(E), hockey-stick** | Directly follows from UMHS T2 and the assumed divergence bound. |
| **(G0)** | True for every valid schedule, including non-monotone schedules. |
| **(G)** | The hypotheses suffice; continuity and strictly increasing grid points are unnecessary. |
| **(F)** | True by the constant-rule, fixed-attack construction. Its omitted recall/schedule validity assumptions are unnecessary for the algebraic identity, although they matter for calling the expression a probability. |
| **(X)** | True. Nonempty `Bad` prevents the vacuous converse problem. |
| **(S1)** | True with its explicit bad-class membership hypothesis. |
| **(S2)** | True. Its lower construction must PASS only the decoded attack class. |
| **Witness** | The numerical facts check, and the protocol assertions follow from the proposed certificates and attainment results. |

For **(R)**, fix a seed and rule. If `Bad` is nonempty, choose a bad submission maximising its PASS probability \(A\). UMPROT’s first-bad bound gives deployment risk at most `capB r b A`, achieved by attacking that submission immediately. Multiplying by that seed’s honeypot survival and averaging over the normalised seed law proves the reverse implication.

At zero budget, a FLAG halts, so the attained value is exactly
\[
S\,E(Mx)\psi,
\]
as written. There is no additional `1-r` term.

Quantifying over `(Ω : Type)` inside the iff creates no encoding trap. `Unit` provides the necessary singleton seed; arbitrary finite seed cardinalities are included. It does not literally quantify over continuous shared-seed laws, although a measurable-mixture extension would follow from the same pointwise bound.

For **(S1)**, choose a bad submission attaining the maximum bad-class pass rate \(A\). Its tested class contributes `binCDF m sc A`; all other survival factors lie in `[0,1]`. Deployment contributes at most `capB r b A`.

For **(S2)**, the necessary construction is
```lean
ψ z := if g z = c x then t else 0
```
with immediate attack `x`. Exact decoding gives pass rate `t` on the attack class and zero on every other tested class. Those other factors are
```lean
binCDF m sc 0 = 1
```
Using a view-blind constant rule instead would generally produce multiple nontrivial test factors and would not establish the claimed lower curve.

The edge cases resolve as follows:

- **Empty `Bad`:** risk is zero. (R)’s right side is vacuous, so its `0 ≤ U` hypothesis is essential unless nonempty `Bad` is assumed.
- **(C), empty `Bad`, negative `g`:** its guard is also essential. Without it, take `nh = 0`, `r = b = 1`, `g ≡ -1`, `U = -1`. The certificate premise holds, but zero risk is not at most `-1`.
- **Nonempty `Bad`:** the envelope condition applied to the constant rule `ψ ≡ t` forces `g t ≥ t` throughout `[0,1]`. Thus negative envelope values there are incompatible with the hypotheses.
- **`N = 0`:** risk is zero. (C) remains true. (S1)’s certificate at `t = 0` implies `U ≥ 0`, so it also remains true. The exactness statements correctly exclude this horizon.
- **Negative `U` in (X) or (S2):** both sides are false under their hypotheses. Their scalar conditions already imply `U ≥ 0`.
- **`b = 0`:** `capB` is the identity, independent of `r`.
- **`r = 0`, positive budget, nonempty `Bad`:** worst-case risk is 1; FLAG an immediate attack and the audit always fails.
- **`r = 1`:** `capB` is the identity for every budget.
- **`κ ≡ 0`:** no test shutdown occurs; worst-case risk is 1 when an immediate bad attack is available.
- **`κ ≡ 1`:** survival is `(1-t)^nh`; endpoints and zero honeypots behave correctly.
- **Empty `Es`:** coverage forces empty `Bad`; otherwise (S1)/(S2)’s hypotheses fail.
- **Extra tested classes containing no bad submissions:** harmless for the upper bound; neutralised by the decoded lower construction.
- **`nh = 0`, `m = 0`, or `sc ≥ m`:** the relevant test survival is 1. With nonempty `Bad` and positive horizon, the exact worst case is 1.
- **`t = 0` and `t = 1`:** the binomial definition handles both, including its `0^0` terms.

`GridCert` is well-formed. Its endpoint equations exclude empty and singleton lists, and consecutive ordering forces every entry into `[0,1]`. Repeated points cause no problem. For a cell containing `t`, the proof is simply
\[
S(t)F(t)\le S(t_i)F(t_{i+1})\le U.
\]
The nonnegativity assumptions justify both multiplications.

The main Lean proof hazard is **(G0)**. Survival need not be antitone in the miss index `j`. With `κ 0 = 1`, `κ 1 = 0`, one remaining honeypot survives with probability `1-h` from index 0 and probability 1 from index 1.

Use the weighted helper instead:
```lean
(1 - κ j) * survH h κ n (j + 1) ≤ survH h κ n j
```
under the usual probability hypotheses. It follows by induction on `n`. A second induction proves pass-rate antitonicity: compare the two recurrences using the induction hypotheses, then use this weighted inequality to control the change in mixture weights.

The remaining helpers should include:

- expectation bounds for valid finite laws and rules;
- normalisation of `push`;
- monotonicity and probability bounds for `capB`;
- empty-bad deployment risk zero;
- one-shot attainment for **every** budget;
- finite attainment of the maximum bad PASS rate;
- constant-rule survival and `binCDF m sc 0 = 1`;
- bounding the class-survival product by one selected factor.

These are infrastructure lemmas. Split the two (E) conjuncts into named results and expose the other results individually; assemble the campaign conjunction afterwards.

The arithmetic-performance objection does not survive testing. On Lean 4.35.0-rc3 with the available Mathlib:

- The supplied grid passes `norm_num` at default heartbeats.
- Its largest rectangle is approximately **0.0739163870**, giving minimum slack **0.0010836130**.
- The lower-point value is exactly
  \[
  \frac{37569208117}{549755813888}
  \approx 0.0683379915.
  \]
- The true maximum is approximately **0.0683392329**, at
  \[
  t=\frac{5+2\sqrt{42}}{143}\approx0.1256047650.
  \]

The grid and lower inequality took about 7.4 seconds combined, including imports. The Witness certifies an interval around the optimum; it does not certify its exact value.

For decision relevance, `3/40` reduces the existing upper bound `2/13` by **51.25%**. That changes the certified number for the same protocol. It does not demonstrate a reduction in actual risk caused by a protocol change.

A CID is justified as a numerical certification milestone if it covers useful parameter rows. I also generated and Lean-checked these curve certificates:

| Parameters, with `L = r = 1` | Existing counting bound | Lean-checked curve upper bound | Grid points |
|---|---:|---:|---:|
| Hard slack, `nh = 100`, `ns = 1` | `2/101 ≈ 0.019802` | `17/2000 = 0.0085` | 35 |
| Soft slack, `nh = 100`, `ns = 5` | `5/101 ≈ 0.049505` | `19/1000 = 0.019` | 23 |

The two larger checks took about 12.8 seconds combined. These are arithmetic certificates; their protocol consequences remain conditional on proving the proposed bridge results.

Add those fixtures, plus a hockey-stick instance with **positive `δ` and imperfect recall**. An example using `η = log 2` would exercise the exponential envelope without introducing an unchecked floating-point approximation. Match the actual DESIGN rows when those files are available.

The prior-art boundary also needs precision:

- **Games for AI Control — verified ID `2409.07985`, v2.** Proposition 4.1 evaluates memoryless threshold Blue policies against an IID attack-rate Red parameter `β`. It does not establish soundness against every history-dependent Red. The paper also runs code when an audit is attempted with no budget, whereas UMPROT halts. Both differences obstruct transferring its recurrence unchanged. [Paper, §4 and Appendix C](https://arxiv.org/html/2409.07985v2)
- **Ctrl-Z — verified ID `2504.10374`.** Appendix E already discusses untrusted monitoring, honeypots, collusion strategies and parameter optimisation. UMCERT’s distinction is the quantified guarantee within its restricted model and Lean-checked arithmetic, rather than the introduction of those mechanisms. [Appendix E](https://arxiv.org/html/2504.10374)
- **LASR — verified ID `2602.20628`, v2.** Appendix B.5 models slack through probabilistic effects of training examples and uses a Poisson approximation. Your trusted shutdown coin is a different mechanism. Preserve the dependency’s explicit “inspired by … not a model of retraining” distinction. [Appendix B](https://arxiv.org/html/2602.20628v2)

The later history-dependent-Red checker needs a separate Bellman soundness theorem. A suitable certificate shape is
```lean
∀ n s a,
  immediateCat s a +
    ∑ s', safeContinue s a s' * V n s' ≤ V (n + 1) s
```
with terminal and transition-validity conditions. Actionwise inequalities permit induction over arbitrary histories. Checking a polynomial in one constant attack rate does not provide that guarantee.

**Final verdict: major revisions; no demonstrated FATAL mathematical defect.**

Fixes, in priority order:

1. Remove blanket certificate exactness; distinguish (R), envelope slack and grid slack.
2. Add `Bad` to the trusted inputs and explicitly scope the policy/model claim.
3. Correct the AOQL identification.
4. Make qualitative coverage and fixed-per-class testing cost explicit.
5. Specify the numerical workflow and its monotonicity/rational-evaluation requirements.
6. Generalise zero-budget attainment and preferably (S2).

I would freeze **(R), (C), both separate (E) results, (G0), (G), (F), (X), (S1), and (S2)** with those documentation corrections; preferably extend (S2) to every budget and decoding on `Es`. Freeze the existing Witness plus hard- and soft-slack `nh = 100` fixtures. Keep stateful-game soundness as a separate milestone.