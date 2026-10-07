**Verdicts: UMADAPT — minor revision, provided (c) is explicitly pointwise. Outcome — major revision.** I found no false displayed formal conjunct. The substantive errors concern what the conjuncts establish, the claimed weakest contract, and the claimed ledger bridge.

I independently enumerated the counterexample with exact rationals. I did not rerun Lean: the workspace contains the prompt, not the projects or pinned dependencies.

1. **MINOR — UMADAPT (a), “along the all-FLAG path the tester’s queries do not depend on the seed.”**

   This is wrong if it means conditioning the actual experiment on all answers being FLAG. That conditioning changes the seed posterior. For example, query a uniformly random class among two classes with `t = 1`: conditional on FLAG, the queried class is the complement of the seed.

   **Fix:** explicitly introduce a reference experiment that forces every monitor answer to FLAG. Its transcript law is seed-independent.

   For a reference transcript \(h\), let \(m_\omega(h)\) count queries whose class equals \(c(\omega)\). Exact decoding gives
   \[
   \Pr[\text{actual transcript }h\text{ with all FLAGs}\mid\omega]
   =\Pr_{\rm ref}[h](1-t)^{m_\omega(h)}.
   \]
   Injectivity on \(S\) implies
   \[
   \sum_{\omega\in S}m_\omega(h)\le n.
   \]
   Consequently, using Bernoulli’s inequality and the keep contract,
   \[
   \frac1k\sum_{\omega\in S}\operatorname{adSurv}_\omega
   \ge 1-\frac{tn}{k}.
   \]

   Deployment from the seed’s immediate bad submission has probability
   \[
   d(t,r,b)=
   \begin{cases}
   t,&b=0,\\
   1-r+rt,&b>0,
   \end{cases}
   \]
   whenever \(N\ge1\). Since \(d\ge t\) and survival is nonnegative, (a) follows. Do not multiply a potentially negative survival lower bound by \(d\) and then casually replace \(d\) with \(t\).

2. **MINOR — `AdTester`, interpreted as the weakest contract.**

   The exact conjunct
   ```lean
   ∀ h, (∀ e ∈ h, e.2.2 = false) → keep h = 1
   ```
   constrains every history, including impossible histories and lengths other than the selected horizon. Those constraints are unnecessary.

   The operative condition is acceptance with probability one in the forced-FLAG reference experiment. A weaker, horizon-specific formulation is:

   ```lean
   def KeepsAllFlagAt {X Z : Type} [Fintype X] [Fintype Z]
       (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
       (keep : Hist X Z → ℝ) (n : ℕ) : Prop :=
     adSurv T M (fun _ => 0) keep n [] = 1
   ```

   Retain lawful `T` and `[0,1]`-valued `keep`. The existing contract is a convenient sufficient condition; call it that, not literally the weakest condition.

   Some acceptance condition is load-bearing: `keep ≡ 0` destroys the proposed bound already at `n = 0`, `t = 1`.

3. **MINOR — UMADAPT docstring, “every slack rule” and early shutdown.**

   “This holds for every slack rule … global or class-aware” needs qualification. It holds for **miss-only rules that accept zero-miss records**. Class-aware rules can also reject insufficient coverage, malformed records, or benign false positives.

   Similarly, inverse honeypots and benign-flag guards violate the contract **when they reject a reachable all-FLAG record**. Their names alone do not imply violation; a disabled or sufficiently permissive guard can satisfy it.

   “Early shutdown is a keep value of 0 on every continuation” describes deterministic rejection. With an unrecorded trusted shutdown coin, the same public history can arise on surviving and rejected branches. After integrating that coin, `keep h` can lie strictly between zero and one.

   **Fix:** say that deterministic rejected prefixes have zero keep on their extensions, while randomized shutdown is represented by conditional survival weights, or by an explicit trusted state.

   End-only `keep` is adequate for terminal risk in this bounded-horizon model. It does not preserve actual stopping times or testing costs.

4. **MINOR — “adaptive tester” generality needs its independence boundary stated.**

   Full histories include honeypots, views and answers; their length supplies the call index. Thus `T h` and randomized `keep h` cover the relevant adaptive choices.

   Persistent private randomness does not create a counterexample: for finite-horizon testers with perfect recall, it can be integrated into behavioral kernels. But this uses independence from the colluder’s seed and the trusted component coins.

   **Fix:** state that independence explicitly. A tester given the seed could query its class immediately and defeat the `n/k` argument.

   The prohibition on showing the test to the generator is unnecessary for this particular lower bound: `seedPolicy` ignores the test. Likewise, the bound only needs a bad PASS in the first deployment round to cause catastrophe. The other deployment branches determine the exact \(d\), but are not essential to the lower bound \(d\ge t\).

   Quantifier order is otherwise sound. `g` is fixed first; the seed law and generator are fixed by \(S\). For every fixed \(t\), the same monitor works against every tester. The optimized \(t\) depends on public \(n,k\), not the tester’s strategy.

5. **MINOR — UMADAPT (b) is only arithmetic, and (a) has an uninformative region.**

   The arithmetic conjunct is true. However, it does not itself mention an adaptive tester or protocol risk. The operational optimized corollary is obtained by combining it with (a).

   **Fix:** freeze a direct protocol-risk corollary at
   \[
   t_*=\min(1,k/(2n)),
   \]
   keeping the current arithmetic conjunct as infrastructure. Include a separate `n = 0` corollary with risk exactly one at `t = 1`.

   The displayed simplified floor is also weaker than the actual optimized quadratic value:
   \[
   \max_{0\le t\le1}t(1-tn/k)=
   \begin{cases}
   1-n/k,&k\ge2n,\\
   k/(4n),&k<2n.
   \end{cases}
   \]
   The draft’s wording “at least” accommodates this.

   When `tn > k`, (a)’s right-hand lower bound is negative. At minimum, expose the nonnegative version:
   \[
   \operatorname{risk}\ge t\max(0,1-tn/k).
   \]

   A stronger bound is available without additional tester assumptions. With \(q=\lfloor n/k\rfloor\), \(a=n\bmod k\),
   \[
   \operatorname{risk}\ge
   \frac{t}{k}\left[(k-a)(1-t)^q+a(1-t)^{q+1}\right].
   \]
   Discrete balancing of the class-hit counts proves it. A balanced deterministic schedule, accepting only zero-miss records, attains it with perfect audits. Thus adaptivity provides no improvement under the minimal all-FLAG-only acceptance contract. The current weaker theorem remains true.

6. **MINOR for the pointwise claim; MAJOR if interpreted after optimization — UMADAPT (c), “the multiplier cannot be kept.”**

   The counterexample’s exact risk is
   \[
   R(t)=t-\frac32t^3+\frac12t^4.
   \]
   Therefore
   \[
   R(3/4)=141/512<21/64.
   \]
   This refutes the nonadaptive formula’s **universal pointwise-in-\(t\)** extension. The chosen \(t\) need not maximize risk.

   It does **not** refute the old optimized floor. The unique maximizer satisfies
   \[
   4t^3-9t^2+2=0,
   \]
   with
   \[
   t\approx0.540876747,\qquad R(t)\approx0.346320476>1/3.
   \]
   Here \(1/3\) is the old optimized floor for `(k,n,n_s) = (2,3,1)`.

   **Fix:** write:
   > The PL_UMLOWERF1 formula fails pointwise in \(t\) for adaptive testers.

   If you intend the stronger optimized impossibility claim, replace or supplement (c) with this fixed tester:

   - `k = n = 4`, `n_s = 1`;
   - query a uniformly random class until the first PASS;
   - thereafter repeat that class;
   - keep iff there is at most one PASS.

   Its query rule can be written:

   ```lean
   def lockT (h : Hist (Fin 4) (Fin 4)) (x : Fin 4) : ℝ :=
     match h.find? (fun e => e.2.2) with
     | none => 1 / 4
     | some e => if x = e.1 then 1 else 0
   ```

   Against the uniform-seed pair, with identity mediation and perfect audits,
   \[
   R_4(t)=\frac t3\left[4(1-t/4)^4-(1-t)^4\right].
   \]
   For every \(t\in[0,1]\),
   \[
   R_4(t)\le\frac43t(1-t/4)^4
   \le\frac{4096}{9375}<\frac12.
   \]
   The second inequality is five-factor AM–GM. The old optimized floor is \(1/2\). This is one tester defeating that floor for **every** \(t\), without a minimax quantifier swap.

The remaining UMADAPT edge checks produce no contradiction:

| Case | Consequence |
|---|---|
| `n = 0` | `keep [] = 1`; risk is \(d\ge t\), and is one at `t = 1`. |
| `k = 1` | Valid; Bernoulli bounds \((1-t)^n\) by \(1-nt\). |
| `t = 0` | Risk is zero if `b = 0`, otherwise \(1-r\); claimed lower bound is zero. |
| `t = 1` | Valid; the lower bound becomes uninformative once `n ≥ k`. |
| `r = 0` or `r = 1` | Covered by the exact deployment expression \(d\). |
| `b = 0`, `N = 1` | Covered; a FLAG halts and a bad PASS catastrophes. |
| Benign queries or queries outside `S` | They may share a selected class, but each query still hits at most one seed class. |
| View-dependent queries/keep | Covered by the reference-transcript argument. |

`Witness` is correct: the seed-false survival probability is \(1/2\), seed-true survival is one, and deployment catastrophe probability is \(1/2\), yielding \(3/8\). Nonempty \(S\) and `N ≥ 1` are essential; dropping the latter immediately falsifies the bound.

The novelty claim should remain limited to the application and formalization. Shoup’s Lemma 1 is the relevant difference lemma: **IACR ePrint 2004/332**, first published in 2004, with the accessible manuscript revised in 2006. [Shoup’s manuscript](https://www.shoup.net/papers/games.pdf)

The hard-distribution method is classical property-testing infrastructure. Goldreich explicitly distinguishes this methodology from invoking minimax equality. Calling the argument “Yao’s principle” is loose; no minimax theorem is needed here. Yao’s original identifier is **10.1109/SFCS.1977.24**, also verified in the bibliography of Ben-David–Blais, **arXiv:2002.10802**. [Goldreich’s lower-bound chapter](https://www.wisdom.weizmann.ac.il/~oded/PDF/pt-lb.pdf), [Ben-David–Blais](https://arxiv.org/html/2002.10802)

Adaptive group testing is not the same query model: pooled queries can interrogate many candidates and permit binary splitting. Here one query has one decoded class. **arXiv:1902.06002** is the verified Aldridge–Johnson–Scarlett survey identifier. [Group-testing survey](https://arxiv.org/html/1902.06002v3)

Acceptance sampling and Wald-style sequential testing establish prior art for sequential decisions, not this exact converse. Mere curtailment of a predetermined test preserves its terminal acceptance event; the counterexample changes later query classes. NIST’s sequential plans instead vary the sample count according to accumulated observations. I found no source establishing this exact control-stack statement, which is insufficient evidence of novelty. [NIST sequential sampling](https://www.itl.nist.gov/div898/handbook/pmc/section2/pmc26.htm)

7. **MINOR — `PartitionClaim` is conservation, not yet a probability partition.**

   The equality is true without `[0,1]` constraints on `φ` or `R`. In audited bad branches,
   \[
   (1-R)+R=1;
   \]
   monitor branches contribute \(\phi+(1-\phi)=1\). Normalization of `M` and `π` completes the induction. Their nonnegativity is unnecessary for this equality.

   But arbitrary real inputs do not produce probabilities. Take `X = Z = Unit`, `M = π = 1`, `Bad = True`, `n = 1`, `u = 0`, `b = 1`, `φ = 2`, `R = 1`. Then
   \[
   (\mathrm{catG},\mathrm{caughtG},\mathrm{haltP},\mathrm{complG})
   =(2,-1,0,0).
   \]

   **Fix:** rename the existing equality `ConservationClaim`, and add nonnegativity under the existing kernel hypotheses plus:

   ```lean
   (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) →
   (∀ h x z, Bad x → 0 ≤ R h x z ∧ R h x z ≤ 1) →
   ∀ n u h,
     0 ≤ catG Bad M φ π R b n u h ∧
     0 ≤ caughtG Bad M φ π R b n u h ∧
     0 ≤ haltP Bad M φ π b n u h ∧
     0 ≤ complG Bad M φ π b n u h
   ```

   Conservation then supplies the upper bounds by one.

   The operational branch audit finds no discrepancy: `deployO` and `gameO` preserve the Boolean games’ branches. `caughtG`, `haltP` and `complG` implement those branches correctly. Their independence from recall where applicable is justified: an audited bad submission terminates regardless of whether its outcome is caught or catastrophe. `MarginalClaim`, `DeployLawClaim` and `GameLawClaim` are true.

8. **MAJOR — `HonestClaim` docstring, “linked by textual identity … of the rate definitions.”**

   `HonestClaim` itself is true. Its operational rates are probabilities of composed `ProbComp`s. Those expressions are not textually identical to finite-kernel expectations.

   **Fix:** prove the induced-rate bridge explicitly. With
   \[
   H_r(x)=\Pr[H=x],\quad \mu_r(x)=\Pr[\mu=x],\quad
   M_r(x,z)=\Pr[M(x)=z],\quad \phi_r(z)=\Pr[D_0(z)=\mathrm{true}],
   \]
   the required identities are
   ```lean
   α₀ = ∑ x, Hr x * ∑ z, Mr x z * φr z
   f₀ = ∑ x, μr x * ∑ z, Mr x z * (1 - φr z)
   ```
   They require finite bind/total-probability arguments and the Boolean-complement identity. If the ledger defines `flagRate` using `1 - E ...`, normalization supplies another equality.

   The actual `PL_UMUSEF1` definitions were not supplied. I therefore cannot certify either the claimed textual copy of its `haltP` or the correspondence to its exact rate definitions. Identical `binCDF` text alone does not establish that bridge.

   Replace the wording with:
   > The same binomial formula, with its parameters identified by the induced-kernel rate bridge.

   Honest completion has no off-by-one error: exactly `b` flags are affordable; the `(b+1)`-st flag halts, including when it occurs in the final round.

| Honest edge case | Result |
|---|---|
| `N = 0` | Completion equals test survival; halted probability is zero. |
| `b ≥ N` | Completion equals test survival; halted probability is zero. |
| `n_s ≥ n_h` | Test survival is one. |
| `α₀ = 0` | Test survival is one. |
| `α₀ = 1`, `n_s < n_h` | Rejection probability is one. |
| `b = 0` | Completion is test survival times \((1-f₀)^N\). |

   Finite benign support and fresh calls make the hypothetical full deployment stream’s flags iid. The actual run is its curtailed prefix. That coupling justifies the binomial completion formula.

9. **MAJOR — `TwoMarginalsClaim`, “two marginals of the same game.”**

   The conjunction is true, but its two clauses instantiate different experiments:

   - safety quantifies over arbitrary `(ρ, D, π)` with seed type `Ω`;
   - availability uses `(pure ())`, seed type `Unit`, monitor `D₀`, and generator `μ`.

   Sharing the function name `gameO` does not make those the same outcome law. This adds no coupling beyond `MarginalClaim` plus `HonestClaim`.

   **Fix:** rename it `AdversarialSafetyAndHonestAvailabilityClaim` and describe two benchmarks of one configured protocol.

   For a literal single-experiment statement, bind one `G` and establish
   \[
   p_{\rm complete}
   =1-p_{\rm catastrophe}-p_{\rm caught}
      -p_{\rm rejected}-p_{\rm halted},
   \]
   together with its safety bound and outcome formulas.

   A catastrophe bound alone supplies no useful completion lower bound. A monitor that always FLAGs, a perfect audit, and an immediate bad submission give catastrophe probability zero and caught probability one.

   A substantive same-experiment coupling requires a workload assumption. For example, use a seed selecting attack mode with probability \(\theta\), otherwise an iid benign mode. Let the monitor be seed-free and view-blind with PASS probability \(p\), with exact root recall \(r\), `b ≥ 1`, `N ≥ 1`. Set
   \[
   S=\operatorname{binCDF}(n_h,n_s,p),\quad
   B=\operatorname{binCDF}(N,b,1-p),\quad q=1-r+rp.
   \]
   One `gameO` then has
   \[
   p_{\rm catastrophe}=\theta Sq,\qquad
   p_{\rm complete}=(1-\theta)SB,
   \]
   and hence
   \[
   (1-\theta)B\,p_{\rm catastrophe}
   =\theta q\,p_{\rm complete}.
   \]
   This is an actual same-law identity. The unmixed identity \(B\,\mathrm{risk}=q\,\mathrm{completion}\) compares two generator instantiations and must be described accordingly.

10. **MINOR — Outcome `Witness` does not explicitly witness the combined hypotheses.**

   All supplied numbers are correct:
   \[
   (27/256,\ 81/256,\ 37/64,\ 0,\ 0)
   \]
   for `(catastrophe, caught, rejected, halted, complete)`, and honest completion/halt probabilities \(15/16,\ 1/16\).

   **Fix:** if this is intended to witness the combined safety/availability benchmark, conjoin domination, recall and benign-support hypotheses. Use `N = 2` in both instances; the immediate-attack instance’s numbers remain unchanged. Include the honest instance’s three omitted zero outcomes.

The fixes should be applied in this order:

1. Correct `TwoMarginalsClaim`’s interpretation and replace the textual-rate bridge claim with an explicit theorem.
2. Make UMADAPT’s reference experiment explicit and restrict (c)’s wording to pointwise failure.
3. Split algebraic conservation from probability bounds.
4. Qualify the tester contract, slack-rule scope and randomized stopping description.
5. Add direct optimized risk and common-configuration witness statements.

I would freeze these conjuncts:

- **UMADAPT:** decoder/colluder validity; averaged adaptive survival lower bound; protocol lower bound (a); direct optimized protocol corollary including `n = 0`; explicitly pointwise counterexample (c); current tightness Witness. Keep arithmetic (b) as infrastructure. Add the four-class counterexample if asserting failure of the old optimized floor.
- **Outcome:** both catastrophe marginals; all five deployment-law clauses; algebraic conservation; probability bounds under lawful rules/recall; both whole-game factorization clauses; all five honest-outcome formulas; explicit induced-rate identities; corrected Witness.
- Rename the existing `TwoMarginalsClaim` as a shared-protocol benchmark conjunction. Freeze a separate single-`G` accounting theorem if retaining “one experiment”; freeze the mixed-workload identity only with its workload hypotheses.

**UMADAPT: minor. Outcome: major. Neither needs rejection of its displayed recursions; neither should be frozen with the current overclaimed interpretations.**