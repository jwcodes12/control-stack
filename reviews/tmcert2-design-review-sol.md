**The literal Lean conjuncts appear mathematically true. TMGAC’s claimed usefulness bridge is nevertheless unfaithful to GAC.** Proving `(UZ)` as written would verify the wrong reward definition.

I compiled both definition blocks with Mathlib and proved the two TMCERT witness checker equalities using kernel reduction. The remaining assessments below use mathematical reasoning and exact arithmetic; they are not Lean proofs of the complete `Claim` or `Witness`.

| Statement | Conjuncts | Truth assessment |
|---|---|---|
| TMCERT | `(S)`, `(S')`, `(Fx)` | True. Supersolution induction and weighted averaging. |
| TMCERT | `(FxGap)` | True: `1/2`, `1/2`, `3/4`. |
| TMCERT | `(Obs)` | True by substitution. |
| TMCERT | `(T)`, `(TR)` | True. Finite Bellman maximisation gives attainment; the stated nonemptiness assumptions suffice. |
| TMCERT | `(U)` | True, including history-dependent nature. Subsolution induction uses the same selected row for reward and continuation. |
| TMCERT | `(Q)` | Soundness statements are true. Plain `by decide` fails on the supplied witnesses in the tested toolchain. |
| TMCERT | `(Vx)`, `(Abs)` | True. `(Abs)` uses an exact finite partition identity for `pushK`. |
| TMCERT | `Witness` | True. The concrete continuation sums are `1/2` at index `1`, and `1` at index `0`. |
| TMGAC | `(L)` | True, including zero coins with positive `TA`. |
| TMGAC | `(Z)` | True as an algebraic identity, including nonmonotone `f`. Probability interpretation needs additional hypotheses. |
| TMGAC | `(UZ)` | True for the supplied recurrence; **not GAC usefulness**. |
| TMGAC | `(M)` | True for the explicitly quantified finite mixtures. Its docstring describes a potentially larger class. |
| TMGAC | `(Lip)` | True with constant `N`. |
| TMGAC | `(W)` | True even when `TA n 0 > 0`. |
| TMGAC | `(T5)`, `Witness` | True. The adapter witness has safety `63/64`, hence risk `1/64`. |

The induction, averaging, lifting, finite-max attainment and vertex results are classical infrastructure. Several conjuncts are immediate corollaries or algebraic rearrangements. That is not a reason to reject them.

1. **MAJOR — TMGAC `uGAC`, `(UZ)`, and the usefulness docstrings omit audited safe solutions.**

   GAC counts a safe solution that passes an audit as used. Deferred solutions do not count. This appears explicitly in Proposition C.2 and its proof. [GAC v2, Appendix C.2](https://arxiv.org/html/2409.07985v2#A3.SS2)

   Your positive-coin immediate reward is `1 - qd`. For a perfect auditor, it must be:

   \[
   1-q_d+q_a.
   \]

   A decisive legal example is one problem, one coin, `qa = qd = 1`. The protocol audits the safe solution and uses it. GAC usefulness is `1`; your recurrence returns `0`.

   Replace the recurrence and reward by:

   ```lean
   noncomputable def usedReward
       (qa qd : ℕ → ℕ → ℝ) (n c : ℕ) : ℝ :=
     1 - qd (n + 1) c +
       if 0 < c then qa (n + 1) c else 0

   noncomputable def uGACUsed
       (qa qd : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
     | 0, _ => 0
     | m + 1, 0 =>
         (1 - qd (m + 1) 0) + uGACUsed qa qd m 0
     | m + 1, c + 1 =>
         (1 - qd (m + 1) (c + 1) + qa (m + 1) (c + 1))
         + qa (m + 1) (c + 1) * uGACUsed qa qd m c
         + (1 - qa (m + 1) (c + 1)) *
             uGACUsed qa qd m (c + 1)
   ```

   Change `(UZ)` to use `usedReward` and `uGACUsed`. The piecewise reward preserves an assumption-free algebraic bridge; its interpretation as GAC usefulness requires valid thresholds and the no-audit convention at zero coins.

   The old recurrence can remain under a name such as `uDirectRun`, described as counting only the explicit `Run` action. It cannot retain the GAC attribution.

   Add an audited-only witness. Otherwise the numerical tests can continue verifying two copies of the same specification error.

2. **MAJOR — TMGAC `(M)`’s docstring must exclude dependence on the current state.**

   The formal conjunct covers finite mixtures of `constRed β`, which ignores **both history and current state**. “Action law … ignores the history, including the round index” does not state that restriction completely.

   Here is a history-independent policy outside the covered class:

   ```lean
   def coinRed :
       RHist (Fin 2) Bool → Fin 2 → Bool → ℝ :=
     fun _ c a =>
       if c.val = 0 then
         (if a then 1 else 0)
       else
         (if a then 0 else 1)
   ```

   On `exG3`, it has risk:

   \[
   9/32>13/50.
   \]

   It ignores history, including history length, but uses the current coin count.

   Replace the class description with:

   > Finite mixtures of policies whose conditional action law, given the seed, is the same Bernoulli rate at every history and current state.

   Also label `(S')` and `(M)` as **finite-support mixtures**. Their statements do not quantify over arbitrary probability measures on seeds.

3. **MINOR — TMCERT `(Q)`’s plain-`decide` claim fails as written; kernel checking survives.**

   On Lean `4.35.0-rc3`, both of these fail:

   ```lean
   example : checkRiskQ 2 1 1 2 wCat wK wV = true := by decide
   example : checkLawfulQ 2 1 1 2 wCat wK = true := by decide
   ```

   Explicitly unfolding the named tables and checker did not resolve the tested failures. These succeed:

   ```lean
   theorem riskCheckKernel :
       checkRiskQ 2 1 1 2 wCat wK wV = true := by
     decide +kernel

   theorem lawfulCheckKernel :
       checkLawfulQ 2 1 1 2 wCat wK = true := by
     decide +kernel
   ```

   The resulting proofs depend only on the standard Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`; there is no native-evaluation axiom in those proofs.

   Concrete fixes:

   - Pin Lean and Mathlib, and make the actual witness proof commands part of the checked artifact.
   - Say “kernel reduction, using `decide +kernel` in the pinned toolchain.”
   - Remove the unconditional claim that using lists makes checking “cheap.”

   With constant-cost table lookup, the dense checker performs roughly `O(t N k m²)` rational operations. Rational sizes, table representation, lookup costs and kernel reduction can dominate. The tiny witness succeeding establishes no realistic-scale performance result.

   `(Q)` also checks **all rows of all supplied models**, corresponding to `adm := True`. It does not directly implement arbitrary row-local admissibility. If that interface is intended, add an admissibility mask and check only masked rows, or explicitly document the table construction that enumerates admissible rows in each cell.

4. **MINOR — TMCERT `(S)`, `(S')`, `(U)` impose admissibility outside the certified horizon, creating unnecessary vacuity.**

   The problematic hypotheses are:

   ```lean
   ∀ n h s a, adm n s a (θ n h s a)
   ```

   and the corresponding honest-selector hypothesis.

   For example, let `adm n s a th := n < N`. A certificate can exist and every needed row can be admissible, but **no selector satisfies the stated hypothesis**, because it also demands admissibility at `n = N`.

   Use:

   ```lean
   def SelectorUpTo {S A Θ : Type}
       (N : ℕ) (adm : ℕ → S → A → Θ → Prop)
       (θ : ℕ → RHist S A → S → A → Θ) : Prop :=
     ∀ n, n < N → ∀ h s a,
       adm n s a (θ n h s a)
   ```

   Make the analogous change for honest nature. Nonnegativity hypotheses can likewise be restricted to `n < N`.

   The remaining edge cases do not falsify the statements:

   - `N = 0`: only the base certificate matters; risk and honest reward are zero.
   - `m = 0`: checker acceptance concerns an empty state space; there is no initial state.
   - `t = 0`: model-row checks are vacuous. With inhabited states and actions, no total selector into `Fin 0` exists.
   - `k = 0`, with inhabited states: `IsPolicy` is impossible because the action sum is zero.
   - Empty admissibility at a needed cell means there may be no admissible selector. Certificate acceptance alone does not establish an executable uncertainty model.
   - `i.castSucc` accesses value-table index `i`; `i.succ` accesses `i+1`. These are correct.
   - `valOfQ` includes index `N`.
   - `gameOfQ`’s zero extension beyond `N` is internally consistent, but provides no deployment extrapolation beyond the certified horizon.
   - `Covered` needs no conditions at `n ≥ N`, because `(Abs)` concludes only for `n ≤ N`.
   - Empty fibres in `pushK` contribute zero; surjectivity of `α` is unnecessary.
   - The nonempty model assumption in `Vrob` prevents an undefined maximum.

   An operational certificate wrapper should make the required inhabited domains and row coverage explicit.

5. **MINOR — `(Abs)` is valid, but exact row equality is an unnecessarily restrictive deployment interface.**

   Equality is a sufficient condition. It need not be weakened for soundness. It becomes awkward when the checked abstract tables contain only polytope vertices: a concrete interior row need not equal any checked vertex.

   `(Vx)` supplies the mathematics for expanding the abstract family to its convex hull. What is missing is the explicit connection between that expansion, the finite rational vertex checks, and deployment coverage.

   Either add convex-hull coverage, or add certificate-specific domination:

   ```lean
   def CoveredV {Sc Ac S A Θ : Type}
       [Fintype Sc] [Fintype S]
       (N : ℕ) (Gc : Game Sc Ac) (α : Sc → S)
       (G : Θ → Game S A)
       (adm : ℕ → S → A → Θ → Prop)
       (V : ℕ → S → ℝ) : Prop :=
     ∀ n, n < N → ∀ x ac, ∃ b th,
       adm n (α x) b th ∧
       Gc.cat n x ac +
           ∑ x', Gc.K n x ac x' * V n (α x') ≤
         (G th).cat n (α x) b +
           ∑ s', (G th).K n (α x) b s' * V n s'
   ```

   Replacing `Covered` by `CoveredV` in `(Abs)` gives a true theorem with the same concrete continuation nonnegativity hypothesis. Exact equality and convex-hull coverage then become corollaries.

   **Do not replace equality with componentwise inequalities without checking signs.** The current certificate definition does not guarantee `V n s ≥ 0` at states whose admissibility constraints are empty.

   Counterexample: abstract states `z,y`; only `z` has admissible rows. Set `V 1 z = 0`, `V 1 y = -1`. At the next index, the abstract row from `z` goes entirely to `y`, permitting `V 2 z = -1`. A concrete row that terminates safely has catastrophe and continuation masses zero, so is componentwise below the abstract row, but its risk is `0 > -1`.

   Componentwise domination becomes sufficient with nonnegative certificate values. `CoveredV` avoids that extra restriction.

6. **MAJOR application gap — `(Abs)` does not establish its own connection to the deployed process, and sampled average ROC estimates do not discharge `Covered`.**

   The theorem covers every policy **of the specified finite concrete Markov game**. Folding private information into the state is necessary when that information affects behaviour or conditional transitions. It is not, by itself, a proof that the resulting `Gc` represents deployment.

   The lab must establish that the rows are the conditional laws after the concrete information and action have been fixed. This includes controller memory, task content, codebase state, persistent randomness, relevant monitor information, and pending audit or execution state.

   More information can destroy the proposed ROC abstraction. Suppose two equally common attack outputs have detection probabilities `1` and `0`. Their average detection probability is `1/2`. A model choosing the second output has detection probability zero. The average ROC does not cover its action.

   Similarly, if Red sees a monitor draw before choosing its output, the applicable rows must be conditioned on that draw. Reusing the unconditional monitor row is unfaithful.

   The concrete obligations are:

   - Define the catastrophe event and horizon, including whether latent damage after the horizon is excluded.
   - Prove or explicitly hypothesise that the finite concrete state represents all relevant history.
   - Cover every allowed concrete output/action, including effects on monitors, auditors and deferred execution.
   - Establish lawful conditional rows and the chosen equality, convex-hull or domination relation.
   - For deployment usefulness, establish concrete honest-row and reward coverage separately. The present `(Abs)` transfers only risk bounds.

   This does not invalidate the conditional theorem. It limits the claim to **capability-independent policy quantification conditional on universal coverage**. A finite attack evaluation does not establish that universal coverage without an additional sampling and transfer hypothesis.

7. **MINOR — `(Z)` is faithful to the safety λ-form, but the docstrings need to distinguish algebra from probability.**

   Write `A = f(qa)`, `D = f(qd)`, and `q = qa`. For a perfect auditor, the λ coefficients are:

   \[
   \lambda_1=D-A-(1-q),\quad
   \lambda_2=1-q,\quad
   \lambda_3=A,\quad
   \lambda_4=0,\quad
   \lambda_5=q,\quad
   \lambda_6=D.
   \]

   Substitution gives your `zGAC` recurrence. The zero-coin boundary also matches under your conventions. [GAC v2, Proposition C.1](https://arxiv.org/html/2409.07985v2#A3.SS1)

   When `f(qd) < f(qa)`, `(Z)` remains true: it is an identity involving signed continuation coefficients. It does **not** describe a lawful game. Likewise, unrestricted `β` need not define a policy.

   Keep the unrestricted identity as infrastructure, and add an adapter-lawfulness lemma. For probability claims require, at the relevant cells:

   ```lean
   0 ≤ qa m c ∧ qa m c ≤ qd m c ∧ qd m c ≤ 1
   0 ≤ f (qa m c) ∧
     f (qa m c) ≤ f (qd m c) ∧ f (qd m c) ≤ 1
   ```

   together with `0 ≤ β ≤ 1` and the stated zero-coin convention.

   Apply the same distinction to TMCERT `(S)`: its weak hypotheses prove an algebraic bound. Calling `risk` a probability additionally requires lawful selected rows.

8. **MINOR — `(Lip)` needs an explicit grid corollary and a certified evaluation route.**

   The constant `N` is valid: couple the Bernoulli choices, and bound the chance of any disagreement among at most `N` choices by `N |b-b'|`.

   However, checking a grid maximum alone does not upper-bound the continuous supremum. If the grid has covering radius `δ` and every grid value is certified at most `U`, the conclusion is:

   \[
   \forall b\in[0,1],\qquad \operatorname{risk}(b)\le U+N\delta.
   \]

   For the grid `j/J`, including both endpoints and with `J > 0`, nearest-point coverage gives `δ = 1/(2J)`.

   Freeze that corollary explicitly. Explain how grid values are certified—through rational instances, exact arithmetic, or proved interval enclosures. Float values plus an unverified numerical ROC are not kernel certificates.

9. **MINOR — the supplied numerical evidence and TMGAC witness wording overstate what was checked.**

   The pasted Python script has a missing outer closing brace in the final `V` dictionary and does not run unchanged.

   After repairing that brace in memory, I reproduced zero reported mismatches and the stated separation/table values. But the safety comparison checks only **241 of the 300 generated instances**: it performs `723` comparisons and skips `177` of the `900` rate-instance combinations.

   Its random `f` is not monotone. Taking `max` in `TD` repairs the game rows while changing the adapter, so skipped comparisons cannot validate the claimed `gacQ` bridge.

   Fix the evidence by:

   - generating genuinely monotone ROC tables and removing the conditional skip;
   - separately testing the unrestricted algebraic identity without clamping `TD`;
   - comparing usefulness against the corrected audited-solution reward;
   - including positive-`TA` zero-coin cases for `(W)`.

   The zero-coin theorem itself is true. With `d_n = TD n 0 - TA n 0 ∈ [0,1]`, attacking has value `1-d_n+d_n v`, while safe behaviour has value `v`. Their difference is `(1-d_n)(1-v) ≥ 0`.

   The separation inequality has a direct exact proof:

   \[
   \frac{13}{50}-
   \left(\frac34b-\frac{21}{32}b^2+\frac5{32}b^3\right)
   =\frac{(5b-4)^2(13-5b)}{800}\ge0.
   \]

   The final TMGAC witness asserts a bridge equality but no numerical result, despite saying the value is computed. Add `zGAC … = 63/64` and risk `= 1/64`.

10. **MINOR — remaining documentation and configuration gaps need explicit boundaries.**

    The blanket sentence “hiding the round index is necessary” is too strong. Your own `(W)` provides a case where the constant-rate optimum already equals the full-information optimum. Say that excluding time-dependent behaviour is part of justifying the constant-rate restriction.

    Split prior-art attribution by claim. Mallen studies restricted observations and distribution shifts; Korbak discusses temporal coordination concerns; Ctrl-Z Appendix L studies time-varying auditing against a constant attack probability. These support different statements. [Mallen §2](https://arxiv.org/html/2412.12480v4#S2), [Korbak §7.5](https://arxiv.org/html/2501.17315), [Ctrl-Z Appendix L](https://arxiv.org/html/2504.10374#A12)

    For a lab configuration, the missing pieces are:

    - **Simultaneous confidence coverage:** bands covering all thresholds and rows selected by the protocol, with quantified calibration and transfer assumptions. Frequentist confidence is not a posterior probability that an observed certificate is trustworthy.
    - **Discrete threshold semantics:** atoms and ties can prevent arbitrary FPRs from being realised. Different thresholds can share an FPR while having different TPRs. Prefer actual threshold/tie rules and their zone probabilities; explicitly disable auditing at zero coins.
    - **Lawful uncertainty sets:** intersect interval bounds with `TA ≤ TD` and probability constraints. `(Vx)` concerns convex combinations of transition rows, not arbitrary nonlinear uncertainty in fitted ROC parameters.
    - **Usefulness checking:** a rational `checkUseQ` and soundness bridge if usefulness is to be certified through the same workflow.
    - **Controller synthesis:** Blue optimisation may be an untrusted generator followed by certification. The current statements prove no Blue optimality or Pareto claim. Recheck certificates after rationalisation; independently rounding each value upward can violate a supersolution inequality.

    “No dependencies” should mean no other campaign dependencies. The files still need explicit Mathlib imports and pinned versions.

**Overall verdicts: TMCERT v1 — minor. TMGAC v0 — major.** I found no FATAL false conjunct. TMCERT can be frozen as a conditional abstract theorem after its interface and checker wording repairs. TMGAC’s GAC usefulness attribution must not be frozen unchanged.

Fixes in priority order:

1. Correct the audited-safe usefulness reward and `(UZ)`; add an audited-only witness.
2. Restrict `(M)`’s documented class to independence from both history and current state.
3. Pin and exercise `decide +kernel`; repair the numerical evidence.
4. Bound selector admissibility by the horizon.
5. Add convex-hull or `CoveredV` deployment coverage and a nonvertex example.
6. Add adapter-lawfulness and grid-margin corollaries; state the deployment and statistical obligations explicitly.

The final conjunct lists I would freeze are:

- **TMCERT:** `S_upTo ∧ S′_upTo ∧ Fx ∧ FxGap ∧ Obs ∧ T ∧ TR ∧ U_upTo ∧ Qrisk ∧ Qlawful ∧ Vx ∧ Abs_eq ∧ Abs_V`. Retain the current witness and add an interior-row coverage witness. Probability-range and checker-to-consumed-bound lemmas should accompany these.
- **TMGAC:** `L ∧ LQ ∧ Z_algebraic ∧ UZ_used ∧ M_finite_const ∧ Lip ∧ Grid_margin ∧ W ∧ T5`. Strengthen the witness with safety `63/64`, risk `1/64`, and corrected usefulness. For the small adapter witness, corrected usefulness is `3/2`. For `exG3` realised with audit and defer FPRs `1/2` while a coin remains, and defer FPR `1/2` at zero coins, corrected honest usefulness is `19/8`.