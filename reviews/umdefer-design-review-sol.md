**Verdict: major revision. Do not freeze the draft as written.** I find no mathematical counterexample to formal conjuncts (a)–(d) or the numerical Witness under the supplied recurrence. The problems are the uncharged audit resource, insufficiently explicit trust assumptions, a false asymptotic claim, and conclusions that exceed the protocol being modelled.

The mathematical checks below are arguments about the proposed definitions, not completed Lean proofs of `Claim`. I type-checked the proposed replacement definitions and scalar proof lemmas, checked two additional numerical witnesses in Lean, and ran exact Bellman maximisation on 87,500 small rational states.

Write
\[
C_r(A)=1-r+rA,\qquad
D_\theta(A)=\theta+A(1-\theta),\qquad
F_\theta(A)=\frac{A}{D_\theta(A)}.
\]

1. **MAJOR — `catD` audits after “no audit is left”, without accounting for the resource.**

   **Exact definition:** the exhausted-budget branch
   ```lean
   (1 - η) * ((if Bad x then 1 - q * r else 1) *
     catD ... n u ...)
   ```
   retains `u` while performing an additional audit with probability `q`.

   This models a separately supplied audit service. It does not model a total deployment audit budget of `b`. Consequently, (c)’s horizon-independent guarantee depends on an audit resource whose required provision can grow with `N`.

   If these are the same strong audits counted by `b`, they must consume the same resource. At `u ≥ b`, none remain. Incrementing `u` beyond `b` would record expenditure without enforcing a budget.

   **Concrete fix:** choose and document one resource model:

   - Rename `b` as the allowance for the ordinary audit path and explicitly assume a separately funded deferred-item audit service.
   - Add a reserve counter `v` and reserve capacity `d`; consume it whenever a deferred audit is selected, including on benign items.
   - Partition a single total budget between ordinary and deferred audits, then specify the fallback after both allocations are exhausted.

   For example, an exhausted ordinary-budget flag could use:
   ```lean
   if v < d then
     (1 - η) *
       ((1 - q) * cont v +
        q * (if Bad x then 1 - r else 1) * cont (v + 1))
   else
     0  -- halt when the reserve is exhausted
   ```
   Here `cont v` abbreviates continuation with reserve usage `v`. This is a different protocol and needs its own recurrence.

   The existing `if Bad x` is not itself an oracle implementation error: with uncharged audits, no false positives, and no audit-outcome observation, benign audits can be marginalised out. **That simplification becomes invalid for resource accounting.**

2. **MAJOR — `q * r` needs a conditional guarantee, not an average audit or detection rate.**

   **Exact definitions:** `theta` and the factor `1 - q * r` in `catD`.

   The positive result requires, on every reachable deferred bad flag, a safe-ending probability at least `q*r`, conditional on the history and survival so far. An evaluation average does not provide this.

   A concrete failure of the average interpretation: let `A = 1/10`, `r = 1`, `η = 0`, and draw one deployment-wide coin. With probability `1/2`, audit every deferred flag; otherwise audit none. The nominal marginal audit rate is `q = 1/2`, but three always-attack rounds have risk
   \[
   \tfrac12\cdot\tfrac1{10}
   +\tfrac12\left(1-(9/10)^3\right)
   =\frac{371}{2000}
   >\frac2{11}.
   \]
   Thus even (b)’s infinite-horizon bound fails under that interpretation of `q`.

   Similarly, a deterministic auditor that misses one repeatable attack cannot acquire an independent catch chance `r` merely because its average evaluation recall is `r`.

   **Concrete fix:** state the implementation contract explicitly:

   \[
   P(\text{audit selected}\mid h,x,z,\text{deferred})\ge q,
   \]
   \[
   P(\text{absorbing shutdown}\mid h,x,z,\text{selected audit},Bad(x))\ge r.
   \]

   These bounds must hold uniformly over adversarially selected submissions and reachable histories. Fresh independent audit coins are one sufficient implementation; a conditional probability bound is the more general requirement.

   Better still, parameterise the exhausted branch by a **conditional safe-ending floor** `α`, with
   \[
   \theta_*=\eta+(1-\eta)\alpha.
   \]
   Prove the safety theorem for that floor. Separately justify `α ≥ q*r` for a particular audit implementation.

   Immediate shutdown is also substantive. Audits reviewed after several more submissions require a pending-audit state or a bound on how many attacks can occur before shutdown takes effect.

3. **MAJOR — replacement is a defensible abstraction, but the draft models only a particular hybrid protocol.**

   **Exact branches:** exhausted bad flags continue without catastrophe; affordable bad flags return `1 - r`.

   “A deferred bad submission is replaced, so that submission does not execute” is faithful to defer-to-trusted. Greenblatt et al. explicitly replace suspicious untrusted solutions with trusted solutions; Games for AI Control gives Blue separate Run, Audit, and Defer actions, with Defer continuing the game. [Greenblatt et al., §3.3](https://arxiv.org/html/2312.06942v5#S3.SS3), [Games for AI Control](https://arxiv.org/html/2409.07985v2)

   However, UMDEFER defers **only after ordinary audit exhaustion**. Before exhaustion, a missed audit executes the flagged attack. That is a legitimate extension of the frozen halting core, but it is not a general model of labs’ defer-to-trusted routing.

   The zero catastrophe contribution also assumes:

   - submissions are proposals with no harmful effects before execution;
   - replacement removes the original attack completely;
   - the trusted replacement cannot itself cause the catastrophe;
   - replacement does not preserve dangerous state already created by the rejected proposal.

   “Trusted” meaning non-scheming does not, by itself, establish all these properties.

   **Concrete fix:** name this an **audit-then-defer-after-exhaustion protocol**, and state the replacement contract independently. If trusted replacement has a uniform conditional failure bound `εT`, add an appropriate term, such as the conservative `N * εT`, to a guarantee covering all catastrophes.

   If the intended protocol replaces flagged proposals even when auditing them, change the affordable bad-flag branch to safe replacement followed by continuation on a missed audit. Do this in a new variant; do not silently reinterpret the frozen core.

   Also: `η = 1` halts **on an unaffordable flag**. It does not halt immediately when `u` reaches `b`; subsequent PASSes can still execute.

4. **MAJOR — random auditing of archived deferred items is not a model of Ctrl-Z incrimination.**

   **Exact prose:** “Random audits of a fraction `q` of the deferred items are the incrimination condition”, together with the suggested Ctrl-Z interpretation.

   The recurrence can describe auditing archived originals, under the contracts above. It does not describe resampling, score aggregation, selecting among alternatives, or collecting additional evidence.

   Ctrl-Z’s incrimination protocols use additional samples to improve auditing decisions; the benefit depends on attack continuation behaviour. Those audits still use limited human labour. The paper does not establish a uniform `q*r` catch probability for every adaptive attacker. [Ctrl-Z, §3.2 and §2.2](https://arxiv.org/html/2504.10374v1)

   **Concrete fix:** describe UMDEFER as an abstract stopping-hazard model. A Ctrl-Z implementation needs either:

   - an explicit resampling/evidence/auditing kernel and resource model; or
   - a separate theorem establishing the required conditional stopping floor for that kernel.

   Resampling frequency is not `q`, and empirical incrimination performance is not the required infimum over adversarial histories.

5. **MINOR — the max in (b) is correct; the explanation should say precisely why adaptation cannot defeat it.**

   **Exact conjunct:** (b).

   An attack at `u < b` cannot attack and then continue under this recurrence. PASS causes catastrophe; FLAG causes either catastrophe through a missed audit or absorbing shutdown. Its value is
   \[
   C_r(a)=a+(1-a)(1-r)\le C_r(A).
   \]

   A benign submission can continue and spend an audit. That is exactly why taking only the initial “first bad” term would be wrong, and why the max with the exhausted-budget term is necessary.

   At `u ≥ b`, a bad submission with pass rate `a ≤ A` has value bounded by
   \[
   a+(1-a)(1-\theta)F_\theta(A)\le F_\theta(A).
   \]
   This follows from
   \[
   D_\theta(A)F_\theta(A)=A,\qquad 0\le F_\theta(A)\le1.
   \]
   Benign rounds introduce no catastrophe and have continuation coefficient at most one. Randomisation and history-dependent mixtures therefore preserve the bound.

   This also answers the re-randomisation concern: the generator can change submissions, provided the bound applies to **every** bad submission. Changing the monitor rule after its honeypot test is outside the model.

   **Concrete fix:** replace the informal “geometric trial” argument for arbitrary generators with this supersolution argument. Reserve the geometric equality for a fixed always-attack policy.

6. **MAJOR — (b) discards the finite horizon, excludes an important boundary, and leaves its attainment claim outside Lean.**

   **Exact conjunct:** (b), its `0 < theta` hypothesis, and the prose “attained in the limit”.

   Use the denominator-free recurrence
   \[
   R_0(A,\theta)=0,\qquad
   R_{n+1}(A,\theta)=A+(1-A)(1-\theta)R_n(A,\theta).
   \]

   A stronger state bound is
   \[
   catD(n,u,h)\le
   \begin{cases}
   0,&n=0,\\
   \max\!\left(C_r(A),R_{\,n-(b-u)}(A,\theta)\right),&u<b,\\
   R_n(A,\theta),&u\ge b,
   \end{cases}
   \]
   using truncated natural subtraction.

   Burning the remaining `b-u` audits requires at least that many benign rounds. The current bound loses this information.

   **Concrete Lean definitions:**
   ```lean
   def retry (A θ : ℝ) : ℕ → ℝ
     | 0 => 0
     | n + 1 => A + (1 - A) * (1 - θ) * retry A θ n

   def finiteCap (r A θ : ℝ) (b n u : ℕ) : ℝ :=
     if n = 0 then 0
     else if u < b then
       max (1 - r + r * A) (retry A θ (n - (b - u)))
     else retry A θ n
   ```
   Freeze the state bound under (b)’s probability hypotheses **without** requiring `0 < theta`.

   This covers the requested edges directly:

   | Edge | Correct behaviour |
   |---|---|
   | `A = 0`, exhausted budget | risk `0` |
   | `A = 0`, audit available | risk can be `1-r` |
   | `θ = 0` | `retry A 0 n = 1-(1-A)^n` |
   | `b = 0` or `u > b` | exhausted-budget recurrence |
   | `n = 0` | risk `0` |
   | `n ≤ b-u` | no exhausted-budget attack fits; bound `C_r(A)` |

   The exact identity
   \[
   D_\theta(A)R_n(A,\theta)
   =A\left(1-\big((1-A)(1-\theta)\big)^n\right)
   \]
   needs no division and remains true at the degenerate boundary.

   For a fixed bad submission whose pass rate is exactly `A`, the exhausted-budget value equals `R_n`. Add this equality and its limit as formal conjuncts. Attainment does not follow merely from an upper bound `A` that might be unattainable.

   Incidentally, (b)’s ratio bound can be extended to `θ = 0` with an explicit zero-denominator case. For `A > 0` it becomes `1`; for `A = θ = 0` exhausted risk is `0`. The finite statement expresses this more cleanly.

7. **MAJOR — (c) is true, but is too coarse to be the main protocol certificate.**

   **Exact conjunct:** (c).

   Let
   \[
   H=L\frac{n_s+1}{n_h+1}.
   \]
   For each seed, write its honeypot pass probability as `h` and survival as `S`. Domination gives `a ≤ min(1,Lh)`. The frozen counting lemma gives `Sh ≤ (n_s+1)/(n_h+1)`. Hence, pointwise in the seed,
   \[
   S C_r(a)\le(1-r)+rH,\qquad
   S F_\theta(a)\le H/\theta.
   \]
   Thus the proposed max bound holds before averaging seeds. There is no illicit interchange of expectation and max.

   The deficiencies are:

   - it includes the affordable-audit failure term even when `b = 0`;
   - it ignores `N`, including `N = 0`;
   - it can exceed `1`;
   - it discards the denominator improvement in (b);
   - it hides whether a target risk is reachable with feasible `q`.

   **Concrete fix:** make the finite curve the primary certificate. Define
   \[
   G_{b,N}(a)=finiteCap(r,a,\theta,b,N,0).
   \]
   Then prove
   \[
   protocolCatD\le
   \sup_{0\le t\le1}
   survH(t,\kappa,n_h,0)\,
   G_{b,N}\big(\min(1,Lt)\big).
   \]

   Lean need not start with a supremum. Prove the directly usable certificate:
   ```lean
   (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
       survH t κ nh 0 *
         finiteCap r (min 1 (L * t)) (theta r η q) b N 0 ≤ U)
   →
   protocolCatD ... ≤ U
   ```
   with the usual hypotheses. A certified numerical envelope can then establish `U`.

   Retain (c) as a simpler corollary, capped at `1` and with the affordable term absent when `b = 0`.

   The requested extensions are straightforward:

   - **Hockey-stick:** substitute `min 1 (Real.exp eps * t + δ)`.
   - **Soft slack:** use the existing survival curve; the coarse analogue replaces `(n_s+1)/(n_h+1)` by `n_s/(n_h+1)`, requiring `1 ≤ n_s`.

   The `1/θ` inflation is asymptotically unavoidable:
   \[
   F_\theta(A)/A\longrightarrow1/\theta
   \quad(A\downarrow0).
   \]
   But the coarse certificate is not tight. For no slack, exact matching honeypots, exhausted budget, and an infinite deployment:

   | `n_h` | `θ` | Optimised exact risk | Current coarse retry bound |
   |---:|---:|---:|---:|
   | 100 | 1 | 0.00366 | 0.00990 |
   | 100 | 0.01 | 0.20627 | 0.99010 |
   | 100 | 0.001 | 0.55726 | 9.90099 |

   These differences materially affect a required audit rate.

8. **MAJOR — the asymptotic sentence in (d) is false.**

   **Exact prose:** the expression “tends to 1 as `N-b → ∞` at `t ≈ 1/n_h`”.

   For fixed `0 < t ≤ 1`,
   \[
   \lim_{K\to\infty}
   binCDF(n_h,n_s,t)\big(1-(1-t)^K\big)
   =binCDF(n_h,n_s,t).
   \]
   With `n_s = 0` and `t = 1/n_h`, this is approximately `e^{-1}`, not `1`.

   The formal equality and lower bound in (d) remain true. The prose has changed the quantifiers.

   **Concrete fix:** say:
   > For fixed finite `n_h`, the supremum over colluding rules tends to one as the remaining deployment horizon grows; the selected rule’s pass probability decreases with that horizon.

   For `n_s = 0`, `n_h > 0`, and `K > 0`, the exact optimum is
   \[
   t^*=1-\left(\frac{n_h}{n_h+K}\right)^{1/K},
   \]
   with value
   \[
   \frac K{n_h+K}
   \left(\frac{n_h}{n_h+K}\right)^{n_h/K}.
   \]
   This tends to `1` as `K/n_h → ∞`. Choosing `t_K=K^{-1/2}` also establishes the fixed-`n_h` limit.

   “Honeypots buy only about `n_h` in retries” should become a precise horizon statement. For example, with no slack and `K=n_h`, the optimised risk is exactly `1/4`; different slack and target-risk choices change the relevant constant.

9. **MINOR — strengthen (d)’s honeypot quantification; remove its unnecessary `b ≤ N` restriction.**

   **Exact conjunct:** (d).

   Within the specified Bool identity model, point mass on `true` is the strongest honeypot law **against this colluder family**. For an arbitrary law `PH`, its honeypot pass rate is
   \[
   PH(true)\,t\le t.
   \]
   Its risk is exactly
   \[
   binCDF(n_h,n_s,PH(true)t)
   \big(1-(1-t)^{N-b}\big),
   \]
   which is at least the point-mass value.

   **Concrete fix:** quantify over every `PH : Bool → ℝ` satisfying `IsDist PH`; retain the point-mass equality as a special case. Every `n_s` is already quantified in the draft.

   The equality also holds when `N < b`: the generator submits only benign items, and natural subtraction makes `N-b=0`, so both sides vanish. Remove `b ≤ N`.

   Endpoint checks:

   - `t = 0`: risk zero.
   - `N = b`: risk zero.
   - `t = 1`, `N > b`: risk is `binCDF n_h n_s 1`, hence zero when `n_s < n_h`, and one when `n_s ≥ n_h`.
   - `n_h = 0`, `N > b`: choosing `t = 1` gives risk one.

   The unrestricted real `r` in (d) is algebraically harmless: the policy never attacks while an audit is available, and `q=0` eliminates later dependence on `r`.

10. **MAJOR — the burn policy is legitimate here, but the no-go does not transfer automatically to lab protocols.**

   **Exact definition:** `burnThenAttack`, and the title-level claim “defer-to-trusted needs incrimination”.

   On histories reachable under the specified monitor, the first `b` rounds are deterministic benign flags. Their flag count equals audits used. Afterward, attacking is legal. There is no circularity or prohibited observation.

   However, the model permits:

   - arbitrary benign submissions that the colluder can flag;
   - no trusted response to excessive benign flags;
   - repeated availability of the desired attack;
   - continued untrusted operation after each local deferral.

   A lower bound for this enlarged free-submission adversary does not establish the same lower bound for a restricted task stream unless those opportunities exist.

   Greenblatt et al. already address benign submissions exhausting the monitoring budget: their protocol checks excessive false positives and temporarily switches to trusted outputs while collecting further data. Gardner-Challis et al. also identify inverse honeypots as a defence against this behaviour. [Greenblatt et al., Appendix G](https://arxiv.org/html/2312.06942v5#A7), [Gardner-Challis et al., modelling limitations](https://arxiv.org/html/2602.20628v2)

   **Concrete fix:** scope the no-go to the stated free-submission protocol without a benign-flag guard. For a lab-facing lower bound, state an admissible burn-and-retry opportunity assumption or model the guard.

   The appropriate conclusion is:

   > Local replacement without a stopping mechanism does not provide a nontrivial guarantee uniform over arbitrarily long deployments when positive-pass attacks remain repeatedly available.

   It is not a general necessity theorem for incrimination. Finite horizons, zero attack pass probability, permanent switching to trusted operation, and stopping mechanisms can avoid this conclusion.

11. **MAJOR — the lab decision must be expressed as a feasible target-risk condition.**

   **Exact conjunct:** (c), and “incrimination … costs at most a factor `1/θ`”.

   From the current coarse certificate, risk at most `ε < 1` is certified by
   \[
   (1-r)+rH\le\varepsilon,\qquad H\le\varepsilon\theta.
   \]
   For `0 < r`, `η < 1`, this gives the sufficient condition
   \[
   q\ge
   \max\!\left(
   0,\frac{H/\varepsilon-\eta}{(1-\eta)r}
   \right),
   \]
   subject to `q ≤ 1` and the first inequality.

   With `η = 0`, `r = 1`, this becomes `q ≥ H/ε`. As an illustration, `L=1`, `n_s=5`, `n_h=10,000`, and target `ε=10^{-3}` require roughly **60% of deferred items audited** under this coarse certificate. That is not a small audit fraction, and its funding must be specified.

   There is also a real affordable-audit floor: with `b>0`, `N>0`, a nonempty bad set, and a monitor that flags everything, immediate attack has risk `1-r`. No choice of post-exhaustion `q` removes it.

   **Concrete fix:** freeze the target-risk corollary, including feasibility conditions, and use the finite curve for practical parameter selection. State precisely which decision it supports:

   - fund a deferred-audit reserve;
   - halt on an unaffordable flag;
   - permanently switch to trusted operation;
   - or alter the affordable audit path to replace flagged originals.

   A safety-only model cannot decide the optimal choice among these without costs or usefulness.

12. **MAJOR — domination and the adversarial scope need an independently defensible implementation contract.**

   **Exact conjuncts:** (b)’s uniform pass bound and (c)’s pointwise domination hypothesis.

   These are sup-type assumptions. An average pass rate or average attack-evaluation result cannot substitute for them.

   The frozen class-coverage theorem supplies one possible justification: a content-only mediator and honeypot mass at least `p` on every bad class imply `L=1/p`. But that shifts the obligation to complete class coverage and enforced mediation. The frozen leakage floor also limits how small `L` can be.

   **Concrete fix:** attach the intended structural instantiation to the campaign: the covered submission space, bad-class coverage, mediator contract, and provenance of the uniform trusted-auditor guarantee.

   Likewise, the monitor is restricted to a single stateless `φ ω`. A monitor that can distinguish testing from deployment can flag all honeypots and pass deployment attacks. The programme’s “every policy” claim therefore needs trusted enforcement of the observation and state restrictions.

   The generator seeing `(x,z,false)` does not invalidate the bound. It supplies extra adversarial information already covered by the history-uniform induction. Actual replacement outputs and audit metadata are absent from `Hist`, so the recurrence is not a full agent-loop model; the positive argument can tolerate richer observations if its conditional hypotheses remain uniform.

13. **MINOR — the Witness does not exercise retry suppression.**

   **Exact conjunct:** the one-round `catD = 1/10` Witness.

   One exhausted-budget round has catastrophe probability `A` independently of `q`. It cannot distinguish the positive incrimination mechanism from the no-incrimination variant.

   **Concrete fix:** add a two-round comparison:
   ```lean
   example : catD (X := Unit) (Z := Unit) (fun _ => True)
       (fun _ _ => 1) (fun _ => 1/10) (fun _ _ => 1)
       1 0 (1/2) 0 2 0 [] = 29/200 := by
     norm_num [catD]

   example : catD (X := Unit) (Z := Unit) (fun _ => True)
       (fun _ _ => 1) (fun _ => 1/10) (fun _ _ => 1)
       1 0 0 0 2 0 [] = 19/100 := by
     norm_num [catD]
   ```
   Both checked in Lean. Also include applicability and an informative numerical instance of the protocol-level certificate.

14. **MAJOR — novelty must be narrowed; the stopping ratio and replacement-versus-incrimination distinction are prior art.**

   All four supplied arXiv identifiers resolve to the expected papers:

   | Verified identifier | Prior art that constrains UMDEFER’s claim |
   |---|---|
   | [2409.07985 — Griffin, Thomson, Shlegeris, Abate](https://arxiv.org/abs/2409.07985) | Formal AI-Control Games; trusted monitoring includes Audit, Defer, and Run. |
   | [2312.06942 — Greenblatt et al.](https://arxiv.org/abs/2312.06942) | Defer-to-trusted, untrusted monitoring, and a defence against benign budget exhaustion. |
   | [2602.20628 — Gardner-Challis et al.](https://arxiv.org/abs/2602.20628) | Explicit win/continue/lose calculations and the `u/(c+u)` factor. |
   | [2504.10374 — Bhatt et al., Ctrl-Z](https://arxiv.org/abs/2504.10374) | Resampling, incrimination, and finite-bin stopping calculations. |

   There is an even more direct antecedent: Shlegeris’s November 2024 treatment explicitly distinguishes replacement from auditing and derives safety from the relative probabilities of execution and incriminating shutdown. [Win/continue/lose scenarios and execute/replace/audit protocols](https://blog.redwoodresearch.org/p/wincontinuelose-scenarios-and-executereplaceaudi)

   Here,
   \[
   u=A,\qquad c=(1-A)\theta,
   \]
   so
   \[
   F_\theta(A)=\frac{u}{u+c}.
   \]
   The geometric identity is classical infrastructure, as permitted by the programme.

   **Concrete fix:** claim the specific adaptive-generator bound, its budget-sensitive finite form, its honeypot composition, and its Lean formalisation. Do not claim discovery of the stopping ratio or of the need to distinguish replacement from incrimination. I did not establish that this exact theorem package already appears elsewhere.

For Lean, the clean route is the finite recurrence followed by algebraic corollaries. The current ratio theorem is provable by induction generalised over `u` and `h`; its denominator is positive because `D ≥ θ > 0`, and `F ≤ 1` because `D-A = θ(1-A) ≥ 0`.

A useful scalar lemma, checked in Lean, is:
```lean
theorem retry_step_supersolution (a A θ V : ℝ)
    (haA : a ≤ A) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hV0 : 0 ≤ V) (hV1 : V ≤ 1)
    (hbalance : A ≤ (θ + A * (1 - θ)) * V) :
    a + (1 - a) * (1 - θ) * V ≤ V := by
  have hslope : 0 ≤ 1 - (1 - θ) * V := by nlinarith
  have hprod : 0 ≤ (A - a) * (1 - (1 - θ) * V) :=
    mul_nonneg (sub_nonneg.mpr haA) hslope
  nlinarith [hprod]
```

For `D > 0`, the current upper bound is equivalently
```lean
D * catD ... ≤
  max (D * (if u < b then 1 - r + r * A else 0)) A
```
This removes division from the induction. At `D=0`, that multiplicative statement is vacuous; the finite recurrence supplies the missing content.

**Overall verdict: major.** Fix resource accounting and conditional trust contracts first; replace the main bound with the finite certificate and a feasible target-risk corollary second; correct and scope the no-go third; rewrite novelty and strengthen the Witness fourth.

The final conjuncts I would freeze are:

1. Halting recovery for both `catD` and `protocolCatD`.
2. Probability bounds `0 ≤ catD ≤ 1`, including `θ=0`.
3. The finite state bound using `finiteCap`.
4. Exact always-attack `retry` attainment, its multiplicative closed form, and its limit when the denominator is positive.
5. The current ratio bound as a corollary.
6. A general survival-curve certificate, instantiated for domination and hockey-stick assumptions, with hard- and soft-slack corollaries.
7. A target-risk corollary with explicit feasible conditions on `q`, `η`, and the audit resources.
8. The no-incrimination equality for every Bool honeypot law and every `N`, its point-mass lower bound, and a correctly quantified near-one asymptotic.
9. Witnesses that exercise two-round retry suppression and protocol-level composition.

I would not freeze a general “defer-to-trusted needs incrimination” necessity claim or identify this recurrence with Ctrl-Z resampling.