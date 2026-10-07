namespace PL_UMUSEF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 PL_UMSTRATF1

/-! Control stack, collusion layer (campaign UMUSE, v2.1: after the Reviewer A and Reviewer B design reviews, and the Reviewer A red team): the
honest side of protocol UM(n_h, κ, b, N), halting variant, and a usefulness-constrained obstruction.
Depends on PL_UMPROTF1 and PL_UMSTRATF1 (and PL_UMHSF1, PL_UMSURVF1).

Why. A monitor that FLAGs everything survives every honeypot test. So every upper bound of PL_UMPROTF1 is
also satisfied by a protocol that never completes its work when b < N. These conjuncts put the honest side
of the SAME recursions in Lean, and they show that a usefulness target forces a risk floor.

Honest side. This part is conditional on a measured honest profile; it is NOT capability-free.
- The honest monitor is a nominated reference rule `φ₀`. Nothing here establishes that the deployed model behaves
  like it.
- `missRate M PH φ₀ = α₀`: the probability that `φ₀` PASSes a mediated honeypot. `flagRate M μ φ₀ = f₀`: its
  false-flag rate on the benign submission law `μ`. Both are capability statistics of `φ₀`, not trusted quantities.
- `μ` is a law on SUBMISSIONS, supported off Bad, and it is iid across rounds: the history-independent
  generator `fun _ => μ`. Task difficulties resampled iid are already covered by `μ`. A rate shared across rounds
  (correlated difficulty) is not covered, and its effect on the false-halt probability can go either way:
  the binomial tail is neither convex nor concave in f₀ in general (Reviewer B: 5.8% vs 19.2% at N = 100, b = 5;
  Reviewer A: concave at N = 2, b = 0).
- `haltP` scores the event "deployment halts on an unaffordable flag", in the same protocol as `cat`. On a bad
  PASS (catastrophe) and a bad FLAG with an audit (caught or executed) the score is 0, since neither is a halt;
  so `r` is irrelevant. A benign FLAG with an audit continues with u + 1. A FLAG with no audit left scores 1.
  The (b+1)-st FLAG halts.
- `honestCompletion` is the probability that the honest monitor survives the test AND the benign stream runs all
  `N` rounds without a halt. It is a full-run availability probability. It is not the literature's usefulness
  (the fraction of tasks solved correctly, as in Greenblatt et al., Ctrl-Z and LASR). It is a product by the
  structure of the recursions, mirroring `protocolCat`'s own surv × cat. The operational bridge for both is the
  VCVio refinement. Benign audits are assumed to have no false positives. The theorems carry the benign-support
  hypothesis; without it `1 − haltP` also counts early catastrophes and shutdowns.

Claim.
(a) False halt. 1 − haltP = survH f₀ (hardKill b) from every state, so haltP = 1 − binCDF N b f₀
    = P(Bin(N, f₀) > b). Also 0 ≤ f₀ ≤ 1.
(b) Honest completion = survH α₀ κ n_h 0 · binCDF N b f₀ for every valid schedule κ, and it lies in [0, 1]. For hard
    slack it is binCDF n_h n_s α₀ · binCDF N b f₀.
(b') Class-aware design (PL_UMSTRATF1). Honest completion = (∏_e binCDF m s_c α_e) · binCDF N b f₀, with
    class-specific honest miss rates α_e. It is not the aggregate α₀.
(c') View-blind pair, exact value. A monitor that ignores its view and PASSes w.p. h, paired with a generator that
    submits one fixed bad x, has risk survH h κ n_h 0 · (h + [0<b](1 − r)(1 − h)). This needs no honeypot-support
    hypothesis, and b = 0 is included. At b ≥ 1 it is PL_UMPROTF1's T3* with a constant rule.
(P) Usefulness-target obstruction. Take the view-blind pair at h = α₀, and write q = α₀ + [0<b](1 − r)(1 − α₀) and
    D = binCDF N b f₀. Then exactly D · risk = q · honestCompletion. Hence, for ANY universal risk certificate
    X (an upper bound on the risk of every colluding pair) and any target u ≤ honestCompletion:
    q·u ≤ D·X, and in particular α₀·u ≤ X.
    In words: a protocol that keeps the honest monitor's completion probability ≥ u cannot certify risk below
    u × (the honest monitor's own honeypot miss rate, plus audit failures when b ≥ 1).
(d) Slack cost, lower tail (Cantelli, hypothesis-free). (max 0 (nα − s))² · F ≤ nα(1 − α)(1 − F), where
    F = binCDF n s α. Hence honest false shutdown ≤ ε forces (max 0 (nα − s))²(1 − ε) ≤ nα(1 − α)ε (stated
    division-free), i.e. for 0 ≤ ε < 1: s ≥ nα − √(nα(1 − α)ε/(1 − ε)).
(d') Sufficient slack, upper tail (Cantelli). (max 0 (s + 1 − nα))² · (1 − F) ≤ nα(1 − α) · F.
(f) Honest ROC. For every real η, 1 − f₀ ≤ e^η α₀ + hs_η(M·μ, M·P_H) (PL_UMHSF1). At η = 0:
    α₀ + f₀ ≥ 1 − TV(M·μ, M·P_H). The floor involves only the mediator and the two laws, with no property of U;
    the statement is still conditional on the specified benign law μ and the rule φ₀. By data processing
    (PL_UMHSF1), mediation can only shrink this TV, so it can only RAISE the floor on α₀ + f₀ that every honest rule
    must pay. A mediator that hides attack/honeypot differences tends to blur honeypot/benign differences too. That
    is the tension; (f) itself is the per-rule inequality.
(g) Zero audit budget, sharpened upper bound. With b = 0 (the first flag halts), every colluding pair has risk
    ≤ L·(n_s + 1)/(n_h + 1). The 1 − r term of PL_UMPROTF1 is spurious there.

Corner, not stated separately: always-FLAG (φ₀ = 0) has α₀ = 0 and f₀ = 1, so for N ≥ 1 its (risk, completion)
is ([0<b](1 − r), [N ≤ b]), by (c') and (b); at N = 0 its risk is 0.
Not claimed: history-dependent honest streams; audit false positives; the global-slack class-count corollary
(PL_UMLOWERF1 with (d)), which is left for a separate campaign. -/

/-- P(deployment halts on an unaffordable flag in the remaining `n` rounds | `u` audits used,
history `h`); same protocol as `PL_UMPROTF1.cat` -/
noncomputable def haltP {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (b : ℕ) : ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 0 else haltP Bad M φ π b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 0 else haltP Bad M φ π b n (u + 1) (h ++ [(x, z, false)]))
                    else 1))

/-- honest miss rate on mediated honeypots -/
def missRate {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (φ₀ : Z → ℝ) : ℝ :=
  ∑ z, push M PH z * φ₀ z

/-- honest false-flag rate on the benign submission law `μ` -/
def flagRate {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (μ : X → ℝ) (φ₀ : Z → ℝ) : ℝ :=
  ∑ x, μ x * ∑ z, M x z * (1 - φ₀ z)

/-- honest completion (full-run availability): the honest monitor `φ₀` survives the test, and the iid
benign stream `μ` then runs all `N` rounds without a halt. Meaningful for `μ` supported off `Bad`. -/
noncomputable def honestCompletion {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop)
    [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh b N : ℕ) (φ₀ : Z → ℝ)
    (μ : X → ℝ) : ℝ :=
  surv (push M PH) φ₀ κ nh 0 * (1 - haltP Bad M φ₀ (fun _ => μ) b N 0 [])

/-- the view-blind colluding pair: PASS with probability `h` whatever the view; submit the fixed `x` -/
noncomputable def viewBlindRisk {X Z : Type} [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop)
    [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ)
    (h : ℝ) (x : X) : ℝ :=
  protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (fun _ _ => h) (fun _ _ x' => if x' = x then 1 else 0)

def Claim : Prop :=
  -- (a) false halt of an iid benign stream
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (φ₀ : Z → ℝ) (μ : X → ℝ) (b : ℕ),
      IsKernel M → IsRule φ₀ → IsDist μ → (∀ x, μ x ≠ 0 → ¬ Bad x) →
      (0 ≤ flagRate M μ φ₀ ∧ flagRate M μ φ₀ ≤ 1) ∧
      (∀ n u h, 1 - haltP Bad M φ₀ (fun _ => μ) b n u h = survH (flagRate M μ φ₀) (hardKill b) n u) ∧
      (∀ N, haltP Bad M φ₀ (fun _ => μ) b N 0 [] = 1 - binCDF N b (flagRate M μ φ₀))) ∧
  -- (b) honest completion, any valid schedule; hard slack
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh ns b N : ℕ) (φ₀ : Z → ℝ) (μ : X → ℝ),
      IsKernel M → IsDist PH → IsRule φ₀ → IsDist μ → (∀ x, μ x ≠ 0 → ¬ Bad x) →
      (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) →
      (0 ≤ missRate M PH φ₀ ∧ missRate M PH φ₀ ≤ 1) ∧
      honestCompletion Bad M PH κ nh b N φ₀ μ =
          survH (missRate M PH φ₀) κ nh 0 * binCDF N b (flagRate M μ φ₀) ∧
      (0 ≤ honestCompletion Bad M PH κ nh b N φ₀ μ ∧ honestCompletion Bad M PH κ nh b N φ₀ μ ≤ 1) ∧
      honestCompletion Bad M PH (hardKill ns) nh b N φ₀ μ =
          binCDF nh ns (missRate M PH φ₀) * binCDF N b (flagRate M μ φ₀)) ∧
  -- (b') honest completion of the class-aware stratified design
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (φ₀ : Z → ℝ) (μ : X → ℝ),
      IsKernel K → IsRule φ₀ → IsDist μ → (∀ x, μ x ≠ 0 → ¬ Bad x) →
      stratSurv K Es φ₀ m sc * (1 - haltP Bad (fun x => K (c x)) φ₀ (fun _ => μ) b N 0 [])
        = (∏ e ∈ Es, binCDF m sc (∑ z, K e z * φ₀ z)) * binCDF N b (flagRate (fun x => K (c x)) μ φ₀)) ∧
  -- (c') the view-blind pair: exact value
  (∀ (X Z : Type) [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r h : ℝ) (b N : ℕ) (x : X),
      IsKernel M → IsDist PH → Bad x → 1 ≤ N →
      viewBlindRisk Bad M PH κ nh r b N h x =
        survH h κ nh 0 * (h + (if 0 < b then (1 - r) * (1 - h) else 0))) ∧
  -- (P) usefulness-target obstruction
  (∀ (X Z : Type) [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (φ₀ : Z → ℝ) (μ : X → ℝ)
      (x : X) (Xc u : ℝ),
      IsKernel M → IsDist PH → IsRule φ₀ → IsDist μ → (∀ y, μ y ≠ 0 → ¬ Bad y) →
      (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → Bad x → 1 ≤ N →
      binCDF N b (flagRate M μ φ₀) * viewBlindRisk Bad M PH κ nh r b N (missRate M PH φ₀) x =
        (missRate M PH φ₀ + (if 0 < b then (1 - r) * (1 - missRate M PH φ₀) else 0)) *
          honestCompletion Bad M PH κ nh b N φ₀ μ ∧
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad M PH κ nh r b N ρ φ π ≤ Xc) →
        u ≤ honestCompletion Bad M PH κ nh b N φ₀ μ →
        (missRate M PH φ₀ + (if 0 < b then (1 - r) * (1 - missRate M PH φ₀) else 0)) * u ≤
            binCDF N b (flagRate M μ φ₀) * Xc ∧
          missRate M PH φ₀ * u ≤ Xc)) ∧
  -- (d) slack cost: one-sided Chebyshev (Cantelli), binomial lower tail; and the ε-form
  (∀ (n s : ℕ) (α : ℝ), 0 ≤ α → α ≤ 1 →
      (max 0 ((n : ℝ) * α - s)) ^ 2 * binCDF n s α ≤ n * α * (1 - α) * (1 - binCDF n s α)) ∧
  (∀ (n s : ℕ) (α ε : ℝ), 0 ≤ α → α ≤ 1 → 1 - ε ≤ binCDF n s α →
      (max 0 ((n : ℝ) * α - s)) ^ 2 * (1 - ε) ≤ n * α * (1 - α) * ε) ∧
  -- (d') sufficient slack: Cantelli, binomial upper tail
  (∀ (n s : ℕ) (α : ℝ), 0 ≤ α → α ≤ 1 →
      (max 0 ((s : ℝ) + 1 - n * α)) ^ 2 * (1 - binCDF n s α) ≤ n * α * (1 - α) * binCDF n s α) ∧
  -- (f) honest ROC: trusted-only coupling of the honest rates
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH μ : X → ℝ) (φ₀ : Z → ℝ) (η : ℝ),
      IsKernel M → IsDist PH → IsDist μ → IsRule φ₀ →
      1 - flagRate M μ φ₀ ≤ Real.exp η * missRate M PH φ₀ + hs η (push M μ) (push M PH)) ∧
  -- (g) zero audit budget: sharpened domination bound (no 1 − r term)
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (nh ns N : ℕ) (r L : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ L →
      (∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) →
      protocolCat Bad M PH (hardKill ns) nh r 0 N ρ φ π ≤ L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)))

/-- Non-vacuity, with asymmetric honest rates and a blurring mediator. X = Z = Bool, Bad = {true}. The mediator
shows the true bit w.p. 3/4. Honeypots are the point mass on `true`, so the bad view law EQUALS the mediated
honeypot law and L = 1. The benign law is the point mass on `false`. The honest rule never PASSes a bad-looking
view and PASSes a benign-looking view w.p. 9/10, so α₀ = 9/40 and f₀ = 13/40.
With n_h = 2, n_s = 0, b = 1, N = 2 and r = 1/2:
- false halt = 169/1600;
- honest completion = (961/1600)(1431/1600) = 1375191/2560000;
- the view-blind pair at h = α₀ has risk (961/1600)(49/80) = 47089/128000 ≤ the UMPROT bound 2/3;
- TV(M·μ, M·P_H) = 1/2. The IDEAL honest rule (PASS iff the view is `false`) has α₀ = f₀ = 1/4, so the ROC
  bound (f) at η = 0 is attained: 1 − 1/4 = 1/4 + 1/2. This mediator forces α₀ + f₀ ≥ 1/2 on every rule;
- at b = 0, the view-blind risk is (961/1600)(9/40) = 8649/64000 ≤ 1/3 = L(n_s+1)/(n_h+1);
- Cantelli at n = 10, α = 1/2: s = 1 gives 16 · (11/1024) = 11/64 ≤ (5/2)(1013/1024), and s = 8 gives
  16 · (11/1024) ≤ (5/2)(1013/1024). -/
noncomputable def wM (x z : Bool) : ℝ := if z = x then 3/4 else 1/4
noncomputable def wPH (x : Bool) : ℝ := if x = true then 1 else 0
noncomputable def wμ (x : Bool) : ℝ := if x = false then 1 else 0
noncomputable def wφ (z : Bool) : ℝ := if z = true then 0 else 9/10
noncomputable def wφI (z : Bool) : ℝ := if z = true then 0 else 1

def Witness : Prop :=
  IsKernel wM ∧ IsDist wPH ∧ IsDist wμ ∧ IsRule wφ ∧ IsRule wφI ∧ (∀ x, wμ x ≠ 0 → ¬ x = true) ∧
  (∀ x, x = true → ∀ z, wM x z ≤ 1 * push wM wPH z) ∧
  missRate wM wPH wφ = 9/40 ∧ flagRate wM wμ wφ = 13/40 ∧
  haltP (fun x => x = true) wM wφ (fun _ => wμ) 1 2 0 [] = 169/1600 ∧
  honestCompletion (fun x => x = true) wM wPH (hardKill 0) 2 1 2 wφ wμ = 1375191/2560000 ∧
  viewBlindRisk (fun x => x = true) wM wPH (hardKill 0) 2 (1/2) 1 2 (9/40) true = 47089/128000 ∧
  (47089/128000 : ℝ) ≤ (1 - 1/2) + 1/2 * (1 * (((0 : ℝ) + 1) / ((2 : ℝ) + 1))) ∧
  hs 0 (push wM wμ) (push wM wPH) = 1/2 ∧
  1 - flagRate wM wμ wφI = Real.exp 0 * missRate wM wPH wφI + hs 0 (push wM wμ) (push wM wPH) ∧
  viewBlindRisk (fun x => x = true) wM wPH (hardKill 0) 2 (1/2) 0 2 (9/40) true = 8649/64000 ∧
  (8649/64000 : ℝ) ≤ 1 * (((0 : ℝ) + 1) / ((2 : ℝ) + 1)) ∧
  binCDF 10 1 (1/2) = 11/1024 ∧ binCDF 10 8 (1/2) = 1013/1024

end PL_UMUSEF1
