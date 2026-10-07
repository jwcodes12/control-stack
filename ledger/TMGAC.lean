namespace PL_TMGACF1
open Finset PL_TMCERTF1

/-! Control stack, trusted-monitoring layer (campaign TMGAC, v1 after the Reviewer-A and Reviewer-B design reviews of v0): the Games-for-AI-Control trusted-monitoring game (Griffin,
Thomson, Shlegeris, Abate, arXiv 2409.07985 v2, §4 and App. C; perfect auditor; memoryless threshold protocols) as an
instance of the certificate checker PL_TMCERTF1, with an exact bridge to its safety and usefulness recurrences, and an
exact separation between GAC's Red class and a Red that knows only the round index. Depends on PL_TMCERTF1.

The game `gac`. The state is the number c ∈ {0, …, C} of audit coins left; the index n is the number of problems left
minus one. Blue's thresholds enter through zone probabilities: a backdoor (Red action `true`) lies in the audit zone
w.p. TA n c and in the audit-or-defer zone w.p. TD n c; a safe solution lies in the audit zone w.p. FA n c. A backdoor
audited with a coin is caught (safe end, absorbing); audited with no coin it is run (GAC: "if the protocol attempts to
audit when no audit coins are left, the code is run instead"); deferred, the game continues; run, catastrophe. A safe
solution in the audit zone uses a coin; otherwise it continues with the same coins.

The threshold adapter `gacQ`. With the trusted monitor's ROC f (TPR at FPR q) and Blue's audit and defer FPRs
qa m c ≤ qd m c (m = problems left, so m = n + 1): TA n c = f (qa (n+1) c), TD n c = f (qd (n+1) c), FA n c = qa (n+1) c.
GAC's convention at c = 0 is that no audit is attempted: qa m 0 = 0, f 0 = 0. It is the only reading under which both
GAC boundary formulas at c = 0 hold; `gac` with TA > 0 at c = 0 (an attempted audit with no coin runs the code) is a third
reading, covered by (L) and (W) but not by the bridges.

Claim.
(L) `gac` is lawful whenever 0 ≤ TA ≤ TD ≤ 1 and 0 ≤ FA ≤ 1.
(LQ) The adapter is lawful for valid thresholds (0 ≤ qa ≤ qd ≤ 1) and an ROC with 0 ≤ f(qa) ≤ f(qd) ≤ 1.
(Z) Bridge to GAC App. C.1 (perfect auditor; λ₁ = D − A − (1 − q), λ₂ = 1 − q, λ₃ = A, λ₄ = 0, λ₅ = q, λ₆ = D with
    A = f(qa), D = f(qd), q = qa): for `constRed β`, 1 − risk equals the safety recurrence zGAC, for every m and c, under
    the c = 0 convention. It is an algebraic identity (true for any real f and β); it is a statement about probabilities
    under (LQ) and 0 ≤ β ≤ 1. The printed c = 0 boundary of Prop. C.1 writes the FPR where its own case analysis needs
    the TPR f(qd); zGAC follows the case analysis.
(UZ) Bridge to GAC's usefulness (App. C.2, perfect auditor): the expected number of honest solutions USED (run, or
    audited and found safe; a deferred solution is replaced by the trusted model's and does not count) is the
    recurrence uGAC, with per-round reward 1 − qd + [c > 0]·qa. So safety and usefulness of the SAME controller are both
    PL_TMCERTF1 quantities (risk with `constRed`; `honestER` with the honest action `false`).
(M) Fixed-rate bound: if every constant rate b ∈ [0, 1] has risk ≤ U, so does every finite-support mixture of
    constant rates (shared random β). GAC's sup over β is therefore a sound bound for finite mixtures of policies whose
    conditional action law, given the seed, is the same Bernoulli rate at EVERY history and current state; it is not a
    certificate in the sense of PL_TMCERTF1.
(Lip) Lipschitz bound for constant rates in any lawful game with Boolean actions: |risk(b) − risk(b')| ≤ N·|b − b'|
    (tight). (Grid) Hence if risk(j/J) ≤ U for j = 0, …, J (J > 0), then risk(b) ≤ U + N/(2J) for every b ∈ [0, 1]. The grid
    values must themselves be certified (exact rational instances or proved enclosures); at N = 100 a tolerance of 10⁻²
    needs J ≈ 5000.
(W) Without loss of generality at C = 0: always backdooring attains the full-information value Vstar.
(T5) Separation (sensitivity to GAC's null-observation assumption). Three problems, one coin; while the coin remains, a
    backdoor is in the audit zone w.p. 3/4 and a safe solution w.p. 1/2; the defer threshold stays at 3/4 when the coin
    is gone (GAC-style; no audit then). Every constant rate has risk 3/4·b − 21/32·b² + 5/32·b³ ≤ 13/50 (equality at
    b = 4/5). The Red that sees only the round index and backdoors the last two problems has risk 11/32, which is the
    full-information value Vstar. 13/50 < 11/32. A Red that ignores the history (no clock) but sees the coin count
    (backdoor iff no coin is left) has risk 9/32 > 13/50. The instance is a genuine GAC protocol (Witness: exG3 = gacQ
    with f q = min 1 (3q/2), qa = qd = 1/2 while the coin remains); it audits half of all honest problems with one coin,
    so it is a small exact illustration, not a realistic configuration.

Reading. GAC states its Red class explicitly (memoryless, null observation: Red does not observe the time or the number of
coins left), so (T5) is not a refutation of GAC: it is an exact measurement of how much GAC's guarantee depends on that
assumption, plus a certificate (PL_TMCERTF1 with Vstar) that holds without it. Excluding time- and state-dependent
behaviour is part of what justifies the constant-rate restriction; it is not always necessary ((W): at C = 0 the
constant rate already attains the full-information value). Float numerics, not Lean
(numerics/gac_realistic.py; reviewers' scripts): with 100 problems, 2 coins, GAC's fitted Beta(7.39, 6.86) /
Beta(8.91, 2.82) score laws, constant audit FPR 2% while coins remain and defer FPR 10%: fixed-rate grid maximum 0.36,
"backdoor only the last 13 problems" 0.67, full information 0.71; a Red that observes only c reaches about 0.57. The
related prior art, by claim: restricted Red observations and the withholding of the round number are deliberate design
choices in Mallen et al. 2412.12480 (subversion-strategy evaluation); temporal coordination through timestamps, dates and
codebase messages is discussed in Korbak et al. 2501.17315 (§7.5); time-varying auditing against a constant attack rate
is studied in Ctrl-Z 2504.10374 (App. L); Greenblatt et al. 2312.06942 discuss the attack-rate choice. Hiding the round
index alone is not sufficient (memory, task order, codebase state and shared signals are other clocks). -/

/-- the GAC trusted-monitoring game with C audit coins; action `true` = backdoor -/
noncomputable def gac (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) : Game (Fin (C + 1)) Bool where
  cat n c a := if a then (if 0 < c.val then 1 - TD n c.val else 1 - TD n c.val + TA n c.val) else 0
  K n c a c' :=
    if a then (if c' = c then TD n c.val - TA n c.val else 0)
    else if 0 < c.val then
      (if c'.val + 1 = c.val then FA n c.val else 0) + (if c' = c then 1 - FA n c.val else 0)
    else (if c' = c then 1 else 0)

/-- GAC's thresholds: ROC f, audit and defer false-positive rates indexed by problems left m = n + 1 -/
noncomputable def gacQ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) : Game (Fin (C + 1)) Bool :=
  gac C (fun n c => f (qa (n + 1) c)) (fun n c => f (qd (n + 1) c)) (fun n c => qa (n + 1) c)

/-- GAC's Red: backdoor with probability β on every problem, whatever the history -/
def constRed {S : Type} (β : ℝ) : RHist S Bool → S → Bool → ℝ :=
  fun _ _ a => if a then β else 1 - β

/-- GAC Prop. 4.1 / App. C, perfect auditor: P(no catastrophe), m problems left, c coins -/
noncomputable def zGAC (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (β : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | m + 1, 0 => (1 - β + β * f (qd (m + 1) 0)) * zGAC f qa qd β m 0
  | m + 1, c + 1 =>
      β * f (qa (m + 1) (c + 1))
      + (β * (f (qd (m + 1) (c + 1)) - f (qa (m + 1) (c + 1))) + (1 - β) * (1 - qa (m + 1) (c + 1)))
          * zGAC f qa qd β m (c + 1)
      + (1 - β) * qa (m + 1) (c + 1) * zGAC f qa qd β m c

/-- the used-solution reward of one honest round (perfect auditor): run, or audited (with a coin) -/
noncomputable def usedReward (qa qd : ℕ → ℕ → ℝ) (n c : ℕ) : ℝ :=
  1 - qd (n + 1) c + (if 0 < c then qa (n + 1) c else 0)

/-- GAC App. C.2, unnormalised: expected number of honest solutions used -/
noncomputable def uGAC (qa qd : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | m + 1, 0 => (1 - qd (m + 1) 0) + uGAC qa qd m 0
  | m + 1, c + 1 => (1 - qd (m + 1) (c + 1) + qa (m + 1) (c + 1)) + qa (m + 1) (c + 1) * uGAC qa qd m c
      + (1 - qa (m + 1) (c + 1)) * uGAC qa qd m (c + 1)

/-- (T5) instance -/
noncomputable def exTA3 (_n c : ℕ) : ℝ := if 0 < c then 3/4 else 0
noncomputable def exTD3 (_n _c : ℕ) : ℝ := 3/4
noncomputable def exFA3 (_n c : ℕ) : ℝ := if 0 < c then 1/2 else 0
noncomputable def exG3 : Game (Fin 2) Bool := gac 1 exTA3 exTD3 exFA3

/-- a Red that ignores the history but sees the coin count: backdoor iff no coin is left -/
def coinRed : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ :=
  fun _ c a => if c.val = 0 then (if a then 1 else 0) else (if a then 0 else 1)

/-- the Red that sees only the round index: wait one problem, then backdoor -/
def clocked3 : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ :=
  fun h _ a => if 1 ≤ h.length then (if a then 1 else 0) else (if a then 0 else 1)

def Claim : Prop :=
  -- (L) lawfulness
  (∀ (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ),
      (∀ n c, 0 ≤ TA n c ∧ TA n c ≤ TD n c ∧ TD n c ≤ 1 ∧ 0 ≤ FA n c ∧ FA n c ≤ 1) →
      Lawful (gac C TA TD FA)) ∧
  -- (LQ) the threshold adapter is lawful
  (∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ),
      (∀ m c, 0 ≤ qa m c ∧ qa m c ≤ qd m c ∧ qd m c ≤ 1 ∧ 0 ≤ f (qa m c) ∧ f (qa m c) ≤ f (qd m c) ∧ f (qd m c) ≤ 1) →
      Lawful (gacQ C f qa qd)) ∧
  -- (Z) bridge to GAC's safety recurrence
  (∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (β : ℝ),
      f 0 = 0 → (∀ m, qa m 0 = 0) →
      ∀ (m : ℕ) (c : Fin (C + 1)),
        1 - risk (fun _ : Unit => gacQ C f qa qd) (fun _ _ _ _ => ()) (constRed β) m c [] =
          zGAC f qa qd β m c.val) ∧
  -- (UZ) bridge to GAC's usefulness recurrence
  (∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (m : ℕ) (c : Fin (C + 1)),
      honestER (fun _ : Unit => gacQ C f qa qd) false (fun _ n c => usedReward qa qd n c.val) (fun _ _ _ => ())
          m c [] = uGAC qa qd m c.val) ∧
  -- (M) fixed-rate bound for mixtures of constant rates
  (∀ (S Ω : Type) [Fintype S] [Fintype Ω] (G : Game S Bool) (ρ : Ω → ℝ) (β : Ω → ℝ) (N : ℕ) (s₀ : S) (U : ℝ),
      (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, 0 ≤ β ω ∧ β ω ≤ 1) →
      (∀ b : ℝ, 0 ≤ b → b ≤ 1 → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] ≤ U) →
      ∑ ω, ρ ω * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed (β ω)) N s₀ [] ≤ U) ∧
  -- (Lip) Lipschitz bound for constant rates
  (∀ (S : Type) [Fintype S] (G : Game S Bool) (N : ℕ) (s₀ : S) (b b' : ℝ),
      Lawful G → 0 ≤ b → b ≤ 1 → 0 ≤ b' → b' ≤ 1 →
      |risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] -
        risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b') N s₀ []| ≤ N * |b - b'|) ∧
  -- (Grid) a finite grid of constant rates bounds every constant rate
  (∀ (S : Type) [Fintype S] (G : Game S Bool) (N J : ℕ) (s₀ : S) (U : ℝ),
      Lawful G → 0 < J →
      (∀ j : ℕ, j ≤ J → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed ((j : ℝ) / J)) N s₀ [] ≤ U) →
      ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
        risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] ≤ U + N / (2 * J)) ∧
  -- (W) at C = 0 always backdooring attains the full-information value
  (∀ (TA TD FA : ℕ → ℕ → ℝ),
      (∀ n c, 0 ≤ TA n c ∧ TA n c ≤ TD n c ∧ TD n c ≤ 1 ∧ 0 ≤ FA n c ∧ FA n c ≤ 1) →
      ∀ (N : ℕ) (c : Fin 1),
        risk (fun _ : Unit => gac 0 TA TD FA) (fun _ _ _ _ => ()) (constRed 1) N c [] =
          Vstar (gac 0 TA TD FA) N c) ∧
  -- (T5) exact separation
  ((∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed b) 3 1 [] = 3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3 ∧
      3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3 ≤ 13/50) ∧
    risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed (4/5)) 3 1 [] = 13/50 ∧
    IsPolicy clocked3 ∧ IsPolicy coinRed ∧
    risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) coinRed 3 1 [] = 9/32 ∧ (13/50 : ℝ) < 9/32 ∧
    risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) clocked3 3 1 [] = 11/32 ∧
    Vstar exG3 3 1 = 11/32 ∧
    (13/50 : ℝ) < 11/32)

/-- the full-information value table of exG3 for n ≤ 3 (c = 0, c = 1), padded with the trivial bound 1 -/
noncomputable def exV3 (n : ℕ) (c : Fin 2) : ℝ :=
  if n = 0 then 0
  else if n = 1 then 1/4
  else if n = 2 then (if c.val = 0 then 7/16 else 1/4)
  else if n = 3 then (if c.val = 0 then 37/64 else 11/32)
  else 1

/-- Non-vacuity and the certificate workflow at the (T5) instance: exG3 IS a GAC protocol (gacQ with f q = min 1 (3q/2),
qa = qd = 1/2 while the coin remains, qa m 0 = 0, qd m 0 = 1/2); it is lawful; the padded table exV3 is a horizon-3
certificate; hence (PL_TMCERTF1 soundness) EVERY history-dependent Red has risk ≤ 11/32 from one coin with three problems
left, and the clocked Red attains it; its honest usefulness is 19/8 used solutions out of 3. The adapter at a second
instance (ROC f q = min 1 (3q), two problems, one coin, qa = 1/4 and qd = 1/2 while the coin remains, qd = 1/4 at c = 0):
safety 63/64 at β = 1/2, usefulness 3/2. An audited-only round (one problem, one coin, qa = qd = 1) has usefulness 1. -/
def Witness : Prop :=
  exG3 = gacQ 1 (fun q => min 1 (3/2 * q)) (fun _ c => if c = 0 then 0 else 1/2) (fun _ _ => 1/2) ∧
  Lawful exG3 ∧
  RiskCertUpTo 3 (fun _ : Unit => exG3) (fun _ _ _ _ => True) exV3 ∧
  (∀ σ : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ, IsPolicy σ →
      risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ 3 1 [] ≤ 11/32) ∧
  risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) clocked3 3 1 [] = 11/32 ∧
  uGAC (fun _ c => if c = 0 then 0 else 1/2) (fun _ _ => 1/2) 3 1 = 19/8 ∧
  zGAC (fun q => min 1 (3 * q)) (fun _ c => if c = 0 then 0 else 1/4) (fun _ c => if c = 0 then 1/4 else 1/2)
      (1/2) 2 1 = 63/64 ∧
  1 - risk (fun _ : Unit => gacQ 1 (fun q => min 1 (3 * q))
        (fun _ c => if c = 0 then 0 else 1/4) (fun _ c => if c = 0 then 1/4 else 1/2))
        (fun _ _ _ _ => ()) (constRed (1/2)) 2 1 [] = 63/64 ∧
  uGAC (fun _ c => if c = 0 then 0 else 1/4) (fun _ c => if c = 0 then 1/4 else 1/2) 2 1 = 3/2 ∧
  uGAC (fun _ c => if c = 0 then 0 else 1) (fun _ _ => 1) 1 1 = 1

end PL_TMGACF1
