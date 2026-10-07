namespace PL_TMLIPF1
open PL_TMCERTF1

/-! Parameter-Lipschitz transfer of finite trusted-monitoring certificates (v2). Depends on PL_TMCERTF1.

Row distance between finite games G and H at (n, s, a): |G.cat − H.cat| + Σ_s' |G.K − H.K|. `RowClose N G H ε`: every
row below horizon N is within ε. If V is a horizon-N risk certificate for G with values in [0, 1] and H is lawful and
row-close, then V(n, ·) + n·ε is a certificate for H (`Transfer`); the one-step core is `OneStep`. `GridTransfer`: if a
finite grid h-covers an ARBITRARY target set under a nonnegative-coefficient Lipschitz relation between parameter
distance and row distance, and every grid model has a [0, 1]-valued certificate bounded by U at the horizon, then every
target model has an explicit certificate (the grid point's certificate inflated by n·L·h) bounded by U + N·L·h.
`GridRisk`: hence every Red policy's risk on every target model is at most U + N·L·h (TMCERTF1 fixed-model soundness).

The parameter set, its coverage and the Lipschitz constant are hypotheses. Nothing here infers coverage from sampled
data or claims a statistical confidence level. Classical technique: Bellman stability / the simulation lemma. -/

def RowClose {S A : Type} [Fintype S] (N : ℕ) (G H : Game S A) (eps : ℝ) : Prop :=
  ∀ n, n < N → ∀ s a,
    |G.cat n s a - H.cat n s a| + ∑ s', |G.K n s a s' - H.K n s a s'| ≤ eps

def InRange {S : Type} (N : ℕ) (V : ℕ → S → ℝ) : Prop :=
  ∀ n, n ≤ N → ∀ s, 0 ≤ V n s ∧ V n s ≤ 1

def Inflated {S : Type} (V : ℕ → S → ℝ) (eps : ℝ) : ℕ → S → ℝ :=
  fun n s => V n s + (n : ℝ) * eps

def BellmanRow {S A : Type} [Fintype S] (G : Game S A) (n : ℕ) (s : S) (a : A)
    (w : S → ℝ) : ℝ := G.cat n s a + ∑ s', G.K n s a s' * w s'

/-- one-step Bellman error: row distance bounds the change of the Bellman row on [0, 1]-valued continuations -/
def OneStep : Prop :=
  ∀ {S A : Type} [Fintype S] (G H : Game S A) (n : ℕ) (s : S) (a : A) (w : S → ℝ) (eps : ℝ),
    (∀ s', 0 ≤ w s' ∧ w s' ≤ 1) →
    |G.cat n s a - H.cat n s a| + ∑ s', |G.K n s a s' - H.K n s a s'| ≤ eps →
    |BellmanRow G n s a w - BellmanRow H n s a w| ≤ eps

def Transfer : Prop :=
  ∀ {S A : Type} [Fintype S] (N : ℕ) (G H : Game S A) (eps : ℝ) (V : ℕ → S → ℝ),
    0 ≤ eps → LawfulUpTo N H →
    RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V →
    InRange N V → RowClose N G H eps →
    RiskCertUpTo N (fun _ : Unit => H) (fun _ _ _ _ => True) (Inflated V eps)

def GridTransfer : Prop :=
  ∀ {P S A : Type} [Fintype S] (N : ℕ)
    (G : P → Game S A) (target : Set P) (grid : Finset P) (dist : P → P → ℝ)
    (L h U : ℝ),
    0 ≤ L → 0 ≤ h →
    (∀ p ∈ target, LawfulUpTo N (G p)) →
    (∀ p ∈ target, ∃ q ∈ grid, dist p q ≤ h) →
    (∀ p ∈ target, ∀ q ∈ grid, RowClose N (G q) (G p) (L * dist p q)) →
    (∀ q ∈ grid, ∃ V, RiskCertUpTo N (fun _ : Unit => G q) (fun _ _ _ _ => True) V ∧
      InRange N V ∧ ∀ s, V N s ≤ U) →
    ∀ p ∈ target, ∃ q ∈ grid, ∃ V : ℕ → S → ℝ,
      dist p q ≤ h ∧
      RiskCertUpTo N (fun _ : Unit => G q) (fun _ _ _ _ => True) V ∧ InRange N V ∧ (∀ s, V N s ≤ U) ∧
      RiskCertUpTo N (fun _ : Unit => G p) (fun _ _ _ _ => True) (Inflated V (L * h)) ∧
      ∀ s, Inflated V (L * h) N s ≤ U + (N : ℝ) * L * h

def GridRisk : Prop :=
  ∀ {P S A : Type} [Fintype S] [Fintype A] (N : ℕ)
    (G : P → Game S A) (target : Set P) (grid : Finset P) (dist : P → P → ℝ)
    (L h U : ℝ),
    0 ≤ L → 0 ≤ h →
    (∀ p ∈ target, LawfulUpTo N (G p)) →
    (∀ p ∈ target, ∃ q ∈ grid, dist p q ≤ h) →
    (∀ p ∈ target, ∀ q ∈ grid, RowClose N (G q) (G p) (L * dist p q)) →
    (∀ q ∈ grid, ∃ V, RiskCertUpTo N (fun _ : Unit => G q) (fun _ _ _ _ => True) V ∧
      InRange N V ∧ ∀ s, V N s ≤ U) →
    ∀ p ∈ target, ∀ (σ : RHist S A → S → A → ℝ) (s₀ : S), IsPolicy σ →
      risk (fun _ : Unit => G p) (fun _ _ _ _ => ()) σ N s₀ [] ≤ U + (N : ℝ) * L * h

def Claim : Prop := OneStep ∧ Transfer ∧ GridTransfer ∧ GridRisk

/-- the always-attack Red on one action -/
def oneσ : RHist Unit Unit → Unit → Unit → ℝ := fun _ _ _ => 1

noncomputable def baseGame : Game Unit Unit where
  cat _ _ _ := 0
  K _ _ _ _ := 0

noncomputable def perturbedGame : Game Unit Unit where
  cat _ _ _ := 1 / 4
  K _ _ _ _ := 0

def zeroCert : ℕ → Unit → ℝ := fun _ _ => 0

/-- horizon accumulation: the same continuation mass, catastrophe 0 vs 1/4 per step -/
noncomputable def accG : Game Unit Unit where
  cat _ _ _ := 0
  K _ _ _ _ := 3 / 4

noncomputable def accH : Game Unit Unit where
  cat _ _ _ := 1 / 4
  K _ _ _ _ := 3 / 4

/-- a real-parameter family: catastrophe p, continuation 1 − p -/
noncomputable def paramGame (p : ℝ) : Game Unit Unit where
  cat _ _ _ := p
  K _ _ _ _ := 1 - p

noncomputable def pGrid : Finset ℝ := {1 / 8, 3 / 8}

noncomputable def gridCert (q : ℝ) : ℕ → Unit → ℝ := fun n _ => if n = 0 then 0 else q

def Witness : Prop :=
  -- (1) N = 1: the one-step inflation is needed and exact
  RowClose 1 baseGame perturbedGame (1 / 4) ∧ LawfulUpTo 1 perturbedGame ∧
  RiskCertUpTo 1 (fun _ : Unit => baseGame) (fun _ _ _ _ => True) zeroCert ∧ InRange 1 zeroCert ∧
  ¬ RiskCertUpTo 1 (fun _ : Unit => perturbedGame) (fun _ _ _ _ => True) zeroCert ∧
  RiskCertUpTo 1 (fun _ : Unit => perturbedGame) (fun _ _ _ _ => True) (Inflated zeroCert (1 / 4)) ∧
  risk (fun _ : Unit => perturbedGame) (fun _ _ _ _ => ()) oneσ 1 () [] = 1 / 4 ∧
  Inflated zeroCert (1 / 4) 1 () = 1 / 4 ∧
  -- (2) N = 2: the error accumulates over the horizon; a one-step inflation is not enough
  LawfulUpTo 2 accG ∧ LawfulUpTo 2 accH ∧ RowClose 2 accG accH (1 / 4) ∧
  RiskCertUpTo 2 (fun _ : Unit => accG) (fun _ _ _ _ => True) zeroCert ∧ InRange 2 zeroCert ∧
  risk (fun _ : Unit => accH) (fun _ _ _ _ => ()) oneσ 2 () [] = 7 / 16 ∧
  (1 / 4 : ℝ) < 7 / 16 ∧ (7 / 16 : ℝ) ≤ Inflated zeroCert (1 / 4) 2 () ∧
  -- (3) a real-parameter grid instance satisfying every hypothesis of GridTransfer/GridRisk
  --     (target [0, 1/2], grid {1/8, 3/8}, h = 1/8, L = 2, U = 3/8, N = 1)
  (∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), LawfulUpTo 1 (paramGame p)) ∧
  (∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ q ∈ pGrid, |p - q| ≤ 1 / 8) ∧
  (∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ q ∈ pGrid,
    RowClose 1 (paramGame q) (paramGame p) (2 * |p - q|)) ∧
  (∀ q ∈ pGrid, RiskCertUpTo 1 (fun _ : Unit => paramGame q) (fun _ _ _ _ => True) (gridCert q) ∧
    InRange 1 (gridCert q) ∧ ∀ s, gridCert q 1 s ≤ 3 / 8) ∧
  risk (fun _ : Unit => paramGame (1 / 2)) (fun _ _ _ _ => ()) oneσ 1 () [] = 1 / 2 ∧
  (3 / 8 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) ≤ 3 / 8 + (1 : ℝ) * 2 * (1 / 8)

end PL_TMLIPF1
