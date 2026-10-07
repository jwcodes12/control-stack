namespace PL_TMLIPF1
open PL_TMCERTF1

def RowGap {S A : Type} [Fintype S] (N : ℕ) (G H : Game S A) (eps : ℝ) : Prop :=
  ∀ n, n < N → ∀ s a,
    |G.cat n s a - H.cat n s a| + ∑ s', |G.K n s a s' - H.K n s a s'| ≤ eps

def InRange {S : Type} (N : ℕ) (V : ℕ → S → ℝ) : Prop :=
  ∀ n, n ≤ N → ∀ s, 0 ≤ V n s ∧ V n s ≤ 1

def Inflated {S : Type} (V : ℕ → S → ℝ) (eps : ℝ) : ℕ → S → ℝ :=
  fun n s => V n s + (n : ℝ) * eps

def BellmanRow {S A : Type} [Fintype S] (G : Game S A) (n : ℕ) (s : S) (a : A)
    (w : S → ℝ) : ℝ := G.cat n s a + ∑ s', G.K n s a s' * w s'

def Transfer : Prop :=
  ∀ {S A : Type} [Fintype S] (N : ℕ) (G H : Game S A) (eps : ℝ) (V : ℕ → S → ℝ),
    0 ≤ eps → LawfulUpTo N H →
    RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V →
    InRange N V → RowGap N G H eps →
    RiskCertUpTo N (fun _ : Unit => H) (fun _ _ _ _ => True) (Inflated V eps)

def GridTransfer : Prop :=
  ∀ {P S A : Type} [DecidableEq P] [Fintype S] (N : ℕ)
    (G : P → Game S A) (target grid : Finset P) (dist : P → P → ℝ)
    (L h U : ℝ),
    0 ≤ L → 0 ≤ h →
    (∀ p, p ∈ target → LawfulUpTo N (G p)) →
    (∀ p, p ∈ target → ∃ q, q ∈ grid ∧ 0 ≤ dist p q ∧ dist p q ≤ h) →
    (∀ p q, p ∈ target → q ∈ grid → 0 ≤ dist p q → RowGap N (G q) (G p) (L * dist p q)) →
    (∀ q, q ∈ grid → ∃ V, RiskCertUpTo N (fun _ : Unit => G q) (fun _ _ _ _ => True) V ∧
      InRange N V ∧ ∀ s, V N s ≤ U) →
    ∀ p, p ∈ target → ∃ q V,
      q ∈ grid ∧
      RiskCertUpTo N (fun _ : Unit => G p) (fun _ _ _ _ => True)
        (Inflated V (L * h)) ∧
      ∀ s, Inflated V (L * h) N s ≤ U + (N : ℝ) * L * h

def Claim : Prop := Transfer ∧ GridTransfer

noncomputable def baseGame : Game Unit Unit where
  cat _ _ _ := 0
  K _ _ _ _ := 0

noncomputable def perturbedGame : Game Unit Unit where
  cat _ _ _ := 1 / 4
  K _ _ _ _ := 0

def zeroCert : ℕ → Unit → ℝ := fun _ _ => 0

noncomputable def toyParam (p : Fin 2) : ℝ := if p = 0 then 0 else 1 / 4

noncomputable def toyGame (p : Fin 2) : Game Unit Unit where
  cat n _ _ := if n = 0 then toyParam p else 0
  K _ _ _ _ := 0

def toyGrid : Finset (Fin 2) := {0}

noncomputable def toyDist (p q : Fin 2) : ℝ := |toyParam p - toyParam q|

def GridWitness : Prop :=
  ∀ p, p ∈ (Finset.univ : Finset (Fin 2)) → ∃ q V,
    q ∈ toyGrid ∧
    RiskCertUpTo 1 (fun _ : Unit => toyGame p) (fun _ _ _ _ => True) (Inflated V (1 / 4)) ∧
    ∀ s, Inflated V (1 / 4) 1 s ≤ 1 / 4

def Witness : Prop :=
  RowGap 1 baseGame perturbedGame (1 / 4) ∧
  RiskCertUpTo 1 (fun _ : Unit => baseGame) (fun _ _ _ _ => True) zeroCert ∧
  InRange 1 zeroCert ∧
  (∀ n, n ≤ 1 → ∀ s, Inflated zeroCert (1 / 4) n s ≤ 1 / 4) ∧
  GridWitness

end PL_TMLIPF1
