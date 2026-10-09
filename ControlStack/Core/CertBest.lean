/-
`best`: choose the better of two certificates and carry ONLY its premises (review: Gemini on `Core/Cert.lean`).

`ProbCert.min` / `QtyCert.min` give the bound `min b₁ b₂` but require BOTH premise lists: their soundness proof uses
both certificates. That is sound, but it asks for more than the smaller bound needs. `best` compares the bounds
(`if c₁.bound ≤ c₂.bound`, classical decidability on ℝ) and returns the winning certificate unchanged. Its bound is
still `min b₁ b₂` (`ProbCert.best_bound`), and its premises are exactly the winner's (`ProbCert.best_premises`), a
sub-list of `min`'s (`ProbCert.best_premises_subset`).

Which to use: `min` when the user will establish both premise sets anyway (it is monotone in both); `best` when the
ledger should list only what the reported number rests on. `best_needs_less` is the witness: a premise-free bound 0
and a bound 1 resting on a premise that does not hold. `min` asks for the unsatisfiable premise, `best` asks for
nothing. No new mathematics.
-/
import ControlStack.Core.Cert

namespace ControlStack.Cert

section Prob

variable {Ω : Type} [Fintype Ω]

open Classical in
/-- the certificate with the smaller bound, with only its own premises -/
noncomputable def ProbCert.best {μ : Ω → ℝ} {A : Ω → Prop} (c₁ c₂ : ProbCert μ A) : ProbCert μ A :=
  if c₁.bound ≤ c₂.bound then c₁ else c₂

theorem ProbCert.best_bound {μ : Ω → ℝ} {A : Ω → Prop} (c₁ c₂ : ProbCert μ A) :
    (ProbCert.best c₁ c₂).bound = Min.min c₁.bound c₂.bound := by
  unfold ProbCert.best
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_lt (not_le.1 h))).symm

theorem ProbCert.best_premises {μ : Ω → ℝ} {A : Ω → Prop} (c₁ c₂ : ProbCert μ A) :
    (ProbCert.best c₁ c₂).premises = if c₁.bound ≤ c₂.bound then c₁.premises else c₂.premises := by
  unfold ProbCert.best
  split_ifs <;> rfl

theorem ProbCert.best_premises_subset {μ : Ω → ℝ} {A : Ω → Prop} (c₁ c₂ : ProbCert μ A) :
    (ProbCert.best c₁ c₂).premises ⊆ (ProbCert.min c₁ c₂).premises := by
  rw [ProbCert.best_premises]
  split_ifs
  · exact fun p hp => List.mem_append_left _ hp
  · exact fun p hp => List.mem_append_right _ hp

/-- **Soundness of `best`**: its premises alone give the bound `min b₁ b₂`. -/
theorem ProbCert.best_sound {μ : Ω → ℝ} {A : Ω → Prop} (c₁ c₂ : ProbCert μ A)
    (hp : AllHold (ProbCert.best c₁ c₂).premises) : prob μ A ≤ Min.min c₁.bound c₂.bound := by
  rw [← ProbCert.best_bound]
  exact (ProbCert.best c₁ c₂).sound hp

end Prob

open Classical in
/-- the quantity certificate with the smaller bound, with only its own premises -/
noncomputable def QtyCert.best {q : ℝ} (c₁ c₂ : QtyCert q) : QtyCert q := if c₁.bound ≤ c₂.bound then c₁ else c₂

theorem QtyCert.best_bound {q : ℝ} (c₁ c₂ : QtyCert q) : (QtyCert.best c₁ c₂).bound = Min.min c₁.bound c₂.bound := by
  unfold QtyCert.best
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_lt (not_le.1 h))).symm

theorem QtyCert.best_premises {q : ℝ} (c₁ c₂ : QtyCert q) :
    (QtyCert.best c₁ c₂).premises = if c₁.bound ≤ c₂.bound then c₁.premises else c₂.premises := by
  unfold QtyCert.best
  split_ifs <;> rfl

theorem QtyCert.best_premises_subset {q : ℝ} (c₁ c₂ : QtyCert q) :
    (QtyCert.best c₁ c₂).premises ⊆ (QtyCert.min c₁ c₂).premises := by
  rw [QtyCert.best_premises]
  split_ifs
  · exact fun p hp => List.mem_append_left _ hp
  · exact fun p hp => List.mem_append_right _ hp

/-- **Soundness of `best`** for quantities. -/
theorem QtyCert.best_sound {q : ℝ} (c₁ c₂ : QtyCert q) (hp : AllHold (QtyCert.best c₁ c₂).premises) :
    q ≤ Min.min c₁.bound c₂.bound := by
  rw [← QtyCert.best_bound]
  exact (QtyCert.best c₁ c₂).sound hp

/-- a premise that does not hold -/
def falsePremise : Premise := ⟨"unsatisfiable", .measurement, False⟩

/-- **`best` needs less than `min`.** For q = 0: a premise-free bound 0, and a bound 1 resting on an unsatisfiable
premise. `min` needs the unsatisfiable premise, so it can never be used. `best` needs nothing and gives 0. -/
theorem best_needs_less :
    let c₁ : QtyCert 0 := ⟨[], 0, fun _ => le_rfl⟩
    let c₂ : QtyCert 0 := ⟨[falsePremise], 1, fun _ => zero_le_one⟩
    (QtyCert.best c₁ c₂).premises = [] ∧ (QtyCert.best c₁ c₂).bound = 0 ∧
      (QtyCert.min c₁ c₂).premises = [falsePremise] ∧ ¬ AllHold (QtyCert.min c₁ c₂).premises := by
  intro c₁ c₂
  refine ⟨by rw [QtyCert.best_premises]; simp [c₁, c₂], by rw [QtyCert.best_bound]; simp [c₁, c₂], rfl, ?_⟩
  intro h
  exact h falsePremise (by simp [QtyCert.min, c₁, c₂])

end ControlStack.Cert

#print axioms ControlStack.Cert.ProbCert.best_bound
#print axioms ControlStack.Cert.ProbCert.best_premises_subset
#print axioms ControlStack.Cert.ProbCert.best_sound
#print axioms ControlStack.Cert.QtyCert.best_bound
#print axioms ControlStack.Cert.QtyCert.best_premises_subset
#print axioms ControlStack.Cert.QtyCert.best_sound
#print axioms ControlStack.Cert.best_needs_less
