-- EXCERPT of ControlStack/Families/F6/ReservedRecall.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.ReservedRecall

open Finset ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit



section Count

variable {N : ℕ}

/-- the hypergeometric miss probability: Σ_{j ≤ min(k,B)} C(k,j)C(N−k,B−j)/C(N,B) · (1−r)^j -/
noncomputable def hypMiss (N B k : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ range (min k B + 1),
    ((Nat.choose k j : ℝ) * (Nat.choose (N - k) (B - j) : ℝ)) / (Nat.choose N B : ℝ) * (1 - r) ^ j

end Count



section Factor

variable {O : Type} [Fintype O]

end Factor

section Adaptive

variable {N : ℕ}

/-- round i was an attack that was NOT caught -/
def attNC (t : List (AOut Unit)) (i : ℕ) : Bool :=
  match t[i]? with
  | some o => o.1 && !o.2.2
  | none => false

/-- accumulated recall discount: (1−r) per reserved round attacked without being caught -/
noncomputable def phi (r : ℝ) (S : Finset (Fin N)) (t : List (AOut Unit)) : ℝ :=
  ∏ j : Fin N, (if j ∈ S ∧ attNC t j = true then (1 - r) else 1)

/-- the per-round discount factor -/
noncomputable def fac (r : ℝ) (S : Finset (Fin N)) (g : List (AOut Unit)) (o : AOut Unit) : ℝ :=
  if memN S g.length ∧ o.1 = true ∧ o.2.2 = false then (1 - r) else 1

/-- success under imperfect recall: ≥ k attacks and never caught -/
noncomputable def recallSucc (k : ℕ) (t : List (AOut Unit)) : ℝ :=
  (if k ≤ (attackSet (N := N) t).card then 1 else 0) * liveInd caughtFlag t

/-- hidden y = the auditor's detection coin (true w.p. r); catch = attack ∧ reserved round ∧ detected -/
noncomputable def recallK (r : ℝ) (σ : List (AOut Unit) → Bool → ℝ) :
    Finset (Fin N) → List (Bool × AOut Unit) → Bool × AOut Unit → ℝ :=
  fun S h yo => σ (h.map Prod.snd) yo.2.1 * (if yo.1 then r else 1 - r) *
    (if yo.2.2.2 = (yo.2.1 && decide (memN S (h.map Prod.snd).length) && yo.1) then 1 else 0)

end Adaptive

end ControlStack.ReservedRecall

