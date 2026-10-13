-- EXCERPT of ControlStack/Families/F6/ReservedAudit.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.ReservedAudit

open Finset ControlStack.Leakage ControlStack.Covert



section General

variable {N : ℕ} {Y Z : Type} [Fintype Y] [Fintype Z]

/-- the attack succeeds: ≥ k attacks, no attacked round in the reserved schedule S, and no catch flag at all -/
noncomputable def successInd (k : ℕ) (S : Finset (Fin N)) (t : List (AOut Z)) : ℝ :=
  survInd k S t * liveInd caughtFlag t

/-- uniform weight on size-B schedules -/
noncomputable def pU (N B : ℕ) (S : Finset (Fin N)) : ℝ :=
  if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0

end General



section Adaptive

variable {N : ℕ} {Y : Type} [Fintype Y]

/-- trusted flag bookkeeping: (flags so far, flag-triggered audits so far). A flagged round is audited while
fewer than Bf earlier rounds were flagged (first-come; false positives consume the budget). -/
def flagStep (Bf : ℕ) (st : ℕ × ℕ) (f : Bool) : ℕ × ℕ :=
  (st.1 + (if f then 1 else 0), st.2 + (if f && decide (st.1 < Bf) then 1 else 0))

def flagRun (Bf : ℕ) (fs : List Bool) : ℕ × ℕ := fs.foldl (flagStep Bf) (0, 0)

/-- the reserved-policy round kernel. Hidden y: this round's flag, drawn from an ARBITRARY law φ that may depend on
the schedule S, the full hidden history and the current attack bit. Visible output: (attack bit a ~ σ, unit, catch
flag), where catch = attack ∧ (round ∈ S ∨ (flag ∧ flag budget left)). -/
noncomputable def reservedK (Bf : ℕ) (σ : List (AOut Unit) → Bool → ℝ)
    (φ : Finset (Fin N) → List (Bool × AOut Unit) → Bool → Bool → ℝ) :
    Finset (Fin N) → List (Bool × AOut Unit) → Bool × AOut Unit → ℝ :=
  fun S h yo => σ (h.map Prod.snd) yo.2.1 * φ S h yo.2.1 yo.1 *
    (if yo.2.2.2 = (yo.2.1 && (decide (memN S (h.map Prod.snd).length) ||
        (yo.1 && decide ((flagRun Bf (h.map Prod.fst)).1 < Bf)))) then 1 else 0)

end Adaptive



section Availability

variable {N : ℕ}

end Availability



section Recall

variable {N : ℕ}

/-- miss probability of a FIXED attack set A against a uniform size-B schedule, when each audited attack round i is
caught independently with probability rec i -/
noncomputable def missRecall (B : ℕ) (A : Finset (Fin N)) (rec : Fin N → ℝ) : ℝ :=
  ∑ S : Finset (Fin N), pU N B S * ∏ i ∈ S ∩ A, (1 - rec i)

end Recall



section Witnesses

end Witnesses

end ControlStack.ReservedAudit

