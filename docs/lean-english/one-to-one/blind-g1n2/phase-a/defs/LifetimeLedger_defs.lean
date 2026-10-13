-- EXCERPT of ControlStack/LifetimeLedger.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.LifetimeLedger

inductive Ev (L : Type) where
  | charge (ℓ : L) (k : ℕ)
  | abort (ℓ : L) (k : ℕ)
  | reopen
  | corrupt
  | restore (g : L → ℕ)

def Ev.isRestore {L : Type} : Ev L → Prop
  | .restore _ => True
  | _ => False

variable {L : Type} [DecidableEq L]

/-- one event: new state and the admission it reports, if any -/
def step (cap : ℕ) : Option (L → ℕ) → Ev L → Option (L → ℕ) × Option (L × ℕ)
  | none, .restore g => (some g, none)
  | none, _ => (none, none)
  | some f, .charge ℓ k =>
      if f ℓ * k ≤ cap then (some (Function.update f ℓ (f ℓ * k)), some (ℓ, k)) else (some f, none)
  | some f, .abort _ _ => (some f, none)
  | some f, .reopen => (some f, none)
  | some _, .corrupt => (none, none)
  | some _, .restore g => (some g, none)

/-- run a trace from a state, accumulating admissions in order -/
def run (cap : ℕ) : Option (L → ℕ) × List (L × ℕ) → List (Ev L) → Option (L → ℕ) × List (L × ℕ)
  | st, [] => st
  | (s, adm), e :: es => run cap ((step cap s e).1, adm ++ (step cap s e).2.toList) es

/-- product of admitted sizes for lineage ℓ -/
def pr (ℓ : L) (adm : List (L × ℕ)) : ℕ := ((adm.filter (fun a => a.1 = ℓ)).map Prod.snd).prod

def Inv (cap : ℕ) (st : Option (L → ℕ) × List (L × ℕ)) : Prop :=
  (∀ f, st.1 = some f → ∀ ℓ, f ℓ = pr ℓ st.2) ∧ ∀ ℓ, pr ℓ st.2 ≤ cap

open ControlStack.Covert in
end ControlStack.LifetimeLedger

