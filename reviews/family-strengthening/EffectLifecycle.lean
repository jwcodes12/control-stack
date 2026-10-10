import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

/-!
F8 review-scoped external-effect lifecycle abstraction.

One *joint* state is shared by arbitrarily tagged agent/delegate requests.
A trusted serialized admission spends from one common cap. A later publish
may leave a file effect before the receipt commits. HALT forbids new publish
events but cannot erase a file that was already durably published.

The model intentionally overapproximates eligibility to publish (it does not
include real lease revocation/expiry or OS capabilities). This is NOT a
refinement proof for the Python service, the filesystem, or the scheduler.
-/
namespace ControlStack.EffectLifecycle

structure State where
  cap : Nat
  spent : Nat
  halted : Bool
  admitted : Finset Nat
  published : Finset Nat
  receipted : Finset Nat
  deriving DecidableEq, Repr

inductive Action where
  | request (agent delegate releaseId cost : Nat)
  | publish (releaseId : Nat)
  | receipt (releaseId : Nat)
  | halt
  deriving DecidableEq, Repr

def step (s : State) (a : Action) : State :=
  match a with
  | .request _ _ releaseId cost =>
      if s.halted = true ∨ cost = 0 ∨ s.spent + cost > s.cap ∨ releaseId ∈ s.admitted
      then s
      else { s with spent := s.spent + cost,
                        admitted := insert releaseId s.admitted }
  | .publish releaseId =>
      if s.halted = true ∨ releaseId ∉ s.admitted then s
      else { s with published := insert releaseId s.published }
  | .receipt releaseId =>
      if s.halted = true ∨ releaseId ∉ s.published then s
      else { s with receipted := insert releaseId s.receipted }
  | .halt => { s with halted := true }

def run (s : State) (events : List Action) : State := events.foldl step s


/-- Admission, publication, receipt and HALT share ONE budget counter.
Every request, including any delegated tag, is charged to that counter.
This is a model property, not a broker correspondence theorem. -/
theorem budget_step (s : State) (a : Action)
    (h : s.spent ≤ s.cap) : (step s a).spent ≤ (step s a).cap := by
  cases a with
  | request agent delegate releaseId cost =>
      by_cases denied :
          s.halted = true ∨ cost = 0 ∨ s.spent + cost > s.cap ∨
            releaseId ∈ s.admitted
      · simpa [step, denied] using h
      · have within_cap : s.spent + cost ≤ s.cap := by omega
        simpa [step, denied] using within_cap
  | publish releaseId =>
      by_cases denied : s.halted = true ∨ releaseId ∉ s.admitted
      · simpa [step, denied] using h
      · simpa [step, denied] using h
  | receipt releaseId =>
      by_cases denied : s.halted = true ∨ releaseId ∉ s.published
      · simpa [step, denied] using h
      · simpa [step, denied] using h
  | halt => simpa [step] using h

theorem budget_run (s : State) (events : List Action)
    (h : s.spent ≤ s.cap) : (run s events).spent ≤ (run s events).cap := by
  induction events generalizing s with
  | nil => simpa [run] using h
  | cons a rest ih =>
      change (run (step s a) rest).spent ≤ (run (step s a) rest).cap
      exact ih (step s a) (budget_step s a h)

/-- A publication request for an unadmitted id cannot create bytes. -/
theorem unknown_effect_cannot_publish (s : State) (id : Nat)
    (h : id ∉ s.admitted) :
    (step s (.publish id)).published = s.published := by
  simp [step, h]

/-- A receipt request cannot invent a publication that has not occurred. -/
theorem missing_publication_cannot_receipt (s : State) (id : Nat)
    (h : id ∉ s.published) :
    (step s (.receipt id)).receipted = s.receipted := by
  simp [step, h]

/-- No fresh external publication after HALT, including from admitted but
not yet delivered work. Does NOT claim cancellation of earlier publications. -/
theorem halted_blocks_publication (s : State) (a : Action)
    (h : s.halted = true) : (step s a).published = s.published := by
  cases a <;> simp [step, h]

theorem halt_absorbing (s : State) (a : Action)
    (h : s.halted = true) : (step s a).halted = true := by
  cases a <;> simp [step, h]

theorem no_publications_in_halted_suffix (s : State) (events : List Action)
    (h : s.halted = true) : (run s events).published = s.published := by
  induction events generalizing s with
  | nil => rfl
  | cons a rest ih =>
      change (run (step s a) rest).published = s.published
      rw [ih (step s a) (halt_absorbing s a h)]
      exact halted_blocks_publication s a h

/-- Positive-effects witness rules out a vacuous all-denied lifecycle. -/
theorem admits_then_publishes :
    let initial : State := ⟨2, 0, false, ∅, ∅, ∅⟩
    let admitted := step initial (.request 1 2 7 1)
    7 ∈ (step admitted (.publish 7)).published := by
  decide

/-- A crash after durable publication and before receipt followed by HALT
can leave published bytes with no committed receipt. Never claim HALT
retroactively deletes such an external effect. -/
theorem halt_cannot_undo_published_unreceipted :
    let initial : State := ⟨2, 0, false, ∅, ∅, ∅⟩
    let admitted := step initial (.request 1 2 7 1)
    let delivered := step admitted (.publish 7)
    let halted := step delivered .halt
    7 ∈ halted.published ∧ 7 ∉ halted.receipted := by
  decide

#print axioms budget_step
#print axioms budget_run
#print axioms unknown_effect_cannot_publish
#print axioms missing_publication_cannot_receipt
#print axioms halted_blocks_publication
#print axioms halt_absorbing
#print axioms no_publications_in_halted_suffix
#print axioms admits_then_publishes
#print axioms halt_cannot_undo_published_unreceipted

end ControlStack.EffectLifecycle
