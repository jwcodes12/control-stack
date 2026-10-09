/-
A reusable, executable certificate for complete model-event transcripts.

NOT a runtime-to-model proof: acceptance establishes that reported pre/post
states are exactly the abstract Lean state transitions, assuming the receipt
records are genuine, complete and faithfully capture each real effect.

The source-only scenario corollaries below are deliberately NOT registered as
deployable refinements in scenario manifests or TrustRoot.
-/
import Mathlib.Tactic
import ControlStack.Families.F2.ChannelInstances
import ControlStack.Scenarios.SC06Artifacts
import ControlStack.Scenarios.SC08Exec
import ControlStack.Scenarios.SC09Priv
import ControlStack.Scenarios.SC10Policy
import ControlStack.Scenarios.SC14Runaway
import ControlStack.Scenarios.SC15Review
import ControlStack.Scenarios.SC17Infra
import ControlStack.Scenarios.SC19Prod
import ControlStack.Scenarios.SC20Data
import ControlStack.Scenarios.SC23Injection

namespace ControlStack.CheckedTrace

universe u v
variable {S : Type u} {O : Type v}

/-- One full-state transition receipt; the externally attested link from real
effects to these values remains an explicit, unproved premise. -/
structure Receipt (S : Type u) (O : Type v) where
  before : S
  op : O
  after : S

def events (rs : List (Receipt S O)) : List O := rs.map Receipt.op

def recordedEnd (s : S) : List (Receipt S O) → S
  | [] => s
  | r :: rs => recordedEnd r.after rs

/-- Fail closed: replay each step under the formal policy, checking BOTH its
reported predecessor and successor. A forged/omitted real-world effect can
still evade this checker if the trusted observation premise fails. -/
def verified [DecidableEq S] (step : S → O → S) : S → List (Receipt S O) → Bool
  | _, [] => true
  | s, r :: rs =>
      decide (r.before = s ∧ r.after = step s r.op) &&
        verified step r.after rs

/-- An accepted transcript's reported final state equals formal replay. This
is a finite-trace theorem, not a claim about unobserved OS/cloud effects. -/
theorem verified_sound [DecidableEq S] (step : S → O → S)
    (rs : List (Receipt S O)) :
    ∀ s, verified step s rs = true →
      recordedEnd s rs = (events rs).foldl step s := by
  induction rs with
  | nil =>
      intro s _
      rfl
  | cons r tail ih =>
      intro s h
      have hb : decide (r.before = s ∧ r.after = step s r.op) = true ∧
          verified step r.after tail = true := by
        cases hd : decide (r.before = s ∧ r.after = step s r.op) <;>
          cases hv : verified step r.after tail <;>
          simp [verified, hd, hv] at h ⊢
      have hAfter : r.after = step s r.op := by
        by_contra hne
        have hfalse :
            decide (r.before = s ∧ r.after = step s r.op) = false := by
          simp [hne]
        simp [hfalse] at hb
      have ht := ih r.after hb.2
      simpa only [recordedEnd, events, List.map_cons, List.foldl_cons, hAfter] using ht

/-- Honest records can be accepted. -/
example :
    verified (fun s (_ : ℕ) => s + 1) 0
      ([⟨0, 7, 1⟩] : List (Receipt ℕ ℕ)) = true := by decide

/-- A fabricated post-state is refused. -/
example :
    verified (fun s (_ : ℕ) => s + 1) 0
      ([⟨0, 7, 2⟩] : List (Receipt ℕ ℕ)) = false := by decide

/-! ## SC-04: typed log alphabet. This controls only explicit record fields;
timing, error text, drop counts and other receiver views remain unbounded
until independently measured or included in the channel model. -/

abbrev SC04Alphabet (templates fields levels : ℕ) :=
  Fin templates × (Fin fields → Fin levels)

theorem sc04_alphabet_card (templates fields levels : ℕ) :
    Fintype.card (SC04Alphabet templates fields levels) =
      templates * levels ^ fields := by
  simp [SC04Alphabet]

/-! ## Formal replay corollaries for the ten deterministic scenario machines.

These DO NOT count as scenario-specific concrete-transition refinements:
they assume the recorded event has exactly the abstract operation type and
the full abstract state on each side. The untrusted actual runtime may emit
an incomplete/fictional record. Source-only until an independently checked
OS/application event extractor and bypass analysis exist.
-/

/-- SC06: accepted abstract-state receipts inherit the existing safety
invariant; complete/genuine production event capture is NOT established. -/
theorem sc06_receipts_sound (P : SC06.Policy)  (rs : List (Receipt SC06.St SC06.Op)) 
    (h : verified (SC06.step P SC06.full) (SC06.init) rs = true) :
    SC06.Good P (recordedEnd SC06.init rs) := by
  have heq := verified_sound (SC06.step P SC06.full) rs (SC06.init) h
  rw [heq]
  exact SC06.sc06_safe P (events rs)

/-- SC08: accepted abstract-state receipts inherit the existing safety
invariant; complete/genuine production event capture is NOT established. -/
theorem sc08_receipts_sound (E : SC08.Env) (files : List (ℕ × ℕ)) (rs : List (Receipt SC08.St SC08.Op)) 
    (h : verified (SC08.step E SC08.full) (⟨files, [], false⟩ : SC08.St) rs = true) :
    SC08.Good E (recordedEnd (⟨files, [], false⟩ : SC08.St) rs) := by
  have heq := verified_sound (SC08.step E SC08.full) rs (⟨files, [], false⟩ : SC08.St) h
  rw [heq]
  exact SC08.sc08_safe E files (events rs)

/-- SC09: accepted abstract-state receipts inherit the existing safety
invariant; complete/genuine production event capture is NOT established. -/
theorem sc09_receipts_sound (P : SC09.Policy)  (rs : List (Receipt SC09.St SC09.Op)) 
    (h : verified (SC09.step P SC09.full) (SC09.init) rs = true) :
    SC09.Good P (recordedEnd SC09.init rs) := by
  have heq := verified_sound (SC09.step P SC09.full) rs (SC09.init) h
  rw [heq]
  exact SC09.sc09_safe P (events rs)

/-- SC10: accepted abstract-state receipts inherit the existing safety
invariant; complete/genuine production event capture is NOT established. -/
theorem sc10_receipts_sound (E : SC10.Env) (hpin : E.h E.pinned = E.pinnedDigest) (rs : List (Receipt SC10.St SC10.Op)) 
    (h : verified (SC10.step E SC10.full) (SC10.init) rs = true) :
    SC10.Good E (recordedEnd SC10.init rs) := by
  have heq := verified_sound (SC10.step E SC10.full) rs (SC10.init) h
  rw [heq]
  exact SC10.sc10_safe E hpin (events rs)

/-- SC14: accepted abstract-state receipts inherit the existing safety
invariant; complete/genuine production event capture is NOT established. -/
theorem sc14_receipts_sound (E : SC14.Env) (exp : ℕ) (rs : List (Receipt SC14.St SC14.Op)) (hops : ∀ o ∈ events rs, SC14.legal o)
    (h : verified (SC14.step E SC14.full) (SC14.init exp) rs = true) :
    SC14.Good E (recordedEnd (SC14.init exp) rs) := by
  have heq := verified_sound (SC14.step E SC14.full) rs (SC14.init exp) h
  rw [heq]
  exact SC14.sc14_safe E exp (events rs) hops

/-- SC15: accepted abstract-state receipts inherit the existing safety
invariant; complete/genuine production event capture is NOT established. -/
theorem sc15_receipts_sound (E : SC15.Env)  (rs : List (Receipt SC15.St SC15.Op)) 
    (h : verified (SC15.step E SC15.full) (SC15.init) rs = true) :
    ∀ c ∈ (recordedEnd SC15.init rs).merged, SC15.MergeOk E (recordedEnd SC15.init rs) c := by
  have heq := verified_sound (SC15.step E SC15.full) rs (SC15.init) h
  rw [heq]
  exact SC15.sc15_safe E (events rs)

/-- SC17: accepted abstract-state receipts inherit the existing safety
invariant; complete/genuine production event capture is NOT established. -/
theorem sc17_receipts_sound (E : SC17.Env) (g0 : List SC17.G) (rs : List (Receipt SC17.St SC17.Op)) 
    (h : verified (SC17.step E SC17.full) (SC17.init g0) rs = true) :
    SC17.Good E (recordedEnd (SC17.init g0) rs) := by
  have heq := verified_sound (SC17.step E SC17.full) rs (SC17.init g0) h
  rw [heq]
  exact SC17.sc17_safe E g0 (events rs)

/-- SC19: accepted abstract-state receipts inherit the existing safety
invariant; complete/genuine production event capture is NOT established. -/
theorem sc19_receipts_sound (E : SC19.Env)  (rs : List (Receipt SC19.St SC19.Op)) 
    (h : verified (SC19.step E SC19.full) (SC19.init) rs = true) :
    SC19.Good E (recordedEnd SC19.init rs) := by
  have heq := verified_sound (SC19.step E SC19.full) rs (SC19.init) h
  rw [heq]
  exact SC19.sc19_safe E (events rs)

/-- SC20: accepted abstract-state receipts inherit the existing safety
invariant; complete/genuine production event capture is NOT established. -/
theorem sc20_receipts_sound (E : SC20.Env)  (rs : List (Receipt SC20.St SC20.Op)) 
    (h : verified (SC20.step E SC20.full) (SC20.init) rs = true) :
    SC20.Good E (recordedEnd SC20.init rs) := by
  have heq := verified_sound (SC20.step E SC20.full) rs (SC20.init) h
  rw [heq]
  exact SC20.sc20_safe E (events rs)

/-- SC23: accepted abstract-state receipts inherit the existing safety
invariant; complete/genuine production event capture is NOT established. -/
theorem sc23_receipts_sound (P : SC23.Policy)  (rs : List (Receipt SC23.St SC23.Op)) 
    (h : verified (SC23.step P SC23.full) (SC23.init) rs = true) :
    SC23.Good P (recordedEnd SC23.init rs) := by
  have heq := verified_sound (SC23.step P SC23.full) rs (SC23.init) h
  rw [heq]
  exact SC23.sc23_safe P (events rs)

/-! ## Deliberate falsification and omission examples -/

/-- A fake predecessor at step two is caught. -/
example :
    verified (fun s (_ : ℕ) => s + 1) 0
      ([⟨0, 7, 1⟩, ⟨9, 8, 10⟩] : List (Receipt ℕ ℕ)) = false := by decide

/-- A fake second successor is caught. -/
example :
    verified (fun s (_ : ℕ) => s + 1) 0
      ([⟨0, 7, 1⟩, ⟨1, 8, 99⟩] : List (Receipt ℕ ℕ)) = false := by decide

/-- Genuine two-step abstract transitions are accepted. -/
example :
    verified (fun s (_ : ℕ) => s + 1) 0
      ([⟨0, 7, 1⟩, ⟨1, 8, 2⟩] : List (Receipt ℕ ℕ)) = true := by decide

/-- Empty reports pass: completeness of real-world receipt capture is NOT proved. -/
example :
    verified (fun s (_ : ℕ) => s + 1) 0
      ([] : List (Receipt ℕ ℕ)) = true := by decide

end ControlStack.CheckedTrace

#print axioms ControlStack.CheckedTrace.verified_sound
#print axioms ControlStack.CheckedTrace.sc06_receipts_sound
#print axioms ControlStack.CheckedTrace.sc08_receipts_sound
#print axioms ControlStack.CheckedTrace.sc09_receipts_sound
#print axioms ControlStack.CheckedTrace.sc10_receipts_sound
#print axioms ControlStack.CheckedTrace.sc14_receipts_sound
#print axioms ControlStack.CheckedTrace.sc15_receipts_sound
#print axioms ControlStack.CheckedTrace.sc17_receipts_sound
#print axioms ControlStack.CheckedTrace.sc19_receipts_sound
#print axioms ControlStack.CheckedTrace.sc20_receipts_sound
#print axioms ControlStack.CheckedTrace.sc23_receipts_sound
#print axioms ControlStack.CheckedTrace.sc04_alphabet_card
