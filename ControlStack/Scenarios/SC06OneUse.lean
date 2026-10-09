/-
SC-06 v2 scoped, explicit-handle/one-use model.

This is a NEW, narrow state machine for sensitive actions on cross-agent
context entries. It does NOT refine the frozen Python harness, certify all
filesystem paths, or cover non-sensitive/local actions. Issuer identities,
typed ingestion, and mandatory effect mediation remain trusted premises.
Unlike SC06Artifacts.ctxOf, each action identifies a context-entry ID;
unlike SC06Artifacts.ActOk, a confirmation ID can authorize at most one effect.
-/
import Mathlib.Tactic

namespace ControlStack.SC06OneUse

structure Roles where
  users : List ℕ
  admins : List ℕ
  sensitive : List ℕ

structure Entry where
  id : ℕ
  reader : ℕ
  writer : ℕ
  val : ℕ
deriving DecidableEq, Repr

structure Confirmation where
  id : ℕ
  issuer : ℕ
  reader : ℕ
  tool : ℕ
  entryId : ℕ
  val : ℕ
deriving DecidableEq, Repr

structure Effect where
  confId : ℕ
  reader : ℕ
  tool : ℕ
  entryId : ℕ
  val : ℕ
deriving DecidableEq, Repr

structure State where
  entries : List Entry
  confirmations : List Confirmation
  effects : List Effect
  halted : Bool
deriving DecidableEq, Repr

inductive Event where
  | ingest (reader writer val : ℕ)
  | confirm (issuer confId reader tool entryId val : ℕ)
  | act (reader tool entryId confId : ℕ)
  | halt (issuer : ℕ)
deriving DecidableEq, Repr

def init : State := ⟨[], [], [], false⟩

/-- Exact context handle and exact one-use confirmation are checked
before the same modeled transition appends a sensitive effect. -/
def allowed (R : Roles) (s : State) (r tool eid cid : ℕ)
    (e : Entry) (c : Confirmation) : Prop :=
  tool ∈ R.sensitive ∧
  e.id = eid ∧ e.reader = r ∧ e.writer ≠ r ∧
  c.id = cid ∧ c.issuer ∈ R.users ∧
  c.reader = r ∧ c.tool = tool ∧ c.entryId = eid ∧
  c.val = e.val ∧ cid ∉ s.effects.map Effect.confId

/-- Constructive decision procedure; avoids noncomputable Classical.decEq
in the executable transition function and finite negative controls. -/
instance allowedDecidable (R : Roles) (s : State) (r tool eid cid : ℕ)
    (e : Entry) (c : Confirmation) :
    Decidable (allowed R s r tool eid cid e c) := by
  unfold allowed
  infer_instance

def step (R : Roles) (s : State) : Event → State
  | .ingest r w v =>
      if s.halted then s else
      { s with entries := ⟨s.entries.length, r, w, v⟩ :: s.entries }
  | .confirm issuer cid r tool eid v =>
      if s.halted then s else
      if issuer ∈ R.users ∧ cid ∉ s.confirmations.map Confirmation.id then
        { s with confirmations := ⟨cid, issuer, r, tool, eid, v⟩ :: s.confirmations }
      else s
  | .act r tool eid cid =>
      if s.halted then s else
      match s.entries.find? (fun e => e.id = eid) with
      | none => s
      | some e =>
          match s.confirmations.find? (fun c => c.id = cid) with
          | none => s
          | some c =>
              if allowed R s r tool eid cid e c then
                { s with effects := ⟨cid, r, tool, eid, e.val⟩ :: s.effects }
              else s
  | .halt issuer =>
      if issuer ∈ R.admins then { s with halted := true } else s

def run (R : Roles) (s : State) (events : List Event) : State :=
  events.foldl (step R) s

/-- A recorded sensitive foreign effect must have an exact-entry source
and an exact user-issued confirmation for that specific handle and value. -/
def EffectOk (R : Roles) (s : State) (x : Effect) : Prop :=
  x.tool ∈ R.sensitive ∧
  ∃ e ∈ s.entries, ∃ c ∈ s.confirmations,
    e.id = x.entryId ∧ e.reader = x.reader ∧
    e.writer ≠ x.reader ∧ e.val = x.val ∧
    c.id = x.confId ∧ c.issuer ∈ R.users ∧
    c.reader = x.reader ∧ c.tool = x.tool ∧
    c.entryId = x.entryId ∧ c.val = x.val

structure Inv (R : Roles) (s : State) : Prop where
  issuers : ∀ c ∈ s.confirmations, c.issuer ∈ R.users
  effects : ∀ x ∈ s.effects, EffectOk R s x
  oneUse : (s.effects.map Effect.confId).Nodup

theorem inv_init (R : Roles) : Inv R init :=
  ⟨by simp [init], by simp [init], by simp [init]⟩

theorem EffectOk.monoEntries {R : Roles} {s : State}
    (x : Effect) (e : Entry) (h : EffectOk R s x) :
    EffectOk R {s with entries := e :: s.entries} x := by
  rcases h with ⟨hs, a, ha, c, hc, rest⟩
  exact ⟨hs, a, List.mem_cons_of_mem _ ha, c, hc, rest⟩

theorem EffectOk.monoConfirmations {R : Roles} {s : State}
    (x : Effect) (c : Confirmation) (h : EffectOk R s x) :
    EffectOk R {s with confirmations := c :: s.confirmations} x := by
  rcases h with ⟨hs, e, he, a, ha, rest⟩
  exact ⟨hs, e, he, a, List.mem_cons_of_mem _ ha, rest⟩

theorem addEntry (R : Roles) (s : State) (h : Inv R s) (e : Entry) :
    Inv R {s with entries := e :: s.entries} := by
  refine ⟨h.issuers, ?_, h.oneUse⟩
  intro x hx
  exact EffectOk.monoEntries x e (h.effects x hx)

theorem addConfirmation (R : Roles) (s : State) (h : Inv R s)
    (c : Confirmation) (hc : c.issuer ∈ R.users) :
    Inv R {s with confirmations := c :: s.confirmations} := by
  refine ⟨?_, ?_, h.oneUse⟩
  · intro a ha
    rcases List.mem_cons.mp ha with hnew | hold
    · subst a; exact hc
    · exact h.issuers a hold
  · intro x hx
    exact EffectOk.monoConfirmations x c (h.effects x hx)

theorem addEffect (R : Roles) (s : State) (h : Inv R s)
    (x : Effect) (hx : EffectOk R s x)
    (hu : x.confId ∉ s.effects.map Effect.confId) :
    Inv R {s with effects := x :: s.effects} := by
  refine ⟨h.issuers, ?_, ?_⟩
  · intro y hy
    rcases List.mem_cons.mp hy with hnew | hold
    · subst y; exact hx
    · exact h.effects y hold
  · simpa [List.map_cons, hu] using h.oneUse

theorem step_inv (R : Roles) (s : State) (op : Event) (h : Inv R s) :
    Inv R (step R s op) := by
  cases op with
  | ingest r w v =>
      by_cases hh : s.halted
      · simpa [step, hh] using h
      · simpa [step, hh] using addEntry R s h ⟨s.entries.length, r, w, v⟩
  | confirm issuer cid r tool eid v =>
      simp only [step]
      split_ifs with hhalt hallow
      · exact h
      · exact addConfirmation R s h ⟨cid, issuer, r, tool, eid, v⟩ hallow.1
      · exact h
  | act r tool eid cid =>
      by_cases hh : s.halted
      · simpa [step, hh] using h
      · cases he : s.entries.find? (fun e => e.id = eid) with
        | none => simpa [step, hh, he] using h
        | some e =>
            cases hc : s.confirmations.find? (fun c => c.id = cid) with
            | none => simpa [step, hh, he, hc] using h
            | some c =>
                by_cases hp : allowed R s r tool eid cid e c
                · have hp' := hp
                  rcases hp with ⟨hs, heid, hr, hforeign, hcid, huser, hreader,
                                  htool, hentry, hval, hu⟩
                  have he_mem : e ∈ s.entries := List.mem_of_find?_eq_some he
                  have hc_mem : c ∈ s.confirmations := List.mem_of_find?_eq_some hc
                  have hx : EffectOk R s ⟨cid, r, tool, eid, e.val⟩ :=
                    ⟨hs, e, he_mem, c, hc_mem, heid, hr, hforeign, rfl,
                     hcid, huser, hreader, htool, hentry, hval⟩
                  have hi := addEffect R s h ⟨cid, r, tool, eid, e.val⟩ hx hu
                  simpa [step, hh, he, hc, hp'] using hi
                · simpa [step, hh, he, hc, hp] using h
  | halt issuer =>
      by_cases hh : issuer ∈ R.admins
      · have hi : Inv R {s with halted := true} := ⟨h.issuers, h.effects, h.oneUse⟩
        simpa [step, hh] using hi
      · simpa [step, hh] using h

theorem run_inv (R : Roles) (s : State) (es : List Event) (h : Inv R s) :
    Inv R (run R s es) := by
  induction es generalizing s with
  | nil => simpa [run] using h
  | cons op rest ih =>
      change Inv R (run R (step R s op) rest)
      exact ih (step R s op) (step_inv R s op h)

/-- All scoped foreign-sensitive effects have exact entry IDs, exact trusted
confirmation matches, and unique confirmation usage over arbitrary traces. -/
theorem scoped_safe (R : Roles) (es : List Event) :
    (∀ x ∈ (run R init es).effects, EffectOk R (run R init es) x) ∧
    ((run R init es).effects.map Effect.confId).Nodup := by
  have h := run_inv R init es (inv_init R)
  exact ⟨h.effects, h.oneUse⟩

def R0 : Roles := ⟨[5], [9], [7]⟩

/-- The second use of a single confirmation cannot append an effect. -/
theorem duplicate_use_blocked :
    (run R0 init [
      .ingest 2 1 42,
      .confirm 5 3 2 7 0 42,
      .act 2 7 0 3,
      .act 2 7 0 3]).effects =
      [⟨3, 2, 7, 0, 42⟩] := by
  decide

/-- Approving one numeric value on another entry ID is not interchangeable:
the wrong handle is rejected, even for equal values from different writers. -/
theorem provenance_handle_not_value_alias :
    (run R0 init [
      .ingest 2 2 42,
      .ingest 2 1 42,
      .confirm 5 3 2 7 0 42,
      .act 2 7 1 3]).effects = [] := by
  decide

/-- One correctly bound confirmation for the second (foreign) context handle
does allow one useful foreign-sensitive effect. -/
theorem useful_foreign_action :
    (run R0 init [
      .ingest 2 2 42,
      .ingest 2 1 42,
      .confirm 5 3 2 7 1 42,
      .act 2 7 1 3]).effects =
       [⟨3, 2, 7, 1, 42⟩] := by
  decide

/-! ## Explicit check-removal counterexamples -/

/-- Artificial weakened step that removes *only* the consumed-confirmation
guard from the sensitive action path. It is not a deployed configuration. -/
def weakStep (R : Roles) (s : State) : Event → State
  | .act r tool eid cid =>
      if s.halted then s else
      match s.entries.find? (fun e => e.id = eid) with
      | none => s
      | some e =>
          match s.confirmations.find? (fun c => c.id = cid) with
          | none => s
          | some c =>
              if allowed R {s with effects := []} r tool eid cid e c then
                { s with effects := ⟨cid, r, tool, eid, e.val⟩ :: s.effects }
              else s
  | ev => step R s ev

def weakRun (R : Roles) (s : State) (es : List Event) : State :=
  es.foldl (weakStep R) s

/-- Exactly the check being proved necessary: allowing reuse produces two
abstract sensitive effects from a single approval, whereas the strong gate
produces only one. -/
theorem disabling_consumption_duplicates_effect :
    (weakRun R0 init [
      .ingest 2 1 42,
      .confirm 5 3 2 7 0 42,
      .act 2 7 0 3,
      .act 2 7 0 3]).effects =
      [⟨3, 2, 7, 0, 42⟩, ⟨3, 2, 7, 0, 42⟩] ∧
    (run R0 init [
      .ingest 2 1 42,
      .confirm 5 3 2 7 0 42,
      .act 2 7 0 3,
      .act 2 7 0 3]).effects =
      [⟨3, 2, 7, 0, 42⟩] := by
  decide

/-- Distinct legitimate confirmations still permit multiple effect attempts
with the same data, one attempt per separate user-issued confirmation. -/
theorem distinct_confirmations_allow_two_effects :
    (run R0 init [
      .ingest 2 1 42,
      .confirm 5 3 2 7 0 42,
      .confirm 5 4 2 7 0 42,
      .act 2 7 0 3,
      .act 2 7 0 4]).effects =
      [⟨4, 2, 7, 0, 42⟩, ⟨3, 2, 7, 0, 42⟩] := by
  decide

/-- An admin HALT prevents subsequent sensitive effects in the model. -/
theorem halt_stops_foreign_action :
    (run R0 init [
      .ingest 2 1 42,
      .confirm 5 3 2 7 0 42,
      .halt 9,
      .act 2 7 0 3]).effects = [] := by
  decide

end ControlStack.SC06OneUse

#print axioms ControlStack.SC06OneUse.scoped_safe
#print axioms ControlStack.SC06OneUse.duplicate_use_blocked
#print axioms ControlStack.SC06OneUse.provenance_handle_not_value_alias
#print axioms ControlStack.SC06OneUse.useful_foreign_action
#print axioms ControlStack.SC06OneUse.disabling_consumption_duplicates_effect
#print axioms ControlStack.SC06OneUse.distinct_confirmations_allow_two_effects
#print axioms ControlStack.SC06OneUse.halt_stops_foreign_action
