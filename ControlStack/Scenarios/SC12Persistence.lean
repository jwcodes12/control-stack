/-
SC-12: an agent must not establish persistence, spawn helpers that outlive it, or replicate past its session.

An abstract lifetime model (pattern of `SC26Transaction.lean`):
- a trusted controller starts sessions; each session has a root entity;
- every process, principal or scheduled job the agent creates (`spawn`) is registered in a TRUSTED REGISTRY under its
  parent's session; a ghost `origin` field records the true lineage (the session whose activity created it);
- ending a session, or an admin HALT, revokes the session's ENTIRE registered lineage; a job fires only while live;
- a `bypass` operation models a creation path outside the registry (refused when the platform allows creation only
  through the registry).

Main results (deployed configuration `full`; adversary class TRACE_ARBITRARY: any spawns, bypass attempts with any
parent/child/claimed session, fires, in any order, interleaved with session starts/ends):
- `sc12_safe`: from `init`, every live entity is registered and of a lineage whose session is active, so nothing of
  an ended session is live;
- `no_fire_after_end`: once a session has ended, no trace makes any job of its lineage fire again;
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`, effect log = job firings); non-vacuity
  `honest_session_lifecycle`.

Necessity witnesses: `registry_bypass_survives` (an unregistered helper outlives the session),
`parent_only_revocation_survives` (revoking only the root leaves children), `foreign_registration_survives` (a job
registered under a different session outlives its creator's session), `no_halt_check_breaks`.

Premises outside the model: every creation path the platform offers goes through the registry (processes, accounts,
cron/systemd/at jobs, cloud resources, credentials), revocation actually kills/invalidates what the registry lists,
and admin credentials are not held by agents. Not claimed: anything about effects a job caused while its session was
live. No new mathematics: inductions over the trace.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC12

open ControlStack.Gate

/-- a live entity: id, registered session label, ghost true lineage, whether it is a scheduled job, registered -/
structure Ent where
  id : ℕ
  sess : ℕ
  origin : ℕ
  job : Bool
  reg : Bool
deriving DecidableEq, Repr

structure St where
  active : List ℕ
  ended : List ℕ
  live : List Ent
  /-- job firings: (job id, its true lineage, length of the ended-session log at that moment) -/
  fired : List (ℕ × ℕ × ℕ)
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | start (caller sess : ℕ)
  /-- `parent` creates `child` through the registry; `claim` is a session label the creator asks for -/
  | spawn (parent child : ℕ) (job : Bool) (claim : ℕ)
  /-- `parent` creates `child` outside the registry -/
  | bypass (parent child : ℕ) (job : Bool)
  | endSession (caller sess : ℕ)
  | fire (j : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  registryOnly : Bool
  lineage : Bool
  revokeLineage : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], [], [], false⟩

def entOf (s : St) (id : ℕ) : Option Ent := s.live.find? (fun e => e.id = id)

def step (admins : List ℕ) (C : Checks) (s : St) : Op → St
  | .start c sess =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ admins ∧ sess ∉ s.active ∧ sess ∉ s.ended ∧ entOf s sess = none then
      { s with active := s.active ++ [sess], live := s.live ++ [⟨sess, sess, sess, false, true⟩] }
    else s
  | .spawn p ch job claim =>
    if s.halted ∧ C.haltCheck then s
    else match entOf s p with
      | none => s
      | some e =>
        if entOf s ch = none then
          { s with live := s.live ++ [⟨ch, if C.lineage then e.sess else claim, e.origin, job, true⟩] }
        else s
  | .bypass p ch job =>
    if s.halted ∧ C.haltCheck then s
    else if C.registryOnly then s
    else match entOf s p with
      | none => s
      | some e => if entOf s ch = none then { s with live := s.live ++ [⟨ch, e.sess, e.origin, job, false⟩] } else s
  | .endSession c sess =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ admins then
      { s with ended := s.ended ++ [sess], active := s.active.filter (fun x => x ≠ sess),
               live := if C.revokeLineage then s.live.filter (fun e => ¬ (e.reg = true ∧ e.sess = sess))
                       else s.live.filter (fun e => ¬ (e.reg = true ∧ e.id = sess)) }
    else s
  | .fire j =>
    if s.halted ∧ C.haltCheck then s
    else match entOf s j with
      | none => s
      | some e => if e.job then { s with fired := s.fired ++ [(j, e.origin, s.ended.length)] } else s
  | .halt c =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ admins then
      { s with halted := true, ended := s.ended ++ s.active, active := [],
               live := s.live.filter (fun e => e.reg = false) }
    else s

def run (admins : List ℕ) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step admins C) s

theorem run_cons (admins : List ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run admins C s (o :: ops) = run admins C (step admins C s o) ops := rfl

/-! ## Invariant and safety -/

def Good (s : St) : Prop := ∀ e ∈ s.live, e.reg = true ∧ e.origin ∈ s.active ∧ e.origin ∉ s.ended

/-- a firing whose lineage had not ended when it fired (the ended log cut at that moment) -/
def FireOk (s : St) (f : ℕ × ℕ × ℕ) : Prop := f.2.2 ≤ s.ended.length ∧ f.2.1 ∉ s.ended.take f.2.2

structure Inv (s : St) : Prop where
  ent : ∀ e ∈ s.live, e.reg = true ∧ e.sess = e.origin ∧ e.origin ∈ s.active
  disj : ∀ x ∈ s.active, x ∉ s.ended
  fired_ok : ∀ f ∈ s.fired, FireOk s f

theorem inv_init : Inv init := ⟨by simp [init], by simp [init], by simp [init]⟩

theorem Inv.good {s : St} (h : Inv s) : Good s := fun e he =>
  let ⟨h1, _, h3⟩ := h.ent e he
  ⟨h1, h3, h.disj _ h3⟩

theorem fireOk_mono {s t : St} (hp : s.ended <+: t.ended) (f : ℕ × ℕ × ℕ) (h : FireOk s f) : FireOk t f := by
  obtain ⟨u, hu⟩ := hp
  refine ⟨h.1.trans (hu ▸ by simp), ?_⟩
  rw [← hu, List.take_append_of_le_length h.1]
  exact h.2

theorem entOf_mem {s : St} {id : ℕ} {e : Ent} (h : entOf s id = some e) : e ∈ s.live := List.mem_of_find?_eq_some h

theorem step_inv (admins : List ℕ) (s : St) (o : Op) (h : Inv s) : Inv (step admins full s o) := by
  cases o with
  | start c sess =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · obtain ⟨_, hna, hne, _⟩ := h2
      refine ⟨fun e he => ?_, fun x hx => ?_, h.fired_ok⟩
      · rcases List.mem_append.1 he with he | he
        · obtain ⟨a, b, c⟩ := h.ent e he; exact ⟨a, b, List.mem_append_left _ c⟩
        · simp at he; subst he; simp
      · rcases List.mem_append.1 hx with hx | hx
        · exact h.disj x hx
        · simp at hx; subst hx; exact hne
    · exact h
  | spawn p ch job claim =>
    cases he : entOf s p with
    | none => simp only [step, he]; split_ifs <;> exact h
    | some e =>
      simp only [step, he, show full.lineage = true from rfl, ite_true]
      split_ifs
      · exact h
      · refine ⟨fun x hx => ?_, h.disj, h.fired_ok⟩
        rcases List.mem_append.1 hx with hx | hx
        · exact h.ent x hx
        · simp at hx; subst hx
          obtain ⟨_, b, c⟩ := h.ent e (entOf_mem he)
          exact ⟨rfl, b, c⟩
      · exact h
  | bypass p ch job =>
    simp only [step, show full.registryOnly = true from rfl, ite_true]
    split_ifs <;> exact h
  | endSession c sess =>
    simp only [step, show full.revokeLineage = true from rfl, ite_true]
    split_ifs
    · exact h
    · refine ⟨fun e he => ?_, fun x hx => ?_,
        fun f hf => fireOk_mono (List.prefix_append _ _) f (h.fired_ok f hf)⟩
      · simp only [List.mem_filter, decide_eq_true_eq, not_and] at he
        obtain ⟨he, hns⟩ := he
        obtain ⟨a, b, c⟩ := h.ent e he
        refine ⟨a, b, List.mem_filter.2 ⟨c, ?_⟩⟩
        simp only [decide_eq_true_eq]
        rw [← b]; exact hns a
      · simp only [List.mem_filter, decide_eq_true_eq] at hx
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨h.disj x hx.1, hx.2⟩
    · exact h
  | fire j =>
    simp only [step]
    split_ifs
    · exact h
    · split
      · exact h
      · split_ifs
        · rename_i e he _
          refine ⟨h.ent, h.disj, fun f hf => ?_⟩
          rcases List.mem_append.1 hf with hf | hf
          · exact h.fired_ok f hf
          · simp at hf; subst hf
            refine ⟨le_rfl, ?_⟩
            rw [List.take_length]
            exact h.disj _ (h.ent e (entOf_mem he)).2.2
        · exact h
  | halt c =>
    simp only [step]
    split_ifs
    · exact h
    · refine ⟨fun e he => ?_, fun x hx => by simp at hx,
        fun f hf => fireOk_mono (List.prefix_append _ _) f (h.fired_ok f hf)⟩
      simp only [List.mem_filter, decide_eq_true_eq] at he
      have := (h.ent e he.1).1
      rw [he.2] at this
      exact absurd this Bool.false_ne_true
    · exact h

theorem run_inv (admins : List ℕ) (s : St) (ops : List Op) (h : Inv s) : Inv (run admins full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv admins s o h)

/-- **SC-12 safety.** After any trace from `init`, every live entity is registered and its true lineage is an
active, never-ended session: nothing of an ended session is live. Adversary: TRACE_ARBITRARY. -/
theorem sc12_safe (admins : List ℕ) (ops : List Op) : Good (run admins full init ops) :=
  (run_inv admins init ops inv_init).good

theorem step_ended (admins : List ℕ) (s : St) (o : Op) (h : Inv s) (sess : ℕ) (hs : sess ∈ s.ended) :
    sess ∈ (step admins full s o).ended ∧
      (step admins full s o).fired.filter (fun f => f.2.1 = sess) = s.fired.filter (fun f => f.2.1 = sess) := by
  cases o with
  | fire j =>
    simp only [step]
    split_ifs
    · exact ⟨hs, rfl⟩
    · split
      · exact ⟨hs, rfl⟩
      · rename_i e he
        split_ifs
        · refine ⟨hs, ?_⟩
          have hne : e.origin ≠ sess := fun heq => h.disj _ (h.ent e (entOf_mem he)).2.2 (heq ▸ hs)
          simp [List.filter_append, hne]
        · exact ⟨hs, rfl⟩
  | endSession c x =>
    simp only [step]
    split_ifs
    all_goals first | exact ⟨hs, rfl⟩ | exact ⟨List.mem_append_left _ hs, rfl⟩
  | halt c =>
    simp only [step]
    split_ifs
    all_goals first | exact ⟨hs, rfl⟩ | exact ⟨List.mem_append_left _ hs, rfl⟩
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals exact ⟨hs, rfl⟩

/-- **No firing after a session ends**: once a session has ended, no trace makes a job of its lineage fire. -/
theorem no_fire_after_end (admins : List ℕ) (s : St) (ops : List Op) (h : Inv s) (sess : ℕ) (hs : sess ∈ s.ended) :
    (run admins full s ops).fired.filter (fun f => f.2.1 = sess) = s.fired.filter (fun f => f.2.1 = sess) := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    rw [run_cons]
    obtain ⟨h1, h2⟩ := step_ended admins s o h sess hs
    rw [ih _ (step_inv admins s o h) h1, h2]

/-! ## Halt -/

theorem step_halted (admins : List ℕ) (s : St) (o : Op) (hh : s.halted = true) : step admins full s o = s := by
  cases o <;> simp [step, full, hh]

/-- **Halt freezes everything**: once halted, no trace changes the state. -/
theorem halt_freezes (admins : List ℕ) (s : St) (ops : List Op) (hh : s.halted = true) : run admins full s ops = s := by
  induction ops with
  | nil => rfl
  | cons o ops ih => rw [run_cons, step_halted admins s o hh, ih]

/-! ## Client of the shared gate interface -/

theorem fired_prefix (admins : List ℕ) (C : Checks) (s : St) (o : Op) : s.fired <+: (step admins C s o).fired := by
  cases o with
  | fire j =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals exact List.prefix_refl _

def sys (admins : List ℕ) : System St Op (ℕ × ℕ × ℕ) where
  step := step admins full
  effects := St.fired

/-- the gate spec: every firing's lineage had not ended when it fired -/
def spec (admins : List ℕ) : Spec (sys admins) where
  Inv := Inv
  ok := FireOk
  step_inv := fun s o h => step_inv admins s o h
  log_prefix := fun s o => fired_prefix admins full s o
  inv_ok := fun _ h f hf => h.fired_ok f hf

/-! ## Non-vacuity and necessity witnesses

Admin 9; session 1 (root entity 1); helper/job 5. -/

/-- **Non-vacuity**: a session's job fires while the session is live; ending the session kills its lineage and the
job no longer fires. -/
theorem honest_session_lifecycle :
    let s := run [9] full init [.start 9 1, .spawn 1 5 true 0, .fire 5, .endSession 9 1, .fire 5]
    s.fired = [(5, 1, 0)] ∧ s.live = [] := by
  decide

/-- a helper created outside the registry outlives its session and keeps firing -/
theorem registry_bypass_survives :
    (run [9] { full with registryOnly := false } init
      [.start 9 1, .bypass 1 5 true, .endSession 9 1, .fire 5]).fired = [(5, 1, 1)] ∧
    (run [9] full init [.start 9 1, .bypass 1 5 true, .endSession 9 1, .fire 5]).fired = [] := by
  decide

/-- revoking only the session's root entity leaves its children running -/
theorem parent_only_revocation_survives :
    (run [9] { full with revokeLineage := false } init
      [.start 9 1, .spawn 1 5 true 0, .endSession 9 1, .fire 5]).fired = [(5, 1, 1)] ∧
    (run [9] full init [.start 9 1, .spawn 1 5 true 0, .endSession 9 1, .fire 5]).fired = [] := by
  decide

/-- a job its creator registers under a different (still active) session outlives the creator's session -/
theorem foreign_registration_survives :
    (run [9] { full with lineage := false } init
      [.start 9 1, .start 9 2, .spawn 1 5 true 2, .endSession 9 1, .fire 5]).fired = [(5, 1, 1)] ∧
    (run [9] full init [.start 9 1, .start 9 2, .spawn 1 5 true 2, .endSession 9 1, .fire 5]).fired = [] := by
  decide

/-- without the halt check, new sessions and jobs start after a halt -/
theorem no_halt_check_breaks :
    (run [9] { full with haltCheck := false } init
      [.start 9 1, .halt 9, .start 9 2, .spawn 2 5 true 0, .fire 5]).fired = [(5, 2, 1)] ∧
    (run [9] full init [.start 9 1, .halt 9, .start 9 2, .spawn 2 5 true 0, .fire 5]).fired = [] := by
  decide

end ControlStack.SC12

#print axioms ControlStack.SC12.sc12_safe
#print axioms ControlStack.SC12.no_fire_after_end
#print axioms ControlStack.SC12.halt_freezes
#print axioms ControlStack.SC12.spec
#print axioms ControlStack.SC12.honest_session_lifecycle
#print axioms ControlStack.SC12.registry_bypass_survives
#print axioms ControlStack.SC12.parent_only_revocation_survives
#print axioms ControlStack.SC12.foreign_registration_survives
#print axioms ControlStack.SC12.no_halt_check_breaks
