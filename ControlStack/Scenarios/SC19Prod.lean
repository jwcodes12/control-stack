/-
SC-19: no irreversible production damage without a fresh, verified restore point and an independent approval of a
bounded change.

An abstract two-phase destructive-operation model (families F3/F5/F7):
- production targets have a version (bumped by every write) and a size (rows/objects);
- a snapshot records a target's version and size; a trusted verifier marks a snapshot verified (a restore test);
- a destructive operation is PREPARED by its author, APPROVED by an approver other than the author, and COMMITTED
  only with a snapshot of the same target that is verified and FRESH (its version is the target's current version, so
  it captures every write), and only if the number of objects affected, counted atomically at commit, is at most `R`;
- an absorbing admin HALT.

Main results (deployed configuration `full`; adversary class TRACE_ARBITRARY: any writes (including concurrent writes
between prepare and commit), snapshots, preparations, approvals by any caller, commits naming any snapshot):
- `sc19_safe`: from `init`, every destructive commit affected at most `R` objects, had a verified snapshot of the same
  target at the version it destroyed, and an approval by an approver other than its author; each operation commits at
  most once;
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`); non-vacuity `honest_destructive_change`.

Necessity witnesses: `stale_snapshot_breaks` (a write after the snapshot is not recoverable), `unverified_snapshot_breaks`,
`blast_radius_race_breaks` (counting affected objects at prepare time, before a concurrent write grows the target),
`no_halt_check_breaks`.

Premises outside the model: destructive effects happen only through `commit`; a verified snapshot can in fact be
restored; approver/verifier/admin credentials are held by those principals. Not claimed: that restoring is fast or
complete for effects outside the target (e.g. downstream consumers). No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC19

open ControlStack.Gate

structure Env where
  approvers : List ℕ
  verifiers : List ℕ
  admins : List ℕ
  R : ℕ

structure Obj where
  t : ℕ
  ver : ℕ
  size : ℕ
deriving DecidableEq, Repr

structure Pend where
  id : ℕ
  author : ℕ
  t : ℕ
  count : ℕ
deriving DecidableEq, Repr

/-- a committed destructive operation: id, author, target, version destroyed, objects actually affected, snapshot -/
structure Destroy where
  id : ℕ
  author : ℕ
  t : ℕ
  ver : ℕ
  actual : ℕ
  snap : ℕ
deriving DecidableEq, Repr

structure St where
  /-- newest first -/
  objs : List Obj
  snaps : List Obj
  verified : List ℕ
  pending : List Pend
  /-- (operation id, approver, author) -/
  approvals : List (ℕ × ℕ × ℕ)
  destroyed : List Destroy
  done : List ℕ
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | write (t n : ℕ)
  | snapshot (t : ℕ)
  | verify (caller i : ℕ)
  | prepare (caller id t : ℕ)
  | approve (caller id : ℕ)
  | commit (id i : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  fresh : Bool
  verified : Bool
  atomicCount : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], [], [], [], [], [], false⟩

def objOf (s : St) (t : ℕ) : Obj := (s.objs.find? (fun o => o.t = t)).getD ⟨t, 0, 0⟩

def pendOf (s : St) (id : ℕ) : Option Pend := s.pending.find? (fun p => p.id = id)

/-- objects affected, as the gate counts them: atomically at commit, or (unsafe) as recorded at prepare -/
def countOf (C : Checks) (s : St) (p : Pend) : ℕ := if C.atomicCount then (objOf s p.t).size else p.count

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .write t n =>
    if s.halted ∧ C.haltCheck then s
    else { s with objs := ⟨t, (objOf s t).ver + 1, (objOf s t).size + n⟩ :: s.objs }
  | .snapshot t => if s.halted ∧ C.haltCheck then s else { s with snaps := s.snaps ++ [objOf s t] }
  | .verify c i =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ E.verifiers ∧ i < s.snaps.length then { s with verified := s.verified ++ [i] } else s
  | .prepare c id t =>
    if s.halted ∧ C.haltCheck then s
    else if pendOf s id = none then { s with pending := s.pending ++ [⟨id, c, t, (objOf s t).size⟩] } else s
  | .approve c id =>
    if s.halted ∧ C.haltCheck then s
    else match pendOf s id with
      | none => s
      | some p => if c ∈ E.approvers ∧ c ≠ p.author then { s with approvals := s.approvals ++ [(id, c, p.author)] }
                  else s
  | .commit id i =>
    if s.halted ∧ C.haltCheck then s
    else match pendOf s id with
      | none => s
      | some p =>
        match s.snaps[i]? with
        | none => s
        | some sn =>
          if id ∉ s.done ∧ (∃ a ∈ s.approvals, a.1 = id ∧ a.2.2 = p.author) ∧ sn.t = p.t ∧
              (C.verified = true → i ∈ s.verified) ∧ (C.fresh = true → sn.ver = (objOf s p.t).ver) ∧
              countOf C s p ≤ E.R then
            { s with destroyed := s.destroyed ++ [⟨id, p.author, p.t, (objOf s p.t).ver, (objOf s p.t).size, i⟩],
                     done := s.done ++ [id],
                     objs := ⟨p.t, (objOf s p.t).ver + 1, 0⟩ :: s.objs }
          else s
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run E C s (o :: ops) = run E C (step E C s o) ops := rfl

/-! ## Invariant and safety -/

def DestroyOk (E : Env) (s : St) (d : Destroy) : Prop :=
  d.actual ≤ E.R ∧ (∃ sn, s.snaps[d.snap]? = some sn ∧ sn.t = d.t ∧ sn.ver = d.ver) ∧ d.snap ∈ s.verified ∧
    ∃ a ∈ s.approvals, a.1 = d.id ∧ a.2.1 ∈ E.approvers ∧ a.2.1 ≠ d.author

def Good (E : Env) (s : St) : Prop := (∀ d ∈ s.destroyed, DestroyOk E s d) ∧ (s.destroyed.map Destroy.id).Nodup

structure Inv (E : Env) (s : St) : Prop where
  appr : ∀ a ∈ s.approvals, a.2.1 ∈ E.approvers ∧ a.2.1 ≠ a.2.2
  dest : ∀ d ∈ s.destroyed, d.actual ≤ E.R ∧ (∃ sn, s.snaps[d.snap]? = some sn ∧ sn.t = d.t ∧ sn.ver = d.ver) ∧
    d.snap ∈ s.verified ∧ ∃ a ∈ s.approvals, a.1 = d.id ∧ a.2.2 = d.author
  done_ok : ∀ d ∈ s.destroyed, d.id ∈ s.done
  nodup : (s.destroyed.map Destroy.id).Nodup

theorem inv_init (E : Env) : Inv E init := ⟨by simp [init], by simp [init], by simp [init], by simp [init]⟩

theorem Inv.good {E : Env} {s : St} (h : Inv E s) : Good E s := by
  refine ⟨fun d hd => ?_, h.nodup⟩
  obtain ⟨h1, h2, h3, a, ha, h4, h5⟩ := h.dest d hd
  obtain ⟨h6, h7⟩ := h.appr a ha
  exact ⟨h1, h2, h3, a, ha, h4, h6, h5 ▸ h7⟩

/-- steps that only grow snapshots, verifications, pending operations or approvals (validly), or change objects -/
theorem inv_mono {E : Env} {s t : St} (h : Inv E s) (hs : s.snaps <+: t.snaps) (hv : s.verified ⊆ t.verified)
    (ha : s.approvals ⊆ t.approvals) (han : ∀ a ∈ t.approvals, a ∉ s.approvals → a.2.1 ∈ E.approvers ∧ a.2.1 ≠ a.2.2)
    (hd : t.destroyed = s.destroyed) (hdn : t.done = s.done) : Inv E t := by
  refine ⟨fun a hm => ?_, fun d hm => ?_, fun d hm => ?_, hd ▸ h.nodup⟩
  · by_cases hx : a ∈ s.approvals
    · exact h.appr a hx
    · exact han a hm hx
  · rw [hd] at hm
    obtain ⟨h1, ⟨sn, hsn, h2⟩, h3, a, hm', h4⟩ := h.dest d hm
    obtain ⟨u, hu⟩ := hs
    have hi : d.snap < s.snaps.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hsn
      simp at hsn
    refine ⟨h1, ⟨sn, ?_, h2⟩, hv h3, a, ha hm', h4⟩
    rw [← hu, List.getElem?_append_left hi]
    exact hsn
  · rw [hd] at hm; rw [hdn]; exact h.done_ok d hm

theorem inv_same {E : Env} {s t : St} (h : Inv E s) (hs : t.snaps = s.snaps) (hv : t.verified = s.verified)
    (ha : t.approvals = s.approvals) (hd : t.destroyed = s.destroyed) (hdn : t.done = s.done) : Inv E t :=
  inv_mono h (hs ▸ List.prefix_refl _) (fun _ x => hv ▸ x) (fun _ x => ha ▸ x) (fun _ hm hn => absurd (ha ▸ hm) hn) hd hdn

theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o) := by
  cases o with
  | approve c id =>
    cases hp : pendOf s id with
    | none => simp only [step, hp]; split_ifs <;> exact h
    | some p =>
      simp only [step, hp]
      split_ifs with h1 h2
      · exact h
      · refine inv_mono h (List.prefix_refl _) (fun _ x => x) (fun _ x => List.mem_append_left _ x) ?_ rfl rfl
        intro a hm hn
        rcases List.mem_append.1 hm with hm | hm
        · exact absurd hm hn
        · simp at hm; subst hm; exact h2
      · exact h
  | commit id i =>
    cases hp : pendOf s id with
    | none => simp only [step, hp]; split_ifs <;> exact h
    | some p =>
      cases hsn : s.snaps[i]? with
      | none => simp only [step, hp, hsn]; split_ifs <;> exact h
      | some sn =>
        simp only [step, hp, hsn]
        split_ifs with h1 h2
        · exact h
        · obtain ⟨hn, ⟨a, ha, hid, hau⟩, ht, hv, hf, hc⟩ := h2
          simp only [full, forall_const, countOf, ite_true] at hv hf hc
          refine ⟨h.appr, fun d hd => ?_, fun d hd => ?_, ?_⟩
          · rcases List.mem_append.1 hd with hd | hd
            · exact h.dest d hd
            · simp at hd; subst hd
              exact ⟨hc, ⟨sn, hsn, ht, hf⟩, hv, a, ha, hid, hau⟩
          · rcases List.mem_append.1 hd with hd | hd
            · exact List.mem_append_left _ (h.done_ok d hd)
            · simp at hd; subst hd; simp
          · simp only [List.map_append, List.map_cons, List.map_nil]
            refine List.nodup_append.2 ⟨h.nodup, List.nodup_singleton _, fun x hx y hy => ?_⟩
            simp only [List.mem_singleton] at hy
            subst hy
            rintro rfl
            obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
            exact hn (h.done_ok d hd)
        · exact h
  | verify c i =>
    simp only [step]
    split_ifs
    · exact h
    · exact inv_mono h (List.prefix_refl _) (fun _ x => List.mem_append_left _ x) (fun _ x => x)
        (fun _ hm hn => absurd hm hn) rfl rfl
    · exact h
  | snapshot t =>
    simp only [step]
    split_ifs
    · exact h
    · exact inv_mono h (List.prefix_append _ _) (fun _ x => x) (fun _ x => x) (fun _ hm hn => absurd hm hn) rfl rfl
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact h | exact inv_same h rfl rfl rfl rfl rfl

theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv E s o h)

/-- **SC-19 safety.** After any trace from `init`, every destructive commit affected at most `R` objects, had a
verified snapshot of the same target at exactly the version it destroyed, and an approval by an approver other than
its author; no operation committed twice. Adversary: TRACE_ARBITRARY (including concurrent writes). -/
theorem sc19_safe (E : Env) (ops : List Op) : Good E (run E full init ops) := (run_inv E init ops (inv_init E)).good

/-! ## Halt -/

theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s := by
  cases o with
  | halt c =>
    simp only [step]
    split_ifs
    · cases s; simp_all
    · rfl
  | _ => simp [step, full, hh]

/-- **Halt freezes**: once halted, no trace changes the state. -/
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s := by
  induction ops with
  | nil => rfl
  | cons o ops ih => rw [run_cons, step_halted E s o hh, ih]

/-! ## Client of the shared gate interface -/

theorem destroyed_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.destroyed <+: (step E C s o).destroyed := by
  cases o with
  | commit id i =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals exact List.prefix_refl _

def sys (E : Env) : System St Op Destroy where
  step := step E full
  effects := St.destroyed

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := DestroyOk E
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => destroyed_prefix E full s o
  inv_ok := fun _ h d hd => h.good.1 d hd

/-! ## Non-vacuity and necessity witnesses

Agent (author) 1, approver 2, verifier 3, admin 9; target 7; blast-radius cap R = 10. -/

def E0 : Env := ⟨[2], [3], [9], 10⟩

/-- **Non-vacuity**: a reviewed, bounded deletion with a fresh verified snapshot commits. -/
theorem honest_destructive_change :
    (run E0 full init [.write 7 5, .snapshot 7, .verify 3 0, .prepare 1 0 7, .approve 2 0, .commit 0 0]).destroyed =
      [⟨0, 1, 7, 1, 5, 0⟩] := by
  decide

/-- a write after the snapshot: the restore point no longer captures what is destroyed -/
theorem stale_snapshot_breaks :
    let ops := [Op.write 7 5, .snapshot 7, .verify 3 0, .write 7 3, .prepare 1 0 7, .approve 2 0, .commit 0 0]
    (run E0 { full with fresh := false } init ops).destroyed = [⟨0, 1, 7, 2, 8, 0⟩] ∧
    (run E0 { full with fresh := false } init ops).snaps.map Obj.ver = [1] ∧
    (run E0 full init ops).destroyed = [] := by
  decide

/-- a snapshot nobody verified is accepted as a restore point -/
theorem unverified_snapshot_breaks :
    (run E0 { full with verified := false } init
      [.write 7 5, .snapshot 7, .prepare 1 0 7, .approve 2 0, .commit 0 0]).destroyed = [⟨0, 1, 7, 1, 5, 0⟩] ∧
    (run E0 full init [.write 7 5, .snapshot 7, .prepare 1 0 7, .approve 2 0, .commit 0 0]).destroyed = [] := by
  decide

/-- counting affected objects at prepare time: a concurrent write grows the target to 25 > R before the commit -/
theorem blast_radius_race_breaks :
    let ops := [Op.write 7 5, .prepare 1 0 7, .write 7 20, .snapshot 7, .verify 3 0, .approve 2 0, .commit 0 0]
    (run E0 { full with atomicCount := false } init ops).destroyed = [⟨0, 1, 7, 2, 25, 0⟩] ∧
    (run E0 full init ops).destroyed = [] := by
  decide

/-- without the halt check, destructive commits continue after a halt -/
theorem no_halt_check_breaks :
    let ops := [Op.write 7 5, .snapshot 7, .verify 3 0, .prepare 1 0 7, .approve 2 0, .halt 9, .commit 0 0]
    (run E0 { full with haltCheck := false } init ops).destroyed = [⟨0, 1, 7, 1, 5, 0⟩] ∧
    (run E0 full init ops).destroyed = [] := by
  decide

end ControlStack.SC19

#print axioms ControlStack.SC19.sc19_safe
#print axioms ControlStack.SC19.halt_freezes
#print axioms ControlStack.SC19.spec
#print axioms ControlStack.SC19.honest_destructive_change
#print axioms ControlStack.SC19.stale_snapshot_breaks
#print axioms ControlStack.SC19.unverified_snapshot_breaks
#print axioms ControlStack.SC19.blast_radius_race_breaks
#print axioms ControlStack.SC19.no_halt_check_breaks
