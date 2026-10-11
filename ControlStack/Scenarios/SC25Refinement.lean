/-
SC-25 refinement: the runtime's event structure (scenarios/SC-25/harness/executor.py, principal.py; prereg
SC25-AUDIT-QUEUE.md) as a concrete machine, with a forward simulation into the Lean model `ControlStack.SC25`.
This brings SC-25 to SC-26's criterion-3 standard.

Concrete machine (`CSt`, `COp`, `stepC`), mirroring the runtime:
- the executor's items, journaled newest first (`submit`, `amend` with content). Each item also stores the digest of
  its content AT SUBMISSION (`cached`), used only by the broken variant below;
- the AUDITOR's own append-only log (principal.py): rows (id, digest, verdict, auditor, FULL CONTENT SEEN); the auditor
  fetches the CURRENT content of the operation (the executor's `svc.sock get`);
- the APPROVER's own log: rows (id, digest, approver, content seen);
- the executor's effect log: (id, content, submitter, digest checked, verdict-log and approval-log lengths);
- `expire id`: the timer sweep. An item with no verdict at all expires (fail closed);
- `check id`: the agent's check request; the volatile `checked` set;
- `fire id`: ONE atomic step. The runtime executor is single-threaded, so the fire-time re-validation cannot interleave
  with an amendment. It reads the CURRENT content, takes its digest, requires a PASS for exactly that digest and, for
  an irreversible content (trusted classifier), an approval of exactly that digest by someone other than the
  submitter, and appends the effect. It also records the implicit check;
- `crash` (volatile `checked` lost; items and logs durable), `restart` (no durable change), `halt`.
`stepC` takes a flag `cachedDigest` (false in the runtime): if true, fire validates against the digest cached at
SUBMISSION instead of the current content's.

Results (deployed, `cachedDigest = false`; adversary class TRACE_ARBITRARY over concrete operations):
- `simulation`: with abstraction α (items ↦ queue; auditor log ↦ verdicts; approver log ↦ approvals; effects ↦
  executed; content fields dropped), every concrete step is matched by model steps:
  α (stepC s o) = SC25.run (α s) (opsOf s o), with fire ↦ [check id, fire id] when it executes, else [];
  expire ↦ [timeout id]; restart ↦ []; the rest ↦ themselves;
- `concrete_safe`: `SC25.Good` holds for α of every reachable concrete state (`sc25_safe` transfers);
- `concrete_content_safe`: under `Set.InjOn h` on every content ever in the items journal, every effect's EXACT content
  appears in the auditor's own log with verdict PASS, for that id, by an auditor (the content-level guarantee of
  `SC25Content.sc25_content_safe`, here read off the auditor's log, as the runtime reconciliation does);
- `cached_digest_breaks`: with `cachedDigest = true`, content 7 is audited, amended to 50, and 50 executes; the
  transferred property fails (`¬ SC25.Good`). This matches the runtime control "digest unchecked". The deployed
  executor refuses.

What the refinement does NOT cover: that the Python code implements this concrete machine (that link stays TESTED,
via reconcile.py over the executor journal, the principals' logs and the effect log); OS identity (SO_PEERCRED pids
as submitter ids); the auditor's policy. The crash of the runtime executor was not exercised (prereg). Classical
forward simulation; no novelty.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC25Audit

namespace ControlStack.SC25Refinement

open ControlStack.SC25

structure CItem where
  id : ℕ
  content : ℕ
  declared : Bool
  submitter : ℕ
  cached : ℕ
deriving DecidableEq, Repr

/-- an auditor log row (principal.py): id, digest, verdict, auditor, content seen -/
structure ARow where
  id : ℕ
  d : ℕ
  pass : Bool
  by_ : ℕ
  content : ℕ
deriving DecidableEq, Repr

/-- an approver log row -/
structure PRow where
  id : ℕ
  d : ℕ
  approver : ℕ
  content : ℕ
deriving DecidableEq, Repr

/-- an effect log record -/
structure ERow where
  id : ℕ
  content : ℕ
  submitter : ℕ
  d : ℕ
  vlen : ℕ
  alen : ℕ
deriving DecidableEq, Repr

structure CSt where
  items : List CItem
  auditLog : List ARow
  apprLog : List PRow
  expired : List ℕ
  checked : List ℕ
  effects : List ERow
  halted : Bool
deriving DecidableEq, Repr

inductive COp where
  | submit (caller id content : ℕ) (declared : Bool)
  | amend (caller id content : ℕ)
  | audit (caller id : ℕ) (pass : Bool)
  | approve (caller id : ℕ)
  | expire (id : ℕ)
  | check (id : ℕ)
  | fire (id : ℕ)
  | crash
  | restart
  | halt (caller : ℕ)
deriving DecidableEq, Repr

def cinit : CSt := ⟨[], [], [], [], [], [], false⟩

def toItem (c : CItem) : Item := ⟨c.id, c.content, c.declared, c.submitter⟩
def toVerdict (a : ARow) : Verdict := ⟨a.id, a.d, a.pass, some a.by_⟩
def toAppr (p : PRow) : Appr := ⟨p.id, p.d, p.approver⟩
def toExec (e : ERow) : Exec := ⟨e.id, e.content, e.submitter, e.vlen, e.alen⟩

/-- the abstraction: drop the content fields of the logs and the cached digests -/
def α (s : CSt) : St :=
  ⟨s.items.map toItem, s.auditLog.map toVerdict, s.apprLog.map toAppr, s.expired, s.checked, s.effects.map toExec,
    s.halted⟩

def citemOf (s : CSt) (id : ℕ) : Option CItem := s.items.find? (fun it => it.id = id)

theorem itemOf_α (s : CSt) (id : ℕ) : itemOf (α s) id = (citemOf s id).map toItem := by
  simp only [itemOf, citemOf, α, List.find?_map]
  rfl

/-- the executor's fire-time validation, with the digest it checks (`dd`) -/
abbrev ValidC (_h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (it : CItem) (dd : ℕ) : Prop :=
  it.id ∉ s.expired ∧ (∃ v ∈ s.auditLog, v.id = it.id ∧ v.pass = true ∧ v.d = dd) ∧
    (cls it.content = true → ∃ ap ∈ s.apprLog, ap.id = it.id ∧ ap.d = dd ∧ ap.approver ≠ it.submitter)

/-- the digest the executor checks at fire time -/
def fireDigest (h : ℕ → ℕ) (cachedDigest : Bool) (it : CItem) : ℕ := if cachedDigest then it.cached else h it.content

def stepC (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (cachedDigest : Bool) (s : CSt) : COp → CSt
  | .submit c id x decl =>
    if s.halted then s
    else if c ∈ R.agents ∧ citemOf s id = none then { s with items := ⟨id, x, decl, c, h x⟩ :: s.items } else s
  | .amend c id x =>
    if s.halted then s
    else match citemOf s id with
      | none => s
      | some it =>
        if c ∈ R.agents ∧ id ∉ s.effects.map ERow.id then { s with items := { it with content := x } :: s.items }
        else s
  | .audit c id pass =>
    if s.halted then s
    else match citemOf s id with
      | none => s
      | some it =>
        if c ∈ R.auditors then { s with auditLog := s.auditLog ++ [⟨id, h it.content, pass, c, it.content⟩] } else s
  | .approve c id =>
    if s.halted then s
    else match citemOf s id with
      | none => s
      | some it =>
        if c ∈ R.approvers then { s with apprLog := s.apprLog ++ [⟨id, h it.content, c, it.content⟩] } else s
  | .expire id =>
    if s.halted then s
    else match citemOf s id with
      | none => s
      | some _ => if ∃ v ∈ s.auditLog, v.id = id then s else { s with expired := s.expired ++ [id] }
  | .check id =>
    if s.halted then s
    else match citemOf s id with
      | none => s
      | some it => if ValidC h cls s it (h it.content) then { s with checked := id :: s.checked } else s
  | .fire id =>
    if s.halted then s
    else match citemOf s id with
      | none => s
      | some it =>
        if id ∉ s.effects.map ERow.id ∧ ValidC h cls s it (fireDigest h cachedDigest it) then
          { s with checked := id :: s.checked,
                   effects := s.effects ++ [⟨id, it.content, it.submitter, fireDigest h cachedDigest it,
                     s.auditLog.length, s.apprLog.length⟩] }
        else s
  | .crash => { s with checked := [] }
  | .restart => s
  | .halt c => if c ∈ R.admins then { s with halted := true } else s

def runC (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (cd : Bool) (s : CSt) (ops : List COp) : CSt :=
  ops.foldl (stepC R h cls cd) s

/-- the model operations matching one concrete step (deployed executor) -/
def opsOf (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) : COp → List Op
  | .submit c id x d => [.submit c id x d]
  | .amend c id x => [.amend c id x]
  | .audit c id p => [.audit c id p]
  | .approve c id => [.approve c id]
  | .expire id => [.timeout id]
  | .check id => [.check id]
  | .fire id =>
    if s.halted then []
    else match citemOf s id with
      | none => []
      | some it => if id ∉ s.effects.map ERow.id ∧ ValidC h cls s it (h it.content) then [.check id, .fire id] else []
  | .crash => [.crash]
  | .restart => []
  | .halt c => [.halt c]

/-! ## Forward simulation -/

theorem valid_iff (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (it : CItem) :
    Valid h cls full (α s) (toItem it) ↔ ValidC h cls s it (h it.content) := by
  simp only [Valid, α, toItem, irrevOf, full, ite_true, true_implies, List.mem_map]
  constructor
  · rintro ⟨h1, ⟨v, ⟨a, ha, rfl⟩, h2, h3, h4⟩, h5⟩
    refine ⟨h1, ⟨a, ha, h2, h3, h4⟩, fun hc => ?_⟩
    obtain ⟨ap, ⟨p, hp, rfl⟩, h6, h7, h8⟩ := h5 hc
    exact ⟨p, hp, h6, h7, h8⟩
  · rintro ⟨h1, ⟨a, ha, h2, h3, h4⟩, h5⟩
    refine ⟨h1, ⟨toVerdict a, ⟨a, ha, rfl⟩, h2, h3, h4⟩, fun hc => ?_⟩
    obtain ⟨p, hp, h6, h7, h8⟩ := h5 hc
    exact ⟨toAppr p, ⟨p, hp, rfl⟩, h6, h7, h8⟩

theorem exec_ids (s : CSt) : (α s).executed.map Exec.id = s.effects.map ERow.id := by
  simp [α, toExec, Function.comp_def]

theorem verdict_ex (s : CSt) (id : ℕ) : (∃ v ∈ (α s).verdicts, v.id = id) ↔ ∃ v ∈ s.auditLog, v.id = id := by
  simp [α, toVerdict]

theorem step_check_valid (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (id : ℕ) (it : CItem)
    (hn : (α s).halted = false) (hi : citemOf s id = some it) (hv : Valid h cls full (α s) (toItem it)) :
    step R h cls full (α s) (.check id) = { α s with checked := id :: (α s).checked } := by
  simp only [step]
  split_ifs with h1
  · simp [hn] at h1
  · rw [itemOf_α, hi]
    simp only [Option.map_some]
    split_ifs; rfl

theorem step_fire_valid (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (id : ℕ) (it : CItem)
    (hn : (α s).halted = false) (hi : citemOf s id = some it) (hv : Valid h cls full (α s) (toItem it))
    (hx : id ∉ s.effects.map ERow.id) :
    step R h cls full { α s with checked := id :: (α s).checked } (.fire id) =
      St.mk (α s).queue (α s).verdicts (α s).approvals (α s).expired (id :: (α s).checked)
        ((α s).executed ++ [Exec.mk id it.content it.submitter (α s).verdicts.length (α s).approvals.length])
        (α s).halted := by
  simp only [step]
  split_ifs with h1
  · simp [hn] at h1
  · have hq : itemOf { α s with checked := id :: (α s).checked } id = itemOf (α s) id := rfl
    rw [hq, itemOf_α, hi]
    simp only [Option.map_some]
    split_ifs with h2
    · rfl
    · exact absurd ⟨List.mem_cons_self, by rw [exec_ids]; exact hx, fun _ => hv⟩ h2

theorem simulation (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (o : COp) :
    α (stepC R h cls false s o) = run R h cls full (α s) (opsOf h cls s o) := by
  have hh : (α s).halted = s.halted := rfl
  cases o with
  | submit c id x d =>
    simp only [stepC, opsOf, run, List.foldl_cons, List.foldl_nil, step, hh, full, and_true, itemOf_α,
      Option.map_eq_none_iff]
    split_ifs <;> simp [α, toItem]
  | amend c id x =>
    cases hi : citemOf s id with
    | none =>
      simp only [stepC, opsOf, run, List.foldl_cons, List.foldl_nil, step, hh, full, and_true, itemOf_α, hi,
        Option.map_none]
      split_ifs <;> rfl
    | some it =>
      simp only [stepC, opsOf, run, List.foldl_cons, List.foldl_nil, step, hh, full, and_true, itemOf_α, hi,
        Option.map_some, exec_ids]
      split_ifs <;> simp [α, toItem]
  | audit c id p =>
    cases hi : citemOf s id with
    | none =>
      simp only [stepC, opsOf, run, List.foldl_cons, List.foldl_nil, step, hh, full, and_true, itemOf_α, hi,
        Option.map_none]
      split_ifs <;> rfl
    | some it =>
      simp only [stepC, opsOf, run, List.foldl_cons, List.foldl_nil, step, hh, full, and_true, itemOf_α, hi,
        Option.map_some]
      split_ifs <;> simp [α, toItem, toVerdict]
  | approve c id =>
    cases hi : citemOf s id with
    | none =>
      simp only [stepC, opsOf, run, List.foldl_cons, List.foldl_nil, step, hh, full, and_true, itemOf_α, hi,
        Option.map_none]
      split_ifs <;> rfl
    | some it =>
      simp only [stepC, opsOf, run, List.foldl_cons, List.foldl_nil, step, hh, full, and_true, itemOf_α, hi,
        Option.map_some]
      split_ifs <;> simp [α, toItem, toAppr]
  | expire id =>
    cases hi : citemOf s id with
    | none =>
      simp only [stepC, opsOf, run, List.foldl_cons, List.foldl_nil, step, hh, full, and_true, itemOf_α, hi,
        Option.map_none]
      split_ifs <;> rfl
    | some it =>
      simp only [stepC, opsOf, run, List.foldl_cons, List.foldl_nil, step, hh, full, and_true, itemOf_α, hi,
        Option.map_some, verdict_ex, Bool.false_eq_true, ite_false]
      split_ifs <;> simp [α]
  | check id =>
    cases hi : citemOf s id with
    | none =>
      simp only [stepC, opsOf, run, List.foldl_cons, List.foldl_nil, step, hh, full, and_true, itemOf_α, hi,
        Option.map_none]
      split_ifs <;> rfl
    | some it =>
      simp only [stepC, opsOf, run, List.foldl_cons, List.foldl_nil, step, hh, full, and_true, itemOf_α, hi,
        Option.map_some]
      have hv := valid_iff h cls s it
      by_cases hhs : s.halted = true
      · simp [hhs]
      · simp only [hhs, ite_false, Bool.false_eq_true]
        have hv' : Valid h cls ⟨true, true, false, true, true⟩ (α s) (toItem it) ↔ ValidC h cls s it (h it.content) := hv
        by_cases hc : ValidC h cls s it (h it.content)
        · rw [ite_eq_left hc, ite_eq_left (hv'.2 hc)]; simp [α]
        · rw [ite_eq_right hc, ite_eq_right (fun x => hc (hv'.1 x))]
  | fire id =>
    by_cases hhs : s.halted = true
    · simp [stepC, opsOf, hhs, run]
    · have hn : (α s).halted = false := by simpa [α] using hhs
      cases hi : citemOf s id with
      | none => simp [stepC, opsOf, hhs, hi, run]
      | some it =>
        by_cases hc : id ∉ s.effects.map ERow.id ∧ ValidC h cls s it (h it.content)
        · have hv := (valid_iff h cls s it).2 hc.2
          have ec : stepC R h cls false s (.fire id) = CSt.mk s.items s.auditLog s.apprLog s.expired
              (id :: s.checked) (s.effects ++ [ERow.mk id it.content it.submitter (h it.content) s.auditLog.length
                s.apprLog.length]) s.halted := by
            simp only [stepC, hhs, Bool.false_eq_true, ite_false, hi]
            split_ifs <;> first | rfl | contradiction
          have eo : opsOf h cls s (.fire id) = [.check id, .fire id] := by
            simp only [opsOf, hhs, Bool.false_eq_true, ite_false, hi]
            split_ifs; rfl
          rw [ec, eo]
          simp only [run, List.foldl_cons, List.foldl_nil]
          rw [step_check_valid R h cls s id it hn hi hv, step_fire_valid R h cls s id it hn hi hv hc.1]
          simp [α, toExec]
        · have ec : stepC R h cls false s (.fire id) = s := by
            simp only [stepC, hhs, Bool.false_eq_true, ite_false, hi]
            split_ifs <;> first | rfl | contradiction
          have eo : opsOf h cls s (.fire id) = [] := by
            simp only [opsOf, hhs, Bool.false_eq_true, ite_false, hi]
            split_ifs; rfl
          rw [ec, eo]; rfl
  | crash => simp [stepC, opsOf, run, step, α]
  | restart => rfl
  | halt c =>
    simp only [stepC, opsOf, run, List.foldl_cons, List.foldl_nil, step]
    split_ifs <;> simp [α]

def absTrace (h : ℕ → ℕ) (cls : ℕ → Bool) (R : Roles) : CSt → List COp → List Op
  | _, [] => []
  | s, o :: ops => opsOf h cls s o ++ absTrace h cls R (stepC R h cls false s o) ops

theorem simulation_run (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (ops : List COp) :
    α (runC R h cls false s ops) = run R h cls full (α s) (absTrace h cls R s ops) := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    change α (runC R h cls false (stepC R h cls false s o) ops) = _
    rw [ih, simulation]
    simp [absTrace, run, List.foldl_append]

theorem α_cinit : α cinit = init := rfl

/-- **SC-25 safety for the concrete executor.** For every concrete trace (any interleaving of submissions, amendments,
audits, approvals, expiries, checks, fires, crashes, restarts, halts), α of the reached state satisfies `SC25.Good`:
every effect had, when it ran, a PASS for exactly its content's digest from an auditor and, if irreversible, an
independent approval of exactly that digest; nothing executed twice. -/
theorem concrete_safe (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp) :
    Good R h cls (α (runC R h cls false cinit ops)) := by
  rw [simulation_run, α_cinit]
  exact sc25_safe R h cls _

/-! ## Content level, read off the auditor's own log -/

/-- the concrete invariant: audit rows record the digest of the content they saw, and every audited or executed
content is in the items journal -/
structure CInv (h : ℕ → ℕ) (s : CSt) : Prop where
  arow : ∀ a ∈ s.auditLog, h a.content = a.d ∧ ∃ it ∈ s.items, it.content = a.content
  erow : ∀ e ∈ s.effects, ∃ it ∈ s.items, it.content = e.content

theorem cinv_init (h : ℕ → ℕ) : CInv h cinit := ⟨by simp [cinit], by simp [cinit]⟩

theorem citemOf_mem {s : CSt} {id : ℕ} {it : CItem} (hi : citemOf s id = some it) : it ∈ s.items :=
  List.mem_of_find?_eq_some hi

theorem cinv_step (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (o : COp) (hs : CInv h s) :
    CInv h (stepC R h cls false s o) := by
  have grow : ∀ t : CSt, t.auditLog = s.auditLog → t.effects = s.effects → s.items ⊆ t.items → CInv h t :=
    fun t h1 h2 h3 => ⟨fun a ha => by
      rw [h1] at ha; obtain ⟨x, ⟨it, hit, hc⟩⟩ := hs.arow a ha; exact ⟨x, it, h3 hit, hc⟩,
      fun e he => by rw [h2] at he; obtain ⟨it, hit, hc⟩ := hs.erow e he; exact ⟨it, h3 hit, hc⟩⟩
  cases o with
  | submit c id x d =>
    simp only [stepC]; split_ifs
    · exact hs
    · exact grow _ rfl rfl (fun _ hy => List.mem_cons_of_mem _ hy)
    · exact hs
  | amend c id x =>
    cases hi : citemOf s id with
    | none => simp only [stepC, hi]; split_ifs <;> exact hs
    | some it =>
      simp only [stepC, hi]
      split_ifs
      all_goals first | exact hs | exact grow _ rfl rfl (fun _ hy => List.mem_cons_of_mem _ hy)
  | audit c id p =>
    cases hi : citemOf s id with
    | none => simp only [stepC, hi]; split_ifs <;> exact hs
    | some it =>
      simp only [stepC, hi]
      split_ifs
      all_goals first
        | exact hs
        | refine ⟨fun a ha => ?_, hs.erow⟩
          rcases List.mem_append.1 ha with ha | ha
          · exact hs.arow a ha
          · simp at ha; subst ha; exact ⟨rfl, it, citemOf_mem hi, rfl⟩
  | fire id =>
    cases hi : citemOf s id with
    | none => simp only [stepC, hi]; split_ifs <;> exact hs
    | some it =>
      simp only [stepC, hi]
      split_ifs
      all_goals first
        | exact hs
        | refine ⟨hs.arow, fun e he => ?_⟩
          rcases List.mem_append.1 he with he | he
          · exact hs.erow e he
          · simp at he; subst he; exact ⟨it, citemOf_mem hi, rfl⟩
  | _ =>
    simp only [stepC]
    repeat' (first | split | split_ifs)
    all_goals first | exact hs | exact grow _ rfl rfl (fun _ hy => hy)

theorem cinv_run (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : CSt) (ops : List COp) (hs : CInv h s) :
    CInv h (runC R h cls false s ops) := by
  induction ops generalizing s with
  | nil => exact hs
  | cons o ops ih => exact ih _ (cinv_step R h cls s o hs)

/-- **Content level.** If the digest is injective on every content in the items journal, every effect's EXACT content
appears in the auditor's own log for that id with verdict PASS, by an auditor. -/
theorem concrete_content_safe (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp)
    (hinj : Set.InjOn h {c | ∃ it ∈ (runC R h cls false cinit ops).items, it.content = c}) :
    ∀ e ∈ (runC R h cls false cinit ops).effects, ∃ a ∈ (runC R h cls false cinit ops).auditLog,
      a.id = e.id ∧ a.content = e.content ∧ a.pass = true ∧ a.by_ ∈ R.auditors := by
  intro e he
  have hg := concrete_safe R h cls ops
  have hc := cinv_run R h cls cinit ops (cinv_init h)
  have he' : toExec e ∈ (α (runC R h cls false cinit ops)).executed := List.mem_map.2 ⟨e, he, rfl⟩
  obtain ⟨⟨v, hv, hid, hpass, hd, b, hby, hb⟩, -⟩ := hg.1 _ he'
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hv)
  obtain ⟨had, it₁, hit₁, hc₁⟩ := hc.arow a ha
  obtain ⟨it₂, hit₂, hc₂⟩ := hc.erow e he
  refine ⟨a, ha, hid, hinj ⟨it₁, hit₁, hc₁⟩ ⟨it₂, hit₂, hc₂⟩ (by rw [had]; exact hd), hpass, ?_⟩
  simp only [toVerdict, Option.some.injEq] at hby
  rw [hby]; exact hb

/-! ## Witness: a fire re-check against the digest cached at submission -/

/-- **Cached digest breaks the transferred property.** Content 7 is audited PASS, the agent amends it to 50, and the
executor that re-checks the SUBMISSION-time digest executes 50: `SC25.Good` fails for α of the reached state. The
deployed executor (current-content digest) refuses. -/
theorem cached_digest_breaks :
    let ops := [COp.submit 1 0 7 false, .audit 2 0 true, .amend 1 0 50, .fire 0]
    (runC R0 id cls0 true cinit ops).effects.map ERow.content = [50] ∧
    (runC R0 id cls0 true cinit ops).auditLog.map ARow.content = [7] ∧
    ¬ Good R0 id cls0 (α (runC R0 id cls0 true cinit ops)) ∧
    (runC R0 id cls0 false cinit ops).effects = [] := by
  refine ⟨by decide, by decide, fun hg => ?_, by decide⟩
  have hex : (α (runC R0 id cls0 true cinit [COp.submit 1 0 7 false, .audit 2 0 true, .amend 1 0 50, .fire 0])).executed
      = [⟨0, 50, 1, 1, 0⟩] := by decide
  have hver : (α (runC R0 id cls0 true cinit [COp.submit 1 0 7 false, .audit 2 0 true, .amend 1 0 50, .fire 0])).verdicts
      = [⟨0, 7, true, some 2⟩] := by decide
  obtain ⟨⟨v, hv, -, -, hd, -⟩, -⟩ := hg.1 ⟨0, 50, 1, 1, 0⟩ (by rw [hex]; simp)
  rw [hver] at hv
  have := List.mem_of_mem_take hv
  simp at this
  subst this
  simp at hd

/-- **Non-vacuity**: the deployed executor runs an audited operation (and an irreversible one after approval). -/
theorem honest_concrete :
    (runC R0 id cls0 false cinit [.submit 1 0 7 false, .audit 2 0 true, .fire 0, .submit 1 1 100 true, .audit 2 1 true,
      .approve 3 1, .crash, .restart, .fire 1]).effects.map ERow.content = [7, 100] := by
  decide

end ControlStack.SC25Refinement

#print axioms ControlStack.SC25Refinement.simulation
#print axioms ControlStack.SC25Refinement.simulation_run
#print axioms ControlStack.SC25Refinement.concrete_safe
#print axioms ControlStack.SC25Refinement.concrete_content_safe
#print axioms ControlStack.SC25Refinement.cached_digest_breaks
#print axioms ControlStack.SC25Refinement.honest_concrete
