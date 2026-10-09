/-
SC-16 refinement: the runtime's event structure (scenarios/SC-16/harness/registry.py, signer.py, admission.py;
prereg/SC16-DEPLOY-ADMISSION.md) as a concrete machine, with a forward simulation into `ControlStack.SC16`
(criterion 3, as for SC-26 and SC-25).

Concrete machine (`CSt`, `COp`, `stepC`):
- the registry's CAS, keyed by digest: `put` stores content under its digest; the FIRST stager of a digest is kept (a
  later put of the same digest changes nothing). Only agents stage here, as in the run;
- the registry's MUTABLE tag table (tag ↦ digest), writable by any client including the agent (`tagSet`);
- the REVIEWER's signed log: rows (digest, target, reviewer, content seen, its stager). The reviewer fetches by digest
  and refuses its own content. Its signature binds (digest, target);
- the APPROVER's signed log: rows (nonce, digest, target, tag, approver). The approver requires a review row for
  exactly (digest, target) and a fresh nonce;
- SIGNATURES are modelled as unforgeable bindings: a row exists in a signed log only if the key holder signed it, and
  the controller accepts exactly the rows in those logs. Ed25519 unforgeability and key custody
  (`signing_key_custody`) are the PREMISE, not proved here;
- the admission controller's `deploy c n t`: one atomic step (the controller is single-threaded). Not halted; the
  approval with nonce `n` exists (its signature verifies); `n` is unused; `t` is the approved target; a review exists
  for exactly (approved digest, approved target); the bytes are fetched BY DIGEST from the CAS and re-hashed to the
  approved digest. Then the deploy record is written and the nonce marked used;
- `halt`.
`stepC` takes a flag `byTag` (false in the runtime): if true, deploy resolves the approval's MUTABLE TAG at deploy time
and deploys whatever it points to, without the digest check (the runtime control `--by-tag`, H6a).

Results (deployed, `byTag = false`; adversary class TRACE_ARBITRARY over concrete operations, including arbitrary tag
moves):
- `simulation`: with α (CAS ↦ cas; review and approval logs ↦ reviews and approvals with the extra fields dropped;
  deploy log ↦ deployed; used nonces ↦ used; slots ↦ []), every concrete step is matched by 0 or 1 model steps:
  put ↦ [stage] when it stores; tagSet ↦ [] (the deployed admission never reads tags, and under `verify` the model
  never reads slots); review ↦ [review]; approve ↦ [approve] when accepted; deploy ↦ [deploy … x] with x the fetched
  content when accepted; halt ↦ [halt]; refused steps ↦ [];
- `concrete_safe`, `concrete_reviewed_content` (under `Set.InjOn h`), `concrete_safe_disjoint`: `SC16.sc16_safe`,
  `SC16.sc16_reviewed_content` and `SC16Disjoint.sc16_safe_disjoint` transfer to every reachable concrete state;
- `by_tag_breaks`: admission by tag deploys content no one reviewed after the agent re-points the tag, and
  `SC16.Good` fails; the deployed admission deploys the reviewed content.

Not covered: that the Python code implements this machine (TESTED by reconcile.py), the signature scheme itself,
key custody, a real OCI registry or webhook, review quality. Classical forward simulation; no novelty.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC16Deploy
import ControlStack.Scenarios.SC16Disjoint

namespace ControlStack.SC16Refinement

open ControlStack.SC16

/-- a signed review row: digest, target, reviewer, content seen, its stager -/
structure RRow where
  d : ℕ
  target : ℕ
  reviewer : ℕ
  content : ℕ
  stager : ℕ
deriving DecidableEq, Repr

/-- a signed approval row: nonce, digest, target, tag, approver -/
structure ARow where
  n : ℕ
  d : ℕ
  target : ℕ
  tag : ℕ
  approver : ℕ
deriving DecidableEq, Repr

/-- a deploy record: nonce, target, content deployed, approved digest -/
structure DRow where
  n : ℕ
  target : ℕ
  content : ℕ
  d : ℕ
deriving DecidableEq, Repr

structure CSt where
  cas : List (ℕ × ℕ)
  /-- tag ↦ digest, newest first -/
  tags : List (ℕ × ℕ)
  revLog : List RRow
  apprLog : List ARow
  used : List ℕ
  depLog : List DRow
  halted : Bool
deriving DecidableEq, Repr

inductive COp where
  | put (caller content : ℕ)
  | tagSet (caller tag d : ℕ)
  | review (caller d target : ℕ)
  | approve (caller n d target tag : ℕ)
  | deploy (caller n target : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

def cinit : CSt := ⟨[], [], [], [], [], [], false⟩

def toRev (r : RRow) : Review := ⟨r.d, r.reviewer, r.content, r.stager⟩
def toAppr (a : ARow) : Appr := ⟨a.n, a.d, a.target, a.tag, a.approver⟩
def toDep (e : DRow) : Dep := ⟨e.n, e.target, e.content⟩

def α (s : CSt) : St :=
  ⟨s.cas, [], s.revLog.map toRev, s.apprLog.map toAppr, s.used, s.depLog.map toDep, s.halted⟩

def ccas (h : ℕ → ℕ) (s : CSt) (d : ℕ) : Option (ℕ × ℕ) := s.cas.find? (fun e => h e.1 = d)
def capprOf (s : CSt) (n : ℕ) : Option ARow := s.apprLog.find? (fun a => a.n = n)
def tagOf (s : CSt) (tag : ℕ) : Option ℕ := (s.tags.find? (fun e => e.1 = tag)).map Prod.snd

theorem casLookup_α (h : ℕ → ℕ) (s : CSt) (d : ℕ) : casLookup h (α s) d = ccas h s d := rfl

theorem apprOf_α (s : CSt) (n : ℕ) : apprOf (α s) n = (capprOf s n).map toAppr := by
  simp only [apprOf, capprOf, α, List.find?_map]; rfl

/-- the content admission fetches: by the approved digest (deployed), or via the mutable tag (`byTag`) -/
def fetch (h : ℕ → ℕ) (byTag : Bool) (s : CSt) (ap : ARow) : Option ℕ :=
  if byTag then (tagOf s ap.tag).bind (fun d => (ccas h s d).map Prod.fst) else (ccas h s ap.d).map Prod.fst

/-- the admission controller's decision: the approval and the content to deploy, if every check passes -/
def depRes (h : ℕ → ℕ) (byTag : Bool) (s : CSt) (n t : ℕ) : Option (ARow × ℕ) :=
  if s.halted then none
  else match capprOf s n with
    | none => none
    | some ap =>
      if n ∉ s.used ∧ t = ap.target ∧ (∃ r ∈ s.revLog, r.d = ap.d ∧ r.target = ap.target) then
        (fetch h byTag s ap).bind (fun x => if byTag ∨ h x = ap.d then some (ap, x) else none)
      else none

def putOk (R : Roles) (h : ℕ → ℕ) (s : CSt) (c x : ℕ) : Prop := s.halted = false ∧ c ∈ R.agents ∧ ccas h s (h x) = none

def apprOk (R : Roles) (s : CSt) (c n d t : ℕ) : Prop :=
  s.halted = false ∧ c ∈ R.approvers ∧ capprOf s n = none ∧ ∃ r ∈ s.revLog, r.d = d ∧ r.target = t

instance (R : Roles) (h : ℕ → ℕ) (s : CSt) (c x : ℕ) : Decidable (putOk R h s c x) := by unfold putOk; infer_instance
instance (R : Roles) (s : CSt) (c n d t : ℕ) : Decidable (apprOk R s c n d t) := by unfold apprOk; infer_instance

def stepC (R : Roles) (h : ℕ → ℕ) (byTag : Bool) (s : CSt) : COp → CSt
  | .put c x => if putOk R h s c x then { s with cas := s.cas ++ [(x, c)] } else s
  | .tagSet _ tag d => if s.halted then s else { s with tags := (tag, d) :: s.tags }
  | .review c d t =>
    if s.halted then s
    else match ccas h s d with
      | none => s
      | some e => if c ∈ R.reviewers ∧ c ≠ e.2 then { s with revLog := s.revLog ++ [⟨d, t, c, e.1, e.2⟩] } else s
  | .approve c n d t tag => if apprOk R s c n d t then { s with apprLog := s.apprLog ++ [⟨n, d, t, tag, c⟩] } else s
  | .deploy _ n t =>
    match depRes h byTag s n t with
    | none => s
    | some (ap, x) => { s with depLog := s.depLog ++ [⟨n, t, x, ap.d⟩], used := s.used ++ [n] }
  | .halt c => if c ∈ R.admins then { s with halted := true } else s

def runC (R : Roles) (h : ℕ → ℕ) (byTag : Bool) (s : CSt) (ops : List COp) : CSt := ops.foldl (stepC R h byTag) s

/-- the model operations matching one concrete step (deployed admission) -/
def opsOf (R : Roles) (h : ℕ → ℕ) (s : CSt) : COp → List Op
  | .put c x => if putOk R h s c x then [.stage c x] else []
  | .tagSet _ _ _ => []
  | .review c d _ => [.review c d]
  | .approve c n d t tag => if apprOk R s c n d t then [.approve c n d t tag] else []
  | .deploy c n t =>
    match depRes h false s n t with
    | none => []
    | some (_, x) => [.deploy c n t x]
  | .halt c => [.halt c]

/-! ## Forward simulation -/

theorem depRes_spec (h : ℕ → ℕ) (s : CSt) (n t : ℕ) (ap : ARow) (x : ℕ) (hd : depRes h false s n t = some (ap, x)) :
    s.halted = false ∧ capprOf s n = some ap ∧ n ∉ s.used ∧ t = ap.target ∧
      (∃ r ∈ s.revLog, r.d = ap.d ∧ r.target = ap.target) ∧ h x = ap.d := by
  unfold depRes at hd
  split_ifs at hd with hh
  split at hd
  · simp at hd
  · rename_i ap' hap
    split_ifs at hd with hc
    · simp only [fetch, Bool.false_eq_true, ite_false, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hd
      obtain ⟨y, ⟨e, he, rfl⟩, hy⟩ := hd
      split_ifs at hy with hx
      simp only [Option.some.injEq, Prod.mk.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      refine ⟨by simpa using hh, hap, hc.1, hc.2.1, hc.2.2, ?_⟩
      simpa using hx

theorem simulation (R : Roles) (h : ℕ → ℕ) (s : CSt) (o : COp) :
    α (stepC R h false s o) = run R h full (α s) (opsOf R h s o) := by
  have hh : (α s).halted = s.halted := rfl
  cases o with
  | put c x =>
    simp only [stepC, opsOf]
    by_cases hp : putOk R h s c x
    · rw [ite_eq_left hp, ite_eq_left hp]
      obtain ⟨hn, ha, _⟩ := hp
      simp only [run, List.foldl_cons, List.foldl_nil, step, hh, hn, full, Bool.false_eq_true, false_and, ite_false]
      rw [ite_eq_left ha]
      rfl
    · rw [ite_eq_right hp, ite_eq_right hp]; rfl
  | tagSet c tag d =>
    simp only [stepC, opsOf]
    split_ifs <;> rfl
  | review c d t =>
    simp only [stepC, opsOf, run, List.foldl_cons, List.foldl_nil, step, hh, full, and_true, casLookup_α]
    by_cases hhs : s.halted = true
    · simp [hhs]
    · simp only [hhs, ite_false, Bool.false_eq_true]
      cases hc : ccas h s d with
      | none => rfl
      | some e =>
        dsimp only
        split_ifs <;> simp_all [α, toRev]
  | approve c n d t tag =>
    simp only [stepC, opsOf]
    by_cases hp : apprOk R s c n d t
    · rw [ite_eq_left hp, ite_eq_left hp]
      obtain ⟨hn, ha, _⟩ := hp
      simp only [run, List.foldl_cons, List.foldl_nil, step, hh, hn, full, Bool.false_eq_true, ite_false, true_or,
        and_true]
      rw [ite_eq_left ha]
      simp [α, toAppr]
    · rw [ite_eq_right hp, ite_eq_right hp]; rfl
  | deploy c n t =>
    simp only [stepC, opsOf]
    cases hd : depRes h false s n t with
    | none => rfl
    | some apx =>
      obtain ⟨ap, x⟩ := apx
      dsimp only
      obtain ⟨hn, hap, hu, ht, hrv, hx⟩ := depRes_spec h s n t ap x hd
      simp only [run, List.foldl_cons, List.foldl_nil, step, hh, hn, full, Bool.false_eq_true, false_and, ite_false,
        apprOf_α, hap, Option.map_some]
      have hrv' : ∃ rv ∈ (α s).reviews, rv.d = (toAppr ap).d := by
        obtain ⟨r, hr, h1, _⟩ := hrv
        exact ⟨toRev r, List.mem_map.2 ⟨r, hr, rfl⟩, h1⟩
      rw [ite_eq_left ⟨hrv', fun _ => hu, fun _ => ht⟩, ite_eq_left ⟨⟩, ite_eq_left (show h x = (toAppr ap).d from hx)]
      simp [α, doDeploy, toDep, hn]
  | halt c =>
    simp only [stepC, opsOf, run, List.foldl_cons, List.foldl_nil, step]
    split_ifs <;> rfl

def absTrace (R : Roles) (h : ℕ → ℕ) : CSt → List COp → List Op
  | _, [] => []
  | s, o :: ops => opsOf R h s o ++ absTrace R h (stepC R h false s o) ops

theorem simulation_run (R : Roles) (h : ℕ → ℕ) (s : CSt) (ops : List COp) :
    α (runC R h false s ops) = run R h full (α s) (absTrace R h s ops) := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    change α (runC R h false (stepC R h false s o) ops) = _
    rw [ih, simulation]
    simp [absTrace, run, List.foldl_append]

theorem α_cinit : α cinit = init := rfl

/-! ## Transfer -/

/-- **SC-16 safety for the concrete admission path.** For every concrete trace (any puts, tag moves, signed reviews
and approvals, deploy requests, halts), α of the reached state satisfies `SC16.Good`. -/
theorem concrete_safe (R : Roles) (h : ℕ → ℕ) (ops : List COp) : Good R h (α (runC R h false cinit ops)) := by
  rw [simulation_run, α_cinit]
  exact sc16_safe R h _

/-- **Deployed content is reviewed content**, for the concrete path, under injectivity on the contents in play. -/
theorem concrete_reviewed_content (R : Roles) (h : ℕ → ℕ) (ops : List COp)
    (hinj : Set.InjOn h {c | (∃ e ∈ (α (runC R h false cinit ops)).deployed, e.content = c) ∨
      ∃ rv ∈ (α (runC R h false cinit ops)).reviews, rv.content = c}) :
    ∀ e ∈ (α (runC R h false cinit ops)).deployed, ∃ rv ∈ (α (runC R h false cinit ops)).reviews,
      rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager := by
  rw [simulation_run, α_cinit] at hinj ⊢
  exact sc16_reviewed_content R h _ hinj

/-- **Disjoint roles**, for the concrete path: every deployed content was reviewed by a non-agent reviewer and deployed
under an approval by a non-agent approver for exactly its target. -/
theorem concrete_safe_disjoint (R : Roles) (h : ℕ → ℕ) (ops : List COp)
    (hrev : ∀ a ∈ R.reviewers, a ∉ R.agents) (happ : ∀ a ∈ R.approvers, a ∉ R.agents)
    (hinj : Set.InjOn h {c | (∃ e ∈ (α (runC R h false cinit ops)).deployed, e.content = c) ∨
      ∃ rv ∈ (α (runC R h false cinit ops)).reviews, rv.content = c}) :
    ∀ e ∈ (α (runC R h false cinit ops)).deployed,
      (∃ rv ∈ (α (runC R h false cinit ops)).reviews, rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧
        rv.reviewer ∉ R.agents ∧ rv.reviewer ≠ rv.stager) ∧
      (∃ ap ∈ (α (runC R h false cinit ops)).approvals, ap.n = e.n ∧ ap.target = e.target ∧ ap.approver ∈ R.approvers ∧
        ap.approver ∉ R.agents) := by
  rw [simulation_run, α_cinit] at hinj ⊢
  exact SC16Disjoint.sc16_safe_disjoint R h _ hrev happ hinj

/-! ## Witness: admission by tag -/

/-- the attack: stage 7 and tag it, get 7 reviewed and approved (approval names tag 0), stage 666 and re-point tag 0
to it, then request the deploy -/
def tagTrace : List COp :=
  [.put 1 7, .tagSet 1 0 7, .review 2 7 5, .approve 3 9 7 5 0, .put 1 666, .tagSet 1 0 666, .deploy 1 9 5]

/-- **Admission by tag breaks the transferred property** (runtime control H6a): it deploys 666, which no one reviewed,
and `SC16.Good` fails; the deployed admission (fetch by digest) deploys the reviewed 7. -/
theorem by_tag_breaks :
    (runC R0 id true cinit tagTrace).depLog.map DRow.content = [666] ∧
    ¬ Good R0 id (α (runC R0 id true cinit tagTrace)) ∧
    (runC R0 id false cinit tagTrace).depLog.map DRow.content = [7] := by
  refine ⟨by decide, fun hg => ?_, by decide⟩
  have hdep : (α (runC R0 id true cinit tagTrace)).deployed = [⟨9, 5, 666⟩] := by decide
  have happ : (α (runC R0 id true cinit tagTrace)).approvals = [⟨9, 7, 5, 0, 3⟩] := by decide
  obtain ⟨ap, hap, -, -, -, hx, -⟩ := hg.1 ⟨9, 5, 666⟩ (by rw [hdep]; simp)
  rw [happ] at hap
  simp at hap
  subst hap
  simp at hx

end ControlStack.SC16Refinement

#print axioms ControlStack.SC16Refinement.simulation
#print axioms ControlStack.SC16Refinement.simulation_run
#print axioms ControlStack.SC16Refinement.concrete_safe
#print axioms ControlStack.SC16Refinement.concrete_reviewed_content
#print axioms ControlStack.SC16Refinement.concrete_safe_disjoint
#print axioms ControlStack.SC16Refinement.by_tag_breaks
