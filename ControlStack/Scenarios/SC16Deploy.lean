/-
SC-16: no code or config ships before trusted evaluation and approval.

One JOINT shared-state transition system for the families the scenario needs (pattern of `SC26Transaction.lean`):
- F4: content-addressed artefacts. An agent stages content into an append-only store; a reviewer reviews a DIGEST and
  the model records exactly the content the reviewer saw (the store's first entry with that digest);
- F7: a one-use approval binds (nonce, digest, target environment) and comes from an approver;
- F1: the only effect is the gate's `deploy`, which deploys content supplied at deploy time (e.g. pulled from a
  registry the agent can push to) only if it hashes to the approved digest, to the approved target, once;
- F3: an absorbing HALT issued by an admin freezes every operation.

The adversary chooses ANY finite sequence of operations with arbitrary caller identities and arbitrary content,
including overwriting mutable staging slots and supplying colliding content at deploy time.

Main results:
- `sc16_safe`: from `init`, after any trace, every deployment consumed a distinct approval for exactly its target, its
  content hashes to the approved digest, and that digest was reviewed by a reviewer who is not the content's stager;
- `sc16_reviewed_content`: if the hash is injective on the contents that appear in the run (`Set.InjOn`, the premise
  of `GateClients.Artifact.deployed_is_reviewed`), every deployed content IS reviewed content;
- `halt_freezes`: after a halt, no trace changes the deployment log;
- `sys`/`spec`: a client of the shared gate interface (`Core/Gate.lean`).

Necessity witnesses: `toctou_slot_breaks` (verify the hash at approval time, deploy from a mutable slot),
`collision_breaks` (the injectivity premise cannot be dropped), `no_target_binding_breaks`,
`self_review_without_distinct_check`, `no_nonce_redeploys`, `no_halt_check_breaks`. Non-vacuity:
`honest_trace_deploys`.

Adversary class (ADVERSARY-CLASSES.md): TRACE_ARBITRARY over this transition system.
Premises outside the model: role credentials are held by the right principals (an approver op is a real approver's
decision), the deploy path is the only route to the target, the hash is collision-resistant on the contents in play.
Not claimed: that reviewed content is harmless, that review was competent, or that the runtime matches this model.
No new mathematics: each theorem is an induction over the trace.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC16

open ControlStack.Gate

structure Roles where
  agents : List ℕ
  reviewers : List ℕ
  approvers : List ℕ
  admins : List ℕ

/-- a review of digest `d` by `reviewer`, who saw `content`, staged by `stager` -/
structure Review where
  d : ℕ
  reviewer : ℕ
  content : ℕ
  stager : ℕ
deriving DecidableEq, Repr

/-- a one-use approval: nonce, digest, target environment, the staging slot it names, approver -/
structure Appr where
  n : ℕ
  d : ℕ
  target : ℕ
  slot : ℕ
  approver : ℕ
deriving DecidableEq, Repr

/-- a deployment: the approval nonce consumed, the target, the content deployed -/
structure Dep where
  n : ℕ
  target : ℕ
  content : ℕ
deriving DecidableEq, Repr

structure St where
  /-- append-only content store: (content, stager) -/
  cas : List (ℕ × ℕ)
  /-- mutable staging slots, newest write first: (slot, content) -/
  slots : List (ℕ × ℕ)
  reviews : List Review
  approvals : List Appr
  used : List ℕ
  deployed : List Dep
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | stage (caller content : ℕ)
  | writeSlot (caller slot content : ℕ)
  | review (caller d : ℕ)
  | approve (caller n d target slot : ℕ)
  /-- deploy approval `n` to `target` with `content` supplied at deploy time -/
  | deploy (caller n target content : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

/-- implementation checks; `full` is the deployed configuration. `verify = false` is the TOCTOU design: the hash is
checked on the named slot at approval time and the slot is re-read at deploy time without a check. -/
structure Checks where
  distinct : Bool
  target : Bool
  nonce : Bool
  verify : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true, true⟩

def init : St := ⟨[], [], [], [], [], [], false⟩

def casLookup (h : ℕ → ℕ) (s : St) (d : ℕ) : Option (ℕ × ℕ) := s.cas.find? (fun e => h e.1 = d)

def slotContent (s : St) (slot : ℕ) : Option ℕ := (s.slots.find? (fun e => e.1 = slot)).map Prod.snd

def apprOf (s : St) (n : ℕ) : Option Appr := s.approvals.find? (fun a => a.n = n)

def doDeploy (s : St) (n t x : ℕ) : St := { s with deployed := s.deployed ++ [⟨n, t, x⟩], used := s.used ++ [n] }

def step (R : Roles) (h : ℕ → ℕ) (C : Checks) (s : St) : Op → St
  | .stage c x =>
    if s.halted ∧ C.haltCheck then s else if c ∈ R.agents then { s with cas := s.cas ++ [(x, c)] } else s
  | .writeSlot c slot x =>
    if s.halted ∧ C.haltCheck then s else if c ∈ R.agents then { s with slots := (slot, x) :: s.slots } else s
  | .review c d =>
    if s.halted ∧ C.haltCheck then s
    else match casLookup h s d with
      | none => s
      | some e =>
        if c ∈ R.reviewers ∧ (C.distinct → c ≠ e.2) then { s with reviews := s.reviews ++ [⟨d, c, e.1, e.2⟩] }
        else s
  | .approve c n d t slot =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ R.approvers ∧ (C.verify ∨ (slotContent s slot).map h = some d) then
      { s with approvals := s.approvals ++ [⟨n, d, t, slot, c⟩] }
    else s
  | .deploy _ n t x =>
    if s.halted ∧ C.haltCheck then s
    else match apprOf s n with
      | none => s
      | some ap =>
        if (∃ rv ∈ s.reviews, rv.d = ap.d) ∧ (C.nonce → n ∉ s.used) ∧ (C.target → t = ap.target) then
          if C.verify then (if h x = ap.d then doDeploy s n t x else s)
          else match slotContent s ap.slot with
            | none => s
            | some y => doDeploy s n t y
        else s
  | .halt c => if c ∈ R.admins then { s with halted := true } else s

def run (R : Roles) (h : ℕ → ℕ) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step R h C) s

theorem run_cons (R : Roles) (h : ℕ → ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run R h C s (o :: ops) = run R h C (step R h C s o) ops := rfl

/-! ## Invariant and safety -/

/-- a review that recorded what the reviewer actually saw, by a reviewer who did not stage it -/
def ReviewOk (R : Roles) (h : ℕ → ℕ) (rv : Review) : Prop :=
  h rv.content = rv.d ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager

/-- a deployment backed by an approval for exactly its target and digest, whose digest was reviewed -/
def DepOk (R : Roles) (h : ℕ → ℕ) (s : St) (e : Dep) : Prop :=
  ∃ ap ∈ s.approvals, ap.n = e.n ∧ ap.target = e.target ∧ ap.approver ∈ R.approvers ∧ h e.content = ap.d ∧
    ∃ rv ∈ s.reviews, rv.d = ap.d ∧ ReviewOk R h rv

structure Inv (R : Roles) (h : ℕ → ℕ) (s : St) : Prop where
  rev_ok : ∀ rv ∈ s.reviews, ReviewOk R h rv
  appr_ok : ∀ ap ∈ s.approvals, ap.approver ∈ R.approvers
  dep_ok : ∀ e ∈ s.deployed, e.n ∈ s.used ∧
    ∃ ap ∈ s.approvals, ap.n = e.n ∧ ap.target = e.target ∧ h e.content = ap.d ∧ ∃ rv ∈ s.reviews, rv.d = ap.d
  dep_nodup : (s.deployed.map Dep.n).Nodup

def Good (R : Roles) (h : ℕ → ℕ) (s : St) : Prop :=
  (∀ e ∈ s.deployed, DepOk R h s e) ∧ (s.deployed.map Dep.n).Nodup

theorem inv_init (R : Roles) (h : ℕ → ℕ) : Inv R h init := ⟨by simp [init], by simp [init], by simp [init], by simp [init]⟩

theorem Inv.good {R : Roles} {h : ℕ → ℕ} {s : St} (hi : Inv R h s) : Good R h s := by
  refine ⟨fun e he => ?_, hi.dep_nodup⟩
  obtain ⟨_, ap, hap, h1, h2, h3, rv, hrv, h4⟩ := hi.dep_ok e he
  exact ⟨ap, hap, h1, h2, hi.appr_ok ap hap, h3, rv, hrv, h4, hi.rev_ok rv hrv⟩

theorem apprOf_mem {s : St} {n : ℕ} {ap : Appr} (h : apprOf s n = some ap) : ap ∈ s.approvals ∧ ap.n = n := by
  have := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using this⟩

/-- a step that only extends reviews/approvals/store/slots (validly) keeps the invariant -/
theorem inv_of_mono {R : Roles} {h : ℕ → ℕ} {s t : St} (hi : Inv R h s) (hrev : s.reviews ⊆ t.reviews)
    (happ : s.approvals ⊆ t.approvals) (hrevn : ∀ rv ∈ t.reviews, rv ∉ s.reviews → ReviewOk R h rv)
    (happn : ∀ ap ∈ t.approvals, ap ∉ s.approvals → ap.approver ∈ R.approvers) (hdep : t.deployed = s.deployed)
    (hused : t.used = s.used) : Inv R h t := by
  refine ⟨fun rv hrv => ?_, fun ap hap => ?_, fun e he => ?_, hdep ▸ hi.dep_nodup⟩
  · by_cases hs : rv ∈ s.reviews
    · exact hi.rev_ok rv hs
    · exact hrevn rv hrv hs
  · by_cases hs : ap ∈ s.approvals
    · exact hi.appr_ok ap hs
    · exact happn ap hap hs
  · rw [hdep] at he
    obtain ⟨hu, ap, hap, h1, h2, h3, rv, hrv, h4⟩ := hi.dep_ok e he
    exact ⟨hused ▸ hu, ap, happ hap, h1, h2, h3, rv, hrev hrv, h4⟩

theorem doDeploy_inv {R : Roles} {h : ℕ → ℕ} {s : St} (hi : Inv R h s) (n t x : ℕ) (ap : Appr)
    (hap : apprOf s n = some ap) (hrv : ∃ rv ∈ s.reviews, rv.d = ap.d) (hn : n ∉ s.used) (ht : t = ap.target)
    (hx : h x = ap.d) : Inv R h (doDeploy s n t x) := by
  obtain ⟨hmem, hapn⟩ := apprOf_mem hap
  refine ⟨hi.rev_ok, hi.appr_ok, fun e he => ?_, ?_⟩
  · simp only [doDeploy] at he ⊢
    rcases List.mem_append.1 he with he | he
    · obtain ⟨hu, h1⟩ := hi.dep_ok e he
      exact ⟨List.mem_append_left _ hu, h1⟩
    · simp at he
      subst he
      exact ⟨by simp, ap, hmem, hapn, ht.symm, hx, hrv⟩
  · simp only [doDeploy, List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.2 ⟨hi.dep_nodup, List.nodup_singleton _, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb
    subst hb
    rintro rfl
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
    exact hn (hi.dep_ok e he).1

theorem step_inv (R : Roles) (h : ℕ → ℕ) (s : St) (o : Op) (hi : Inv R h s) : Inv R h (step R h full s o) := by
  cases o with
  | stage c x =>
    simp only [step]
    split_ifs
    · exact hi
    · exact inv_of_mono hi (fun _ h => h) (fun _ h => h) (fun _ h hn => absurd h hn) (fun _ h hn => absurd h hn)
        rfl rfl
    · exact hi
  | writeSlot c slot x =>
    simp only [step]
    split_ifs
    · exact hi
    · exact inv_of_mono hi (fun _ h => h) (fun _ h => h) (fun _ h hn => absurd h hn) (fun _ h hn => absurd h hn)
        rfl rfl
    · exact hi
  | review c d =>
    simp only [step]
    split_ifs
    · exact hi
    · split
      · exact hi
      · rename_i e he
        split_ifs with hc
        · obtain ⟨hc1, hc2⟩ := hc
          simp only [full, forall_const] at hc2
          refine inv_of_mono hi (fun _ hx => List.mem_append_left _ hx) (fun _ h => h) ?_
            (fun _ h hn => absurd h hn) rfl rfl
          intro rv hrv hn
          rcases List.mem_append.1 hrv with hrv | hrv
          · exact absurd hrv hn
          · simp at hrv
            subst hrv
            have := List.find?_some he
            simp only [decide_eq_true_eq] at this
            exact ⟨this, hc1, hc2⟩
        · exact hi
  | approve c n d t slot =>
    simp only [step]
    split_ifs with h1 h2
    · exact hi
    · refine inv_of_mono hi (fun _ h => h) (fun _ hx => List.mem_append_left _ hx) (fun _ h hn => absurd h hn) ?_
        rfl rfl
      intro ap hap hn
      rcases List.mem_append.1 hap with hap | hap
      · exact absurd hap hn
      · simp at hap; subst hap; exact h2.1
    · exact hi
  | deploy c n t x =>
    simp only [step, show full.verify = true from rfl, show full.haltCheck = true from rfl,
      show full.nonce = true from rfl, show full.target = true from rfl, and_true, forall_const, ite_true]
    split_ifs
    · exact hi
    · split
      · exact hi
      · rename_i ap hap
        split_ifs with h2 h3
        · obtain ⟨hrv, hn, ht⟩ := h2
          exact doDeploy_inv hi n t x ap hap hrv hn ht h3
        · exact hi
        · exact hi
  | halt c =>
    simp only [step]
    split_ifs
    · exact inv_of_mono hi (fun _ h => h) (fun _ h => h) (fun _ h hn => absurd h hn) (fun _ h hn => absurd h hn)
        rfl rfl
    · exact hi

theorem run_inv (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op) (hi : Inv R h s) : Inv R h (run R h full s ops) := by
  induction ops generalizing s with
  | nil => exact hi
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv R h s o hi)

/-- **SC-16 safety.** After any trace from `init`, every deployment consumed a distinct approval for exactly its
target, its content hashes to the approved digest, and that digest was reviewed (the review recorded the content the
reviewer saw) by a reviewer who is not that content's stager. Adversary: TRACE_ARBITRARY. -/
theorem sc16_safe (R : Roles) (h : ℕ → ℕ) (ops : List Op) : Good R h (run R h full init ops) :=
  (run_inv R h init ops (inv_init R h)).good

/-- **Deployed content is reviewed content**, if the hash is injective on the contents that appear in the run
(deployed or reviewed). Global injectivity is not assumed. -/
theorem sc16_reviewed_content (R : Roles) (h : ℕ → ℕ) (ops : List Op)
    (hinj : Set.InjOn h {c | (∃ e ∈ (run R h full init ops).deployed, e.content = c) ∨
                             ∃ rv ∈ (run R h full init ops).reviews, rv.content = c}) :
    ∀ e ∈ (run R h full init ops).deployed, ∃ rv ∈ (run R h full init ops).reviews,
      rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager := by
  intro e he
  obtain ⟨ap, _, _, _, _, hx, rv, hrv, hd, hok⟩ := (sc16_safe R h ops).1 e he
  refine ⟨rv, hrv, hinj (Or.inr ⟨rv, hrv, rfl⟩) (Or.inl ⟨e, he, rfl⟩) (by rw [hok.1, hd, hx]), hok.2⟩

/-! ## Absorbing halt -/

theorem step_halted (R : Roles) (h : ℕ → ℕ) (s : St) (o : Op) (hh : s.halted = true) :
    step R h full s o = s := by
  cases o with
  | halt c =>
    simp only [step]
    split_ifs
    · cases s; simp_all
    · rfl
  | _ => simp [step, full, hh]

/-- **Halt freezes deployments**: once halted, no trace changes the state (in particular the deployment log). -/
theorem halt_freezes (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op) (hh : s.halted = true) :
    run R h full s ops = s := by
  induction ops with
  | nil => rfl
  | cons o ops ih => rw [run_cons, step_halted R h s o hh, ih]

/-! ## Client of the shared gate interface -/

theorem deployed_prefix (R : Roles) (h : ℕ → ℕ) (C : Checks) (s : St) (o : Op) :
    s.deployed <+: (step R h C s o).deployed := by
  cases o with
  | deploy c n t x =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | review c d =>
    simp only [step]
    split_ifs
    · exact List.prefix_refl _
    · split
      · exact List.prefix_refl _
      · split_ifs <;> exact List.prefix_refl _
  | _ => simp only [step]; split_ifs <;> exact List.prefix_refl _

def sys (R : Roles) (h : ℕ → ℕ) : System St Op Dep where
  step := step R h full
  effects := St.deployed

def spec (R : Roles) (h : ℕ → ℕ) : Spec (sys R h) where
  Inv := Inv R h
  ok := DepOk R h
  step_inv := fun s o hi => step_inv R h s o hi
  log_prefix := fun s o => deployed_prefix R h full s o
  inv_ok := fun _ hi e he => hi.good.1 e he

/-! ## Non-vacuity and necessity witnesses

Roles: agent 1, reviewer 2, approver 3, admin 4. Content 7 is the reviewed artefact; target 5. -/

def R0 : Roles := ⟨[1], [2], [3], [4]⟩

/-- **Non-vacuity**: the honest path deploys the reviewed content to the approved target. -/
theorem honest_trace_deploys :
    (run R0 id full init [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]).deployed = [⟨0, 5, 7⟩] := by
  decide

/-- TOCTOU: checking the hash of a mutable slot at approval time and re-reading the slot at deploy time deploys
content that nobody reviewed -/
theorem toctou_slot_breaks :
    let s := run R0 id { full with verify := false } init
      [.stage 1 7, .writeSlot 1 0 7, .review 2 7, .approve 3 0 7 5 0, .writeSlot 1 0 666, .deploy 1 0 5 0]
    s.deployed = [⟨0, 5, 666⟩] ∧ s.reviews.map Review.content = [7] := by
  decide

/-- with verification at deploy time (deployed configuration), the same attack deploys nothing -/
theorem verify_blocks_toctou :
    (run R0 id full init
      [.stage 1 7, .writeSlot 1 0 7, .review 2 7, .approve 3 0 7 5 0, .writeSlot 1 0 666, .deploy 1 0 5 666]).deployed
      = [] := by
  decide

/-- a hash collision on contents in play deploys unreviewed content, even with every check on: the injectivity premise
of `sc16_reviewed_content` cannot be dropped -/
theorem collision_breaks :
    let s := run R0 (· % 10) full init [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 17]
    s.deployed = [⟨0, 5, 17⟩] ∧ s.reviews.map Review.content = [7] := by
  decide

/-- without target binding, an approval for target 5 deploys to target 6 -/
theorem no_target_binding_breaks :
    let s := run R0 id { full with target := false } init
      [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 6 7]
    s.deployed = [⟨0, 6, 7⟩] ∧ s.approvals.map Appr.target = [5] := by
  decide

def R1 : Roles := ⟨[1], [1, 2], [3], [4]⟩

/-- if a stager is also a reviewer and the distinctness check is off, it reviews its own content, which deploys -/
theorem self_review_without_distinct_check :
    let s := run R1 id { full with distinct := false } init
      [.stage 1 7, .review 1 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]
    s.deployed = [⟨0, 5, 7⟩] ∧ s.reviews = [⟨7, 1, 7, 1⟩] := by
  decide

/-- with the distinctness check, the self-review is refused and nothing deploys -/
theorem distinct_blocks_self_review :
    (run R1 id full init [.stage 1 7, .review 1 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]).deployed = [] := by
  decide

/-- without the nonce check, one approval deploys twice -/
theorem no_nonce_redeploys :
    (run R0 id { full with nonce := false } init
      [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 7, .deploy 1 0 5 7]).deployed =
      [⟨0, 5, 7⟩, ⟨0, 5, 7⟩] := by
  decide

/-- without the halt check, an approved deployment still happens after the halt -/
theorem no_halt_check_breaks :
    (run R0 id { full with haltCheck := false } init
      [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .halt 4, .deploy 1 0 5 7]).deployed = [⟨0, 5, 7⟩] ∧
    (run R0 id full init [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .halt 4, .deploy 1 0 5 7]).deployed = [] := by
  decide

end ControlStack.SC16

#print axioms ControlStack.SC16.sc16_safe
#print axioms ControlStack.SC16.sc16_reviewed_content
#print axioms ControlStack.SC16.halt_freezes
#print axioms ControlStack.SC16.spec
#print axioms ControlStack.SC16.honest_trace_deploys
#print axioms ControlStack.SC16.toctou_slot_breaks
#print axioms ControlStack.SC16.verify_blocks_toctou
#print axioms ControlStack.SC16.collision_breaks
#print axioms ControlStack.SC16.no_target_binding_breaks
#print axioms ControlStack.SC16.self_review_without_distinct_check
#print axioms ControlStack.SC16.distinct_blocks_self_review
#print axioms ControlStack.SC16.no_nonce_redeploys
#print axioms ControlStack.SC16.no_halt_check_breaks
