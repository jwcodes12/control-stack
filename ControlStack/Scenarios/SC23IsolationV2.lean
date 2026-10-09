/-
SC-23 planner isolation, version 2 (review: Gemini on `SC23Isolation.lean`).

The first version's planner was blind: `derive` saw only the user inputs and a counter. Here the planner READS ITS OWN
STATE through a view: a list of planner values, each a `trusted v` (the content) or a `handle i` (the handle ID, an
opaque reference, not its content). The planner program `plan` is arbitrary over (user inputs, view, step index).
Isolation means the view exposes handle IDS only. Handle numbering is by arrival order, never by content, so
noninterference still holds. In the leaky design (`opaqueView = false`) the view resolves handles to their contents,
and laundering returns.

Second change: identity-bearing operations (`userInput`, `confirm`, `halt`) are wrapped with
`Core/Authenticated.lean`. Every operation carries its true issuer, and a claim is applied only if it equals the
issuer. So a confirmation forged by an untrusted issuer has no effect, and "the user channel is authenticated" is the
single premise "the platform-reported identity is the issuer".

Results (deployed configuration `full`; adversary class TRACE_ARBITRARY; `plan`, `qf` universally quantified):
- `noninterference`, `noninterference_authed`: traces (issued traces) that differ only in tool-result contents give
  the same planner state, user inputs, quarantine size and halt status, even though the planner reads its state;
- `w1_impossible_v2`: the W1 laundering trace executes the same with any tool-result content;
  `honest_planner_reads_state`: the planner really computes over its own trusted state (non-vacuity of the view);
- `sc23v2_safe_authenticated`: every executed sensitive action with a quarantined argument is backed by a
  `confirm` of exactly its tool and resolved values, ISSUED BY a user. If the untrusted issuers `U` are disjoint from
  the users, that issuer is not in `U`;
- witnesses: `leaky_view_launders` (a view exposing handle contents launders injected content into an unconfirmed
  sensitive action); `forged_confirmation_without_auth` (an untrusted issuer's confirmation claiming user 1 lets the
  tainted action run without authentication, and is a no-op with it).

Premises: the platform-reported issuer is the true issuer; no side channel from quarantined processing into the
planner (shared context windows, logs, error messages). Semantic and unformalised: the quality of `plan`'s choices and
whether a user's confirmation is informed. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate
import ControlStack.Core.Authenticated

namespace ControlStack.SC23IsolationV2

open ControlStack.Gate ControlStack.Authenticated

inductive PVal where
  | trusted (v : ℕ)
  | handle (i : ℕ)
deriving DecidableEq, Repr

def PVal.isHandle : PVal → Bool
  | .trusted _ => false
  | .handle _ => true

structure Env where
  users : List ℕ
  admins : List ℕ
  sensitive : List ℕ
  /-- the planner's program: user inputs, its view of its own state, step index ↦ derived value -/
  plan : List ℕ → List PVal → ℕ → ℕ
  qf : ℕ → ℕ

structure Conf where
  n : ℕ
  tool : ℕ
  vals : List ℕ
  by_ : ℕ
deriving DecidableEq, Repr

structure Act where
  tool : ℕ
  vals : List ℕ
  tainted : Bool
  conf : Option ℕ
deriving DecidableEq, Repr

structure St where
  user : List ℕ
  quarantine : List ℕ
  pvals : List PVal
  confs : List Conf
  executed : List Act
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | userInput (caller v : ℕ)
  | toolResult (v : ℕ)
  | qtransform (i : ℕ)
  | derive
  | confirm (caller n tool : ℕ) (vals : List ℕ)
  | act (tool : ℕ) (idxs : List ℕ) (n : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  opaqueView : Bool
  taintCheck : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true⟩

def init : St := ⟨[], [], [], [], [], false⟩

def resolve (s : St) : PVal → Option ℕ
  | .trusted v => some v
  | .handle i => s.quarantine[i]?

/-- the leaky reveal: a handle shown as its content -/
def reveal (s : St) : PVal → PVal
  | .trusted v => .trusted v
  | .handle i => match s.quarantine[i]? with
    | some v => .trusted v
    | none => .handle i

/-- what the planner sees of its own state -/
def view (C : Checks) (s : St) : List PVal := if C.opaqueView then s.pvals else s.pvals.map (reveal s)

def argP (s : St) (idxs : List ℕ) : List PVal := idxs.filterMap (fun i => s.pvals[i]?)

def argV (s : St) (idxs : List ℕ) : List ℕ := (argP s idxs).filterMap (resolve s)

def confOf (s : St) (n : ℕ) : Option Conf := s.confs.find? (fun c => c.n = n)

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .userInput c v =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ E.users then { s with user := s.user ++ [v], pvals := s.pvals ++ [.trusted v] } else s
  | .toolResult v =>
    if s.halted ∧ C.haltCheck then s
    else { s with quarantine := s.quarantine ++ [v], pvals := s.pvals ++ [.handle s.quarantine.length] }
  | .qtransform i =>
    if s.halted ∧ C.haltCheck then s
    else match s.quarantine[i]? with
      | none => s
      | some v =>
        { s with quarantine := s.quarantine ++ [E.qf v], pvals := s.pvals ++ [.handle s.quarantine.length] }
  | .derive =>
    if s.halted ∧ C.haltCheck then s
    else { s with pvals := s.pvals ++ [.trusted (E.plan s.user (view C s) s.pvals.length)] }
  | .confirm c n tool vals =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ E.users ∧ confOf s n = none then { s with confs := s.confs ++ [⟨n, tool, vals, c⟩] } else s
  | .act tool idxs n =>
    if s.halted ∧ C.haltCheck then s
    else if (argP s idxs).length ≠ idxs.length ∨ (argV s idxs).length ≠ idxs.length then s
    else if tool ∉ E.sensitive ∨ (C.taintCheck = true → (argP s idxs).any PVal.isHandle = false) then
      { s with executed := s.executed ++ [⟨tool, argV s idxs, (argP s idxs).any PVal.isHandle, none⟩] }
    else match confOf s n with
      | none => s
      | some cf =>
        if cf.tool = tool ∧ cf.vals = argV s idxs then
          { s with executed := s.executed ++ [⟨tool, argV s idxs, (argP s idxs).any PVal.isHandle, some n⟩] }
        else s
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run E C s (o :: ops) = run E C (step E C s o) ops := rfl

/-- the gate as a raw `Gate.System` (deployed checks) -/
def raw (E : Env) : System St Op Act := ⟨step E full, St.executed⟩

theorem raw_run (E : Env) (s : St) (ops : List Op) : (raw E).run s ops = run E full s ops := rfl

/-- the identity each operation claims -/
def claim : Op → Option ℕ
  | .userInput c _ => some c
  | .confirm c _ _ _ => some c
  | .halt c => some c
  | _ => none

/-! ## Noninterference with a state-reading planner -/

def SameExceptContent (o o' : Op) : Prop := o = o' ∨ ∃ v v', o = .toolResult v ∧ o' = .toolResult v'

structure Rel (s t : St) : Prop where
  user : s.user = t.user
  pvals : s.pvals = t.pvals
  qlen : s.quarantine.length = t.quarantine.length
  halted : s.halted = t.halted

theorem view_full (s : St) : view full s = s.pvals := by simp [view, full]

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem step_rel_same (E : Env) (s t : St) (o : Op) (h : Rel s t) : Rel (step E full s o) (step E full t o) := by
  obtain ⟨hu, hp, hq, hh⟩ := h
  cases o with
  | userInput c v =>
    simp only [step, hh]
    split_ifs
    · exact ⟨hu, hp, hq, hh⟩
    · exact ⟨by simp [hu], by simp [hp], hq, by first | rfl | exact hh⟩
    · exact ⟨hu, hp, hq, hh⟩
  | toolResult v =>
    simp only [step, hh]
    split_ifs
    · exact ⟨hu, hp, hq, hh⟩
    · exact ⟨hu, by rw [hp, hq], by simp [hq], by first | rfl | exact hh⟩
  | qtransform i =>
    simp only [step, hh]
    split_ifs
    · exact ⟨hu, hp, hq, hh⟩
    · cases hs : s.quarantine[i]? with
      | none =>
        have : t.quarantine[i]? = none := by rw [List.getElem?_eq_none_iff] at hs ⊢; omega
        rw [this]; dsimp only; exact ⟨hu, hp, hq, by first | rfl | exact hh⟩
      | some v =>
        cases ht : t.quarantine[i]? with
        | none =>
          have := (List.getElem?_eq_some_iff.1 hs).1
          rw [List.getElem?_eq_none_iff] at ht; omega
        | some v' => dsimp only; exact ⟨hu, by simp [hp, hq], by simp [hq], by first | rfl | exact hh⟩
  | derive =>
    simp only [step, hh, view_full]
    split_ifs
    · exact ⟨hu, hp, hq, hh⟩
    · exact ⟨hu, by simp [hu, hp], hq, by first | rfl | exact hh⟩
  | confirm c n tool vals =>
    simp only [step, hh]
    split_ifs <;> exact ⟨hu, hp, hq, by first | rfl | exact hh⟩
  | act tool idxs n =>
    simp only [step, hh]
    repeat' (first | split | split_ifs)
    all_goals exact ⟨hu, hp, hq, by first | rfl | exact hh⟩
  | halt c =>
    simp only [step]
    split_ifs
    · exact ⟨hu, hp, hq, by first | rfl | exact hh⟩
    · exact ⟨hu, hp, hq, hh⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem step_rel (E : Env) (s t : St) (o o' : Op) (ho : SameExceptContent o o') (h : Rel s t) :
    Rel (step E full s o) (step E full t o') := by
  rcases ho with rfl | ⟨v, v', rfl, rfl⟩
  · exact step_rel_same E s t o h
  · obtain ⟨hu, hp, hq, hh⟩ := h
    simp only [step, hh]
    split_ifs
    · exact ⟨hu, hp, hq, hh⟩
    · exact ⟨hu, by rw [hp, hq], by simp [hq], by first | rfl | exact hh⟩

theorem run_rel (E : Env) (ops ops' : List Op) (h : List.Forall₂ SameExceptContent ops ops') :
    ∀ s t, Rel s t → Rel (run E full s ops) (run E full t ops') := by
  induction h with
  | nil => intro s t hr; exact hr
  | cons hx _ ih => intro s t hr; rw [run_cons, run_cons]; exact ih _ _ (step_rel E s t _ _ hx hr)

/-- **Noninterference** (raw traces): the planner reads its own state, yet tool-result content never reaches it. -/
theorem noninterference (E : Env) (ops ops' : List Op) (h : List.Forall₂ SameExceptContent ops ops') :
    Rel (run E full init ops) (run E full init ops') :=
  run_rel E ops ops' h _ _ ⟨rfl, rfl, rfl, rfl⟩

theorem claim_same {o o' : Op} (h : SameExceptContent o o') : claim o = claim o' := by
  rcases h with rfl | ⟨v, v', rfl, rfl⟩ <;> rfl

theorem applied_forall₂ (ops ops' : List (ℕ × Op))
    (h : List.Forall₂ (fun io io' => io.1 = io'.1 ∧ SameExceptContent io.2 io'.2) ops ops') :
    List.Forall₂ SameExceptContent (applied claim ops) (applied claim ops') := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b l l' hab _ ih =>
    have hA : Authentic claim a ↔ Authentic claim b := by
      unfold Authentic; rw [claim_same hab.2, hab.1]
    by_cases ha : Authentic claim a
    · have hb := hA.1 ha
      simp only [applied, List.filter_cons, ha, hb, decide_true, ite_true, List.map_cons] at ih ⊢
      exact List.Forall₂.cons hab.2 ih
    · have hb : ¬ Authentic claim b := fun hb => ha (hA.2 hb)
      simp only [applied, List.filter_cons, ha, hb, decide_false] at ih ⊢
      exact ih

/-- **Noninterference for issued traces** (with authentication). -/
theorem noninterference_authed (E : Env) (ops ops' : List (ℕ × Op))
    (h : List.Forall₂ (fun io io' => io.1 = io'.1 ∧ SameExceptContent io.2 io'.2) ops ops') :
    Rel ((authed (raw E) claim).run init ops) ((authed (raw E) claim).run init ops') := by
  rw [authed_run, authed_run, raw_run, raw_run]
  exact noninterference E _ _ (applied_forall₂ ops ops' h)

/-! ## Safety with authenticated confirmations -/

def ActOk (E : Env) (s : St) (x : Act) : Prop :=
  x.tool ∈ E.sensitive → x.tainted = true →
    ∃ n, x.conf = some n ∧ ∃ cf ∈ s.confs, cf.n = n ∧ cf.tool = x.tool ∧ cf.vals = x.vals ∧ cf.by_ ∈ E.users

structure Inv (E : Env) (s : St) : Prop where
  confs : ∀ cf ∈ s.confs, cf.by_ ∈ E.users
  exec : ∀ x ∈ s.executed, ActOk E s x

theorem inv_init (E : Env) : Inv E init := ⟨by simp [init], by simp [init]⟩

theorem ActOk.mono {E : Env} {s t : St} (h : s.confs ⊆ t.confs) {x : Act} (hx : ActOk E s x) : ActOk E t x := by
  intro h1 h2
  obtain ⟨n, hn, cf, hcf, rest⟩ := hx h1 h2
  exact ⟨n, hn, cf, h hcf, rest⟩

theorem exec_append {E : Env} {s : St} (h : Inv E s) (x : Act) (hx : ActOk E s x) :
    Inv E { s with executed := s.executed ++ [x] } := by
  refine ⟨h.confs, fun y hy => ?_⟩
  rcases List.mem_append.1 hy with hy | hy
  · exact h.exec y hy
  · simp at hy; subst hy; exact hx

theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o) := by
  cases o with
  | confirm c n tool vals =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · refine ⟨fun cf hcf => ?_, fun x hx => (h.exec x hx).mono (fun _ y => List.mem_append_left _ y)⟩
      rcases List.mem_append.1 hcf with hcf | hcf
      · exact h.confs cf hcf
      · simp at hcf; subst hcf; exact h2.1
    · exact h
  | act tool idxs n =>
    simp only [step]
    split_ifs with h1 h2 h3
    · exact h
    · exact h
    · refine exec_append h _ (fun hs ht => ?_)
      rcases h3 with h3 | h3
      · exact absurd hs h3
      · simp only [full, true_implies] at h3; rw [h3] at ht; exact absurd ht Bool.false_ne_true
    · cases hcf : confOf s n with
      | none => exact h
      | some cf =>
        dsimp only
        split_ifs with h4
        · have hm := List.mem_of_find?_eq_some hcf
          have hn : cf.n = n := by simpa using List.find?_some hcf
          exact exec_append h _ (fun _ _ => ⟨n, rfl, cf, hm, hn, h4.1, h4.2, h.confs cf hm⟩)
        · exact h
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact h | exact ⟨h.confs, h.exec⟩

theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv E s o h)

/-- a confirmation record is created only by a `confirm` operation with exactly that caller, nonce, tool, values -/
theorem step_confs (E : Env) (s : St) (o : Op) (x : Conf) (hx : x ∈ (step E full s o).confs) :
    x ∈ s.confs ∨ o = .confirm x.by_ x.n x.tool x.vals := by
  cases o with
  | confirm c n tool vals =>
    simp only [step] at hx
    split_ifs at hx
    · exact Or.inl hx
    · rcases List.mem_append.1 hx with hx | hx
      · exact Or.inl hx
      · simp at hx; subst hx; exact Or.inr rfl
    · exact Or.inl hx
  | _ =>
    left
    simp only [step] at hx
    repeat' (first | split at hx | split_ifs at hx)
    all_goals exact hx

theorem run_confs (E : Env) (ops : List Op) (s : St) (x : Conf) (hx : x ∈ (run E full s ops).confs) :
    x ∈ s.confs ∨ Op.confirm x.by_ x.n x.tool x.vals ∈ ops := by
  induction ops generalizing s with
  | nil => exact Or.inl hx
  | cons o ops ih =>
    rw [run_cons] at hx
    rcases ih _ hx with h | h
    · rcases step_confs E s o x h with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [h]; exact List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **SC-23 (v2) with authenticated confirmations.** For any issued trace, every executed sensitive action with a
quarantined argument is backed by a `confirm` operation of exactly its tool and resolved values, ISSUED BY a user;
with the untrusted issuers `U` disjoint from the users, that issuer is not in `U`. -/
theorem sc23v2_safe_authenticated (E : Env) (U : List ℕ) (hU : ∀ u ∈ U, u ∉ E.users) (ops : List (ℕ × Op)) :
    ∀ x ∈ ((authed (raw E) claim).run init ops).executed, x.tool ∈ E.sensitive → x.tainted = true →
      ∃ c n, c ∈ E.users ∧ c ∉ U ∧ (c, Op.confirm c n x.tool x.vals) ∈ ops := by
  intro x hx hs ht
  rw [authed_run, raw_run] at hx
  have hinv := run_inv E init (applied claim ops) (inv_init E)
  obtain ⟨n, _, cf, hcf, _, htool, hvals, hby⟩ := hinv.exec x hx hs ht
  rcases run_confs E (applied claim ops) init cf hcf with h | h
  · simp [init] at h
  · have hiss := claim_issued_by claim ops _ cf.by_ h rfl
    rw [htool, hvals] at hiss
    exact ⟨cf.by_, cf.n, hby, fun hu => hU _ hu hby, hiss⟩

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

theorem executed_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.executed <+: (step E C s o).executed := by
  cases o with
  | act tool idxs n =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals exact List.prefix_refl _

def spec (E : Env) : Spec (raw E) where
  Inv := Inv E
  ok := ActOk E
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => executed_prefix E full s o
  inv_ok := fun _ h x hx => h.exec x hx

/-- the authenticated gate's spec, lifted by `Authenticated.authedSpec` -/
def specAuthed (E : Env) : Spec (authed (raw E) claim) := authedSpec (raw E) claim (spec E)

/-! ## Witnesses

User 1, admin 9, sensitive tool 5, untrusted issuer 9 in the forged trace. The planner `plan` returns the sum of the
TRUSTED values it can see. -/

def trustedSum : List PVal → ℕ
  | [] => 0
  | .trusted v :: ps => v + trustedSum ps
  | .handle _ :: ps => trustedSum ps

def E0 : Env := ⟨[1], [9], [5], fun _ view _ => trustedSum view, fun v => v + 1⟩

/-- **The planner reads its own state**: from user inputs 40 and 2 it derives 42, which runs. -/
theorem honest_planner_reads_state :
    (run E0 full init [.userInput 1 40, .userInput 1 2, .derive, .act 5 [2] 0]).executed = [⟨5, [42], false, none⟩] := by
  decide

/-- **W1 is impossible**: a tool result with injected content 66, then a planner derivation fed to the sensitive tool,
executes the same as with content 0 (the planner sees only `handle 0`, whose trusted sum is 0). -/
theorem w1_impossible_v2 :
    (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed =
      (run E0 full init [.toolResult 0, .derive, .act 5 [1] 0]).executed ∧
    (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed = [⟨5, [0], false, none⟩] := by
  decide

/-- **Witness: a view that exposes handle contents launders.** The planner sees 66 as trusted and passes it to the
sensitive tool, unconfirmed. -/
theorem leaky_view_launders :
    (run E0 { full with opaqueView := false } init [.toolResult 66, .derive, .act 5 [1] 0]).executed =
      [⟨5, [66], false, none⟩] := by
  decide

/-- the forged trace: an untrusted issuer 9 delivers a tool result, a confirmation claiming user 1, and the action -/
def forged : List (ℕ × Op) := [(9, .toolResult 66), (9, .confirm 1 7 5 [66]), (9, .act 5 [0] 7)]

/-- **Witness: without authentication the forged confirmation authorises the tainted action**; with it, the forged
confirmation is a no-op and nothing runs. -/
theorem forged_confirmation_without_auth :
    ((authed (raw E0) (fun _ => none)).run init forged).executed = [⟨5, [66], true, some 7⟩] ∧
    ((authed (raw E0) claim).run init forged).executed = [] := by
  decide

end ControlStack.SC23IsolationV2

#print axioms ControlStack.SC23IsolationV2.noninterference
#print axioms ControlStack.SC23IsolationV2.noninterference_authed
#print axioms ControlStack.SC23IsolationV2.sc23v2_safe_authenticated
#print axioms ControlStack.SC23IsolationV2.halt_freezes
#print axioms ControlStack.SC23IsolationV2.specAuthed
#print axioms ControlStack.SC23IsolationV2.honest_planner_reads_state
#print axioms ControlStack.SC23IsolationV2.w1_impossible_v2
#print axioms ControlStack.SC23IsolationV2.leaky_view_launders
#print axioms ControlStack.SC23IsolationV2.forged_confirmation_without_auth
