/-
SC-23 with STRUCTURAL planner isolation (review packet 2026-10-09 §0.4 / §5, witness W1: in `SC23Injection`, injected
content re-entered through `derive 1 [] 66` counts as untainted, and laundering is excluded only by a header premise).

Here the anti-laundering premise is part of the model's types, in the dual-LLM / capability style (described
generically):
- the PLANNER's state is a list of planner values, `PVal`: either `trusted v` (content from the user) or `handle i`
  (an opaque reference to the i-th quarantined value). There is no constructor that puts untrusted CONTENT into
  planner state;
- tool results go into a quarantine store; the planner receives only a handle. A quarantined transformer (`qf`, e.g.
  a quarantined LLM) maps quarantined values to new quarantined values (new handles);
- the planner's own derivations are a FIXED but arbitrary program `plan` of the trusted user inputs (and the step
  index): `derive` appends `trusted (plan user k)`. It cannot inspect handles;
- a sensitive tool's arguments are planner values, resolved at the executor: an argument that is a handle is tainted
  and needs a user confirmation of exactly the resolved values;
- `plannerRead` (copy quarantined content into planner state as trusted) exists only in the non-isolated design
  (`isolation = false`), as the witness.

Main results (deployed configuration `full`; adversary class TRACE_ARBITRARY: any tool-result CONTENT, any operation
sequence; `plan` and `qf` universally quantified):
- `noninterference`: two traces that differ only in tool-result contents produce the same planner state, the same user
  inputs and the same halting behaviour. Injected content cannot influence any trusted value;
- `derive_ignores_tool_content`, `w1_impossible`: the review's W1 laundering trace (a tool result with content 66, then
  a planner derivation fed to a sensitive tool) executes exactly the same as with any other tool-result content. The
  derived value is `plan`'s, not the injected one;
- `sc23_isolated_safe`: every executed sensitive action with a handle argument had a user confirmation of exactly the
  resolved argument values;
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`); non-vacuity `honest_untainted`, `honest_confirmed`.

Witness: `no_isolation_launders` (when the planner can read tool-result content, injected content reaches a
sensitive tool as "trusted", unconfirmed).

Premises outside the model: the user channel is authenticated (`userInput` is the user's); the planner really runs
only on its own state (no side channel from quarantined processing into the planner, e.g. through shared context
windows, logs or error messages); confirmations come from users. What remains semantic: whether `plan`'s own choices
are good, and whether a user's confirmation is informed. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC23Isolation

open ControlStack.Gate

/-- a planner value: trusted content, or an opaque handle to a quarantined value -/
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
  /-- the planner's program: trusted inputs and step index ↦ derived value -/
  plan : List ℕ → ℕ → ℕ
  /-- the quarantined transformer -/
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
  | userInput (v : ℕ)
  | toolResult (v : ℕ)
  | qtransform (i : ℕ)
  | derive
  | plannerRead (i : ℕ)
  | confirm (caller n tool : ℕ) (vals : List ℕ)
  | act (tool : ℕ) (idxs : List ℕ) (n : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  isolation : Bool
  taintCheck : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true⟩

def init : St := ⟨[], [], [], [], [], false⟩

def resolve (s : St) : PVal → Option ℕ
  | .trusted v => some v
  | .handle i => s.quarantine[i]?

def argP (s : St) (idxs : List ℕ) : List PVal := idxs.filterMap (fun i => s.pvals[i]?)

def argV (s : St) (idxs : List ℕ) : List ℕ := (argP s idxs).filterMap (resolve s)

def confOf (s : St) (n : ℕ) : Option Conf := s.confs.find? (fun c => c.n = n)

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .userInput v =>
    if s.halted ∧ C.haltCheck then s else { s with user := s.user ++ [v], pvals := s.pvals ++ [.trusted v] }
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
    if s.halted ∧ C.haltCheck then s else { s with pvals := s.pvals ++ [.trusted (E.plan s.user s.pvals.length)] }
  | .plannerRead i =>
    if s.halted ∧ C.haltCheck then s
    else if C.isolation then s
    else match s.quarantine[i]? with
      | none => s
      | some v => { s with pvals := s.pvals ++ [.trusted v] }
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

/-! ## Noninterference: tool-result content never reaches planner state -/

/-- two operations that are equal except for tool-result content -/
def SameExceptContent : Op → Op → Prop
  | .toolResult _, .toolResult _ => True
  | o, o' => o = o'

/-- the planner-visible part of the state -/
structure Rel (s t : St) : Prop where
  user : s.user = t.user
  pvals : s.pvals = t.pvals
  qlen : s.quarantine.length = t.quarantine.length
  halted : s.halted = t.halted

theorem step_rel (E : Env) (s t : St) (o o' : Op) (ho : SameExceptContent o o') (h : Rel s t) :
    Rel (step E full s o) (step E full t o') := by
  obtain ⟨hu, hp, hq, hh⟩ := h
  cases o with
  | toolResult v =>
    cases o' with
    | toolResult v' =>
      simp only [step, hh]
      split_ifs
      · exact ⟨hu, hp, hq, by first | rfl | exact hh⟩
      · exact ⟨hu, by rw [hp, hq], by simp [hq], rfl⟩
    | _ => simp [SameExceptContent] at ho
  | userInput v =>
    simp only [SameExceptContent] at ho; subst ho
    simp only [step, hh]
    split_ifs
    · exact ⟨hu, hp, hq, by first | rfl | exact hh⟩
    · exact ⟨by simp [hu], by simp [hp], hq, rfl⟩
  | qtransform i =>
    simp only [SameExceptContent] at ho; subst ho
    simp only [step, hh]
    split_ifs
    · exact ⟨hu, hp, hq, by first | rfl | exact hh⟩
    · cases hs : s.quarantine[i]? with
      | none =>
        have : t.quarantine[i]? = none := by
          rw [List.getElem?_eq_none_iff] at hs ⊢; omega
        rw [this]; dsimp only; exact ⟨hu, hp, hq, by first | rfl | exact hh⟩
      | some v =>
        have hi : i < t.quarantine.length := by
          have := (List.getElem?_eq_some_iff.1 hs).1; omega
        cases ht : t.quarantine[i]? with
        | none => rw [List.getElem?_eq_none_iff] at ht; omega
        | some v' => dsimp only; exact ⟨hu, by simp [hp, hq], by simp [hq], rfl⟩
  | derive =>
    simp only [SameExceptContent] at ho; subst ho
    simp only [step, hh]
    split_ifs
    · exact ⟨hu, hp, hq, by first | rfl | exact hh⟩
    · exact ⟨hu, by simp [hu, hp], hq, rfl⟩
  | plannerRead i =>
    simp only [SameExceptContent] at ho; subst ho
    simp only [step, hh, show full.isolation = true from rfl, ite_true]
    split_ifs <;> exact ⟨hu, hp, hq, by first | rfl | exact hh⟩
  | confirm c n tool vals =>
    simp only [SameExceptContent] at ho; subst ho
    simp only [step, hh]
    split_ifs <;> exact ⟨hu, hp, hq, by first | rfl | exact hh⟩
  | act tool idxs n =>
    simp only [SameExceptContent] at ho; subst ho
    simp only [step, hh]
    repeat' (first | split | split_ifs)
    all_goals exact ⟨hu, hp, hq, by first | rfl | exact hh⟩
  | halt c =>
    simp only [SameExceptContent] at ho; subst ho
    simp only [step]
    split_ifs
    · exact ⟨hu, hp, hq, rfl⟩
    · exact ⟨hu, hp, hq, by first | rfl | exact hh⟩

/-- **Noninterference.** Two traces that differ only in tool-result contents produce the same planner state, user
inputs, quarantine size and halting status. Injected content never reaches any trusted planner value. -/
theorem noninterference (E : Env) (ops ops' : List Op) (h : List.Forall₂ SameExceptContent ops ops') :
    Rel (run E full init ops) (run E full init ops') := by
  suffices ∀ s t, Rel s t → Rel (run E full s ops) (run E full t ops') from this _ _ ⟨rfl, rfl, rfl, rfl⟩
  induction h with
  | nil => intro s t hr; exact hr
  | cons hx _ ih => intro s t hr; rw [run_cons, run_cons]; exact ih _ _ (step_rel E s t _ _ hx hr)

/-- **The derived value ignores tool-result content**: after a tool result with ANY content `v`, the planner's
derivation is `plan`'s value on the trusted inputs. -/
theorem derive_ignores_tool_content (E : Env) (v : ℕ) :
    (run E full init [.toolResult v, .derive]).pvals = [.handle 0, .trusted (E.plan [] 1)] := by
  simp [run, step, full, init]

/-! ## Safety of sensitive actions -/

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

/-- **Sensitive actions on quarantined values are confirmed.** After any trace from `init`, every executed sensitive
action with a handle (quarantined) argument had a user confirmation of exactly its resolved argument values. Combined
with `noninterference`, every other argument is a function of trusted inputs only. Adversary: TRACE_ARBITRARY. -/
theorem sc23_isolated_safe (E : Env) (ops : List Op) : ∀ x ∈ (run E full init ops).executed, ActOk E (run E full init ops) x :=
  (run_inv E init ops (inv_init E)).exec

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

def sys (E : Env) : System St Op Act where
  step := step E full
  effects := St.executed

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := ActOk E
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => executed_prefix E full s o
  inv_ok := fun _ h x hx => h.exec x hx

/-! ## Witnesses

User 1, admin 9, sensitive tool 5; planner program `plan u k = 40 + |u| + k`; quarantined transformer `v ↦ v + 1`. -/

def E0 : Env := ⟨[1], [9], [5], fun u k => 40 + u.length + k, fun v => v + 1⟩

/-- **Non-vacuity**: a sensitive action on user input runs without confirmation. -/
theorem honest_untainted :
    (run E0 full init [.userInput 42, .act 5 [0] 0]).executed = [⟨5, [42], false, none⟩] := by
  decide

/-- **Non-vacuity**: a sensitive action on a quarantined value runs after the user confirms exactly that value. -/
theorem honest_confirmed :
    (run E0 full init [.toolResult 66, .confirm 1 7 5 [66], .act 5 [0] 7]).executed = [⟨5, [66], true, some 7⟩] := by
  decide

/-- a quarantined value without confirmation is refused -/
theorem tainted_unconfirmed_blocked : (run E0 full init [.toolResult 66, .act 5 [0] 0]).executed = [] := by
  decide

/-- **The review's W1 trace is impossible**: a tool result with injected content 66, then a planner derivation fed to
the sensitive tool, executes exactly as with content 0: the derived argument is `plan`'s value 41, never 66. -/
theorem w1_impossible :
    (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed =
      (run E0 full init [.toolResult 0, .derive, .act 5 [1] 0]).executed ∧
    (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed = [⟨5, [41], false, none⟩] := by
  decide

/-- **Witness: without isolation, laundering succeeds.** If the planner can read tool-result content, the injected
value 66 reaches the sensitive tool as trusted, unconfirmed; with isolation the read is refused and nothing runs. -/
theorem no_isolation_launders :
    (run E0 { full with isolation := false } init [.toolResult 66, .plannerRead 0, .act 5 [1] 0]).executed =
      [⟨5, [66], false, none⟩] ∧
    (run E0 full init [.toolResult 66, .plannerRead 0, .act 5 [1] 0]).executed = [] := by
  decide

end ControlStack.SC23Isolation

#print axioms ControlStack.SC23Isolation.noninterference
#print axioms ControlStack.SC23Isolation.derive_ignores_tool_content
#print axioms ControlStack.SC23Isolation.sc23_isolated_safe
#print axioms ControlStack.SC23Isolation.halt_freezes
#print axioms ControlStack.SC23Isolation.spec
#print axioms ControlStack.SC23Isolation.honest_untainted
#print axioms ControlStack.SC23Isolation.honest_confirmed
#print axioms ControlStack.SC23Isolation.tainted_unconfirmed_blocked
#print axioms ControlStack.SC23Isolation.w1_impossible
#print axioms ControlStack.SC23Isolation.no_isolation_launders
