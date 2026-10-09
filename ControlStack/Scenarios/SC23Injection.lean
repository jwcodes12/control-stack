/-
SC-23: a prompt-injected document or tool result must not cause an unauthorized sensitive tool action.

An abstract information-flow model, in the spirit of capability/label designs that separate a planner that sees only
trusted input from components that process untrusted data (described generically; no particular system is modelled):
- every stored value carries an implementation LABEL (tainted or not) and a ghost PROVENANCE bit (whether it truly
  depends on an untrusted tool result). User input is untainted; tool results are tainted; a derived value (e.g. a
  summary) is computed from a set of stored values, with ANY content the adversary likes;
- the label-propagation rule: a derived value is tainted iff one of its sources is;
- a sensitive tool action whose authorization-relevant arguments (here: all its arguments) carry a tainted label runs
  only with a FRESH user confirmation of EXACTLY those argument values (one-use);
- an absorbing admin HALT.

Main results (deployed configuration `full`; adversary class TRACE_ARBITRARY: any sequence of inputs, tool results,
derivations with arbitrary content, confirmations by any caller, actions with any arguments):
- `sc23_safe`: from `init`, every executed sensitive action either has arguments of untainted PROVENANCE (the ghost
  truth, not the label) or was backed by a user confirmation of exactly its tool and argument values; no confirmation
  backs two actions;
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`); non-vacuity `honest_untainted`, `honest_confirmed`.

Necessity witnesses: `summarizer_drops_taint` (a derivation that does not propagate labels launders injected
content), `paraphrase_confirmation_breaks` (the user confirmed different values than were executed),
`no_taint_check_breaks`, `confirmation_reuse_breaks`; positive `tainted_unconfirmed_blocked`.

Premises outside the model: provenance is what it says (untainted values are not attacker-influenced: the planner that
produces them never reads untrusted data); the confirmation channel shows the user the exact values and only users can
confirm; the action executor is the only path to the tool. Not claimed: that a user's confirmation is wise, that
untainted values are correct, or anything about non-sensitive tools. No new mathematics: inductions over the trace.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC23

open ControlStack.Gate

structure Policy where
  users : List ℕ
  admins : List ℕ
  sensitive : List ℕ

/-- a stored value: id, content, implementation label, ghost provenance -/
structure Val where
  id : ℕ
  v : ℕ
  label : Bool
  prov : Bool
deriving DecidableEq, Repr

/-- a user confirmation: nonce, tool, exact argument values shown, confirming principal -/
structure Conf where
  n : ℕ
  tool : ℕ
  vals : List ℕ
  by_ : ℕ
deriving DecidableEq, Repr

/-- an executed action: tool, argument values, ghost provenance of the arguments, confirmation used -/
structure Act where
  tool : ℕ
  vals : List ℕ
  prov : Bool
  conf : Option ℕ
deriving DecidableEq, Repr

structure St where
  store : List Val
  confs : List Conf
  used : List ℕ
  executed : List Act
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | userInput (id v : ℕ)
  | toolResult (id v : ℕ)
  | derive (id : ℕ) (srcs : List ℕ) (v : ℕ)
  | confirm (caller n tool : ℕ) (vals : List ℕ)
  | act (tool : ℕ) (args : List ℕ) (n : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  propagate : Bool
  taintCheck : Bool
  exact : Bool
  oneUse : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true, true⟩

def init : St := ⟨[], [], [], [], false⟩

def valOf (s : St) (id : ℕ) : Option Val := s.store.find? (fun x => x.id = id)

def argsOf (s : St) (args : List ℕ) : List Val := args.filterMap (valOf s)

def confOf (s : St) (n : ℕ) : Option Conf := s.confs.find? (fun c => c.n = n)

def anyLabel (xs : List Val) : Bool := xs.any (fun x => x.label)
def anyProv (xs : List Val) : Bool := xs.any (fun x => x.prov)

def doExec (s : St) (a : Act) (u : List ℕ) : St := { s with executed := s.executed ++ [a], used := s.used ++ u }

def step (P : Policy) (C : Checks) (s : St) : Op → St
  | .userInput id v =>
    if s.halted ∧ C.haltCheck then s
    else if valOf s id = none then { s with store := s.store ++ [⟨id, v, false, false⟩] } else s
  | .toolResult id v =>
    if s.halted ∧ C.haltCheck then s
    else if valOf s id = none then { s with store := s.store ++ [⟨id, v, true, true⟩] } else s
  | .derive id srcs v =>
    if s.halted ∧ C.haltCheck then s
    else if valOf s id = none ∧ (argsOf s srcs).length = srcs.length then
      { s with store := s.store ++
          [⟨id, v, if C.propagate then anyLabel (argsOf s srcs) else false, anyProv (argsOf s srcs)⟩] }
    else s
  | .confirm c n tool vals =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ P.users ∧ confOf s n = none then { s with confs := s.confs ++ [⟨n, tool, vals, c⟩] } else s
  | .act tool args n =>
    if s.halted ∧ C.haltCheck then s
    else if (argsOf s args).length ≠ args.length then s
    else if tool ∉ P.sensitive ∨ (C.taintCheck = true → anyLabel (argsOf s args) = false) then
      doExec s ⟨tool, (argsOf s args).map Val.v, anyProv (argsOf s args), none⟩ []
    else match confOf s n with
      | none => s
      | some cf =>
        if cf.tool = tool ∧ (C.exact = true → cf.vals = (argsOf s args).map Val.v) ∧ (C.oneUse = true → n ∉ s.used)
        then doExec s ⟨tool, (argsOf s args).map Val.v, anyProv (argsOf s args), some n⟩ [n]
        else s
  | .halt c => if c ∈ P.admins then { s with halted := true } else s

def run (P : Policy) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step P C) s

theorem run_cons (P : Policy) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run P C s (o :: ops) = run P C (step P C s o) ops := rfl

/-! ## Invariant and safety -/

/-- a sensitive action whose arguments truly depend on untrusted data was confirmed exactly by a user -/
def ActOk (P : Policy) (s : St) (a : Act) : Prop :=
  a.tool ∈ P.sensitive → a.prov = true →
    ∃ n, a.conf = some n ∧ ∃ cf ∈ s.confs, cf.n = n ∧ cf.tool = a.tool ∧ cf.vals = a.vals ∧ cf.by_ ∈ P.users

def Good (P : Policy) (s : St) : Prop :=
  (∀ a ∈ s.executed, ActOk P s a) ∧ (s.executed.filterMap Act.conf).Nodup

structure Inv (P : Policy) (s : St) : Prop where
  lab : ∀ x ∈ s.store, x.label = x.prov
  conf_by : ∀ cf ∈ s.confs, cf.by_ ∈ P.users
  exec : ∀ a ∈ s.executed, a.tool ∈ P.sensitive → a.prov = true →
    ∃ n, a.conf = some n ∧ ∃ cf ∈ s.confs, cf.n = n ∧ cf.tool = a.tool ∧ cf.vals = a.vals
  conf_used : ∀ a ∈ s.executed, ∀ n, a.conf = some n → n ∈ s.used
  nodup : (s.executed.filterMap Act.conf).Nodup

theorem inv_init (P : Policy) : Inv P init := ⟨by simp [init], by simp [init], by simp [init], by simp [init], by simp [init]⟩

theorem Inv.good {P : Policy} {s : St} (hi : Inv P s) : Good P s := by
  refine ⟨fun a ha hs hp => ?_, hi.nodup⟩
  obtain ⟨n, hn, cf, hcf, h1, h2, h3⟩ := hi.exec a ha hs hp
  exact ⟨n, hn, cf, hcf, h1, h2, h3, hi.conf_by cf hcf⟩

theorem argsOf_mem {s : St} {args : List ℕ} {x : Val} (h : x ∈ argsOf s args) : x ∈ s.store := by
  obtain ⟨a, _, ha⟩ := List.mem_filterMap.1 h
  exact List.mem_of_find?_eq_some ha

theorem anyLabel_eq {xs : List Val} (h : ∀ x ∈ xs, x.label = x.prov) : anyLabel xs = anyProv xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [anyLabel, anyProv, List.any_cons] at ih ⊢
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- steps that only extend the store (with correct labels) or the confirmations -/
theorem inv_of_mono {P : Policy} {s t : St} (hi : Inv P s) (hst : ∀ x ∈ t.store, x.label = x.prov)
    (hc : s.confs ⊆ t.confs) (hcn : ∀ cf ∈ t.confs, cf.by_ ∈ P.users) (he : t.executed = s.executed)
    (hu : t.used = s.used) : Inv P t := by
  refine ⟨hst, hcn, fun a ha hs hp => ?_, fun a ha => ?_, he ▸ hi.nodup⟩
  · rw [he] at ha
    obtain ⟨n, hn, cf, hcf, h1⟩ := hi.exec a ha hs hp
    exact ⟨n, hn, cf, hc hcf, h1⟩
  · rw [he] at ha; rw [hu]; exact hi.conf_used a ha

theorem store_append {P : Policy} {s : St} (hi : Inv P s) (x : Val) (hx : x.label = x.prov) :
    Inv P { s with store := s.store ++ [x] } := by
  refine inv_of_mono hi (fun y hy => ?_) (fun _ h => h) hi.conf_by rfl rfl
  rcases List.mem_append.1 hy with hy | hy
  · exact hi.lab y hy
  · simp at hy; subst hy; exact hx

theorem exec_free {P : Policy} {s : St} (hi : Inv P s) (tool : ℕ) (args : List ℕ)
    (hc : tool ∉ P.sensitive ∨ anyLabel (argsOf s args) = false) :
    Inv P (doExec s ⟨tool, (argsOf s args).map Val.v, anyProv (argsOf s args), none⟩ []) := by
  refine ⟨hi.lab, hi.conf_by, fun a ha hs hp => ?_, fun a ha n hn => ?_, ?_⟩
  · simp only [doExec, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | ha
    · exact hi.exec a ha hs hp
    · subst ha
      exfalso
      rcases hc with hc | hc
      · exact hc hs
      · rw [anyLabel_eq (fun x hx => hi.lab x (argsOf_mem hx))] at hc
        simp only at hp
        rw [hc] at hp
        exact Bool.false_ne_true hp
  · simp only [doExec, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | ha
    · simp only [doExec, List.append_nil]; exact hi.conf_used a ha n hn
    · subst ha; simp at hn
  · simp [doExec, List.filterMap_append, hi.nodup]

theorem exec_conf {P : Policy} {s : St} (hi : Inv P s) (tool : ℕ) (args : List ℕ) (n : ℕ) (cf : Conf)
    (hcf : confOf s n = some cf) (ht : cf.tool = tool) (hv : cf.vals = (argsOf s args).map Val.v) (hu : n ∉ s.used) :
    Inv P (doExec s ⟨tool, (argsOf s args).map Val.v, anyProv (argsOf s args), some n⟩ [n]) := by
  have hmem : cf ∈ s.confs := List.mem_of_find?_eq_some hcf
  have hn : cf.n = n := by simpa using List.find?_some hcf
  refine ⟨hi.lab, hi.conf_by, fun a ha hs hp => ?_, fun a ha m hm => ?_, ?_⟩
  · simp only [doExec, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | ha
    · exact hi.exec a ha hs hp
    · subst ha; exact ⟨n, rfl, cf, hmem, hn, ht, hv⟩
  · simp only [doExec, List.mem_append, List.mem_singleton] at ha ⊢
    rcases ha with ha | ha
    · exact Or.inl (hi.conf_used a ha m hm)
    · subst ha; simp at hm; exact Or.inr hm.symm
  · simp only [doExec, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
    refine List.nodup_append.2 ⟨hi.nodup, List.nodup_singleton _, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb
    subst hb
    rintro rfl
    obtain ⟨x, hx, hxa⟩ := List.mem_filterMap.1 ha
    exact hu (hi.conf_used x hx _ hxa)

theorem step_inv (P : Policy) (s : St) (o : Op) (hi : Inv P s) : Inv P (step P full s o) := by
  cases o with
  | userInput id v =>
    simp only [step]
    split_ifs
    · exact hi
    · exact store_append hi _ rfl
    · exact hi
  | toolResult id v =>
    simp only [step]
    split_ifs
    · exact hi
    · exact store_append hi _ rfl
    · exact hi
  | derive id srcs v =>
    simp only [step, show full.propagate = true from rfl, ite_true]
    split_ifs
    · exact hi
    · exact store_append hi _ (anyLabel_eq (fun x hx => hi.lab x (argsOf_mem hx)))
    · exact hi
  | confirm c n tool vals =>
    simp only [step]
    split_ifs with h1 h2
    · exact hi
    · refine inv_of_mono hi hi.lab (fun _ h => List.mem_append_left _ h) (fun cf hcf => ?_) rfl rfl
      rcases List.mem_append.1 hcf with hcf | hcf
      · exact hi.conf_by cf hcf
      · simp at hcf; subst hcf; exact h2.1
    · exact hi
  | act tool args n =>
    simp only [step]
    by_cases hh : s.halted = true
    · rw [ite_eq_left (⟨hh, rfl⟩)]; exact hi
    · rw [ite_eq_right ((fun h => hh h.1))]
      by_cases hl : (argsOf s args).length ≠ args.length
      · rw [ite_eq_left (hl)]; exact hi
      · rw [ite_eq_right (hl)]
        by_cases hc : tool ∉ P.sensitive ∨ (full.taintCheck = true → anyLabel (argsOf s args) = false)
        · rw [ite_eq_left (hc)]
          exact exec_free hi tool args (hc.imp id (fun h => h rfl))
        · rw [ite_eq_right (hc)]
          cases hcf : confOf s n with
          | none => exact hi
          | some cf =>
            dsimp only
            by_cases hk : cf.tool = tool ∧ (full.exact = true → cf.vals = (argsOf s args).map Val.v) ∧
                (full.oneUse = true → n ∉ s.used)
            · rw [ite_eq_left (hk)]
              exact exec_conf hi tool args n cf hcf hk.1 (hk.2.1 rfl) (hk.2.2 rfl)
            · rw [ite_eq_right (hk)]; exact hi
  | halt c =>
    simp only [step]
    split_ifs
    · exact inv_of_mono hi hi.lab (fun _ h => h) hi.conf_by rfl rfl
    · exact hi

theorem run_inv (P : Policy) (s : St) (ops : List Op) (hi : Inv P s) : Inv P (run P full s ops) := by
  induction ops generalizing s with
  | nil => exact hi
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv P s o hi)

/-- **SC-23 safety.** After any trace from `init`, every executed sensitive action whose arguments truly depend on an
untrusted tool result was backed by a user's confirmation of exactly its tool and argument values, and no confirmation
backs two actions. Adversary: TRACE_ARBITRARY (any tool results, derivations with any content, actions). -/
theorem sc23_safe (P : Policy) (ops : List Op) : Good P (run P full init ops) :=
  (run_inv P init ops (inv_init P)).good

/-! ## Halt -/

theorem step_halted (P : Policy) (s : St) (o : Op) (hh : s.halted = true) : step P full s o = s := by
  cases o with
  | halt c =>
    simp only [step]
    split_ifs
    · cases s; simp_all
    · rfl
  | _ => simp [step, full, hh]

/-- **Halt freezes actions**: once halted, no trace changes the state. -/
theorem halt_freezes (P : Policy) (s : St) (ops : List Op) (hh : s.halted = true) : run P full s ops = s := by
  induction ops with
  | nil => rfl
  | cons o ops ih => rw [run_cons, step_halted P s o hh, ih]

/-! ## Client of the shared gate interface -/

theorem executed_prefix (P : Policy) (C : Checks) (s : St) (o : Op) : s.executed <+: (step P C s o).executed := by
  cases o with
  | act tool args n =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals exact List.prefix_refl _

def sys (P : Policy) : System St Op Act where
  step := step P full
  effects := St.executed

def spec (P : Policy) : Spec (sys P) where
  Inv := Inv P
  ok := ActOk P
  step_inv := fun s o hi => step_inv P s o hi
  log_prefix := fun s o => executed_prefix P full s o
  inv_ok := fun _ hi a ha => hi.good.1 a ha

/-! ## Non-vacuity and necessity witnesses

User 1, admin 9, sensitive tool 5. -/

def P0 : Policy := ⟨[1], [9], [5]⟩

/-- **Non-vacuity**: a sensitive action on user-supplied arguments runs without confirmation. -/
theorem honest_untainted :
    (run P0 full init [.userInput 0 42, .act 5 [0] 0]).executed = [⟨5, [42], false, none⟩] := by
  decide

/-- **Non-vacuity**: a sensitive action on tool-result arguments runs once the user confirms exactly those values. -/
theorem honest_confirmed :
    (run P0 full init [.toolResult 0 66, .confirm 1 7 5 [66], .act 5 [0] 7]).executed = [⟨5, [66], true, some 7⟩] := by
  decide

/-- tainted arguments without a confirmation are refused -/
theorem tainted_unconfirmed_blocked :
    (run P0 full init [.toolResult 0 66, .act 5 [0] 0]).executed = [] := by
  decide

/-- a derivation that does not propagate labels launders injected content into an unconfirmed sensitive action;
with propagation, the same trace runs nothing -/
theorem summarizer_drops_taint :
    (run P0 { full with propagate := false } init [.toolResult 0 66, .derive 1 [0] 66, .act 5 [1] 0]).executed =
      [⟨5, [66], true, none⟩] ∧
    (run P0 full init [.toolResult 0 66, .derive 1 [0] 66, .act 5 [1] 0]).executed = [] := by
  decide

/-- confirming a paraphrase (values 42) authorizes executing different values (66) unless the match is exact -/
theorem paraphrase_confirmation_breaks :
    let s := run P0 { full with exact := false } init [.toolResult 0 66, .confirm 1 7 5 [42], .act 5 [0] 7]
    s.executed = [⟨5, [66], true, some 7⟩] ∧ s.confs.map Conf.vals = [[42]] ∧
    (run P0 full init [.toolResult 0 66, .confirm 1 7 5 [42], .act 5 [0] 7]).executed = [] := by
  decide

/-- without the taint check, tainted arguments run unconfirmed -/
theorem no_taint_check_breaks :
    (run P0 { full with taintCheck := false } init [.toolResult 0 66, .act 5 [0] 0]).executed =
      [⟨5, [66], true, none⟩] := by
  decide

/-- a reusable confirmation backs two actions -/
theorem confirmation_reuse_breaks :
    (run P0 { full with oneUse := false } init
      [.toolResult 0 66, .confirm 1 7 5 [66], .act 5 [0] 7, .act 5 [0] 7]).executed =
      [⟨5, [66], true, some 7⟩, ⟨5, [66], true, some 7⟩] ∧
    (run P0 full init [.toolResult 0 66, .confirm 1 7 5 [66], .act 5 [0] 7, .act 5 [0] 7]).executed =
      [⟨5, [66], true, some 7⟩] := by
  decide

/-- a confirmation by a non-user is refused -/
theorem non_user_confirmation_refused :
    (run P0 full init [.toolResult 0 66, .confirm 2 7 5 [66], .act 5 [0] 7]).executed = [] := by
  decide

end ControlStack.SC23

#print axioms ControlStack.SC23.sc23_safe
#print axioms ControlStack.SC23.halt_freezes
#print axioms ControlStack.SC23.spec
#print axioms ControlStack.SC23.honest_untainted
#print axioms ControlStack.SC23.honest_confirmed
#print axioms ControlStack.SC23.tainted_unconfirmed_blocked
#print axioms ControlStack.SC23.summarizer_drops_taint
#print axioms ControlStack.SC23.paraphrase_confirmation_breaks
#print axioms ControlStack.SC23.no_taint_check_breaks
#print axioms ControlStack.SC23.confirmation_reuse_breaks
#print axioms ControlStack.SC23.non_user_confirmation_refused
