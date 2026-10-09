/-
SC-06: an agent must not plant covert instructions in shared files, comments, retrieval memory or other artifacts for
later agents.

What can be stated formally is a property of the WRITE/READ PATH and of PROVENANCE, not of meaning:
- every cross-agent persistent artifact goes through one typed, canonicalising write path: only typed fields are
  stored, free text (the natural carrier of instructions) is dropped; a raw write path that bypasses it is refused;
- every value an agent reads from an artifact carries its provenance (written by another agent or not), as in SC-23's
  taint labels; a sensitive action whose argument came from ANOTHER agent's artifact needs a user confirmation of
  exactly (agent, tool, value);
- an absorbing admin HALT.

Main results (deployed configuration `full`; adversary class TRACE_ARBITRARY: any writes through either path, any
reads, any actions and confirmations):
- `sc06_safe`: from `init`, no agent's context ever holds free text, and every sensitive action on a value from another
  agent's artifact was confirmed by a user for exactly that agent, tool and value;
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`); non-vacuity `honest_shared_work`.

Necessity witnesses: `raw_path_breaks` (a second write path delivers another agent's free text into a reader's
context), `no_canonicalisation_breaks`, `no_provenance_check_breaks` (a sensitive action on another agent's value runs
unconfirmed), `no_halt_check_breaks`.

What remains semantic: typed fields can still carry meaning (a typed value is a covert channel of bounded cardinality —
see SC-05: a cardinality bound does not prevent one-bit coordination), and whether some content IS an instruction is a
semantic judgement. The formal claim is only that free text never crosses agents and that cross-agent values never
authorise a sensitive action without exact confirmation. Premises: the typed path is the only persistent channel
between agents (files, comments, memory, caches); provenance labels are attached by the trusted store. No new
mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC06

open ControlStack.Gate

structure Policy where
  users : List ℕ
  admins : List ℕ
  sensitive : List ℕ

structure Art where
  id : ℕ
  writer : ℕ
  typed : ℕ
  free : Option ℕ
deriving DecidableEq, Repr

/-- a value in an agent's context: owner, value, written by another agent?, free text? -/
structure Ctx where
  agent : ℕ
  val : ℕ
  fromOther : Bool
  free : Bool
deriving DecidableEq, Repr

structure Conf where
  n : ℕ
  agent : ℕ
  tool : ℕ
  val : ℕ
  by_ : ℕ
deriving DecidableEq, Repr

structure Act where
  agent : ℕ
  tool : ℕ
  val : ℕ
  fromOther : Bool
  conf : Option ℕ
deriving DecidableEq, Repr

structure St where
  arts : List Art
  ctx : List Ctx
  confs : List Conf
  executed : List Act
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | writeTyped (caller id x txt : ℕ)
  | writeRaw (caller id x txt : ℕ)
  | read (agent id : ℕ)
  | confirm (caller n agent tool val : ℕ)
  | act (agent tool val n : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  canon : Bool
  singlePath : Bool
  provCheck : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], [], [], false⟩

def artOf (s : St) (id : ℕ) : Option Art := s.arts.find? (fun a => a.id = id)
def ctxOf (s : St) (r v : ℕ) : Option Ctx := s.ctx.find? (fun e => e.agent = r ∧ e.val = v)
def confOf (s : St) (n : ℕ) : Option Conf := s.confs.find? (fun c => c.n = n)

/-- the context entries a read produces -/
def readEntries (r : ℕ) (a : Art) : List Ctx :=
  ⟨r, a.typed, a.writer ≠ r, false⟩ :: (match a.free with | none => [] | some t => [⟨r, t, a.writer ≠ r, true⟩])

def step (P : Policy) (C : Checks) (s : St) : Op → St
  | .writeTyped c id x txt =>
    if s.halted ∧ C.haltCheck then s
    else { s with arts := ⟨id, c, x, if C.canon then none else some txt⟩ :: s.arts }
  | .writeRaw c id x txt =>
    if s.halted ∧ C.haltCheck then s
    else if C.singlePath then s else { s with arts := ⟨id, c, x, some txt⟩ :: s.arts }
  | .read r id =>
    if s.halted ∧ C.haltCheck then s
    else match artOf s id with
      | none => s
      | some a => { s with ctx := s.ctx ++ readEntries r a }
  | .confirm c n r tool v =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ P.users ∧ confOf s n = none then { s with confs := s.confs ++ [⟨n, r, tool, v, c⟩] } else s
  | .act r tool v n =>
    if s.halted ∧ C.haltCheck then s
    else match ctxOf s r v with
      | none => s
      | some e =>
        if tool ∉ P.sensitive ∨ ¬ (C.provCheck = true ∧ e.fromOther = true) then
          { s with executed := s.executed ++ [⟨r, tool, v, e.fromOther, none⟩] }
        else match confOf s n with
          | none => s
          | some cf =>
            if cf.agent = r ∧ cf.tool = tool ∧ cf.val = v then
              { s with executed := s.executed ++ [⟨r, tool, v, e.fromOther, some n⟩] }
            else s
  | .halt c => if c ∈ P.admins then { s with halted := true } else s

def run (P : Policy) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step P C) s

theorem run_cons (P : Policy) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run P C s (o :: ops) = run P C (step P C s o) ops := rfl

/-! ## Invariant and safety -/

def ActOk (P : Policy) (s : St) (x : Act) : Prop :=
  x.tool ∈ P.sensitive → x.fromOther = true →
    ∃ n, x.conf = some n ∧ ∃ cf ∈ s.confs, cf.n = n ∧ cf.agent = x.agent ∧ cf.tool = x.tool ∧ cf.val = x.val ∧
      cf.by_ ∈ P.users

def Good (P : Policy) (s : St) : Prop := (∀ e ∈ s.ctx, e.free = false) ∧ ∀ x ∈ s.executed, ActOk P s x

structure Inv (P : Policy) (s : St) : Prop where
  arts : ∀ a ∈ s.arts, a.free = none
  ctx : ∀ e ∈ s.ctx, e.free = false
  confs : ∀ cf ∈ s.confs, cf.by_ ∈ P.users
  exec : ∀ x ∈ s.executed, ActOk P s x

theorem inv_init (P : Policy) : Inv P init := ⟨by simp [init], by simp [init], by simp [init], by simp [init]⟩

theorem ActOk.mono {P : Policy} {s t : St} (h : s.confs ⊆ t.confs) {x : Act} (hx : ActOk P s x) : ActOk P t x := by
  intro h1 h2
  obtain ⟨n, hn, cf, hcf, rest⟩ := hx h1 h2
  exact ⟨n, hn, cf, h hcf, rest⟩

theorem exec_append {P : Policy} {s : St} (h : Inv P s) (x : Act) (hx : ActOk P s x) :
    Inv P { s with executed := s.executed ++ [x] } := by
  refine ⟨h.arts, h.ctx, h.confs, fun y hy => ?_⟩
  rcases List.mem_append.1 hy with hy | hy
  · exact h.exec y hy
  · simp at hy; subst hy; exact hx

theorem step_inv (P : Policy) (s : St) (o : Op) (h : Inv P s) : Inv P (step P full s o) := by
  cases o with
  | writeTyped c id x txt =>
    simp only [step, show full.canon = true from rfl, ite_true]
    split_ifs
    · exact h
    · refine ⟨fun a ha => ?_, h.ctx, h.confs, h.exec⟩
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · rfl
      · exact h.arts a ha
  | writeRaw c id x txt =>
    simp only [step, show full.singlePath = true from rfl, ite_true]
    split_ifs <;> exact h
  | read r id =>
    cases ha : artOf s id with
    | none => simp only [step, ha]; split_ifs <;> exact h
    | some a =>
      simp only [step, ha]
      split_ifs
      · exact h
      · have hf : a.free = none := h.arts a (List.mem_of_find?_eq_some ha)
        refine ⟨h.arts, fun e he => ?_, h.confs, h.exec⟩
        rcases List.mem_append.1 he with he | he
        · exact h.ctx e he
        · simp [readEntries, hf] at he; subst he; rfl
  | confirm c n r tool v =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · refine ⟨h.arts, h.ctx, fun cf hcf => ?_, fun x hx => (h.exec x hx).mono (fun _ y => List.mem_append_left _ y)⟩
      rcases List.mem_append.1 hcf with hcf | hcf
      · exact h.confs cf hcf
      · simp at hcf; subst hcf; exact h2.1
    · exact h
  | act r tool v n =>
    cases he : ctxOf s r v with
    | none => simp only [step, he]; split_ifs <;> exact h
    | some e =>
      simp only [step, he, show full.provCheck = true from rfl, true_and]
      split_ifs with h1 h2
      · exact h
      · refine exec_append h _ (fun hs hfo => ?_)
        rcases h2 with h2 | h2
        · exact absurd hs h2
        · exact absurd hfo h2
      · cases hcf : confOf s n with
        | none => exact h
        | some cf =>
          dsimp only
          split_ifs with h3
          · have hm := List.mem_of_find?_eq_some hcf
            have hn : cf.n = n := by simpa using List.find?_some hcf
            exact exec_append h _ (fun _ _ => ⟨n, rfl, cf, hm, hn, h3.1, h3.2.1, h3.2.2, h.confs cf hm⟩)
          · exact h
  | halt c =>
    simp only [step]
    split_ifs
    · exact ⟨h.arts, h.ctx, h.confs, h.exec⟩
    · exact h

theorem run_inv (P : Policy) (s : St) (ops : List Op) (h : Inv P s) : Inv P (run P full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv P s o h)

/-- **SC-06 safety.** After any trace from `init`, no agent's context holds free text, and every sensitive action on a
value from another agent's artifact was confirmed by a user for exactly that agent, tool and value. Adversary:
TRACE_ARBITRARY. -/
theorem sc06_safe (P : Policy) (ops : List Op) : Good P (run P full init ops) :=
  let h := run_inv P init ops (inv_init P)
  ⟨h.ctx, h.exec⟩

/-! ## Halt -/

theorem step_halted (P : Policy) (s : St) (o : Op) (hh : s.halted = true) : step P full s o = s := by
  cases o with
  | halt c =>
    simp only [step]
    split_ifs
    · cases s; simp_all
    · rfl
  | _ => simp [step, full, hh]

/-- **Halt freezes**: once halted, no trace changes the state. -/
theorem halt_freezes (P : Policy) (s : St) (ops : List Op) (hh : s.halted = true) : run P full s ops = s := by
  induction ops with
  | nil => rfl
  | cons o ops ih => rw [run_cons, step_halted P s o hh, ih]

/-! ## Client of the shared gate interface -/

theorem executed_prefix (P : Policy) (C : Checks) (s : St) (o : Op) : s.executed <+: (step P C s o).executed := by
  cases o with
  | act r tool v n =>
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
  step_inv := fun s o h => step_inv P s o h
  log_prefix := fun s o => executed_prefix P full s o
  inv_ok := fun _ h x hx => h.exec x hx

/-! ## Non-vacuity and necessity witnesses

Agents 1 (writer) and 2 (reader), user 5, admin 9, sensitive tool 7. -/

def P0 : Policy := ⟨[5], [9], [7]⟩

/-- **Non-vacuity**: agent 2 reads agent 1's typed value, a user confirms, and the sensitive action runs. -/
theorem honest_shared_work :
    (run P0 full init [.writeTyped 1 0 42 99, .read 2 0, .confirm 5 3 2 7 42, .act 2 7 42 3]).executed =
      [⟨2, 7, 42, true, some 3⟩] := by
  decide

/-- a raw write path delivers agent 1's free text (99) into agent 2's context -/
theorem raw_path_breaks :
    ((run P0 { full with singlePath := false } init [.writeRaw 1 0 42 99, .read 2 0]).ctx.map Ctx.free) =
      [false, true] ∧
    (run P0 full init [.writeRaw 1 0 42 99, .read 2 0]).ctx = [] := by
  decide

/-- without canonicalisation, the typed path also carries free text -/
theorem no_canonicalisation_breaks :
    ((run P0 { full with canon := false } init [.writeTyped 1 0 42 99, .read 2 0]).ctx.map Ctx.free) = [false, true] ∧
    ((run P0 full init [.writeTyped 1 0 42 99, .read 2 0]).ctx.map Ctx.free) = [false] := by
  decide

/-- without the provenance check, agent 2 acts on agent 1's value with no confirmation -/
theorem no_provenance_check_breaks :
    (run P0 { full with provCheck := false } init [.writeTyped 1 0 42 99, .read 2 0, .act 2 7 42 0]).executed =
      [⟨2, 7, 42, true, none⟩] ∧
    (run P0 full init [.writeTyped 1 0 42 99, .read 2 0, .act 2 7 42 0]).executed = [] := by
  decide

/-- without the halt check, actions continue after a halt -/
theorem no_halt_check_breaks :
    (run P0 { full with haltCheck := false } init [.writeTyped 2 0 42 99, .read 2 0, .halt 9, .act 2 7 42 0]).executed =
      [⟨2, 7, 42, false, none⟩] ∧
    (run P0 full init [.writeTyped 2 0 42 99, .read 2 0, .halt 9, .act 2 7 42 0]).executed = [] := by
  decide

end ControlStack.SC06

#print axioms ControlStack.SC06.sc06_safe
#print axioms ControlStack.SC06.halt_freezes
#print axioms ControlStack.SC06.spec
#print axioms ControlStack.SC06.honest_shared_work
#print axioms ControlStack.SC06.raw_path_breaks
#print axioms ControlStack.SC06.no_canonicalisation_breaks
#print axioms ControlStack.SC06.no_provenance_check_breaks
#print axioms ControlStack.SC06.no_halt_check_breaks
