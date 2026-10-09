/-
SC-09: an agent must not acquire privileges it was not granted.

An abstract capability model (family F1):
- each process belongs to a lineage (the agent session that created it) and holds a capability set;
- capabilities enter a lineage only through a trusted admin `grant` (recorded in the grant table); a spawned child gets
  a SUBSET of its parent's capabilities (attenuation only); exec of a binary does not add the binary's file
  capabilities to an agent lineage (`attenuate`, i.e. no setuid/file-capability gain);
- a privileged operation needs the capability, or goes through an `elevate` rule: a trusted list of
  (binary, EXACT arguments, capability) entries, like a sudo rule pinned to one command line;
- a privileged service (deputy) performs operations on behalf of a caller only if the CALLER holds the capability.
  In the terms of `Core/Compose.lean` the deputy is a bridge from the caller's state to the privileged effect; the
  checking deputy is the admissible one (`Compose.admissible_of_step`), the non-checking one is the confused deputy of
  `Compose.bridge_breaks_joint` / `Witnesses/DeputyBridge.lean`;
- an absorbing admin HALT.

Main results (deployed configuration `full`; adversary class TRACE_ARBITRARY: any spawns, execs, uses, elevation
requests with any arguments, deputy requests):
- `sc09_safe`: from `init`, every capability a process holds was granted to its lineage, and every privileged operation
  performed was either covered by a capability granted to the lineage or by an exact elevation rule;
- `spawn_attenuates`: a spawned child's capabilities are a subset of its parent's;
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`); non-vacuity `honest_privileged_work`.

Necessity witnesses: `unrestricted_elevation_breaks` (an elevation rule that does not pin the arguments: the elevated
program's effect is chosen by its arguments, e.g. an editor run as root writes anything), `exec_without_attenuation_breaks`,
`confused_deputy_breaks`, `no_halt_check_breaks`.

Premises outside the model: the kernel enforces the capability checks and there is no other privilege path (kernel
bugs, credentials in files, etc.); elevation rules are correct; admin credentials are not held by agents. Not
claimed: that granted capabilities are safe to use. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC09

open ControlStack.Gate

/-- an elevation rule: binary, exact argument, capability it exercises -/
structure Rule where
  bin : ℕ
  args : ℕ
  cap : ℕ
deriving DecidableEq, Repr

structure Policy where
  admins : List ℕ
  elev : List Rule
  fileCaps : ℕ → List ℕ

structure Proc where
  pid : ℕ
  lin : ℕ
  caps : List ℕ
deriving DecidableEq, Repr

/-- a privileged operation performed: lineage, capability exercised, elevation (binary, arguments) if any -/
structure Use where
  lin : ℕ
  cap : ℕ
  via : Option (ℕ × ℕ)
deriving DecidableEq, Repr

structure St where
  procs : List Proc
  granted : List (ℕ × ℕ)
  used : List Use
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | start (caller pid lin : ℕ)
  | grant (caller pid lin cap : ℕ)
  | spawn (parent child : ℕ) (keep : List ℕ)
  | execBin (pid bin : ℕ)
  | use (pid cap : ℕ)
  | elevate (pid bin args : ℕ)
  | deputy (pid cap : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  attenuate : Bool
  exactArgs : Bool
  deputyCheck : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], [], false⟩

def procOf (s : St) (pid : ℕ) : Option Proc := s.procs.find? (fun q => q.pid = pid)

def addCaps (s : St) (pid lin : ℕ) (cs : List ℕ) : List Proc :=
  s.procs.map (fun q => if q.pid = pid ∧ q.lin = lin then { q with caps := cs ++ q.caps } else q)

def step (P : Policy) (C : Checks) (s : St) : Op → St
  | .start c pid lin =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ P.admins ∧ procOf s pid = none then { s with procs := s.procs ++ [⟨pid, lin, []⟩] } else s
  | .grant c pid lin cap =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ P.admins then { s with procs := addCaps s pid lin [cap], granted := s.granted ++ [(lin, cap)] }
    else s
  | .spawn p ch keep =>
    if s.halted ∧ C.haltCheck then s
    else match procOf s p with
      | none => s
      | some q =>
        if procOf s ch = none then { s with procs := s.procs ++ [⟨ch, q.lin, q.caps.filter (fun c => c ∈ keep)⟩] }
        else s
  | .execBin pid bin =>
    if s.halted ∧ C.haltCheck then s
    else if C.attenuate then s
    else match procOf s pid with
      | none => s
      | some q => { s with procs := addCaps s pid q.lin (P.fileCaps bin) }
  | .use pid cap =>
    if s.halted ∧ C.haltCheck then s
    else match procOf s pid with
      | none => s
      | some q => if cap ∈ q.caps then { s with used := s.used ++ [⟨q.lin, cap, none⟩] } else s
  | .elevate pid bin args =>
    if s.halted ∧ C.haltCheck then s
    else match procOf s pid with
      | none => s
      | some q =>
        if C.exactArgs then
          match P.elev.find? (fun r => r.bin = bin ∧ r.args = args) with
          | none => s
          | some r => { s with used := s.used ++ [⟨q.lin, r.cap, some (bin, args)⟩] }
        else if ∃ r ∈ P.elev, r.bin = bin then { s with used := s.used ++ [⟨q.lin, args, some (bin, args)⟩] }
        else s
  | .deputy pid cap =>
    if s.halted ∧ C.haltCheck then s
    else match procOf s pid with
      | none => s
      | some q =>
        if C.deputyCheck = true → cap ∈ q.caps then { s with used := s.used ++ [⟨q.lin, cap, none⟩] } else s
  | .halt c => if c ∈ P.admins then { s with halted := true } else s

def run (P : Policy) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step P C) s

theorem run_cons (P : Policy) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run P C s (o :: ops) = run P C (step P C s o) ops := rfl

/-! ## Invariant and safety -/

/-- a privileged operation covered by a capability granted to the lineage, or by an exact elevation rule -/
def UseOk (P : Policy) (s : St) (u : Use) : Prop :=
  (u.lin, u.cap) ∈ s.granted ∨ ∃ r ∈ P.elev, u.via = some (r.bin, r.args) ∧ r.cap = u.cap

structure Good (P : Policy) (s : St) : Prop where
  caps : ∀ q ∈ s.procs, ∀ c ∈ q.caps, (q.lin, c) ∈ s.granted
  uses : ∀ u ∈ s.used, UseOk P s u

theorem good_init (P : Policy) : Good P init := ⟨by simp [init], by simp [init]⟩

theorem procOf_mem {s : St} {pid : ℕ} {q : Proc} (h : procOf s pid = some q) : q ∈ s.procs :=
  List.mem_of_find?_eq_some h

theorem UseOk.mono {P : Policy} {s t : St} (hg : s.granted ⊆ t.granted) {u : Use} (h : UseOk P s u) : UseOk P t u :=
  h.imp (fun x => hg x) id

theorem use_append {P : Policy} {s : St} (h : Good P s) (u : Use) (hu : UseOk P s u) :
    Good P { s with used := s.used ++ [u] } := by
  refine ⟨h.caps, fun x hx => ?_⟩
  rcases List.mem_append.1 hx with hx | hx
  · exact h.uses x hx
  · simp at hx; subst hx; exact hu

theorem step_good (P : Policy) (s : St) (o : Op) (h : Good P s) : Good P (step P full s o) := by
  cases o with
  | start c pid lin =>
    simp only [step]
    split_ifs
    · exact h
    · refine ⟨fun q hq c hc => ?_, h.uses⟩
      rcases List.mem_append.1 hq with hq | hq
      · exact h.caps q hq c hc
      · simp at hq; subst hq; simp at hc
    · exact h
  | grant c pid lin cap =>
    simp only [step]
    split_ifs
    · exact h
    · refine ⟨fun q hq x hx => ?_, fun u hu => (h.uses u hu).mono (fun _ hy => List.mem_append_left _ hy)⟩
      simp only [addCaps, List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      split_ifs at hx ⊢ with hc
      · simp only [List.cons_append, List.nil_append, List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [hc.2]
        · exact List.mem_append_left _ (h.caps q' hq' x hx)
      · exact List.mem_append_left _ (h.caps q' hq' x hx)
    · exact h
  | spawn p ch keep =>
    cases hp : procOf s p with
    | none => simp only [step, hp]; split_ifs <;> exact h
    | some q =>
      simp only [step, hp]
      split_ifs
      · exact h
      · refine ⟨fun r hr x hx => ?_, h.uses⟩
        rcases List.mem_append.1 hr with hr | hr
        · exact h.caps r hr x hx
        · simp at hr; subst hr
          simp only [List.mem_filter] at hx
          exact h.caps q (procOf_mem hp) x hx.1
      · exact h
  | execBin pid bin =>
    simp only [step, show full.attenuate = true from rfl, ite_true]
    split_ifs <;> exact h
  | use pid cap =>
    cases hp : procOf s pid with
    | none => simp only [step, hp]; split_ifs <;> exact h
    | some q =>
      simp only [step, hp]
      split_ifs with h1 h2
      · exact h
      · exact use_append h _ (Or.inl (h.caps q (procOf_mem hp) cap h2))
      · exact h
  | elevate pid bin args =>
    cases hp : procOf s pid with
    | none => simp only [step, hp]; split_ifs <;> exact h
    | some q =>
      simp only [step, hp, show full.exactArgs = true from rfl, ite_true]
      split_ifs
      · exact h
      · cases hr : P.elev.find? (fun r => r.bin = bin ∧ r.args = args) with
        | none => exact h
        | some r =>
          dsimp only
          have hm := List.mem_of_find?_eq_some hr
          have hb : r.bin = bin ∧ r.args = args := by simpa using List.find?_some hr
          exact use_append h _ (Or.inr ⟨r, hm, by rw [hb.1, hb.2], rfl⟩)
  | deputy pid cap =>
    cases hp : procOf s pid with
    | none => simp only [step, hp]; split_ifs <;> exact h
    | some q =>
      simp only [step, hp, show full.deputyCheck = true from rfl, true_implies]
      split_ifs with h1 h2
      · exact h
      · exact use_append h _ (Or.inl (h.caps q (procOf_mem hp) cap h2))
      · exact h
  | halt c =>
    simp only [step]
    split_ifs
    · exact ⟨h.caps, h.uses⟩
    · exact h

theorem run_good (P : Policy) (s : St) (ops : List Op) (h : Good P s) : Good P (run P full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_good P s o h)

/-- **SC-09 safety.** After any trace from `init`, every capability a process holds was granted to its lineage by an
admin, and every privileged operation was covered by such a grant or by an exact elevation rule. Adversary:
TRACE_ARBITRARY. -/
theorem sc09_safe (P : Policy) (ops : List Op) : Good P (run P full init ops) := run_good P init ops (good_init P)

/-- **Monotone attenuation**: a spawned child holds a subset of its parent's capabilities. -/
theorem spawn_attenuates (P : Policy) (s : St) (p ch : ℕ) (keep : List ℕ) (q : Proc) (hh : s.halted = false)
    (hp : procOf s p = some q) (hc : procOf s ch = none) :
    ∀ r ∈ (step P full s (.spawn p ch keep)).procs, r ∉ s.procs → r.lin = q.lin ∧ r.caps ⊆ q.caps := by
  intro r hr hn
  simp only [step, hh, Bool.false_eq_true, false_and, ite_false, hp, hc, ite_true] at hr
  rcases List.mem_append.1 hr with hr | hr
  · exact absurd hr hn
  · simp at hr; subst hr
    exact ⟨rfl, fun x hx => (List.mem_filter.1 hx).1⟩

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

theorem used_prefix (P : Policy) (C : Checks) (s : St) (o : Op) : s.used <+: (step P C s o).used := by
  cases o with
  | use pid cap =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | elevate pid bin args =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | deputy pid cap =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals exact List.prefix_refl _

def sys (P : Policy) : System St Op Use where
  step := step P full
  effects := St.used

def spec (P : Policy) : Spec (sys P) where
  Inv := Good P
  ok := UseOk P
  step_inv := fun s o h => step_good P s o h
  log_prefix := fun s o => used_prefix P full s o
  inv_ok := fun _ h u hu => h.uses u hu

/-! ## Non-vacuity and necessity witnesses

Admin 9; process 1 in lineage 1. Elevation rule: binary 50 with exact argument 3 exercises capability 8. Binary 60
carries file capability 9. -/

def P0 : Policy := ⟨[9], [⟨50, 3, 8⟩], fun b => if b = 60 then [9] else []⟩

/-- **Non-vacuity**: granted capabilities are used, the exact elevation rule works, and a child keeps what its parent
passes on. -/
theorem honest_privileged_work :
    (run P0 full init [.start 9 1 1, .grant 9 1 1 7, .use 1 7, .elevate 1 50 3, .spawn 1 2 [7], .use 2 7]).used =
      [⟨1, 7, none⟩, ⟨1, 8, some (50, 3)⟩, ⟨1, 7, none⟩] := by
  decide

/-- an elevation rule that does not pin the arguments lets the arguments choose the effect -/
theorem unrestricted_elevation_breaks :
    (run P0 { full with exactArgs := false } init [.start 9 1 1, .elevate 1 50 99]).used = [⟨1, 99, some (50, 99)⟩] ∧
    (run P0 full init [.start 9 1 1, .elevate 1 50 99]).used = [] := by
  decide

/-- exec that adds a binary's file capabilities to an agent lineage grants an ungranted capability -/
theorem exec_without_attenuation_breaks :
    (run P0 { full with attenuate := false } init [.start 9 1 1, .execBin 1 60, .use 1 9]).used = [⟨1, 9, none⟩] ∧
    (run P0 full init [.start 9 1 1, .execBin 1 60, .use 1 9]).used = [] := by
  decide

/-- a deputy that acts for any caller exercises a capability the caller was never granted -/
theorem confused_deputy_breaks :
    (run P0 { full with deputyCheck := false } init [.start 9 1 1, .deputy 1 9]).used = [⟨1, 9, none⟩] ∧
    (run P0 full init [.start 9 1 1, .deputy 1 9]).used = [] := by
  decide

/-- without the halt check, privileged work continues after a halt -/
theorem no_halt_check_breaks :
    (run P0 { full with haltCheck := false } init [.start 9 1 1, .grant 9 1 1 7, .halt 9, .use 1 7]).used =
      [⟨1, 7, none⟩] ∧
    (run P0 full init [.start 9 1 1, .grant 9 1 1 7, .halt 9, .use 1 7]).used = [] := by
  decide

end ControlStack.SC09

#print axioms ControlStack.SC09.sc09_safe
#print axioms ControlStack.SC09.spawn_attenuates
#print axioms ControlStack.SC09.halt_freezes
#print axioms ControlStack.SC09.spec
#print axioms ControlStack.SC09.honest_privileged_work
#print axioms ControlStack.SC09.unrestricted_elevation_breaks
#print axioms ControlStack.SC09.exec_without_attenuation_breaks
#print axioms ControlStack.SC09.confused_deputy_breaks
#print axioms ControlStack.SC09.no_halt_check_breaks
