-- EXCERPT of ControlStack/Scenarios/SC09Priv.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

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

/-- a privileged operation covered by a capability granted to the lineage, or by an exact elevation rule -/
def UseOk (P : Policy) (s : St) (u : Use) : Prop :=
  (u.lin, u.cap) ∈ s.granted ∨ ∃ r ∈ P.elev, u.via = some (r.bin, r.args) ∧ r.cap = u.cap

structure Good (P : Policy) (s : St) : Prop where
  caps : ∀ q ∈ s.procs, ∀ c ∈ q.caps, (q.lin, c) ∈ s.granted
  uses : ∀ u ∈ s.used, UseOk P s u

def sys (P : Policy) : System St Op Use where
  step := step P full
  effects := St.used

def spec (P : Policy) : Spec (sys P) where
  Inv := Good P
  ok := UseOk P
  step_inv := fun s o h => step_good P s o h
  log_prefix := fun s o => used_prefix P full s o
  inv_ok := fun _ h u hu => h.uses u hu



def P0 : Policy := ⟨[9], [⟨50, 3, 8⟩], fun b => if b = 60 then [9] else []⟩

end ControlStack.SC09

