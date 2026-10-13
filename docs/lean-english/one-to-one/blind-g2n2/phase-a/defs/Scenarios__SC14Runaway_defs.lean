-- EXCERPT of ControlStack/Scenarios/SC14Runaway.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC14

open ControlStack.Gate

/-- a resource vector: (compute, tokens, network); `+` and `≤` are componentwise -/
abbrev Vec := ℕ × ℕ × ℕ

def total (v : Vec) : ℕ := v.1 + v.2.1 + v.2.2

structure Env where
  cap : Vec
  rate : Vec
  admins : List ℕ

/-- a usage record: actual usage, clock at the step, expiry in force -/
abbrev Use := Vec × ℕ × ℕ

structure St where
  spent : Vec
  window : Vec
  clock : ℕ
  expiry : ℕ
  usage : List Use
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | work (actual reported : Vec)
  | tick
  | setExpiry (caller t : ℕ)
  | rollback
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  meter : Bool
  perResource : Bool
  rate : Bool
  expiry : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true, true⟩

def init (exp : ℕ) : St := ⟨0, 0, 0, exp, [], false⟩

def charge (C : Checks) (actual reported : Vec) : Vec := if C.meter then actual else reported

def capOk (E : Env) (C : Checks) (v : Vec) : Prop := if C.perResource then v ≤ E.cap else total v ≤ total E.cap

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .work a r =>
    if s.halted ∧ C.haltCheck then s
    else if (C.expiry = true → s.clock < s.expiry) ∧ capOk E C (s.spent + charge C a r) ∧
        (C.rate = true → s.window + charge C a r ≤ E.rate) then
      { s with spent := s.spent + charge C a r, window := s.window + charge C a r,
               usage := s.usage ++ [(a, s.clock, s.expiry)] }
    else s
  | .tick => if s.halted ∧ C.haltCheck then s else { s with clock := s.clock + 1, window := 0 }
  | .setExpiry c t => if s.halted ∧ C.haltCheck then s else if c ∈ E.admins then { s with expiry := t } else s
  | .rollback => { s with spent := 0 }
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

/-- anti-rollback premise -/
def legal : Op → Prop
  | .rollback => False
  | _ => True



/-- actual usage in window `t` -/
def windowSum (s : St) (t : ℕ) : Vec := ((s.usage.filter (fun u => u.2.1 = t)).map Prod.fst).sum

def usedTotal (s : St) : Vec := (s.usage.map Prod.fst).sum

def Good (E : Env) (s : St) : Prop :=
  usedTotal s ≤ E.cap ∧ (∀ t, windowSum s t ≤ E.rate) ∧ ∀ u ∈ s.usage, u.2.1 < u.2.2

structure Inv (E : Env) (s : St) : Prop where
  spent_eq : s.spent = usedTotal s
  spent_le : s.spent ≤ E.cap
  win_eq : s.window = windowSum s s.clock
  win_le : s.window ≤ E.rate
  past : ∀ t, t < s.clock → windowSum s t ≤ E.rate
  clocks : ∀ u ∈ s.usage, u.2.1 ≤ s.clock
  exp_ok : ∀ u ∈ s.usage, u.2.1 < u.2.2

def sys (E : Env) : System St {o : Op // legal o} Use where
  step := fun s o => step E full s o.1
  effects := St.usage

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := fun _ u => u.2.1 < u.2.2
  step_inv := fun s o h => step_inv E s o.1 o.2 h
  log_prefix := fun s o => usage_prefix E full s o.1
  inv_ok := fun _ h u hu => h.exp_ok u hu



def E0 : Env := ⟨(10, 10, 10), (5, 5, 5), [9]⟩

end ControlStack.SC14

