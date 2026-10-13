namespace PL_bg1a_8
open ControlStack.SC07Liveness

def Back_sc07_safe : Prop :=
  ∀ (E : Env) (ops : List Op),
    let s := run E full init ops
    (∀ e ∈ s.log, e.dest ∈ E.allow) ∧
      (∀ w : ℕ, wsum s w ≤ E.q)


def BackAt (E : Env) (ops : List Op) : Prop :=
  (∀ e ∈ (run E full init ops).log, e.dest ∈ E.allow) ∧ (∀ w : ℕ, wsum (run E full init ops) w ≤ E.q)
def OrigAt (E : Env) (ops : List Op) : Prop :=
  (∀ e ∈ (run E full init ops).log, e.dest ∈ E.allow) ∧ (∀ w : ℕ, wsum (run E full init ops) w ≤ E.q)

def Claim : Prop :=
  (Back_sc07_safe = (∀ (E : Env) (ops : List Op), BackAt E ops)) ∧
  (∀ (E : Env) (ops : List Op), BackAt E ops ↔ OrigAt E ops)

def Witness : Prop :=
  let s := run (⟨[1], 5, [0]⟩ : Env) full init [.send 1 5, .send 1 1, .send 2 0, .tick, .send 1 5]
  s.log = [⟨1, 5, 0⟩, ⟨1, 5, 1⟩] ∧ wsum s 0 = 5 ∧ wsum s 1 = 5 ∧ total s = 10
end PL_bg1a_8
