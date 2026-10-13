namespace PL_bg1n3_6
open ControlStack.SC07Liveness

def FrozenBack : Prop :=
  (run E0 full init [Op.send 10 6, Op.send 10 4]).log =
      [⟨10, 6, 0⟩] ∧
  (run E0 full init [Op.send 10 6, Op.tick, Op.send 10 4]).log =
      [⟨10, 6, 0⟩, ⟨10, 4, 1⟩]

def BackAt  : Prop :=
  (run E0 full init [Op.send 10 6, Op.send 10 4]).log = [⟨10, 6, 0⟩] ∧ (run E0 full init [Op.send 10 6, Op.tick, Op.send 10 4]).log = [⟨10, 6, 0⟩, ⟨10, 4, 1⟩]

def OriginalAt  : Prop :=
  (run E0 full init [.send 10 6, .send 10 4]).log = [⟨10, 6, 0⟩] ∧ (run E0 full init [.send 10 6, .tick, .send 10 4]).log = [⟨10, 6, 0⟩, ⟨10, 4, 1⟩]

def Claim : Prop :=
  (FrozenBack ↔  BackAt) ∧
  ( (BackAt ↔ OriginalAt))

def Witness : Prop :=
  E0.allow = [10] ∧ E0.q = 8 ∧ BackAt

end PL_bg1n3_6
