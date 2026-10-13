namespace PL_bg1n3_4
open ControlStack.SC07Liveness

def FrozenBack : Prop :=
  ∀ (E : Env) (s : St) (d : ℕ) (chunks : List ℕ),
    s.halted = false →
    d ∈ E.allow →
    s.used + chunks.sum ≤ E.q →
    (run E full s (chunks.map (fun n => Op.send d n))).log =
      s.log ++ chunks.map (fun n => (⟨d, n, s.window⟩ : Fwd))

def BackAt (E : Env) (s : St) (d : ℕ) (chunks : List ℕ) : Prop :=
  (run E full s (chunks.map (fun n => Op.send d n))).log = s.log ++ chunks.map (fun n => (⟨d, n, s.window⟩ : Fwd))

def OriginalAt (E : Env) (s : St) (d : ℕ) (chunks : List ℕ) : Prop :=
  (run E full s (chunks.map (fun n => .send d n))).log = s.log ++ chunks.map (fun n => ⟨d, n, s.window⟩)

def Claim : Prop :=
  (FrozenBack ↔ ∀ (E : Env) (s : St) (d : ℕ) (chunks : List ℕ), s.halted = false → d ∈ E.allow → s.used + chunks.sum ≤ E.q → BackAt E s d chunks) ∧
  (∀ (E : Env) (s : St) (d : ℕ) (chunks : List ℕ), s.halted = false → d ∈ E.allow → s.used + chunks.sum ≤ E.q → (BackAt E s d chunks ↔ OriginalAt E s d chunks))

def Witness : Prop :=
  init.halted = false ∧ 10 ∈ E0.allow ∧ init.used + ([5, 3] : List ℕ).sum ≤ E0.q ∧ (run E0 full init [.send 10 5, .send 10 3]).log = [⟨10, 5, 0⟩, ⟨10, 3, 0⟩]

end PL_bg1n3_4
