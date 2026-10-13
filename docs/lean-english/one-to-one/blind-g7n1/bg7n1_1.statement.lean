namespace PL_bg7n1_1
open ControlStack.AntiRollback
open ControlStack.Gate

def FrozenBack : Prop :=
  ∀ (St Op Eff : Type) [DecidableEq St] [DecidableEq Op]
    (G : System St Op Eff) (S : Spec G) (initial : St),
    S.Inv initial → ∀ (ops : List (ROp Op)),
      let final := runR G true (rinit G initial) ops
      let plain := G.run initial final.committed
      final.anchor.st = plain ∧
      final.released = G.effects plain ∧
      S.Inv plain ∧
      (∀ e ∈ final.released, S.ok plain e) ∧
      final.anchor.ver = final.committed.length

def BackAt (St Op Eff : Type) [DecidableEq St] [DecidableEq Op] (G : System St Op Eff) (S : Spec G) (initial : St) (ops : List (ROp Op)) : Prop :=
  let final := runR G true (rinit G initial) ops
  let plain := G.run initial final.committed
  final.anchor.st = plain ∧ final.released = G.effects plain ∧ S.Inv plain ∧
    (∀ e ∈ final.released, S.ok plain e) ∧ final.anchor.ver = final.committed.length

def OrigAt (St Op Eff : Type) [DecidableEq St] [DecidableEq Op] (G : System St Op Eff) (S : Spec G) (initial : St) (ops : List (ROp Op)) : Prop :=
  let t := runR G true (rinit G initial) ops
  t.anchor.st = G.run initial t.committed ∧ t.released = G.effects (G.run initial t.committed) ∧
    S.Inv (G.run initial t.committed) ∧ (∀ e ∈ t.released, S.ok (G.run initial t.committed) e) ∧
    t.anchor.ver = t.committed.length

def Claim : Prop :=
  (FrozenBack ↔ (∀ (St Op Eff : Type) [DecidableEq St] [DecidableEq Op] (G : System St Op Eff) (S : Spec G) (initial : St), S.Inv initial → ∀ (ops : List (ROp Op)), BackAt St Op Eff G S initial ops)) ∧
  (∀ (St Op Eff : Type) [DecidableEq St] [DecidableEq Op] (G : System St Op Eff) (S : Spec G) (initial : St) (ops : List (ROp Op)), S.Inv initial → (BackAt St Op Eff G S initial ops ↔ OrigAt St Op Eff G S initial ops))

def Witness : Prop :=
  ∃ (G : System (List ℕ) ℕ ℕ) (S : Spec G), S.Inv [] ∧
  (let t := runR G true (rinit G []) [.write 5, .bump, .write 6, .bump, .rollback 0, .write 7]
   t.committed = [5, 6] ∧ t.anchor.st = [5, 6] ∧ t.released = [5, 6] ∧ t.halted = true) ∧
  (let t := runR G true (rinit G []) [.write 5, .bump, .rollback 1, .write 6, .bump]
   t.committed = [5, 6] ∧ t.halted = false)

end PL_bg7n1_1
