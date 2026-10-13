namespace ControlStack.AntiRollback

open ControlStack.Gate

def Back_rollback_transfer : Prop :=
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

end ControlStack.AntiRollback
