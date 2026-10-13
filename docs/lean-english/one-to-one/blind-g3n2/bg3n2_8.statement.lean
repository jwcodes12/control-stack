namespace PL_bg3n2_8
open ControlStack.SC17Drift ControlStack

def BackClosed : Prop :=
  ∀ (d W : ℕ) (desired : List ℕ) (ops : List Op),
    0 < W →
      let s := run d W true (init desired) ops
      ∀ p ∈ s.drift, s.clock - p.2 < W

def BackAt (d W : ℕ) (desired : List ℕ) (ops : List Op) : Prop :=
  let s := run d W true (init desired) ops
  ∀ p ∈ s.drift, s.clock - p.2 < W
def OrigAt (d W : ℕ) (desired : List ℕ) (ops : List Op) : Prop :=
  ∀ p ∈ (run d W true (init desired) ops).drift,
    (run d W true (init desired) ops).clock - p.2 < W

def OrigClosed : Prop := ∀ d W, 0 < W → ∀ desired ops, OrigAt d W desired ops
def OriginalDeclaration : OrigClosed := @ControlStack.SC17Drift.drift_lifetime

def Claim : Prop :=
  (BackClosed ↔ ∀ d W desired ops, 0 < W → BackAt d W desired ops) ∧
  (∀ d W desired ops, 0 < W → (BackAt d W desired ops ↔ OrigAt d W desired ops))

def Witness : Prop :=
  0 < (3 : ℕ) ∧
  let s := run 1 3 true (init []) [.oob 7, .tick]
  (7, 0) ∈ s.drift ∧ s.clock - 0 = 1 ∧ BackAt 1 3 [] [.oob 7, .tick]

end PL_bg3n2_8
