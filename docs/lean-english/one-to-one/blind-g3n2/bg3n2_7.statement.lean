namespace PL_bg3n2_7
open ControlStack.SC17Drift ControlStack

def BackClosed : Prop :=
  ∀ (d W : ℕ) (desired : List ℕ) (ops : List Op),
    0 < W →
      let s := run d W true (init desired) ops
      (s.live.filter (fun g => decide (g ∉ s.desired))).length ≤ d * W

def BackAt (d W : ℕ) (desired : List ℕ) (ops : List Op) : Prop :=
  let s := run d W true (init desired) ops
  (s.live.filter (fun g => decide (g ∉ s.desired))).length ≤ d * W
def OrigAt (d W : ℕ) (desired : List ℕ) (ops : List Op) : Prop :=
  ((run d W true (init desired) ops).live.filter
    (fun g => g ∉ (run d W true (init desired) ops).desired)).length ≤ d * W

def OrigClosed : Prop := ∀ d W, 0 < W → ∀ desired ops, OrigAt d W desired ops
def OriginalDeclaration : OrigClosed := @ControlStack.SC17Drift.drift_bounded

def Claim : Prop :=
  (BackClosed ↔ ∀ d W desired ops, 0 < W → BackAt d W desired ops) ∧
  (∀ d W desired ops, 0 < W → (BackAt d W desired ops ↔ OrigAt d W desired ops))

def Witness : Prop :=
  0 < (3 : ℕ) ∧ 0 < (1 : ℕ) ∧
  let s := run 1 3 true (init [1]) [.oob 7, .tick, .oob 7]
  (s.live.filter (fun g => decide (g ∉ s.desired))).length = 2 ∧
  s.drift.length = 2 ∧ BackAt 1 3 [1] [.oob 7, .tick, .oob 7]

end PL_bg3n2_7
