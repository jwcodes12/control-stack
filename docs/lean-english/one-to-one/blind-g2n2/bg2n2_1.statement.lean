namespace PL_bg2n2_1

open ControlStack ControlStack.SC12

def FrozenBack : Prop :=
∀ (admins : List ℕ) (s : St) (sess : ℕ) (ops : List Op),
    Inv s → sess ∈ s.ended →
      ((run admins full s ops).fired.filter (fun f => decide (f.2.1 = sess))) =
        (s.fired.filter (fun f => decide (f.2.1 = sess)))

def BackAt (admins : List ℕ) (s : St) (sess : ℕ) (ops : List Op) : Prop :=
  ((run admins full s ops).fired.filter (fun f => decide (f.2.1 = sess))) =
    (s.fired.filter (fun f => decide (f.2.1 = sess)))
def OrigAt (admins : List ℕ) (s : St) (sess : ℕ) (ops : List Op) : Prop :=
  (run admins full s ops).fired.filter (fun f => f.2.1 = sess) =
    s.fired.filter (fun f => f.2.1 = sess)
def Claim : Prop := ∀ (admins : List ℕ) (s : St) (sess : ℕ) (ops : List Op),
  Inv s → sess ∈ s.ended → (BackAt admins s sess ops ↔ OrigAt admins s sess ops)
def Witness : Prop := ∃ (s : St) (ops : List Op),
  Inv s ∧ 1 ∈ s.ended ∧ ops ≠ [] ∧ s.fired = [(5, 1, 0)] ∧
  (run [9] full s ops).fired = [(5, 1, 0), (6, 2, 1)]

end PL_bg2n2_1
