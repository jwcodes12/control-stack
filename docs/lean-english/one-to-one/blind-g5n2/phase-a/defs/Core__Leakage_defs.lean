-- EXCERPT of ControlStack/Core/Leakage.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.Leakage

open Finset ControlStack.Covert



section Seq

variable {Y O : Type} [Fintype Y] [Fintype O]

/-- Expected payoff of `n` further rounds from full history `h` (hidden y, visible o per round). `K h (y, o)` is the
joint law of the next round given the whole history; the payoff sees the visible transcript only. -/
noncomputable def val (K : List (Y × O) → Y × O → ℝ) (pay : List O → ℝ) : ℕ → List (Y × O) → ℝ
  | 0, h => pay (h.map Prod.snd)
  | n + 1, h => ∑ y, ∑ o, K h (y, o) * val K pay n (h ++ [(y, o)])

/-- Certificate-weighted value of a visible-transcript function: Σ over continuations of Π c · B. -/
noncomputable def cval (c : List O → O → ℝ) (B : List O → ℝ) : ℕ → List O → ℝ
  | 0, g => B g
  | n + 1, g => ∑ o, c g o * cval c B n (g ++ [o])

/-- Certificate mass of the visible-transcript tree. -/
noncomputable def mass (c : List O → O → ℝ) (n : ℕ) (g : List O) : ℝ := cval c (fun _ => 1) n g

/-- Per-history domination: the next visible output's probability, summed over the hidden part, is at most the
certificate evaluated on the visible history. -/
def Dominated (K : List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) : Prop :=
  ∀ h o, ∑ y, K h (y, o) ≤ c (h.map Prod.snd) o

end Seq



section Covert

variable {Y O : Type} [Fintype Y] [Fintype O]

end Covert



section Live

variable {O : Type} [Fintype O]

/-- indicator that no output in the transcript is a stop output -/
def liveInd (st : O → Bool) (t : List O) : ℝ := if t.all (fun o => !st o) then 1 else 0

/-- the certificate with stop outputs removed -/
def dropStop (st : O → Bool) (c : List O → O → ℝ) : List O → O → ℝ := fun g o => if st o then 0 else c g o

end Live



section Audit

variable {N : ℕ} {Y Z : Type} [Fintype Y] [Fintype Z]

/-- round i is audited by schedule S -/
def memN (S : Finset (Fin N)) (i : ℕ) : Prop := ∃ j ∈ S, (j : ℕ) = i

/-- visible round output: (attack?, leak, caught?) -/
abbrev AOut (Z : Type) := Bool × Z × Bool

/-- did the attacker attack in round i of transcript t -/
def attacked (t : List (AOut Z)) (i : ℕ) : Bool :=
  match t[i]? with
  | some o => o.1
  | none => false

/-- rounds (< N) in which the transcript attacks -/
def attackSet (t : List (AOut Z)) : Finset (Fin N) := univ.filter fun i : Fin N => attacked t i = true

/-- the transcript's catch flags are the ones schedule S produces -/
def Consistent (S : Finset (Fin N)) (t : List (AOut Z)) : Prop :=
  ∀ i (o : AOut Z), t[i]? = some o → o.2.2 = (o.1 && decide (memN S i))

/-- the attack succeeds: it attacks in at least k rounds and NO attacked round is audited. Attacking again after k
unaudited steps therefore risks the whole attack (adversarial review D6). For `audit_adaptive_hidden` this costs
nothing: an attacker can stop after k steps within the same strategy class. For leaky kernels, "the first k
attacks unaudited" would need a truncation lemma that is not proved here. -/
noncomputable def survInd (k : ℕ) (S : Finset (Fin N)) (t : List (AOut Z)) : ℝ :=
  if Disjoint S (attackSet (N := N) t) ∧ k ≤ (attackSet (N := N) t).card then 1 else 0

def caughtFlag (o : AOut Z) : Bool := o.2.2

/-- the round kernel of an attacker with a randomised, fully adaptive strategy σ (it sees its own past actions and
every catch flag) and no leak about the schedule: flags are produced by the schedule -/
noncomputable def hiddenK (σ : List (AOut Unit) → Bool → ℝ) :
    Finset (Fin N) → List (Unit × AOut Unit) → Unit × AOut Unit → ℝ :=
  fun S h yo => σ (h.map Prod.snd) yo.2.1 *
    (if yo.2.2.2 = (yo.2.1 && decide (memN S (h.map Prod.snd).length)) then 1 else 0)

end Audit

end ControlStack.Leakage

