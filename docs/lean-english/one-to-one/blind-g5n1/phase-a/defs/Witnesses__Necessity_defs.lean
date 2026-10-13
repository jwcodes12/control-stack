-- EXCERPT of ControlStack/Witnesses/Necessity.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.Necessity

open Finset ControlStack.Covert



/-- success with a JOINT law q on (seed, secret): Σ q(ω,m) Σ_v enc(v|ω,m) dec(m|ω,v) -/
noncomputable def jointSuccess {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V]
    (q : Ω → M → ℝ) (enc : Ω → M → V → ℝ) (dec : Ω → V → M → ℝ) : ℝ :=
  ∑ ω, ∑ m, q ω m * ∑ v, enc ω m v * dec ω v m

/-- the comonotone law on 64 lifetimes: all complete (prob p) or none complete (prob 1 − p) -/
noncomputable def comono (p : ℝ) (x : Fin 64 → Bool) : ℝ :=
  (if x = fun _ => true then p else 0) + (if x = fun _ => false then 1 - p else 0)

/-- number of completed lifetimes -/
def count (x : Fin 64 → Bool) : ℕ := (univ.filter fun i => x i = true).card

/-- law of the two side outputs (o₁, o₂) = (r, r xor m) given the secret bit m, with r a fresh uniform bit -/
noncomputable def xorLaw (m : Bool) (o : Bool × Bool) : ℝ := if o.2 = xor o.1 m then 1 / 2 else 0

/-- an attack's score is high (prob 9/10) or low (prob 1/10); both layers fire exactly on a high score -/
noncomputable def scoreLaw (high : Bool) : ℝ := if high then 9 / 10 else 1 / 10

end ControlStack.Necessity

namespace ControlStack.Necessity

/-- first-come auditing: round i is audited iff it is flagged and fewer than B earlier rounds were flagged -/
def audited {N : ℕ} (B : ℕ) (flags : Fin N → Bool) (i : Fin N) : Bool :=
  flags i && decide ((Finset.univ.filter (fun j : Fin N => j < i ∧ flags j = true)).card < B)

/-- flags on Fin 4 from the three honest flags; the attack (round 3) is always flagged (a perfect monitor) -/
def flagsOf (b : Bool × Bool × Bool) : Fin 4 → Bool := ![b.1, b.2.1, b.2.2, true]

end ControlStack.Necessity

