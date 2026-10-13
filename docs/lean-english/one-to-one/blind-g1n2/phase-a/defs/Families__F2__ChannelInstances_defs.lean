-- EXCERPT of ControlStack/Families/F2/ChannelInstances.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.ChannelInstances

open Finset ControlStack.Covert ControlStack.Leakage

section General

variable {Ω M Y O : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] [Fintype O]

end General



section SC02

variable {Ω Y O : Type} [Fintype Ω] [Fintype Y] [Fintype O]

end SC02



section SC04

end SC04



section GPU

variable {J : ℕ}

/-- per-quantum certificate: the larger of the two observation likelihoods -/
noncomputable def wmax (W : Bool → Fin J → ℝ) (o : Fin J) : ℝ := max (W true o) (W false o)

/-- the per-quantum round kernel: the sender picks occupancy s from enc (adaptive to the full history), then the
receiver's quantised completion time o ~ W s -/
noncomputable def gpuK {Ω M : Type} (enc : Ω → M → List (Bool × Fin J) → Bool → ℝ) (W : Bool → Fin J → ℝ) :
    Ω → M → List (Bool × Fin J) → Bool × Fin J → ℝ :=
  fun ω m h z => enc ω m h z.1 * W z.1 z.2

/-- the example matrix, J = 4: idle = (.4,.3,.2,.1), busy = (.1,.2,.3,.4) -/
noncomputable def gpuW : Bool → Fin 4 → ℝ :=
  fun s o => if s then ![1 / 10, 2 / 10, 3 / 10, 4 / 10] o else ![4 / 10, 3 / 10, 2 / 10, 1 / 10] o

/-- a jittered matrix, 2%-close: idle = (.26,.25,.25,.24), busy = (.24,.25,.25,.26) -/
noncomputable def gpuWj : Bool → Fin 4 → ℝ :=
  fun s o => if s then ![24 / 100, 25 / 100, 25 / 100, 26 / 100] o else ![26 / 100, 25 / 100, 25 / 100, 24 / 100] o

end GPU

end ControlStack.ChannelInstances

