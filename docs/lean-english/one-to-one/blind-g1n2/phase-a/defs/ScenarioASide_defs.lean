-- EXCERPT of ControlStack/ScenarioASide.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.
namespace ControlStack.ScenarioASide
open ControlStack.Covert ControlStack.SideChannel ControlStack.ScenarioARepair

/-- the noiseless one-bit side kernel -/
def idKernel : Bool → Bool → ℝ := fun s o => if s = o then 1 else 0

/-- an injective code for (transcript, side bit) pairs into the secret space -/
noncomputable def emb : Transcript × Bool → Fin (2 ^ 32) :=
  fun y => Fin.castLE card_obs (Fintype.equivFin _ y)

open Classical in
end ControlStack.ScenarioASide

