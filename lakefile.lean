import Lake
open Lake DSL

/-! Control stack: Lean-verified, capability-free guarantees for AI control.
Second Lake project of the programme (pinned to VCVio's toolchain). Never make a third. -/

package ControlStack where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @ "9146f78c4f1bc2c9d8d92da686e9e375315ae5e7"

@[default_target] lean_lib ControlStack
