import Lake
open Lake DSL

/-! Control stack: Lean-verified, capability-free guarantees for AI control.
Interface-level Lake project (pinned to VCVio's toolchain). The ledger statements and proofs are checked
separately in `ledger-check/` (Mathlib v4.35.0-rc3). -/

package ControlStack where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @ "9146f78c4f1bc2c9d8d92da686e9e375315ae5e7"

@[default_target] lean_lib ControlStack
