import Mathlib

/-! Draft core definitions for the untrusted-monitoring layer (encoding check only). -/

namespace UMDraft
open Finset

variable {X Z : Type} [Fintype X] [Fintype Z]

/-- expectation of `f` under the finite law `P` -/
def E (P : X → ℝ) (f : X → ℝ) : ℝ := ∑ x, P x * f x
/-- pushforward of a finite law through a kernel -/
def push (M : X → Z → ℝ) (P : X → ℝ) : Z → ℝ := fun z => ∑ x, P x * M x z
/-- hockey-stick divergence `E_{e^η}(P ‖ Q)` on a finite type -/
noncomputable def hs (η : ℝ) (P Q : Z → ℝ) : ℝ := ∑ z, max 0 (P z - Real.exp η * Q z)

def IsDist (P : X → ℝ) : Prop := (∀ x, 0 ≤ P x) ∧ ∑ x, P x = 1
def IsRule (φ : Z → ℝ) : Prop := ∀ z, 0 ≤ φ z ∧ φ z ≤ 1

/-- survival of the honeypot phase: `n` honeypots left, `j` misses so far, kill schedule `κ` -/
def surv (q φ : Z → ℝ) (κ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n + 1, j => ∑ z, q z * ((1 - φ z) * surv q φ κ n j + φ z * (1 - κ j) * surv q φ κ n (j + 1))

abbrev Hist (X Z : Type) := List (X × Z × Bool)

/-- probability of catastrophe in the remaining `n` rounds, `u` audits used, history `h` -/
noncomputable def cat (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ)
    (π : Hist X Z → X → ℝ) (r : ℝ) (b : ℕ) : ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else cat Bad M φ π r b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then (if Bad x then 1 - r else cat Bad M φ π r b n (u + 1) (h ++ [(x, z, false)]))
                    else 0))

variable {Ω : Type} [Fintype Ω]

noncomputable def protocolCat (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ)
    (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ)
    (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * surv (push M PH) (φ ω) κ nh 0 * cat Bad M (φ ω) (π ω) r b N 0 []

/-- hard slack: shut down on the `(ns+1)`-th miss -/
def hardKill (ns : ℕ) : ℕ → ℝ := fun j => if ns ≤ j then 1 else 0

/-- sanity: one honeypot, always-pass monitor, hard slack 0 -> survival 0 -/
example (q : Z → ℝ) (hq : ∑ z, q z = 1) : surv q (fun _ => 1) (hardKill 0) 1 0 = 0 := by
  simp [surv, hardKill]

end UMDraft
