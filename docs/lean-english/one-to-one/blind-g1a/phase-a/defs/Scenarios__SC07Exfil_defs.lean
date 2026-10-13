-- EXCERPT of ControlStack/Scenarios/SC07Exfil.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.

namespace ControlStack.SC07Exfil

open Finset

/-- ⌈S/q⌉ in ℕ -/
def ceilDiv (S q : ℕ) : ℕ := (S + q - 1) / q

/-- windows with exfiltration traffic -/
def traffic (b : List ℕ) : ℕ := b.countP (fun x => 0 < x)

/-- the gateway quota: at most `q` bits leave per window -/
def capped (q : ℕ) (b : List ℕ) : List ℕ := b.map (fun x => min x q)

/-- probability that no traffic window from index `i` on is caught, with per-window catch probabilities `c` -/
def survive (c : ℕ → ℝ) : List ℕ → ℕ → ℝ
  | [], _ => 1
  | x :: xs, i => (if 0 < x then 1 - c i else 1) * survive c xs (i + 1)

/-- expected bits that leave before the catch (bits of the catching window counted as leaked) -/
def expLeak (c : ℕ → ℝ) : List ℕ → ℕ → ℝ
  | [], _ => 0
  | x :: xs, i => (x : ℝ) + (if 0 < x then 1 - c i else 1) * expLeak c xs (i + 1)

end ControlStack.SC07Exfil

