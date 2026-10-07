namespace PL_UMSTRATF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

/-! Control stack, collusion layer (DESIGN.md v1 §3, campaign UMSTRAT): stratified honeypots with
class-aware shutdown.  Depends on PL_UMPROTF1 (and PL_UMHSF1, PL_UMSURVF1).

Setting.
- The mediator is content-only: the view of submission `x` has law `K (c x)` for a trusted kernel `K`
  on content classes.
- For each bad class `e ∈ Es`, Blue runs `m` honeypots of class `e` (mediated law `K e`; Blue knows each
  honeypot's class).
- Class-aware shutdown: the monitor is shut down if any class has more than `sc` misses (PASSes).
- Then the protocol of PL_UMPROTF1 runs.

Because honeypots and attacks of the same class have identical mediated laws, there is no factor for the
number of classes (contrast with the global iid test). -/

/-- survival of the stratified, class-aware honeypot test -/
def stratSurv {Z C : Type} [Fintype Z] (K : C → Z → ℝ) (Es : Finset C) (φ : Z → ℝ) (m sc : ℕ) : ℝ :=
  ∏ e ∈ Es, surv (K e) φ (hardKill sc) m 0

/-- P(uncaught catastrophe) with the stratified test -/
noncomputable def stratProtocolCat {X Z C Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc : ℕ)
    (r : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * stratSurv K Es (φ ω) m sc * cat Bad (fun x => K (c x)) (φ ω) (π ω) r b N 0 []

def Claim : Prop :=
  -- upper bound: every colluding pair, every adaptive generator
  (∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      0 ≤ r → r ≤ 1 → (∀ x, Bad x → c x ∈ Es) →
      stratProtocolCat Bad K c Es m sc r b N ρ φ π
        ≤ (1 - r) + r * (((sc : ℝ) + 1) / ((m : ℝ) + 1))) ∧
  -- attainment (classes decodable from views): for every bad class and every t ∈ [0,1] a colluding
  -- pair achieves binCDF m sc t · (1 − r + r t)
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq C] [DecidableEq X] (Bad : X → Prop)
      [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (g : Z → C) (Es : Finset C) (m sc b N : ℕ)
      (r t : ℝ) (x : X),
      IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → Bad x → c x ∈ Es → 1 ≤ N → 1 ≤ b →
      0 ≤ t → t ≤ 1 →
      stratProtocolCat Bad K c Es m sc r b N (fun _ : Unit => 1)
          (fun _ z => if g z = c x then t else 0) (fun _ _ x' => if x' = x then 1 else 0)
        = binCDF m sc t * (1 - r + r * t))

/-- Non-vacuity: two classes, identity class kernel on Bool, 12 honeypots per class, slack 1: the bound
2/13 is informative, and the attaining colluder with t = 1/6 reaches binCDF 12 1 (1/6) · 1/6 > 0. -/
def Witness : Prop :=
  IsKernel (fun (e : Bool) (z : Bool) => if z = e then (1 : ℝ) else 0) ∧
  (1 - (1 : ℝ)) + 1 * (((1 : ℝ) + 1) / ((12 : ℝ) + 1)) = 2 / 13 ∧
  0 < binCDF 12 1 (1/6) * (1 - 1 + 1 * (1/6 : ℝ))

end PL_UMSTRATF1
