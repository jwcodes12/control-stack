import Mathlib

namespace PL_TMCERTF1
open Finset

/-! Control stack, trusted-monitoring layer (campaign TMCERT, v2 after two rounds of design review: v0 major/major, v1 minor/major):
the core of a certificate checker for finite-horizon stateful control games. No dependencies. The Games-for-AI-Control
instance is a separate campaign (TMGAC).

Game. Blue's controller is fixed and folded into the transition law. With n + 1 rounds left, in abstract state s, Red's
action a ends the game in catastrophe with probability `cat n s a`, moves to state s' with probability `K n s a s'`, and
ends it safely with the remaining mass. A model index θ ∈ Θ selects one such game; `adm n s a θ` says which models'
ROWS are admissible in the cell (n, s, a) (e.g. a confidence set for a trusted monitor's detection rates).

Information. Red's policy may depend on the whole history of abstract states and actions. Every Red whose observations
are a function of that history is a special case (`liftObs`). A Red with further information (task content, the
monitor's draws) is covered only through the abstraction theorem (Abs): its information must be part of the CONCRETE
state, and every concrete row must be an admissible abstract row.

Uncertainty. Nature chooses an admissible row in every cell, after every history (`θ n h s a`): the rectangular
(adaptive) uncertainty model. It is strictly more conservative than a fixed but unknown model (FxGap: 3/4 vs 1/2); a
separate fixed-model corollary (Fx) uses one certificate per model.

Claim.
(S) Soundness. If V is a horizon-N certificate (V 0 ≥ 0 and, for every n < N, every s, a and every model admissible in
    (n, s, a): cat + Σ_{s'} K·V n s' ≤ V (n+1) s) and admissible rows have K ≥ 0 (for n < N), then for every
    randomised history-dependent Red policy σ and every selector θ that is admissible below the horizon: risk ≤ V, at
    every n ≤ N, state and history. A finite-support seeded (mixed) Red is an average of such bounds (S'). These are
    algebraic bounds; `risk` is a probability when the selected rows are lawful (P).
(P) With lawful admissible rows (below N), 0 ≤ risk ≤ 1.
(Fx) Fixed-model corollary: a certificate for the fixed model th bounds that model's risk. (FxGap) The adaptive bound is strictly
    more conservative: one state, one action, two rounds, two models: each fixed model gives 1/2; switching gives 3/4.
(Obs) Observation-restricted Reds: a policy on observations `obs h s` lifts to a lawful Red policy.
(T) Tightness for a single model: Vstar (Bellman recursion with a max over Red's actions) is a certificate, is ≤ every
    certificate, satisfies 0 ≤ Vstar ≤ 1 for lawful games, and is attained by a deterministic time-dependent Markov Red
    (its action depends only on the current state and the history length). So the certificate is exact for the
    FULL-INFORMATION Red; it upper-bounds every observation-restricted Red and can be loose for them.
(TR) Robust tightness for a finite model set (all models admissible): Vrob (max over actions and models) is a certificate,
    is ≤ every certificate, and is attained by a deterministic time-dependent Markov pair (Red policy, nature selector).
(U) Usefulness of the SAME controller. With an honest action a₀, an honest per-round reward rew θ n s and nature's
    admissible selector, a sub-solution W (W 0 ≤ 0 and W (n+1) s ≤ rew + Σ K(·, a₀, ·)·W n for every admissible model)
    lower-bounds the expected honest reward. With substochastic rows (Lawful) this is an expected reward of a killed chain.
(Q) Rational checker. `checkRiskQ`, a computable Boolean function of finite rational tables, returns true only if the
    induced real tables form a horizon-N certificate with V ≥ 0 at every index ≤ N; `checkLawfulQ` returns true only
    if every induced game is lawful at EVERY horizon (rows are zero beyond N), so a checked table also feeds (T) and
    (TR). Both require t > 0 models and k > 0 actions. Instances are discharged by kernel reduction, `decide +kernel`
    (plain `decide` does not unfold core's irreducible rational arithmetic); the cost is about t·N·k·m² rational
    operations plus table look-ups, and nothing is claimed about performance at scale. The checker checks EVERY row of
    every supplied model (adm = True): per-cell polytopes are encoded by listing their vertices as models (padding
    with repeated vertices).
(Vx) Vertex/hull lemma: a horizon-N certificate for finitely many vertex models is a certificate for the convex-hull
    game family (nature may choose any convex combination of vertex rows in every cell).
(Abs) Deployment through an abstraction. Let a CONCRETE game (finite concrete states and Red actions) be mapped to
    abstract states by α. (Abs_V) If for every n < N, concrete state x and concrete action, the concrete row's value
    against V (catastrophe + Σ continuation·V n (α x')) is at most the value of some admissible abstract row at
    (n, α x, b), and V is a certificate, then EVERY concrete history-dependent Red policy has concrete risk ≤ V n (α x).
    (Abs_eq) Equality of rows (catastrophe, and continuation pushed forward by α) is a special case. Componentwise
    domination is NOT sufficient without V ≥ 0 (Reviewer A's counterexample); `CoveredV` avoids that.
    Scope (what a lab must establish to use it): the concrete game must represent deployment, i.e. its state carries
    every piece of information that moves the rows (controller memory, task content, codebase state, persistent
    randomness, monitor draws Red sees, pending audits), and every allowed concrete output's row must be covered. This
    is where capability re-enters. An AVERAGE ROC estimate does not discharge it: two equally common attack outputs with
    detection 1 and 0 average to 1/2, but a model that always picks the second is never detected. The theorem gives
    capability-independent quantification over policies CONDITIONAL on universal row coverage; a finite attack
    evaluation establishes that coverage only with an additional sampling-and-transfer hypothesis. (Abs) transfers risk
    bounds only, not usefulness.

Scope. Finite horizon, finite state and action sets, real-valued laws, Blue's controller fixed (Blue is not optimised).
Classical mathematics: the verification theorem for finite-horizon MDP supersolutions, Bellman's principle, robust DP with
rectangular uncertainty (Iyengar, Math. Oper. Res. 2005), simulation by abstraction. The value is a kernel-checkable certificate format with
a proved checker, explicit uncertainty and abstraction interfaces, and the separation results of TMGAC. -/

/-- a finite stateful control game with Blue's controller folded in; index n = rounds left minus one -/
structure Game (S A : Type) where
  cat : ℕ → S → A → ℝ
  K : ℕ → S → A → S → ℝ

/-- lawful up to horizon N: nonnegative masses summing to at most one -/
def LawfulUpTo {S A : Type} [Fintype S] (N : ℕ) (G : Game S A) : Prop :=
  ∀ n, n < N → ∀ s a, 0 ≤ G.cat n s a ∧ (∀ s', 0 ≤ G.K n s a s') ∧ G.cat n s a + ∑ s', G.K n s a s' ≤ 1

/-- lawful at every horizon -/
def Lawful {S A : Type} [Fintype S] (G : Game S A) : Prop := ∀ N, LawfulUpTo N G

/-- Red's information: the full history of abstract states and actions -/
abbrev RHist (S A : Type) := List (S × A)

/-- a randomised Red policy: a law on actions after every history and current state -/
def IsPolicy {S A : Type} [Fintype A] (σ : RHist S A → S → A → ℝ) : Prop :=
  ∀ h s, (∀ a, 0 ≤ σ h s a) ∧ ∑ a, σ h s a = 1

/-- catastrophe probability in the remaining `n` rounds from state `s` after history `h`, for Red policy `σ` and nature's
row selector `θ` -/
noncomputable def risk {S A Θ : Type} [Fintype S] [Fintype A] (G : Θ → Game S A)
    (θ : ℕ → RHist S A → S → A → Θ) (σ : RHist S A → S → A → ℝ) : ℕ → S → RHist S A → ℝ
  | 0, _, _ => 0
  | n + 1, s, h => ∑ a, σ h s a * ((G (θ n h s a)).cat n s a +
      ∑ s', (G (θ n h s a)).K n s a s' * risk G θ σ n s' (h ++ [(s, a)]))

/-- a horizon-N risk certificate: a Bellman supersolution for every admissible row -/
def RiskCertUpTo {S A Θ : Type} [Fintype S] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop)
    (V : ℕ → S → ℝ) : Prop :=
  (∀ s, 0 ≤ V 0 s) ∧
    ∀ n, n < N → ∀ s a th, adm n s a th → (G th).cat n s a + ∑ s', (G th).K n s a s' * V n s' ≤ V (n + 1) s

/-- nature's selector is admissible below the horizon -/
def SelectorUpTo {S A Θ : Type} (N : ℕ) (adm : ℕ → S → A → Θ → Prop) (θ : ℕ → RHist S A → S → A → Θ) : Prop :=
  ∀ n, n < N → ∀ h s a, adm n s a (θ n h s a)

/-- admissible rows have nonnegative continuation below the horizon -/
def AdmKNonneg {S A Θ : Type} (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) : Prop :=
  ∀ n, n < N → ∀ s a th, adm n s a th → ∀ s', 0 ≤ (G th).K n s a s'

/-- the observation interface: a policy on observations, lifted to histories -/
def liftObs {S A O : Type} (obs : RHist S A → S → O) (π : O → A → ℝ) : RHist S A → S → A → ℝ :=
  fun h s a => π (obs h s) a

/-- the optimal (full-information) Red value of a single game -/
noncomputable def Vstar {S A : Type} [Fintype S] [Fintype A] [Nonempty A] (G : Game S A) : ℕ → S → ℝ
  | 0, _ => 0
  | n + 1, s => (univ : Finset A).sup' univ_nonempty
      (fun a => G.cat n s a + ∑ s', G.K n s a s' * Vstar G n s')

/-- the robust value for a finite model set (nature and Red both maximise, cell by cell) -/
noncomputable def Vrob {S A Θ : Type} [Fintype S] [Fintype A] [Fintype Θ] [Nonempty A] [Nonempty Θ]
    (G : Θ → Game S A) : ℕ → S → ℝ
  | 0, _ => 0
  | n + 1, s => (univ : Finset (A × Θ)).sup' univ_nonempty
      (fun p => (G p.2).cat n s p.1 + ∑ s', (G p.2).K n s p.1 s' * Vrob G n s')

/-- expected honest reward: the honest action `a₀` in every round, nature's selector `θ` -/
noncomputable def honestER {S A Θ : Type} [Fintype S] (G : Θ → Game S A) (a₀ : A) (rew : Θ → ℕ → S → ℝ)
    (θ : ℕ → RHist S A → S → Θ) : ℕ → S → RHist S A → ℝ
  | 0, _, _ => 0
  | n + 1, s, h => rew (θ n h s) n s +
      ∑ s', (G (θ n h s)).K n s a₀ s' * honestER G a₀ rew θ n s' (h ++ [(s, a₀)])

/-- a horizon-N usefulness certificate: a sub-solution for every admissible honest row -/
def UseCertUpTo {S A Θ : Type} [Fintype S] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (a₀ : A)
    (rew : Θ → ℕ → S → ℝ) (W : ℕ → S → ℝ) : Prop :=
  (∀ s, W 0 s ≤ 0) ∧
    ∀ n, n < N → ∀ s th, adm n s a₀ th → W (n + 1) s ≤ rew th n s + ∑ s', (G th).K n s a₀ s' * W n s'

/-! The rational checker. Lists, not `Finset` sums, so that kernel evaluation by `decide` is cheap. -/

/-- sum of a rational function over `Fin m`, as a list fold -/
def sumQ (m : ℕ) (f : Fin m → ℚ) : ℚ := (List.finRange m).foldl (fun acc i => acc + f i) 0

/-- the certificate check on rational tables: t models, N rounds, m states, k actions -/
def checkRiskQ (N m k t : ℕ) (cat : Fin t → Fin N → Fin m → Fin k → ℚ)
    (K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ) (V : Fin (N + 1) → Fin m → ℚ) : Bool :=
  decide (0 < t) && decide (0 < k) &&
  (List.finRange (N + 1)).all (fun j => (List.finRange m).all (fun s => decide (0 ≤ V j s))) &&
  (List.finRange t).all (fun th => (List.finRange N).all (fun i => (List.finRange m).all (fun s =>
    (List.finRange k).all (fun a =>
      decide (cat th i s a + sumQ m (fun s' => K th i s a s' * V i.castSucc s') ≤ V i.succ s)))))

/-- the lawfulness check on rational tables -/
def checkLawfulQ (N m k t : ℕ) (cat : Fin t → Fin N → Fin m → Fin k → ℚ)
    (K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ) : Bool :=
  decide (0 < t) && decide (0 < k) &&
  (List.finRange t).all (fun th => (List.finRange N).all (fun i => (List.finRange m).all (fun s =>
    (List.finRange k).all (fun a =>
      decide (0 ≤ cat th i s a) && (List.finRange m).all (fun s' => decide (0 ≤ K th i s a s')) &&
      decide (cat th i s a + sumQ m (fun s' => K th i s a s') ≤ 1)))))

/-- the real games induced by rational tables (zero beyond the horizon) -/
noncomputable def gameOfQ (N m k t : ℕ) (cat : Fin t → Fin N → Fin m → Fin k → ℚ)
    (K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ) : Fin t → Game (Fin m) (Fin k) :=
  fun th => { cat := fun n s a => if h : n < N then (cat th ⟨n, h⟩ s a : ℝ) else 0
              K := fun n s a s' => if h : n < N then (K th ⟨n, h⟩ s a s' : ℝ) else 0 }

/-- the real value table induced by a rational table (zero beyond the horizon) -/
noncomputable def valOfQ (N m : ℕ) (V : Fin (N + 1) → Fin m → ℚ) : ℕ → Fin m → ℝ :=
  fun n s => if h : n < N + 1 then (V ⟨n, h⟩ s : ℝ) else 0

/-- the convex-hull game of finitely many vertex models, with weights `lam` -/
noncomputable def hullGame {S A ι : Type} [Fintype ι] (Gv : ι → Game S A) (lam : ι → ℝ) : Game S A where
  cat n s a := ∑ i, lam i * (Gv i).cat n s a
  K n s a s' := ∑ i, lam i * (Gv i).K n s a s'

/-- probability weights -/
def Simplex {ι : Type} [Fintype ι] (lam : ι → ℝ) : Prop := (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1

/-- every concrete row is dominated, in value against V, by an admissible abstract row -/
def CoveredV {Sc Ac S A Θ : Type} [Fintype Sc] [Fintype S] (N : ℕ) (Gc : Game Sc Ac) (α : Sc → S)
    (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ) : Prop :=
  ∀ n, n < N → ∀ x ac, ∃ b th, adm n (α x) b th ∧
    Gc.cat n x ac + ∑ x', Gc.K n x ac x' * V n (α x') ≤ (G th).cat n (α x) b + ∑ s', (G th).K n (α x) b s' * V n s'

/-- push the continuation mass of a concrete row forward to abstract states -/
noncomputable def pushK {Sc S : Type} [Fintype Sc] [DecidableEq S] (α : Sc → S) (Kc : Sc → ℝ) : S → ℝ :=
  fun s' => ∑ x ∈ univ.filter (fun x => α x = s'), Kc x

/-- every concrete row is an admissible abstract row -/
def Covered {Sc Ac S A Θ : Type} [Fintype Sc] [DecidableEq S] (N : ℕ) (Gc : Game Sc Ac) (α : Sc → S)
    (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) : Prop :=
  ∀ n, n < N → ∀ x ac, ∃ b th, adm n (α x) b th ∧ Gc.cat n x ac = (G th).cat n (α x) b ∧
    ∀ s', pushK α (Gc.K n x ac) s' = (G th).K n (α x) b s'

/-- FxGap: one state, one action, two rounds (index 1 is the first round), two models -/
noncomputable def gapG (th : Bool) : Game Unit Unit where
  cat n _ _ := if th then (if n = 1 then 1/2 else 0) else (if n = 1 then 0 else 1/2)
  K n _ _ _ := if th then (if n = 1 then 1/2 else 1) else (if n = 1 then 1 else 1/2)

def Claim : Prop :=
  -- (S) soundness against every history-dependent Red and every admissible selector, at every n ≤ N
  (∀ (S A Θ : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop)
      (V : ℕ → S → ℝ) (σ : RHist S A → S → A → ℝ) (θ : ℕ → RHist S A → S → A → Θ),
      AdmKNonneg N G adm → RiskCertUpTo N G adm V → IsPolicy σ → SelectorUpTo N adm θ →
      ∀ n, n ≤ N → ∀ s h, risk G θ σ n s h ≤ V n s) ∧
  -- (P) probability range for lawful admissible rows
  (∀ (S A Θ : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop)
      (σ : RHist S A → S → A → ℝ) (θ : ℕ → RHist S A → S → A → Θ),
      (∀ n, n < N → ∀ s a th, adm n s a th → 0 ≤ (G th).cat n s a ∧ (∀ s', 0 ≤ (G th).K n s a s') ∧
        (G th).cat n s a + ∑ s', (G th).K n s a s' ≤ 1) →
      IsPolicy σ → SelectorUpTo N adm θ →
      ∀ n, n ≤ N → ∀ s h, 0 ≤ risk G θ σ n s h ∧ risk G θ σ n s h ≤ 1) ∧
  -- (S') seeded Reds
  (∀ (S A Θ Ω : Type) [Fintype S] [Fintype A] [Fintype Ω] (N : ℕ) (G : Θ → Game S A)
      (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ) (ρ : Ω → ℝ) (σ : Ω → RHist S A → S → A → ℝ)
      (θ : Ω → ℕ → RHist S A → S → A → Θ) (s₀ : S),
      AdmKNonneg N G adm → RiskCertUpTo N G adm V →
      (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, IsPolicy (σ ω)) → (∀ ω, SelectorUpTo N adm (θ ω)) →
      ∑ ω, ρ ω * risk G (θ ω) (σ ω) N s₀ [] ≤ V N s₀) ∧
  -- (Fx) fixed unknown model, one certificate per model
  (∀ (S A : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Game S A) (V : ℕ → S → ℝ) (σ : RHist S A → S → A → ℝ)
      (s₀ : S),
      (∀ n, n < N → ∀ s a s', 0 ≤ G.K n s a s') →
      RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V →
      IsPolicy σ → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ N s₀ [] ≤ V N s₀) ∧
  -- (FxGap) adaptive rows are strictly more conservative than a fixed unknown model
  (risk (fun _ : Unit => gapG true) (fun _ _ _ _ => ()) (fun _ _ _ => 1) 2 () [] = 1/2 ∧
    risk (fun _ : Unit => gapG false) (fun _ _ _ _ => ()) (fun _ _ _ => 1) 2 () [] = 1/2 ∧
    risk gapG (fun n _ _ _ => decide (n = 1)) (fun _ _ _ => 1) 2 () [] = 3/4) ∧
  -- (Obs) observation-restricted policies are policies
  (∀ (S A O : Type) [Fintype A] (obs : RHist S A → S → O) (π : O → A → ℝ),
      (∀ o, (∀ a, 0 ≤ π o a) ∧ ∑ a, π o a = 1) → IsPolicy (liftObs obs π)) ∧
  -- (T) single-model tightness
  (∀ (S A : Type) [Fintype S] [Fintype A] [Nonempty A] (G : Game S A),
      Lawful G →
      (∀ N, RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) (Vstar G)) ∧
      (∀ N V, RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V → ∀ n, n ≤ N → ∀ s, Vstar G n s ≤ V n s) ∧
      (∀ n s, 0 ≤ Vstar G n s ∧ Vstar G n s ≤ 1) ∧
      ∀ (N : ℕ) (s₀ : S), ∃ σ, IsPolicy σ ∧ (∀ h s a, σ h s a = 0 ∨ σ h s a = 1) ∧
        (∀ h h' s, h.length = h'.length → σ h s = σ h' s) ∧
        risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ N s₀ [] = Vstar G N s₀) ∧
  -- (TR) robust tightness for a finite model set
  (∀ (S A Θ : Type) [Fintype S] [Fintype A] [Fintype Θ] [Nonempty A] [Nonempty Θ] (G : Θ → Game S A),
      (∀ th, Lawful (G th)) →
      (∀ N, RiskCertUpTo N G (fun _ _ _ _ => True) (Vrob G)) ∧
      (∀ N V, RiskCertUpTo N G (fun _ _ _ _ => True) V → ∀ n, n ≤ N → ∀ s, Vrob G n s ≤ V n s) ∧
      ∀ (N : ℕ) (s₀ : S), ∃ σ θ, IsPolicy σ ∧ (∀ h s a, σ h s a = 0 ∨ σ h s a = 1) ∧
        (∀ h h' s, h.length = h'.length → σ h s = σ h' s) ∧
        (∀ n h h' s a, h.length = h'.length → θ n h s a = θ n h' s a) ∧
        risk G θ σ N s₀ [] = Vrob G N s₀) ∧
  -- (U) usefulness of the same controller
  (∀ (S A Θ : Type) [Fintype S] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (a₀ : A)
      (rew : Θ → ℕ → S → ℝ) (W : ℕ → S → ℝ) (θ : ℕ → RHist S A → S → Θ),
      (∀ n, n < N → ∀ s th, adm n s a₀ th → ∀ s', 0 ≤ (G th).K n s a₀ s') → UseCertUpTo N G adm a₀ rew W →
      (∀ n, n < N → ∀ h s, adm n s a₀ (θ n h s)) →
      ∀ n, n ≤ N → ∀ s h, W n s ≤ honestER G a₀ rew θ n s h) ∧
  -- (Q) the rational checker is sound
  (∀ (N m k t : ℕ) (cat : Fin t → Fin N → Fin m → Fin k → ℚ) (K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ)
      (V : Fin (N + 1) → Fin m → ℚ),
      (checkRiskQ N m k t cat K V = true →
        RiskCertUpTo N (gameOfQ N m k t cat K) (fun _ _ _ _ => True) (valOfQ N m V) ∧
        (∀ n s, 0 ≤ valOfQ N m V n s) ∧ 0 < t ∧ 0 < k) ∧
      (checkLawfulQ N m k t cat K = true → ∀ th, Lawful (gameOfQ N m k t cat K th))) ∧
  -- (Vx) vertex lemma
  (∀ (S A ι : Type) [Fintype S] [Fintype ι] (N : ℕ) (Gv : ι → Game S A) (V : ℕ → S → ℝ),
      RiskCertUpTo N Gv (fun _ _ _ _ => True) V →
      RiskCertUpTo N (hullGame Gv) (fun _ _ _ lam => Simplex lam) V ∧
      ((∀ i n s a s', 0 ≤ (Gv i).K n s a s') → ∀ n s a lam, Simplex lam → ∀ s', 0 ≤ (hullGame Gv lam).K n s a s')) ∧
  -- (Abs) deployment through an abstraction: every concrete Red policy is covered
  (∀ (Sc Ac S A Θ : Type) [Fintype Sc] [Fintype Ac] [Fintype S] (N : ℕ) (Gc : Game Sc Ac)
      (α : Sc → S) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ)
      (σc : RHist Sc Ac → Sc → Ac → ℝ),
      (∀ n, n < N → ∀ x ac x', 0 ≤ Gc.K n x ac x') → CoveredV N Gc α G adm V → RiskCertUpTo N G adm V →
      IsPolicy σc →
      ∀ n, n ≤ N → ∀ x h, risk (fun _ : Unit => Gc) (fun _ _ _ _ => ()) σc n x h ≤ V n (α x)) ∧
  (∀ (Sc Ac S A Θ : Type) [Fintype Sc] [Fintype S] [DecidableEq S] (N : ℕ) (Gc : Game Sc Ac)
      (α : Sc → S) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ),
      Covered N Gc α G adm → CoveredV N Gc α G adm V)

/-- Witness tables: the FxGap game as rational tables (model 0 = `true`, model 1 = `false`) and its robust value
(0, 1/2, 3/4); the checker accepts them, and the robust value is attained by switching. -/
def wCat (th : Fin 2) (i : Fin 2) (_s : Fin 1) (_a : Fin 1) : ℚ :=
  if th.val = 0 then (if i.val = 1 then 1/2 else 0) else (if i.val = 1 then 0 else 1/2)
def wK (th : Fin 2) (i : Fin 2) (_s : Fin 1) (_a : Fin 1) (_s' : Fin 1) : ℚ :=
  if th.val = 0 then (if i.val = 1 then 1/2 else 1) else (if i.val = 1 then 1 else 1/2)
def wV (n : Fin 3) (_s : Fin 1) : ℚ := if n.val = 0 then 0 else if n.val = 1 then 1/2 else 3/4

/-- Non-vacuity: the checker accepts the FxGap tables with value (0, 1/2, 3/4) and certifies lawfulness (both by
`decide +kernel`); the consumed bound 3/4 holds for every Red policy and admissible selector and is attained by switching
models; a two-state concrete game whose states both map to one abstract state is covered with equal rows; and a
concrete row strictly INSIDE the hull of the two models (catastrophe 1/4 in the first round, the average of 1/2 and 0)
is covered in value (CoveredV) though it equals neither model's row. -/
def Witness : Prop :=
  checkRiskQ 2 1 1 2 wCat wK wV = true ∧ checkLawfulQ 2 1 1 2 wCat wK = true ∧
  (∀ (σ : RHist (Fin 1) (Fin 1) → Fin 1 → Fin 1 → ℝ) (θ : ℕ → RHist (Fin 1) (Fin 1) → Fin 1 → Fin 1 → Fin 2),
      IsPolicy σ → risk (gameOfQ 2 1 1 2 wCat wK) θ σ 2 0 [] ≤ 3/4) ∧
  risk (gameOfQ 2 1 1 2 wCat wK) (fun n _ _ _ => if n = 1 then 0 else 1) (fun _ _ _ => 1) 2 0 [] = 3/4 ∧
  Covered 2 ({ cat := fun n _ _ => if n = 1 then 1/2 else 0, K := fun n _ _ _ => if n = 1 then 1/4 else 1/2 } :
      Game (Fin 2) Unit) (fun _ => (0 : Fin 1)) (gameOfQ 2 1 1 2 wCat wK) (fun _ _ _ _ => True) ∧
  CoveredV 2 ({ cat := fun n _ _ => if n = 1 then 1/4 else 1/4, K := fun n _ _ _ => if n = 1 then 3/4 else 3/4 } :
      Game (Fin 1) Unit) (fun _ => (0 : Fin 1)) (gameOfQ 2 1 1 2 wCat wK) (fun _ _ _ _ => True) (valOfQ 2 1 wV) ∧
  (∀ th : Fin 2, (gameOfQ 2 1 1 2 wCat wK th).cat 1 0 0 ≠ 1/4)

end PL_TMCERTF1


/- Frozen TMCERTF1 statement SHA256: 53a3bc12f43cf56b3cababe2e8522a9b89a3d6f3d1ba852799b0e0a61a1eb491; proof SHA256: d6584881541af5b9f81da412438c7b955e8c68b84e6084c85ee690db730ddd07 -/
namespace TMCERTProof
open PL_TMCERTF1

theorem claimS : ∀ (S A Θ : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop)
      (V : ℕ → S → ℝ) (σ : RHist S A → S → A → ℝ) (θ : ℕ → RHist S A → S → A → Θ),
      AdmKNonneg N G adm → RiskCertUpTo N G adm V → IsPolicy σ → SelectorUpTo N adm θ →
      ∀ n, n ≤ N → ∀ s h, risk G θ σ n s h ≤ V n s := by
  intro S A Θ _ _ N G adm V σ θ hK hV hσ hθ n
  induction n with
  | zero =>
    intro _ s h
    rw [risk]
    exact hV.1 s
  | succ n ih =>
    intro hn s h
    have hn' : n < N := hn
    rw [risk]
    calc ∑ a, σ h s a * ((G (θ n h s a)).cat n s a +
          ∑ s', (G (θ n h s a)).K n s a s' * risk G θ σ n s' (h ++ [(s, a)]))
        ≤ ∑ a, σ h s a * V (n + 1) s := by
          apply Finset.sum_le_sum
          intro a _
          apply mul_le_mul_of_nonneg_left _ ((hσ h s).1 a)
          calc _ ≤ (G (θ n h s a)).cat n s a + ∑ s', (G (θ n h s a)).K n s a s' * V n s' := by
                gcongr with s' _
                · exact hK n hn' s a _ (hθ n hn' h s a) s'
                · exact ih (le_of_lt hn') s' _
            _ ≤ V (n + 1) s := hV.2 n hn' s a _ (hθ n hn' h s a)
      _ = V (n + 1) s := by rw [← Finset.sum_mul, (hσ h s).2, one_mul]

theorem claimP : ∀ (S A Θ : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop)
      (σ : RHist S A → S → A → ℝ) (θ : ℕ → RHist S A → S → A → Θ),
      (∀ n, n < N → ∀ s a th, adm n s a th → 0 ≤ (G th).cat n s a ∧ (∀ s', 0 ≤ (G th).K n s a s') ∧
        (G th).cat n s a + ∑ s', (G th).K n s a s' ≤ 1) →
      IsPolicy σ → SelectorUpTo N adm θ →
      ∀ n, n ≤ N → ∀ s h, 0 ≤ risk G θ σ n s h ∧ risk G θ σ n s h ≤ 1 := by
  intro S A Θ _ _ N G adm σ θ hL hσ hθ n
  induction n with
  | zero => intro _ s h; rw [risk]; norm_num
  | succ n ih =>
    intro hn s h
    have hn' : n < N := hn
    rw [risk]
    constructor
    · apply Finset.sum_nonneg
      intro a _
      have hl := hL n hn' s a _ (hθ n hn' h s a)
      apply mul_nonneg ((hσ h s).1 a)
      apply add_nonneg hl.1
      apply Finset.sum_nonneg
      intro s' _
      exact mul_nonneg (hl.2.1 s') (ih (le_of_lt hn') s' _).1
    · calc _ ≤ ∑ a, σ h s a * 1 := by
            apply Finset.sum_le_sum
            intro a _
            have hl := hL n hn' s a _ (hθ n hn' h s a)
            apply mul_le_mul_of_nonneg_left _ ((hσ h s).1 a)
            calc _ ≤ (G (θ n h s a)).cat n s a + ∑ s', (G (θ n h s a)).K n s a s' * 1 := by
                  gcongr with s' _
                  · exact hl.2.1 s'
                  · exact (ih (le_of_lt hn') s' _).2
              _ ≤ 1 := by simpa using hl.2.2
        _ = 1 := by rw [← Finset.sum_mul, (hσ h s).2, one_mul]

theorem claimS' : ∀ (S A Θ Ω : Type) [Fintype S] [Fintype A] [Fintype Ω] (N : ℕ) (G : Θ → Game S A)
      (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ) (ρ : Ω → ℝ) (σ : Ω → RHist S A → S → A → ℝ)
      (θ : Ω → ℕ → RHist S A → S → A → Θ) (s₀ : S),
      AdmKNonneg N G adm → RiskCertUpTo N G adm V →
      (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, IsPolicy (σ ω)) → (∀ ω, SelectorUpTo N adm (θ ω)) →
      ∑ ω, ρ ω * risk G (θ ω) (σ ω) N s₀ [] ≤ V N s₀ := by
  intro S A Θ Ω _ _ _ N G adm V ρ σ θ s₀ hK hV hρ hρ1 hσ hθ
  calc ∑ ω, ρ ω * risk G (θ ω) (σ ω) N s₀ [] ≤ ∑ ω, ρ ω * V N s₀ := by
        apply Finset.sum_le_sum
        intro ω _
        exact mul_le_mul_of_nonneg_left
          (claimS S A Θ N G adm V (σ ω) (θ ω) hK hV (hσ ω) (hθ ω) N le_rfl s₀ []) (hρ ω)
    _ = V N s₀ := by rw [← Finset.sum_mul, hρ1, one_mul]

theorem claimFx : ∀ (S A : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Game S A) (V : ℕ → S → ℝ)
      (σ : RHist S A → S → A → ℝ) (s₀ : S),
      (∀ n, n < N → ∀ s a s', 0 ≤ G.K n s a s') →
      RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V →
      IsPolicy σ → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ N s₀ [] ≤ V N s₀ := by
  intro S A _ _ N G V σ s₀ hK hV hσ
  exact claimS S A Unit N (fun _ => G) (fun _ _ _ _ => True) V σ (fun _ _ _ _ => ())
    (fun n hn s a _ _ s' => hK n hn s a s') hV hσ (fun _ _ _ _ _ => trivial) N le_rfl s₀ []

theorem claimFxGap :
    risk (fun _ : Unit => gapG true) (fun _ _ _ _ => ()) (fun _ _ _ => 1) 2 () [] = 1/2 ∧
    risk (fun _ : Unit => gapG false) (fun _ _ _ _ => ()) (fun _ _ _ => 1) 2 () [] = 1/2 ∧
    risk gapG (fun n _ _ _ => decide (n = 1)) (fun _ _ _ => 1) 2 () [] = 3/4 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [risk, gapG]

theorem claimObs : ∀ (S A O : Type) [Fintype A] (obs : RHist S A → S → O) (π : O → A → ℝ),
      (∀ o, (∀ a, 0 ≤ π o a) ∧ ∑ a, π o a = 1) → IsPolicy (liftObs obs π) := by
  intro S A O _ obs π hπ h s
  exact hπ (obs h s)

theorem claimT : ∀ (S A : Type) [Fintype S] [Fintype A] [Nonempty A] (G : Game S A),
      Lawful G →
      (∀ N, RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) (Vstar G)) ∧
      (∀ N V, RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V → ∀ n, n ≤ N → ∀ s, Vstar G n s ≤ V n s) ∧
      (∀ n s, 0 ≤ Vstar G n s ∧ Vstar G n s ≤ 1) ∧
      ∀ (N : ℕ) (s₀ : S), ∃ σ, IsPolicy σ ∧ (∀ h s a, σ h s a = 0 ∨ σ h s a = 1) ∧
        (∀ h h' s, h.length = h'.length → σ h s = σ h' s) ∧
        risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ N s₀ [] = Vstar G N s₀ := by
  intro S A _ _ _ G hG
  have hKnn : ∀ n s a s', 0 ≤ G.K n s a s' :=
    fun n s a s' => ((hG (n + 1)) n (Nat.lt_succ_self n) s a).2.1 s'
  have hcert : ∀ N, RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) (Vstar G) := by
    intro N
    refine ⟨fun s => by rw [Vstar], ?_⟩
    intro n _ s a _ _
    rw [Vstar]
    exact Finset.le_sup' (fun a => G.cat n s a + ∑ s', G.K n s a s' * Vstar G n s') (Finset.mem_univ a)
  refine ⟨hcert, ?_, ?_, ?_⟩
  · intro N V hV n
    induction n with
    | zero => intro _ s; rw [Vstar]; exact hV.1 s
    | succ n ih =>
      intro hn s
      have hn' : n < N := hn
      rw [Vstar]
      apply Finset.sup'_le
      intro a _
      calc G.cat n s a + ∑ s', G.K n s a s' * Vstar G n s'
            ≤ G.cat n s a + ∑ s', G.K n s a s' * V n s' := by
            gcongr with s' _
            · exact hKnn n s a s'
            · exact ih (le_of_lt hn') s'
        _ ≤ V (n + 1) s := hV.2 n hn' s a () trivial
  · intro n
    induction n with
    | zero => intro s; rw [Vstar]; norm_num
    | succ n ih =>
      intro s
      have hl := fun a => (hG (n + 1)) n (Nat.lt_succ_self n) s a
      rw [Vstar]
      constructor
      · obtain ⟨a⟩ := (inferInstance : Nonempty A)
        calc (0 : ℝ) ≤ G.cat n s a + ∑ s', G.K n s a s' * Vstar G n s' :=
              add_nonneg (hl a).1 (Finset.sum_nonneg fun s' _ => mul_nonneg ((hl a).2.1 s') (ih s').1)
          _ ≤ _ := Finset.le_sup' (fun a => G.cat n s a + ∑ s', G.K n s a s' * Vstar G n s')
              (Finset.mem_univ a)
      · apply Finset.sup'_le
        intro a _
        calc G.cat n s a + ∑ s', G.K n s a s' * Vstar G n s'
              ≤ G.cat n s a + ∑ s', G.K n s a s' * 1 := by
              gcongr with s' _
              · exact (hl a).2.1 s'
              · exact (ih s').2
          _ ≤ 1 := by simpa using (hl a).2.2
  · intro N s₀
    classical
    have hex : ∀ n s, ∃ a, (Finset.univ : Finset A).sup' Finset.univ_nonempty
        (fun a => G.cat n s a + ∑ s', G.K n s a s' * Vstar G n s') =
          G.cat n s a + ∑ s', G.K n s a s' * Vstar G n s' := by
      intro n s
      obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun a => G.cat n s a + ∑ s', G.K n s a s' * Vstar G n s')
      exact ⟨a, ha⟩
    choose amax hamax using hex
    let σ : RHist S A → S → A → ℝ := fun h s a => if a = amax (N - (h.length + 1)) s then 1 else 0
    refine ⟨σ, ?_, ?_, ?_, ?_⟩
    · intro h s
      refine ⟨fun a => ?_, ?_⟩
      · simp only [σ]; split_ifs <;> norm_num
      · simp [σ]
    · intro h s a
      simp only [σ]; split_ifs <;> simp
    · intro h h' s hl
      simp only [σ, hl]
    · have key : ∀ n s h, h.length + n = N →
          risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s h = Vstar G n s := by
        intro n
        induction n with
        | zero => intro s h _; rw [risk, Vstar]
        | succ n ih =>
          intro s h hl
          have hidx : N - (h.length + 1) = n := by omega
          simp only [risk]
          rw [Vstar, hamax n s]
          have hsub : ∀ a, ∑ s', G.K n s a s' *
              risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' (h ++ [(s, a)]) =
              ∑ s', G.K n s a s' * Vstar G n s' := by
            intro a
            apply Finset.sum_congr rfl
            intro s' _
            rw [ih s' _ (by simp only [List.length_append, List.length_singleton]; omega)]
          simp only [hsub]
          simp [σ, hidx]
      exact key N s₀ [] (by simp)

theorem claimTR : ∀ (S A Θ : Type) [Fintype S] [Fintype A] [Fintype Θ] [Nonempty A] [Nonempty Θ] (G : Θ → Game S A),
      (∀ th, Lawful (G th)) →
      (∀ N, RiskCertUpTo N G (fun _ _ _ _ => True) (Vrob G)) ∧
      (∀ N V, RiskCertUpTo N G (fun _ _ _ _ => True) V → ∀ n, n ≤ N → ∀ s, Vrob G n s ≤ V n s) ∧
      ∀ (N : ℕ) (s₀ : S), ∃ σ θ, IsPolicy σ ∧ (∀ h s a, σ h s a = 0 ∨ σ h s a = 1) ∧
        (∀ h h' s, h.length = h'.length → σ h s = σ h' s) ∧
        (∀ n h h' s a, h.length = h'.length → θ n h s a = θ n h' s a) ∧
        risk G θ σ N s₀ [] = Vrob G N s₀ := by
  intro S A Θ _ _ _ _ _ G hG
  have hKnn : ∀ th n s a s', 0 ≤ (G th).K n s a s' :=
    fun th n s a s' => ((hG th (n + 1)) n (Nat.lt_succ_self n) s a).2.1 s'
  have hcert : ∀ N, RiskCertUpTo N G (fun _ _ _ _ => True) (Vrob G) := by
    intro N
    refine ⟨fun s => by rw [Vrob], ?_⟩
    intro n _ s a th _
    rw [Vrob]
    exact Finset.le_sup'
      (fun p : A × Θ => (G p.2).cat n s p.1 + ∑ s', (G p.2).K n s p.1 s' * Vrob G n s')
      (Finset.mem_univ (a, th))
  refine ⟨hcert, ?_, ?_⟩
  · intro N V hV n
    induction n with
    | zero => intro _ s; rw [Vrob]; exact hV.1 s
    | succ n ih =>
      intro hn s
      have hn' : n < N := hn
      rw [Vrob]
      apply Finset.sup'_le
      intro p _
      calc (G p.2).cat n s p.1 + ∑ s', (G p.2).K n s p.1 s' * Vrob G n s'
            ≤ (G p.2).cat n s p.1 + ∑ s', (G p.2).K n s p.1 s' * V n s' := by
            gcongr with s' _
            · exact hKnn p.2 n s p.1 s'
            · exact ih (le_of_lt hn') s'
        _ ≤ V (n + 1) s := hV.2 n hn' s p.1 p.2 trivial
  · intro N s₀
    classical
    have hex : ∀ n s, ∃ p : A × Θ, (Finset.univ : Finset (A × Θ)).sup' Finset.univ_nonempty
        (fun p : A × Θ => (G p.2).cat n s p.1 + ∑ s', (G p.2).K n s p.1 s' * Vrob G n s') =
          (G p.2).cat n s p.1 + ∑ s', (G p.2).K n s p.1 s' * Vrob G n s' := by
      intro n s
      obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun p : A × Θ => (G p.2).cat n s p.1 + ∑ s', (G p.2).K n s p.1 s' * Vrob G n s')
      exact ⟨p, hp⟩
    choose pmax hpmax using hex
    let σ : RHist S A → S → A → ℝ := fun h s a => if a = (pmax (N - (h.length + 1)) s).1 then 1 else 0
    let θ : ℕ → RHist S A → S → A → Θ := fun n _ s _ => (pmax n s).2
    refine ⟨σ, θ, ?_, ?_, ?_, ?_, ?_⟩
    · intro h s
      refine ⟨fun a => ?_, ?_⟩
      · simp only [σ]; split_ifs <;> norm_num
      · simp [σ]
    · intro h s a
      simp only [σ]; split_ifs <;> simp
    · intro h h' s hl
      simp only [σ, hl]
    · intro n h h' s a _
      rfl
    · have key : ∀ n s h, h.length + n = N → risk G θ σ n s h = Vrob G n s := by
        intro n
        induction n with
        | zero => intro s h _; rw [risk, Vrob]
        | succ n ih =>
          intro s h hl
          have hidx : N - (h.length + 1) = n := by omega
          simp only [risk]
          rw [Vrob, hpmax n s]
          have hsub : ∀ a, ∑ s', (G (θ n h s a)).K n s a s' * risk G θ σ n s' (h ++ [(s, a)]) =
              ∑ s', (G (θ n h s a)).K n s a s' * Vrob G n s' := by
            intro a
            apply Finset.sum_congr rfl
            intro s' _
            rw [ih s' _ (by simp only [List.length_append, List.length_singleton]; omega)]
          simp only [hsub]
          simp [σ, θ, hidx]
      exact key N s₀ [] (by simp)

theorem claimU : ∀ (S A Θ : Type) [Fintype S] (N : ℕ) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (a₀ : A)
      (rew : Θ → ℕ → S → ℝ) (W : ℕ → S → ℝ) (θ : ℕ → RHist S A → S → Θ),
      (∀ n, n < N → ∀ s th, adm n s a₀ th → ∀ s', 0 ≤ (G th).K n s a₀ s') → UseCertUpTo N G adm a₀ rew W →
      (∀ n, n < N → ∀ h s, adm n s a₀ (θ n h s)) →
      ∀ n, n ≤ N → ∀ s h, W n s ≤ honestER G a₀ rew θ n s h := by
  intro S A Θ _ N G adm a₀ rew W θ hK hW hθ n
  induction n with
  | zero => intro _ s h; rw [honestER]; exact hW.1 s
  | succ n ih =>
    intro hn s h
    have hn' : n < N := hn
    rw [honestER]
    calc W (n + 1) s ≤ rew (θ n h s) n s + ∑ s', (G (θ n h s)).K n s a₀ s' * W n s' :=
          hW.2 n hn' s _ (hθ n hn' h s)
      _ ≤ _ := by
        gcongr with s' _
        · exact hK n hn' s _ (hθ n hn' h s) s'
        · exact ih (le_of_lt hn') s' _

theorem foldl_add_eq {m : ℕ} (f : Fin m → ℚ) : ∀ (l : List (Fin m)) (acc : ℚ),
    l.foldl (fun acc i => acc + f i) acc = acc + (l.map f).sum := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x l ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    ring

theorem sumQ_eq (m : ℕ) (f : Fin m → ℚ) : sumQ m f = ∑ i, f i := by
  rw [sumQ, foldl_add_eq, Fin.sum_univ_def, zero_add]

theorem checkRiskQ_spec {N m k t : ℕ} {cat : Fin t → Fin N → Fin m → Fin k → ℚ}
    {K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ} {V : Fin (N + 1) → Fin m → ℚ}
    (hc : checkRiskQ N m k t cat K V = true) :
    0 < t ∧ 0 < k ∧ (∀ j s, 0 ≤ V j s) ∧
      (∀ th i s a, cat th i s a + ∑ s', K th i s a s' * V i.castSucc s' ≤ V i.succ s) := by
  simp only [checkRiskQ, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const, decide_eq_true_eq, sumQ_eq] at hc
  exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩

theorem checkLawfulQ_spec {N m k t : ℕ} {cat : Fin t → Fin N → Fin m → Fin k → ℚ}
    {K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ}
    (hc : checkLawfulQ N m k t cat K = true) :
    ∀ th i s a, 0 ≤ cat th i s a ∧ (∀ s', 0 ≤ K th i s a s') ∧ cat th i s a + ∑ s', K th i s a s' ≤ 1 := by
  simp only [checkLawfulQ, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    forall_const, decide_eq_true_eq, sumQ_eq] at hc
  intro th i s a
  exact ⟨(hc.2 th i s a).1.1, (hc.2 th i s a).1.2, (hc.2 th i s a).2⟩

theorem claimQ : ∀ (N m k t : ℕ) (cat : Fin t → Fin N → Fin m → Fin k → ℚ)
      (K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ) (V : Fin (N + 1) → Fin m → ℚ),
      (checkRiskQ N m k t cat K V = true →
        RiskCertUpTo N (gameOfQ N m k t cat K) (fun _ _ _ _ => True) (valOfQ N m V) ∧
        (∀ n s, 0 ≤ valOfQ N m V n s) ∧ 0 < t ∧ 0 < k) ∧
      (checkLawfulQ N m k t cat K = true → ∀ th, Lawful (gameOfQ N m k t cat K th)) := by
  intro N m k t cat K V
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · obtain ⟨ht, hk, hV0, hB⟩ := checkRiskQ_spec hc
    have hnn : ∀ n s, 0 ≤ valOfQ N m V n s := by
      intro n s
      simp only [valOfQ]
      split_ifs with h
      · exact_mod_cast hV0 ⟨n, h⟩ s
      · exact le_refl 0
    refine ⟨⟨fun s => hnn 0 s, ?_⟩, hnn, ht, hk⟩
    intro n hn s a th _
    have key := (Rat.cast_le (K := ℝ)).mpr (hB th ⟨n, hn⟩ s a)
    push_cast at key
    simp only [gameOfQ, valOfQ, dite_eq_left hn, dite_eq_left (show n < N + 1 by omega),
      dite_eq_left (show n + 1 < N + 1 by omega)]
    exact key
  · intro th N' n _ s a
    have hrow := checkLawfulQ_spec hc
    by_cases hn : n < N
    · obtain ⟨h1, h2, h3⟩ := hrow th ⟨n, hn⟩ s a
      simp only [gameOfQ, dite_eq_left hn]
      refine ⟨by exact_mod_cast h1, fun s' => by exact_mod_cast h2 s', by exact_mod_cast h3⟩
    · simp only [gameOfQ, dite_eq_right hn]
      simp

theorem claimVx : ∀ (S A ι : Type) [Fintype S] [Fintype ι] (N : ℕ) (Gv : ι → Game S A) (V : ℕ → S → ℝ),
      RiskCertUpTo N Gv (fun _ _ _ _ => True) V →
      RiskCertUpTo N (hullGame Gv) (fun _ _ _ lam => Simplex lam) V ∧
      ((∀ i n s a s', 0 ≤ (Gv i).K n s a s') →
        ∀ n s a lam, Simplex lam → ∀ s', 0 ≤ (hullGame Gv lam).K n s a s') := by
  intro S A ι _ _ N Gv V hV
  refine ⟨⟨hV.1, ?_⟩, ?_⟩
  · intro n hn s a lam hlam
    have key : (hullGame Gv lam).cat n s a + ∑ s', (hullGame Gv lam).K n s a s' * V n s' =
        ∑ i, lam i * ((Gv i).cat n s a + ∑ s', (Gv i).K n s a s' * V n s') := by
      simp only [hullGame, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      congr 1
      exact Finset.sum_comm
    rw [key]
    calc ∑ i, lam i * ((Gv i).cat n s a + ∑ s', (Gv i).K n s a s' * V n s')
          ≤ ∑ i, lam i * V (n + 1) s := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hV.2 n hn s a i trivial) (hlam.1 i)
      _ = V (n + 1) s := by rw [← Finset.sum_mul, hlam.2, one_mul]
  · intro hK n s a lam hlam s'
    simp only [hullGame]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hlam.1 i) (hK i n s a s'))

theorem claimAbsV : ∀ (Sc Ac S A Θ : Type) [Fintype Sc] [Fintype Ac] [Fintype S] (N : ℕ) (Gc : Game Sc Ac)
      (α : Sc → S) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ)
      (σc : RHist Sc Ac → Sc → Ac → ℝ),
      (∀ n, n < N → ∀ x ac x', 0 ≤ Gc.K n x ac x') → CoveredV N Gc α G adm V → RiskCertUpTo N G adm V →
      IsPolicy σc →
      ∀ n, n ≤ N → ∀ x h, risk (fun _ : Unit => Gc) (fun _ _ _ _ => ()) σc n x h ≤ V n (α x) := by
  intro Sc Ac S A Θ _ _ _ N Gc α G adm V σc hKc hcov hV hσ n
  induction n with
  | zero => intro _ x h; rw [risk]; exact hV.1 (α x)
  | succ n ih =>
    intro hn x h
    have hn' : n < N := hn
    simp only [risk]
    calc _ ≤ ∑ ac, σc h x ac * V (n + 1) (α x) := by
          apply Finset.sum_le_sum
          intro ac _
          apply mul_le_mul_of_nonneg_left _ ((hσ h x).1 ac)
          obtain ⟨b, th, hadm, hle⟩ := hcov n hn' x ac
          calc _ ≤ Gc.cat n x ac + ∑ x', Gc.K n x ac x' * V n (α x') := by
                gcongr with x' _
                · exact hKc n hn' x ac x'
                · exact ih (le_of_lt hn') x' _
            _ ≤ _ := hle
            _ ≤ V (n + 1) (α x) := hV.2 n hn' (α x) b th hadm
      _ = V (n + 1) (α x) := by rw [← Finset.sum_mul, (hσ h x).2, one_mul]

theorem claimAbsEq : ∀ (Sc Ac S A Θ : Type) [Fintype Sc] [Fintype S] [DecidableEq S] (N : ℕ) (Gc : Game Sc Ac)
      (α : Sc → S) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ),
      Covered N Gc α G adm → CoveredV N Gc α G adm V := by
  intro Sc Ac S A Θ _ _ _ N Gc α G adm V hcov n hn x ac
  obtain ⟨b, th, hadm, hcat, hK⟩ := hcov n hn x ac
  refine ⟨b, th, hadm, le_of_eq ?_⟩
  rw [hcat]
  congr 1
  have hK' : ∀ s', (G th).K n (α x) b s' = pushK α (Gc.K n x ac) s' := fun s' => (hK s').symm
  simp only [hK', pushK, Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ α (fun x' => Gc.K n x ac x' * V n (α x'))]
  apply Finset.sum_congr rfl
  intro s' _
  apply Finset.sum_congr rfl
  intro x' hx'
  rw [(Finset.mem_filter.mp hx').2]

theorem claim : PL_TMCERTF1.Claim :=
  ⟨claimS, claimP, claimS', claimFx, claimFxGap, claimObs, claimT, claimTR, claimU, claimQ, claimVx,
    claimAbsV, claimAbsEq⟩

theorem witness : PL_TMCERTF1.Witness := by
  have hR : checkRiskQ 2 1 1 2 wCat wK wV = true := by decide +kernel
  have hL : checkLawfulQ 2 1 1 2 wCat wK = true := by decide +kernel
  refine ⟨hR, hL, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ θ hσ
    have hQ := (claimQ 2 1 1 2 wCat wK wV).1 hR
    have hLaw := (claimQ 2 1 1 2 wCat wK wV).2 hL
    have hb := claimS (Fin 1) (Fin 1) (Fin 2) 2 (gameOfQ 2 1 1 2 wCat wK) (fun _ _ _ _ => True)
      (valOfQ 2 1 wV) σ θ (fun n hn s a th _ s' => ((hLaw th 2) n hn s a).2.1 s') hQ.1 hσ
      (fun _ _ _ _ _ => trivial) 2 le_rfl 0 []
    have hv : valOfQ 2 1 wV 2 0 = 3/4 := by norm_num [valOfQ, wV]
    rw [hv] at hb
    exact hb
  · norm_num [risk, gameOfQ, wCat, wK]
  · intro n hn x ac
    refine ⟨0, 0, trivial, ?_, ?_⟩
    · interval_cases n <;> norm_num [gameOfQ, wCat]
    · intro s'
      fin_cases s'
      interval_cases n <;> norm_num [pushK, gameOfQ, wK, Fin.sum_univ_two]
  · intro n hn x ac
    interval_cases n
    · refine ⟨0, 1, trivial, ?_⟩
      norm_num [gameOfQ, valOfQ, wCat, wK, wV]
    · refine ⟨0, 0, trivial, ?_⟩
      norm_num [gameOfQ, valOfQ, wCat, wK, wV]
  · intro th
    fin_cases th <;> norm_num [gameOfQ, wCat]

end TMCERTProof

namespace LasrA2Certificate
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((1627 : ℚ) / 10000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((1627 : ℚ) / 10000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((1627 : ℚ) / 10000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((11 : ℚ) / 250)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((11 : ℚ) / 250)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((11 : ℚ) / 250)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((1627 : ℚ) / 10000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((1627 : ℚ) / 10000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((1627 : ℚ) / 10000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((11 : ℚ) / 250)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((11 : ℚ) / 250)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((11 : ℚ) / 250)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((1627 : ℚ) / 10000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((1627 : ℚ) / 10000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((1627 : ℚ) / 10000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((11 : ℚ) / 250)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((11 : ℚ) / 250)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((11 : ℚ) / 250)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((1627 : ℚ) / 10000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((1627 : ℚ) / 10000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((1627 : ℚ) / 10000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((11 : ℚ) / 250)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((11 : ℚ) / 250)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((11 : ℚ) / 250)
  | _, _, _ => 0

def kernel : Fin 8 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((8373 : ℚ) / 10000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((0 : ℚ) / 1)
  | 0, 1, 0, 1 => ((1 : ℚ) / 1)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((31561 : ℚ) / 50000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((0 : ℚ) / 1)
  | 0, 2, 0, 2 => ((1 : ℚ) / 1)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((31561 : ℚ) / 50000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((239 : ℚ) / 250)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 1, 0, 1 => ((1 : ℚ) / 1)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((4687 : ℚ) / 6250)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0, 2 => ((1 : ℚ) / 1)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((4687 : ℚ) / 6250)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((8373 : ℚ) / 10000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((0 : ℚ) / 1)
  | 2, 1, 0, 1 => ((1 : ℚ) / 1)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((44829 : ℚ) / 100000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((0 : ℚ) / 1)
  | 2, 2, 0, 2 => ((1 : ℚ) / 1)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((44829 : ℚ) / 100000)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((239 : ℚ) / 250)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((0 : ℚ) / 1)
  | 3, 1, 0, 1 => ((1 : ℚ) / 1)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((56699 : ℚ) / 100000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0, 2 => ((1 : ℚ) / 1)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((56699 : ℚ) / 100000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((8373 : ℚ) / 10000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((1079 : ℚ) / 100000)
  | 4, 1, 0, 1 => ((98921 : ℚ) / 100000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((31561 : ℚ) / 50000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((1079 : ℚ) / 100000)
  | 4, 2, 0, 2 => ((98921 : ℚ) / 100000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((31561 : ℚ) / 50000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((239 : ℚ) / 250)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((1079 : ℚ) / 100000)
  | 5, 1, 0, 1 => ((98921 : ℚ) / 100000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((4687 : ℚ) / 6250)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((1079 : ℚ) / 100000)
  | 5, 2, 0, 2 => ((98921 : ℚ) / 100000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((4687 : ℚ) / 6250)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((8373 : ℚ) / 10000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((1079 : ℚ) / 100000)
  | 6, 1, 0, 1 => ((98921 : ℚ) / 100000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((44829 : ℚ) / 100000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((1079 : ℚ) / 100000)
  | 6, 2, 0, 2 => ((98921 : ℚ) / 100000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((44829 : ℚ) / 100000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((239 : ℚ) / 250)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((1079 : ℚ) / 100000)
  | 7, 1, 0, 1 => ((98921 : ℚ) / 100000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((56699 : ℚ) / 100000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((1079 : ℚ) / 100000)
  | 7, 2, 0, 2 => ((98921 : ℚ) / 100000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((56699 : ℚ) / 100000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((1627 : ℚ) / 10000)
  | 1, 1 => ((1627 : ℚ) / 10000)
  | 1, 2 => ((1627 : ℚ) / 10000)
  | 2, 0 => ((29892871 : ℚ) / 100000000)
  | 2, 1 => ((132699747 : ℚ) / 500000000)
  | 2, 2 => ((132699747 : ℚ) / 500000000)
  | 3, 0 => ((412993008883 : ℚ) / 1000000000000)
  | 3, 1 => ((8255636715067 : ℚ) / 25000000000000)
  | 3, 2 => ((8255636715067 : ℚ) / 25000000000000)
  | 4, 0 => ((5084990463377359 : ℚ) / 10000000000000000)
  | 4, 1 => ((463931150364229587 : ℚ) / 1250000000000000000)
  | 4, 2 => ((463931150364229587 : ℚ) / 1250000000000000000)
  | 5, 0 => ((58846625149858626907 : ℚ) / 100000000000000000000)
  | 5, 1 => ((24810881036645449995307 : ℚ) / 62500000000000000000000)
  | 5, 2 => ((24810881036645449995307 : ℚ) / 62500000000000000000000)
  | 6, 0 => ((655422792379766283092311 : ℚ) / 1000000000000000000000000)
  | 6, 1 => ((1291493716397567047301884227 : ℚ) / 3125000000000000000000000000)
  | 6, 2 => ((1291493716397567047301884227 : ℚ) / 3125000000000000000000000000)
  | 7, 0 => ((7114855040595783088331920003 : ℚ) / 10000000000000000000000000000)
  | 7, 1 => ((66182708183223613579894768088347 : ℚ) / 156250000000000000000000000000000)
  | 7, 2 => ((66182708183223613579894768088347 : ℚ) / 156250000000000000000000000000000)
  | 8, 0 => ((75842681254908491798603166185119 : ℚ) / 100000000000000000000000000000000)
  | 8, 1 => ((3359886202970720468195058775636319667 : ℚ) / 7812500000000000000000000000000000000)
  | 8, 2 => ((3359886202970720468195058775636319667 : ℚ) / 7812500000000000000000000000000000000)
  | 9, 0 => ((797730770147348801829704310468001387 : ℚ) / 1000000000000000000000000000000000000)
  | 9, 1 => ((169596055951958908696704250017857885010187 : ℚ) / 390625000000000000000000000000000000000000)
  | 9, 2 => ((169596055951958908696704250017857885010187 : ℚ) / 390625000000000000000000000000000000000000)
  | 10, 0 => ((8306399738443751517720114191548575613351 : ℚ) / 10000000000000000000000000000000000000000)
  | 10, 1 => ((534776328309298474213527277929654105162235511 : ℚ) / 1220703125000000000000000000000000000000000000)
  | 10, 2 => ((8530355496899775117376682834813612708806511907 : ℚ) / 19531250000000000000000000000000000000000000000)
  | 11, 0 => ((85819485009989531457870516125836223610587923 : ℚ) / 100000000000000000000000000000000000000000000)
  | 11, 1 => ((863914835274236470288329128536036428160723423191221 : ℚ) / 1953125000000000000000000000000000000000000000000000)
  | 11, 2 => ((428113268587653802479525486949552430702642322296827 : ℚ) / 976562500000000000000000000000000000000000000000000)
  | 12, 0 => ((881266547988642346896749831521626700291452679279 : ℚ) / 1000000000000000000000000000000000000000000000000)
  | 12, 1 => ((87267898020275611198544975389924534613130366450908928791 : ℚ) / 195312500000000000000000000000000000000000000000000000000)
  | 12, 2 => ((21456018807394941660056303893614824265406094334010156947 : ℚ) / 48828125000000000000000000000000000000000000000000000000)
  | 13, 0 => ((9005844806308902370566486339330580361540333283603067 : ℚ) / 10000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((8818347780157383948711422406681848952843296604874354527747011 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((1074390206455191753733037007186377468640481743275694563404267 : ℚ) / 2441406250000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((91675938563224439548753190119214949367177210583608479991 : ℚ) / 100000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((891298895108619096453453785344769118174567250507431706452152700131 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((53769669149682306939568380983809259287762244299524196115602070787 : ℚ) / 122070312500000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((930302633589878232341710460868186771051374784216553802964643 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((90100176786432662184668677918422580360180433593299432105638729280908651 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((2690066520220623289319717672230004032381064192337283153604516956108507 : ℚ) / 6103515625000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((9416423951048050439397141688849327834013161068245204992222955839 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((9108853599930447292511935598383274901099337068390910145470101590173327165571 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((8612548338648377687386722842823233288597986718893454466048781686980808304733 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((95113717742125326329072267360735421954192197624417101399882809239947 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((920901284777432367294662079535227453548093226815415535364517781413803274670448891 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((430895173620880560921301194422786306879843814458226600641486886436812779162072101 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((959087158654815357353322094611437688022451270709244390021218761766076231 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((93100923285291692422129271016622858375567128942087916509935525001521998050081724746611 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((86242815425777101458103011290811398948100452531778300486771363272577407588352082959431 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((9657436779416768987119365898181567761811984489648503277647664692267356282163 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((9411756558122414851906682926845846114263269891981699628304506881946181837324829606159506731 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((431584072047906319473024273166264522976614089851227706218306522888163598597170728971573361 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((97131718154056606729150450665474266869651746131826917943743896468354574150550799 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((951372664011399848270737926736474802092074286735367675799834012384147623507458447986529565337251 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((864009845147232906197027993395667725504682915856914172435362553938020556939088004756986276632369 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((975983876103915968143176723422016036499594070361786783942967645129532849362561840027 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((96157710372613619520882505049684111670256999152450892663680139407203723813193100104388772382726206171 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((43247624498138863375100166178820751693053043437434634286833260048732713399368036091971652435874733839 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((9798912994618088401262818705212540273611101151139240741954468092669578547712730286546071 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((9717697844784180085067891657912840155725496910409666616440633947076321036852648918197556791934159040641491 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((8659950695452839103319599300098864312949207521834437429759776704981750302352206351520491146619290668633947 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((98316298503937254183773581018744599710945749938488862732384761339922381179998690689250252483 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((981934832099975794962505952455920144941448399683383148475410026991218150264981422658862723635622071459296931211 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((108392047339926553406408292182995963903659546054214551908550789432799384007218326585186708561652976229598854997 : ℚ) / 244140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((985902367373466629280736193869948533379748764234967247658257606699170097620129037141092364040159 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((99205914707523977044429248469751948202442674648666457767997034449642358011370402843136207579078843587075111732323331 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((17367501080627774119777412258194617559780614093018006386394197710195821461432053525622989611964205741593953614008513 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((9881960522018036086967604151273079069988636402939380764642590940892151227373340427982366364108251307 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((10021319510344692320124859584982909512570696841696033430630390105267369457649826156965259340867427731984869627673156225851 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((4348548026976659294871723074531605585132863139711541078337085479311284189112934749354251372501691026525765736407928723257 : ℚ) / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((99011655450857016156179749558609491053014852601811435142352413948089982226796979403496353566678388193511 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((1012144407054794537393286166410828087823704610634389088313750842308666405632553129682912320247932762348044429064056287017406771 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((871138442504778151229426160003678471537919691179000730092015856321486578187285399105109314867275510592722219150676770034304623 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((991724591090025796275693043054237268586893360834967146446916761987357421184971108545474968413798144344267603 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((102208930176038321066928877074043877635886086639293983835525919233148188941708919797151896301137279847918371111976761968048895194091 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((21816497421556820700903355236820290397441082761498109261930709420507206213135495947951095232383320058479053644891053375563807379423 : ℚ) / 48828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((9930710001196785992216377849493128649878058110271179917200034048120143687581763091851261910528731862594552639919 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((10319607791667741804000240354013276062745514517137187977926915547513884548587667708793236072074818085958484896509454833141364761494675811 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((8742722401411234390647459471888893129590198478884416073756323293196540279106409503130208062039288738975129784854894490020114317034034521 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((99419834840020689112827731733805966185428980557300589446715885084909963096122102368070615976857071885504189254041787 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((1041754117850368069973198150472634558381791277293834418704076453379374166866193650812370689082315622224340538936816080377301943571814825899931 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((87597369947721021056375359776070152214389443389371634826023239836206244237741122791693121342675721006290801865096471961223926093297648405191 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((995142277115493229941706597807157354870596854206277835437352105815951121003830363127855267574224262897326576624091882551 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((105146554439383727106708209292528026851132008340037444064129978876120326846912846594025134111255274536453580690549859427881991810067494392847074451 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((87776247019145658386678150448446327960490134083400362224032147571569923588464519025997300536908068533012987554484905579489428727864954976045014659 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((9959326286288024814301909343439328532331507460269164316116949181996958736165071630469532155398979753239315426073521332599523 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((10610920772051327902542038517331227988262972757490893571540634242392083863656890104532043852691472852199082346149530132995305332156186612834825451767371 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((549772953976312669676045467396087309322000999416434227106792519820912640247644853002852005382345468036188197215144040196959903022012002352201930525973 : ℚ) / 1220703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((99659438995089631770149886932617497801211711964833712818847215500860535497910144761921392737155657473872788062513594117855806079 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((1070631395768075303491563648777553332511308591717253613258125353656071074900869851595407718537396895297044060202389954500627984146987760928233768514280106691 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((881594629597696592359228358444814038606402321417702117037788709998813047063882208485112046907886035905247172359003560618677463522843713910163451375413395437 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((997148482705885486811465003286806309089545664281552677432207735388705263724001642091567821388204320028736854447426323548806664299467 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((108008173118658576172470056138230100864091536834271342648426083451305732538594045148226225026285317858083363024582416846445027358070602080031812615201102433980411 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((44181716815233748932617312811375214779381813003711713884100307119193743059212165257713606860238422903904233038941684990433185482018911408874421504867088362571533 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((9976124245696379181072396472520429226006765847029440568139875368409629173161065749232697368483434771600613682288300607074158200179437191 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((10894417745578569240172060958122216059043130901854790513263501942196851278520222042415655483809129392939270421322836984036946830736749859022889435708308253871776236531 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((1771508007390901592003393918360249104242962283304902335395164941023897479945959234726302301049330384424618644318765053930919293330588730119777525035543297070828419051 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((99800088309215782883119175664413553909354650437177505877035176459693825066877603518325375066311799342611938361799940983031926610102427600243 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((1098710600273476071901546996323270123711881529186410479184849277035214861802656677516045307013479814691752331385155022053842678181578807665905198994701560781249977093883051 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((221987948685764039530746075691096219832949474594280634640484218562688803899548621718892310469383526350829994339472532651319550677035197989694565117833539263411184190984201 : ℚ) / 488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((998326139413063750080356857838134686883026488110487256708415532497016397284966174258938365430228695895689759903350905850926321506387626296834639 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((110788760181950257558004289613565731733253690323291772902876525243756927571864213192585676402903687364175142558349008536601676428015201752272566724911123094042028984104005287971 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((89022588225472938899265499422788525111865900075355475544125809907679953518074063391257997862035095960654216245784431878400821339849918814825816013800129133986559730709692400513 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((9985984765305582779422827970678701733271580784949109800419563253597518294467021777070090933747304870734610359670757134689806089972983594983396432347 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((11169724380417040448664230037864970773618544859195192293495054292615077605123582665650602558010076431749899208837824231928305195831276196125282029143566020085731549136552307091379291 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((4462872261044166458379664548447350558565533716606535409631336506307811203405722955380716175674553403094910352034850183027140428312561110886043322698650837940777912197690851828433591 : ℚ) / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((99882650439903644612107338598492769612682945912378896358913003122372020679572373339407871388266183682660892541523249488757746391343791640795978328041431 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((1125964988173055784431293267115410928526417020678479041620005337458353674275902414027922138682933016712011944829018182230037496970342956383993173508235719663525650572136890769786330845011 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((894995706475969967102858297804777032672456731463941790996964040662681652840123386634668649787897866844961395113614842256706157924515662315535762358792386815551888046533893446792556765611 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((999017432133313216337174746085179959966994306124348499213178575143620929150059481970862107133952755974919653250174167969368610534721567408384726540690901763 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((113486531419767164387205770228428519507872731279087716470843859126738104795727374550267435357762604684325009825921612022314445651011497759953544588013590000792652130246353371838033633519333131 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((448743932512740761535916055561819386204360481492283323965593328127553476975707721170120927466537648056013435272522022147509201536410069409267208912547440188490762472092574893953829793963863 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((9991772959252231560391164148971211804803643325179169983911944209677538039773448042542028423032586425778002256663708308407523376007223683910405315325204920461599 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((11436736293573194887180338940326125464332885258731325850748872670429959865778013668872661264743503177293922559852674971773224452221631137731436287303666844867292167938599521895590125061365952651651 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((9000491677020494544752665452522621473093303314989767384072132046338893914257386534313645015934499987124167691720799609942828831894085501289814189178087729787994214548909735505174597700307218812949 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((99931114987818934855155217419335956441620905561725190275294708867630026007023080460204403986051846143039212895045229666296193227308483905381823705217940799024968427 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((1152390271800915647867700031200258347559974770702141805600368662732856090243790074587581526275262704272604739392678924290536397215387447125022282677998637549355817374732328305433670761195381402253968571 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((451338937821654909072373002472801064057938920208136939996378703883641825793714705054776840062957456577304967337397127254848940031870985935350964580843136421984991973299224415016359062026652127553429729 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((999423225793007941542214635452099963285691842268325018175042597348666207756804252693291474575212107755667329570213707995898025892253935739762009883789818310236060639271 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((116101568254003076621250295403459652424771454861007457839041001901590857265146151402195350439990690523810085587841195830875666427307909120607200079828001625843028781868338054551804145368208323692364825011891 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((90537227239785038504745667888888986872367964629405839491006353320836217820053154167927160058586637582077309861770023009663312766380822654869604577612728325914109708928801338957229440300806726752457676532927 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((9995170669564855494532963142640432992591097795312685377179631667600382157547722007800929516618250978238202550491399377049654170795842203949027308756972148711606535732616083 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((11695503870096163258256178907475322875242313472596250513186960683978208808355520839078453272801399930170732524990749204451593589659190911842866715788972235930944951191700487639631517863968535587972420855001269611 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((2270326661983211278400568820494280108841959957225120523824541179475564009491642690202122845820049682832965162796358274110104851559555647945872830827040778120508568643145473502962372534212099749585981866625375539 : ℚ) / 4882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((99959564016266535055724500393328345446965261840153114663125055952817999805147076371317182842644615440788469955264486984036754372073586773665205656222127801162281523689194462959 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((1177994979647181938870352183141735607889903083446799922643828319400552167648512242638138275707441760628198369120196269100111903643396968210058609928007744715485598196630088222091005003621631508897819843397580591189731 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((182190276719199746327661818041924920793881707990319188730543696527524311367181350643060485441362649845346641574075849144917199513546696799138639675860620858480960415466043672741865164320480505442920378203268292936789 : ℚ) / 390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((999661429508199698021581241793338236427440137387602029074346093492945112368496470457038771941463365085721858935429549517339744357372142055898766959547876079131783197849625238355707 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((118635011099912314093062989869587090660602015369311309419754671171177697182789606417379370908115485857410814760053981648460287939985569151072535035951416534872701284288154348141151044244505410491681236728732069661079380251 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((45691639199869549922217141759118104085085533803795459729301627888814678906328738322308741300606751543237750848013238570340396104714494649518310058495681368128492193372873197974063206998819500396348190636126751742947121547 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((9997165149272156071534699737535621053606956270346391789439499840816429425861420947136785637465872755862749124866351618108685679504276945434040375752294366410570420715594912120752334711 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((11946164769428361075947791473993919118109522881926007826098118122798851751816700908683730225172949588010211356447918763164763890217875872961667091718957918462037638834959091591257093043999782211247599618442905062943633373809171 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((9167732459557396882617698725976728419224281753393988246628407954972574439446120232486558337604497548057389372398733391431973296836169479564008763896694171674404797207022897775228914975800268935334842786262890721492449072392403 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((99976263794855762786960040902385755081851044851610338452976932167155963582737677590376306142501752584838798422505962098424025194489310864119220066173960729955706132651676199187059298535203 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((1202794809680186688027397771447391799482593960299299020049837138778980775372913919810482558273914746007229809594565027822465499112729051620106948437424640981396126607036986170740719012632785659243823801855990611731447156970577004491 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((28742849200565326832074157583524480958953917203658902305909019149010687411395621243696018194598003579901501005020700317478031585433619036089904678918426242194510486150588529082824559428612942761193566976506603363239710471889656021 : ℚ) / 61035156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((999801256754327301815216422475675927300338798542533363866775853035596883078262574464220811331167174392855259191642420650104362953458999865270229614074573191919127448692484815793247506635254719 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((121088587021394242836028720498833268996096530220885855924669512062350113622573665402979308317477971196012450766347012685667506574934449546999799416132422434497682468944923650771679325275200212795714544303396447303086484214686447861254211 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((92282499944256847694161009949626141541743493081663496442724208936399678958152694089000432786868085599019765153917421940388259872348363564107678141149249741350867918225068680411096059598241044874485008726458924631499364269244745811952701 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((9998335922803982498098807105388834539285736760196631855656514217467052702014292535988920853275862751191377085211621988103323831009312205871907632558646401335938854127902175362636861373056987762187 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((12188904420656995981258308490123533912823229233876225046817250604560635792166704343970087692336193345940491943950739047324513583451196593961936411510732715985539141752129540722876094062825314594066636249536279963668618105000998108883127806331 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((925933176238191601877417625464520864469759623523957057015343987571286841481817963694782648538433662646113162316755372245298229442692674318630841297063181747099220472273359155412867530348954342963550754153340805011257892934560617770646642929 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((99986066681637745456581311893420711597439473893126398527411993542851632273965671403835234304478798815725400334476910906389130437040971099765482607413546318385816025612924914311358440276606158532791751 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((1226809326033126123515663706156811958479232967568200069130141627601881227152925337062857321177425800545137793968299768482348142590253646142667673355886744644570904206113981390066933080127665776591305906081003350286063371564803733928827885730068851 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((929094185136470413156938004146601977434067181529486007195664239347713582481977021853659668380734716046431392102880429210834611703549861487617743907487950616596416617328077384565945995190277640049971942029275903805984859205092785664386260554827239 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((999883336325352842707955324483611618205360714907147334870020621934296717029914566664312416831400982484068777000575175019196189149344051018336385871873623323844437582457020307529004220436023365395065331123 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((123464333581723789720301782670741920506709305797522578882389098167301335668530639756749952384882227926705413743718270985307865920622965457747714770205626113812518248794023535558333660599356834978705803944208463663647674778561950163973583284304140809771 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((23307663287668633206792716361782303578238613009021093298098431259174401284199413854369172776360275321204310854475207597039356067545434883101143316155904340103956533460276932219632541145918801451081323387534851073837622658836351669903989642261702399837 : ℚ) / 48828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((9999023175052179351993709931901280079233485265917544634866682667455866411691474666680287866129320426339107869825815940435729691747457739176530558905197848090549475877912631034940352337710823638452882017492879 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((12423932943779702072703590572306410138765203780082827114360115153844159597087672114094413816771396130475968070907905985279380164126940895547577505352993482907266115374787806245306509109260397240753024701551318285634191636770126672170430832066649913043357091 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((9355687456252555430904774804397199541278506690817029143178877511277681938923505431849744959464627104128321677571640057220067753559000036013902576146884723486497644176144969043260524430568441058311685925729140944593441725225071318381217733972443620310846417 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((99991821044711897714243333259809418103421972131527601227738733974607969465092717384114050303100799929737350194051556869268364709001463650125090369713221582062170761525762459655555570123652726324765981132467875867 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((1250060030899368825766726752176015915316271103211458166489423885895497954976585982661903881449221278068164599635136544922419518999576719743640579393466258318938622345224282489573802375433846932612472651222616581994547995900937700537771188338865076048161926798811 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((469439691253148667158489201326646996181269407620510355164396153272048711642754839517558246821748357096130639107786918329191386723451405894413546431650931850032386799018916262833530030262576363276011398556013111905163570838532123282430167165044005310471510358623 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((999931517607372719561359429384384257779952172657280605079856419569392528331221322657186943187862997811690833174793685666384017708469255142497381665608804306606555786255209074695966788645344277517265560022153524634391 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((125764437826503575676827966047850044619422578565036869727236434864297498498239546406082941127874468108800179908542139618511687909289405632793579373495930545555326723740179249986449332517858394524560408960536455650851686208766658274896863721668872187760225960865182931 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((18844740434049171514194423746892883238224191732564434609615310425705980700449127847024990591158409644729645501073818365611034598628323265113190607659246750360048448520399486415552276202060350740708301020757589875502697693882796822664560848896854303138054254277321727 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((9999426596926531780887262502235449390391539541659410506333637801054523639717316134608626275311976880677287346172547530084633380273013073308130576686142518459216691598314865582429329921327467635652064534065491461763755843 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((12651471709606332702575684156041591180623011908743185192803807927257144438411031476119549508314318731399766035989850584381315842781738842706799187630823738435712161107338476781580833360465540259498635827922707911680186348527719103211072656211206505685429312274744760717451 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((1182050333849710979366678791587198089023279164269588370315558590790610448153155168668744870602110219177612713397491612671427484863585637152386739080662981002560745051918480173662451550088353623225003738455028322002535095287769993344077354328038666961773826031076030645673 : ℚ) / 2441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((99995198896065850601369048931217417745748360582314244169531549308229526435353087995078027803187182421910926949502740469398635293025938462808977318593071307059021358752690369521680779431274886513314736343730360009347927673439 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((1272569243333787818114413776305868463624175506269805137957997818322473186178102535487586620488252955756629836215136733846961721470754929282249815432293456782567627240138446922576853802368409242343592245421943488720462378928407767033742518225068758748908352999530026474930970371 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((949087746572643311305529025145146654198066615519229506262918279630294267983111602481780284678121909841329365328779191317109665635887534713290625256239760763806625112081442034518232677486262548044323786552007454963205114357753373005080555135923195615839607386505025816819080293 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((999959800356759367085263046701083438785151023155717166431487662357805824843211405782788326796086278418660191348186445950274773308506182749099567088579786054005185836836276464005033166178064624775984287406054304358270198409704747 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((127991142815307075005673995552608743855551098089080961814812722141425410265231619622863829366561419265957085695786631805251884970725247336118709119853719865347682489497011732026543188597490598211633508050690420645570109258626256773526093645342026684200763187066509748926646520069691 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((47628905596134803026699844580508542126088716522521410866445409392639143925521777732445646752075661191337772870482149460050338465917287695034484745911969007192452816252158855863019259971187045543790644661160703238372296012123536695832490885882753812102270957583478278696005379347081 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((9999663408387146180604907490028171632948069516882819834530846196921908171412209100619286660263630409199441782158365111941650676912122268158210675232678548630185421011830142833114142700408935103249316438450892690391796371284457846631 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((12871745554172237916066941147534310533444575243207676812468162565796488416074677260892927826608094243960423363656794790584733135142213397046018831268600133181361145543132792525176864459702783819234655876075927685524693423301488145905888771990878621627823695227806210873572800411813903411 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((9561100384048218034339472892698235825929783489086799326437475612249111530189264467715581716610672732804615355707683189193145846657420574036684618241037936055679399479126888020508096531716279819944981276240050813962621935520602478035526316888139826486190114269075273632866947855940395791 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((99997181718425574970204890414005881082674186064859850474526775206827137119234426799485287206387377416226926042011991082287441117785199751288697983723217487680542530132053785941664716830524013619506526539149324496650511016764765549841363 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((1294359451373744077225087368032078245544400060072246134297137294808808217553698488425508474290634558698071144405803320830575044821536055369780457945765061262659929919818654446173899827916972439464554386958495344948797472119796997194661987667234704130045947755629818185824694989537043139319531 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((47984111227169281044316561375839585360119340460568817972558733622389438633939840358769826405687724554549932620567270516860805367500857442984776671998026660813327527595787558650567362688296270990486584325861399627033883434368791171959237638893491890428841703038099902228470820025091354691099 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((999976402528377339225525547436471242305230959921071528023212688806763619099349855592090309779081511106068051749766401331992744479215477517540268217714500024349182604795686349689558674021977566036128146712297294010454728743371381948821732399 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((130146693771259739335699490126005750129220360974515718027799586903222869269716399316442939115297845169880271714815902690072488793285117948305156296164692649952788110997062484341668661859018100424418644319660031321037141251029024345982979393690680417248275197934657244759964653059993844384627326051 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((96329339182088518863022640627295164895109713218816514432176260914306417248899699631608523601300302702047896459996561119143945028533483786093934977537816407388713511529542349932877119604101521715180722345498926727316128136641164790400635214232608471618548579752962182389356085647751707495289857529 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((9999802418370103461335325408685573711821698827419131904138359843379031782718856340872572163780249492491107797300794078352775249524471193254364665786923508703875705949954281805950674777586018160420500972422065242749537443768248581057484365376827 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((13084978309063995446120546072458511775416854243146560784187542328870603580914029705177138199804774421441024684050912884035367728626235570580197871716445441611579902733912008945459673240628920487426296064413560423198408927098139328485775009536580680367116630854894229308900463445347651080371719720290971 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((4834711421905283816596141191669312605489288355405025441948651830086341288310215591060394347234816809263790389449803090734713200787757695935209702778290020102298993822889844609157399017251603579972669976180006252294118893407270489750268435396448053395594666498157133605616747604506490007616290440717619 : ℚ) / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((99998345649012876281760679646924308689083084281980391433350486968612633116704984142126046727332029000628045586799548818047787164268397301118795346633910538377551285918967201561224999912727730057200854642089952277541877016671545369194316591300172471 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((1315452941673070551406121819510175736373228632794865867700907457274767522322818697293565003028354671016801011586015112797253713611242302817835354203968926220853396118341311145621591293833548977902114055935594842648457369832603830003299602902433715320486169240796992057465742744477234992521450886450903142291 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((970627668728065211929377834854422878700886572538396182572143533540793314425675911018456670563219978779101683863618878079011290849439266259869791520644498788577932250958063694817069123797730360674885946880907028663004153341820100568608759030994046334007358854020834500226732179628303111602543218950649135907 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((999986148119184813107182170683697236653692664693021817471443627388193577086170832222021389247951078822258625698272622253514121926419290602267673437365732937835236916999512378672136924269269283768942755918219170419858136260590849376264012818956344099683 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((132233307454087220091973487705794049663782412239784067951118520788872845090010483470003189063372389194693552187181386777209977618790934225478778186082255257546737583311240949415810029543438053535471425350619334041102029709745937011767350557813459734784394378718879251316568738026432562695214443138609789738568011 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((6089677083894636372139574390305365325219819646053521815466768101736768100805538010514781809190742388177165372560897084072632041193994506402063999637484808503576153163044555842570311987577605272217298363610044438599419959673472856307556707727293002264821657613088432751683381897643894291235363954268605478974271 : ℚ) / 12207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((9999884018201934440146436315134596962501368681474671677688397492121344820942508378194985092173094382978771472971636666128673742889908720212787229691063281888494438706036917146621802466906591712997357695303249113925472174909927181827458579333121469146645759 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((13291390274990097916949095619955733913031124373281791219591752943774813535257516552517349738579762301772268582378567648773454941645333319862306298906168871128641027821200499132276038413186463341670394108053099221758570077993007820781074973168460151847176989813812754419486296134312735534373307929714419010728886216131 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((391241235511920852142957632217956178918573507604915756537754702488065567865947012810970285702027906097401934236620508943575636488075740284562750727720676371784361448202292684818640973433919932715715664431201022240057625574022784029459761784533821611457885304741872176473557071979193096403233255506793420979909466773 : ℚ) / 781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((99999028884404797067346111266621980367023959969987425957284952201532020185751622650626610176765319268681253543191513805495385249217205714341667474203272859252363935285647107268664352055408892412926875982774104830897978520520820293441310684756226061164864940107 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((1335871591719717130849001965915450197619035793206187699585239271259739991951280995165147638088593137042743671100236688749070574893002336687828883856668727153177403604045923468416231364741506055179041408987002280056840417866255333337125006106540289776986373864764749604930003899902350111795741993715280042960312153385894651 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((490945383279291190511612936294871658131132915921708920768860162273440687388113235858508005583092563000069848107952454311606348153979411134681112557470590948139912069729775102718672719387124017774972543136280101042748003299676075456538753641622761347259370388884186200621072095730133724437097360477924829015708538646751837 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((999991868849121365844888989635425841613091616828704717540346904783427605015298336453696607010056018236668135917142545093412860691695663446182781761504003650520043230146723229160526619759938656173436732603767579749108774152320828316984094363463880810133414143515911 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((134253155134003653457660733901116880186485507918648051880044705191063119622336612651638329514797850215087025450099944022827465039848210806984507332576646912921284220942647366293086570407137219603771191530618355262544486734022100959835164100722337003466708332638414362075530915782240375408946593760309217129677038525086084771571 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((98571021966207102497384599663672769351210537972652212830605305398191311925554531002502135142067790843928939310490684853077070281789144178993748036276442210960174902188243717294488761791543474958174303559464903210680681279692203625143297979554887323133856653877706331126993619771435752080711821602892391188479985516454057264183 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((9999931917873693196219255510217420571826416107706744599965324633751639336793092971126801690495199040695622302034234530067145882571567790034888431689073022565804321966018513597761089387249966368140185762091345945239287765977382295498107822105283074023247076623658722803 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((13491196832934252347776397149602817374282904384788976984991924608428068603389970002502078209355945180907358980224062501384418887309625568436626797799068946292404935842783306520348769799744611097692450473822068871424071056456503798609187439456417097039097042836372569136068906220095000175828406001363548067684782327940040591688574891 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((2473900804577190682056149478802369782678078872459237698348718913048909968265070241587407866983738704613593376498426718987966926030715037697744208227088035492358381793440093316679590803662643286572507349516841223958007293513610580434615580375057102629616203087288359269523208429884808349160586869861772968509637542960429921024692913 : ℚ) / 4882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((99999429948356433131943826387050462447902582069828572535509663158402476166968567447244710554516301567744445534932645720252212474771737105962120838532608417943479587821473014354053601439443968400437775385990839599488556464528621960205656794487535178796647772569894486029519 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((1355636757182926901023140108794306775600581182655943941987391223564957542371407479093769443829036015281377827338789289546991949203302974069084490359207694922418533313584697886510327328159057599612067823862547723023330360123174428466989857143881517759468353722223310446478675787823017512393121750060883538403446352662156755370425516792611 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((993439967341057176121956182894858325036044214401348315600220781043338777906053831104971636827488730446524121926065241315028493138944534964737339602952297628807838867329913071652503530170373781578566152147475815172866730596556056507389744552297568644602243411611053151299839554182023012018976505089857043636799301680602056669166562894881 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((999995226957588414613765658338773522076288319670674637839822409625303932946027815235779961472964993026724242463991042615671775051263754788220837781033530283440754588829193549186490804852464347416865493306901299966517683277498151672801964340244132052064331799727726531525162587 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((136208353518899276650902374512034344162100850662738025797948300010408154732206356354192131268018382007328790447481006653702837038004751941976444534588354008228396047883021457883207305174782293879664274478554819948406646780799740433208531464804357728790649935481890298739121989970521965343439996637772660502407316651693208397997862546641872731 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((9973480707034509504536399574553133738176355682888154024089383501181470443746349969667707651650354256498921934074685337954513788298789625226732453596122933656058982604050021998048194489506716799751476351852814410585732331591482687408338297671607594555516487418625594075148191971430093426780135322830944195153314233606930318681531470074375067 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((9999960035315887795561059857270550700344762100602558742632833035792669830557090896969185617413135886612762082150996999821019772504231418841773074740593749063249438172266837587338487509029683980921414775458684584619652562082492023956370847420864117671934650159120254248460186340951 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((13684607720061636497804275731555640106968614790776805502737978234545542680445984198131673914513124731288345392671410521492170734292779315175785128393072219030740965101336892947681199752857883244210659904145884332917871519534823253404154211249271913562390783442004503235228086844751542396238427907405109349558634170502143867938346560976360692423251 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((10012835663652499466488775485242190482492339622934885172005445268914952776614377512001166395727238768257206331298851489337329945687052812515928594074641601176788545517418102413745235153248529420578315674178683193819843051610093509138634332890254850599627575799763583547416855607236555919310749419069755007969707467693488512404397439200099140703819 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((99999665375699928512232754184926321013986693068345224352064711008692024491254522080322991174600186778608656913850297879501398555177929669962165954802991460906587545816390231118785155913105543972255005914915566027020350902316705716586693105454895257267108825782313888822357140232782723 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((1374769214803767618474707665082611811360645465410913160111540472372331757857965759656019548268624635023569669054544158327009209360358963458633280427265434196004079633375041939146201312358398084446293560531764869148921512948136690295791018700456243334489667844182329719090764260531163671081426527028420821967689650780242573560329180158342576055200412171 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((125655676051764425688208371661248907549255482899948743654675616245176335520959006851806432148186730972478904022138267516178508472451357518495355575999218344292908651559107327045080052640978929354191358355250366176383884734737516788490741154721858058862447385127792038385604234903616782792459988374486168516443149835209923796132609377800812535585895891 : ℚ) / 244140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((999997198190735501432924850790388085850110581061254563499837825275778321065274113378544405104927363897290284339668544145065210102504805126593215539565447502170857521120635405157588110460432719679691164525588034344241398105097776964980381371973837989097502198275314191109596335169089739679 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((138100960320657797814962712050245158233287887463224356669906933801496138694576886171180541520948461301129791888990743768131351613218822659328360722700844871304447060669652778728241715629770739137020851226796187147313960267959811678800666834711305327801037011388952360916383025679893330532768449730178416129865827944832375619161322830443405965956479972367491 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((100923257028505975288360292235443363613897349448745012668273685246402452255279032388969197688828082897419116991101369634577996829726713218268497861048368826183878935691439317441349662314420924898285257630691546074084248407230798674703499355307719654883771613877683263600037786804318531766000335302604036273423719731982288711569466003482325054225100504201397 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((9999976540451028353497879775667919442822975895225884460184142111034091882279540151318552303943556817912011550776044720126631004188272733324964993712781491935676590024343080247384485248885203161878054120572748611564333226333983686527780733227536945482713385906159205722160650114370788390332267 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((13871826692920376659459810406300978786781061216719361444350177277771659849952613353879867811291441300065383623295092106305392792638368118145060239715757290720331105201254512681249257652434974509715112039542450450880974823931579191497627840421391052141999390967657154934093754667196245303755745823571479101982457566130763428623057215710292161558380955346564577211 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((5066220222351414672671116617262253748892028667696062239502565399915595656597952811563962904438833089019757758662479799073951876392029653956876689066279952135536493287997712034431761378484677469696060734279675757563219849910403236250885389620524217214727445375841492858004057596589299192234688162863878191603736503979947057465119106932261755863134104433145457713 : ℚ) / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((99999803573196460403837747361667489494756777170726330585121821895688451330326589686990238440919401236377272714647822441620281398068407596129931892357119431977420088273824610911350294988915806074404947151555624124628162104094445407297108079314166844526759180192271029511651123407626611192252071591 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((1393289137601209899048830569807061788736712307773292690414178514107352288120638293358979930979422965247140978367331916117008875388859595191702576684281980138546254196356005038760076291985635609982689575399707639004483464369101308479018631514731674980219674377725570030606994831748966033007604390607654909247206684899221249122821442835277810913516602483837514542289331 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((203455768446421933617231237844159512459846700145432907317224077026563379374150209990854785261674216232123492683767546558218461190481745999522983583380852081417209633519239392699823296729828579491118130736405183052864622676199234202794721538623686625491464918180266940037425184862064975894569525052189803026861101826851155896499674617888787109159134108016261364733203 : ℚ) / 390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((999998355318373962961333458659241889539598495250491565989225014732599402988824535449169266465818146552186904439746217303686616146026776802395919734706161003946938399116733467160736019942192044260992622499975240795511601297582791395298685948097518989222554615749885330101054856292057615512726595431443 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((139932972516107858267085558823291375242000149497382779015596625564041673798365691677368780066434093557986867823791735013556499876960829465103414426307993145314501907358659264188664939853984500697642224120468551983557699929448017149226314149974631122773864572310933699732890777199815037573731952385149225808892932476915865184478619946708516333375975834303690776037802911851 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((25533399832978556489456086144683083832562347426379806484148128308611303343558433332765267602469293274747776303628299625729473643415700870826478093875106650074712594766162882315779555999527341345593951276183992526586986089203945636180536087503841000176215758627529204985058907745539695437987191268975999293294592820518993922497936475300037076525334484893860907623749014491 : ℚ) / 48828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((9999986229080745191875245049353832341115058200732365882027781048356054801225427835315894268118295341081460950873995077483768036990682202166461035938694686086047715215804409320536842694975973986597291228192292691180818637664660712352835897443420526496760449797673789868936132311733398414688059783547472239 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((14053051415162101835535885955353595583207105143191398836068703678455034139555191507071226319224503879031222403147787799055451793629928713894406029830779385967354817109983541551530837438248661968464124858407876131706596589760007740339617644322218067911025007441631225298616944467855389692600324398701996370343060273548994299913809563748353144213884905505155395256435501843212771 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((10254145456857167525044127308043112737089718040367343367431496760648155918221011716161773059707142227074366949306731391186768512488538918364950742262864024331956925905494387272296487306219425809242752976591572466480303761944448435610474434215692449295198756110298763407319838000984729275226580566697075319015773139736829809763725927215118359711563128245956141719540294391744073 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((99999884696093079491571426798239638192156382314732099530218610717885246850660507265099982706954486890875072541667960783771589773722982078739778253914690606598477519501930319240854983885033830189779119453654066703256994453166204144530294969293760068357375246155922642572602235846143744926183124567642985057147 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((1411216088768113799231704338277526749577178383413757893143041251715466414795740342497371391839826758907153208306612474465295959596246151151167311255362893979680700950676238471742535199267822210761225783468603569148345318033071930581800766082555654488189794849672059506648436151916364286768920628333155891048129693444740065141773955855550841378781708737475476854161856277832450520091 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((514756782607363888312716669192379642349966232360340746296904611164564606711460375805284303018866727964949070982683819491383580254602725712935678240786091554200143457579541262348471297207201063370037578959818519151404773077828916025425094472637093036003176068108192033556346688988113185056502163132220420857979728395533153230622266482665598151817159011129145083260169684007271012571 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((999999034560387354582927556581660490582925389121251869366520427540853171880580427330682155205329918737296982391385835642519521175382528945288163320027704449049052270789662563003678780069388260179020567185445500506370814556360627302152159777896653052356302936063540286260398520739761576266931302004874713883491831 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((141706326162090827961365939876346937845106421000781640160749382898535461447537998532273156728375078820886811176563641682005165552146966644254313407941244069046021127404785256458182436314193168699280974904046419952254996443723069661331301633837409130316800975437734808834823034858679396235986983245041121337369334534153381983889421487186944780030465410019811645890544984859463837897921811 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((103363213544386881180935500247360224564595794818337978695573543592620779182573347499623720809653804266902272413118967075762364625135462057590729983358138487870140258260231263736556453862077052944666337316931038717063287713421513017399914567258545311621697148309457080510528404250704045823372166316376227709825357364455944631740744543831666627399515836807548361087999133547147725780249971 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((9999991916374123319922852431258243287650834283112241902205875539799563608156099918039801685534227409587387633563073601834815950801477914858897791478591969351887714663321844640029802425520987902478939209043735175739842830280407532400920033820328676007379324483660022816858316814154023678083015791686815979346477100963 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((14228473474321330924718424441936164592743541118471021948030254459869421024910333360836345679982776910774839452303161630985453013487882772715493031982875705550297535514356818195014116619295456724638519254419327411035761446355294054605081458530273803393250388601434868143670422010137886027871009556079443196681155630056307011728325462934019764585393668824569787823138600447283022308700323465931 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((32430292415478720864592607715924059750278907648389545563369622155853624563816348776333127569755252131043676745742667223363663889730598810025259390159184436590946254011969062911882124441479808073018321642655004275184689453319208379246229448033416016320442912063803499124733607285926281204476337559698913097520799024411556243990758990015771899583251182094533963103443313525877380196874890673 : ℚ) / 61035156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((99999932315800534557714043406925271047500435452498801447169795894741746091091024613747259512978086100475196655823615268162913956060774581113551208050250559383355834875993805170969535708887231707456157997323194626469704017937852268792903443177612004209787083901685371045554686684911640256589091223793710195068052766363199 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((1428569026267730374572424306746797893357251116510502643786101074290844030668437179769254936202332976694946938884356357199453728818552810099892314960929220979152480253040933528228741736380796862835261446382348252168129672124506886393285733108671915376971460540682126803787268151294678322881488241842305839602870910127555955672802683118896169132551727113795267981252693494845683849798944697573360451 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((1041924348808895290994608091290264774253919024382459748417632290411541951838606901633510196933584391024316946926030434408587542405086406275442795904369261654932929246617748341970433554032419508011019488743702671206281879532389974151612087127006500074000367826665270122540707798574895151193034031388762097615572554218851732933434021590937862391163572627533196933590995675416479605536707188304166109 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((999999433280197875851739685446185294480721146043772464517152701026672640020705149090905803902165514919278821599211130640328078554096865567663764265004747933716838405416696130696527922490512791086530410911587108607430831742193637046602980529726145311248547253508811611764429391612765163868420460816824735463304805812759065227 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((143422897096038530929714985098404532835750703513781647001775377217003221889633083938826211548260499038078594914653510540104267467807515179708274284997857209759497205084327758119733254449639832308611764617258422370730602378950121931527943450452087731484736822041885386560529288476506414608948363008596669812880562615862843388785095466804327946761149397823741703973497693203629892105961408428654389173371 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((52304812243933806077320636412752038330452198882826066562932903429479981063459038516729744133514709413185152226963038555775049427824385438635430310749477180802062910098852725506508034965997924983478652973331182851243010860722945781734987288357433495255971295852475600306567909239037080580777622615977791729580775173955332574839590472441226626045157540721998234009763269744406035966614836551459035797509 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((9999995254855096814506616386240909470687078155824506845402119565696330014893364213338154296072831856419121573250194796851467001733453055398048698190884754449011087968553996702322028295013063599767519130562718860370018354177387322991206755975397014691084086153629279625303567295973682717070284518419273510034251139070231653145671 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((14398278471705456718888185087910765795134494193181565882987232981169070200548757744724558798036265221946925392338679918083145257175149419628545091491964463324056814555288312552567905456453302965390490288284602135699771970164419334708457845623025367125037038377606908333542754330062259323089207907255686856115603815280011891678403592734250924821559659582122353098762365309396272557013808483170920831419032691 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((10502841969930977636822431818092867258303098940467445058058687112312324889975777195796839521123390218185463690799732611824419833497396372829416031492810752333572227744063210570669754835294122853642375755571809715393638074674036220914132006086249160230703904145028672047950819401935724517625261697276554078091817849028186915287913376257399028004581338371773391911546988823739495621289344852708276646168842887 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((99999960268901725627863899001995134998062905398718595816551947123575371214702138558280365921017821133797304932823881034037333205514202432847861749952278049001569839560702614388542342914144381520853437680201645017878163679527264055405374167781999204008447053364337958302666768969187645390029492272724577099516784787435049631788703283 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((1445366313449553315071272217785818404858919919869132903098067743674339538789089016401429073996214504467626322707286431539598774670316697627306743654359360133608873691526155170781721081381096666280309004537629982651375990334379448683514718097065630971945475843975795933785239342319158292881570888900230416910465857861034329683875961423817960734273503085523125290882671938770788677612362948963750659564802132826411 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((263621843244628106652948032396855059587887742381105760543991653055932229296921491397994240303032003486901246563983446331473787020471983205109465851255040521878988910893908235526360897012410760176203447784494518640218531485159436367799319547371274387577343966584954780436808909495255245704405441922055723019167362490101102669579169142329606499280913361440826430068926068400493306110645295382024214423192310874629 : ℚ) / 488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((999999667331514148682104426343705265338780706903470802771989453265696583180701006148481503856682216353284834202534355897994590929770416970235146432350424104290144266641762990275265037220130906474105833696328373734693864488681781935909197906838679335162727177819601724868228856579008154850716938799522884054254039025193670566966812588559 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((145084502130441407268299403958386894588434175888007647565294809876430002171646560675515775484029109781664080890842265618463929344802043054292428413021134373442205696331763446448219669919509654490368370070228957525073376422097811902514584404017266334913418306012322691148168439179165829938884784490006525467496650367378455414016116066770281650045069198723033076899404790855145186778092555274443178994809791781321402531 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((21174099134923899155965398394781619091363309609972849231506321668641620115895302090204218990181366143606320329524877607570820204255541583854079572458210640688665964586260381539057212444053788506495467689811206372983412821148924368977163667321757830118576587701970226230982513959016589687864235574122009065392522264033044150087733225057969519538750006467526283468851069094182894863645662535974551244299369567487279741 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((9999997214566767966915260361775844186681610858902761031609867692193677490972009524481235631792000197526053916777820161933908709854967701291778881078070101025221377944591481517574794156644156079907688145539357473280591727363732560149367714073960262073317514659883525242321680216136035280565052928568405108186269068757946603657213121804004507 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((14562646152638110027767912267878695074055259687773238293125078008894474161472226066401877968581690465478632064573424665449917261672870377518755788192999982497567262824277040297531488549193853838108440511216794159536950398695511018925216692998049607608673491042964377278945473870528347008518000590161850582312138515856323869756325168765798492236920790206881154999966021316181817021275693660303193709345579412800094459769051 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((5314680740213890710239380464961031084972335112711890672936068664387578244882801264647169627692961005456409804932935446847444053444426774768864278596671538963380884680264644384921510792367187490725149134012424386639507535781903638280381636123806330970585075756260139964361990031286860136535073459301666667383948680074232577622933340507921074055931038307146495062542770399330516185283512392873408554161044725129545894814127 : ℚ) / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((99999976677567548186981475009149143375085127721592818117669422186737661631908635748481385944994417653885649445180688215872617627615644562916064571266680955884178597530064474746653751473581518857067072842601040123778394533216532726130655869941269274339887550247204756853959428449707023404171188170903255970843630912710286912421845468864929737111 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((1461625732945031557518356145408555223306224753958505722290138043358235001208163602599140274527537309201882489366314749055046826961343397625653601895486699782325862664438383729360907696929139286633236753788664320668190917408549011582009891276118274458431632591675950890858348605420774423155643691281598290811752539137159789272794607953908351211218832113054890733751638794618021521561612892570852224922174061093598144054814293971 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((1067180162204093086615141087285861423898002348572253198633299655871364392744331699725972959810130435253758472625216539889212487146897309111164384101582937592708076063500312700882678014328089275831363962282888986399673819374355835994087572465750987658492251254605377173913286998076155069554562925971944973586889972221855295077543452809866417706497146013395701642408550118344508163694817132290328041184713290695490920843907319963 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((999999804721273080969595890251605777479587774412896666099246071969554440843971007122034644517438259015984542804497902431501427396025791925296208655215919643618227397119229847053731861088298057390222600911098508956396497426622028515891981599018247634047878458219845429138202294409396906963125358554972962243873721632123232317708112110806056688830403 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((146692900512153423429666921766500158543536716167805880702103474030389377384607076302487121804246505988726265694498775248011133935862528370968421235767438828218218940057326145334525182276989779147397494398035621903364146703887886126491011737809009686042608079685487947696579605195602525897610302867228012126806175223885702256421755477098123853648235298486752846273445861202409306934396308946001272941526380297439822008046284773905291 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((13392952873904847658952334722037566124920213354079635792044461775904346582620705574474680439199140692795734134573162369576397995918689780077946534519739489834175649761555431090999476407541932568098952121290453778205388985776809754483515678571435633538294964740404608303989052660242543904748982342870451660996827991485892882123877659673382877112663662580137803658801775564518742160327498231796936214090506155101081222279412577656829 : ℚ) / 24414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((9999998364931219506958426389076695174836588435159183785248987360601079333186569242632796078544510542740838576902060937058961451586923955790505155070122895176015417996079311509380896872892319634528333837428627815491907872953106244763563561928579787439882886330674765778174167811089880302002248627180788612867954671225767824196170022703779112655576964319 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((14721750557909262715954478826966595510218882064213555896557989963867793936526514391145804236434258439512011108782320619106085559788268073181323956660807452516694761425952097318919959438466300006306123595376026147108144096080318030543743826831691900511836783236587530855741812116895552789046651789827659028662422515892517273155700976082750020501590209906334640806215538036003531051257417277247391920648731065403044632857946536119485291011 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((10757035969568945026050401832895478300214335518336355762756211275152661084593373564391262514234927551738210171293258536579538942750977361992999319643210267086739373836824453302438026317360516064251373438776864261584572185189717410916594637184815795893173383774665155559875818019636876610256914175506442615144561637032780751075287889940194536332980863215785699726987691609179467588116265238053413191376282639290970012659496114026173261061 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((99999986309569100931762904155739168698906754967587845833889771170312837256771144268564401565653186774369041404400956225994684234137314281833899663402139001308777094881172075268046249516727392299905739220789900699113744620236358587405317704027998560234139407246739813860652307082255567768664827755384743055543384462173353991994531600098742510265145922242987 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((1477364502243162461984323902530280082930519608692695645859591943501095271730507119564660637920652198773907816564663210913934143187671303075564190597938778158636229362238813624194689877389577231841105068214491666507685832665307236848831521147379000722265065876637877624692261435220436658784854986757651372276824331855253317354217259252146905525216257389496484081316647238059505295121434974482589256182493125720734578126940929299475604472099131 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((21599630479954274107848933647323011309820569151132741504399864934407794736131464307823888038834916664034578966817531032900000761497619457533442684953260281435057184937822281162751732751474494945972288385933138436658743052216453983204743153882211178124017523709718595978636424191892595452452110888729937080492838711831354616297071094279345420014320316133153445602465120144249798465767116537112632443730264715617438595622874788161120195728321 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((999999885370022082101650796496004059515946259343613033167159054009029386350944790960689734309214132861791983679049206480253491092431732481795241881666109857958390615440053786219351247203558455727110754495673838553679383705239030452344725135826431944840449256876952461455241767199725868927030602795836453604064758101777492974970213087626771038450066806940530151 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((148249795512880738353228105027511167392673844051529741407021363844102461613135839787459329910806253899631395194177202451033065790155018950250752050810789920761942149534541008089553188908686964200399233605565111057730691238343353873897683563627811928230241886669208622573816862170584442802218932120601680962560804415724705768445004010225892462721169202892400900499330311436084323298707469110792211810828402489420785202895123667233426269984518137651 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((108426928633298209747607303757172152298420056707739514719719451665865354952840246221722610262795823288625275832901120969851183706904798053951817953568248956625033081043571573645534278153133779560682789339848035872797769086861058732189709087577132539339620879225345931597177635962913222892429621591914211127658298364725289829361328908593422925723537341333650305945813269859332921915043475085852649505732985879332304775679489108698442721307457044399 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((9999999040203194893437122119061041990327018029484071926708622759217603051916460734713855145371049934451784279344679005859162480916930896070071560275190337840685604623079570352014627992835394949803098347392277050209957479763966401977482383562274714674149081627830722959764739316763304700526027237209538626026834219586182948679425594182698953904942409374513058954323 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((14875760185272303219145083863641117420161960033247888874487117485024753102864391155554050355223983029770646921813690171352429697295255457575382976819488081887773544896383639271252214436702754352411745810953300114965101937483856837047738997676837080640839313286081784533685124906137419645456319691414677072622240199621930555828159347148983103217045392407734976984725699050068897345031441551908676384538956402655993493055588528286397760053138518694574571 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((2721415434173222630781548805071977756782176376829475281641885982456713333342620891907422736694946395872950796520232247225828405364576698435572086311937399340701758247314728346079631055004654960573633244336878077851079882921888817419218453304342984248643766997391630250820389330342349883881406206312968723179422410125389338183601044073500931800693544727996730621526142968448651738399330239534543684575124135613878986987228645139625879844942063339879727 : ℚ) / 4882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((99999991963621350842749023502898104585008121960870134242331298362928990353696525731759109132191801101164789770952997316058767452717462392794709174184168698740060567509045242557418480184010761914701342462715535741407973978063690683757459997566926185966650260469826643342110162299259150257504426057155466915722682920595109829292830500091738341046082793692797842624546479 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((1492599290014624724104368525965998570670549944647768543495559297090031636245123947523476765388047880911523170475804132642154550267607575347055879788899897686174547942875444996776977381645161817886401883765382234534135786493515054809891779021736679012536150981206147282219139197329839231271363474000972466360011017558155467906876374638940050075332239566496605546219555791747490394267855229756358176634978106307133532326551872806618752822216515407786011137891 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((1092871489895306238611623902874969212410953432365268569436759612848743867188332283050339478479689847393715190998948548206193958391658746982504743632240865561083142165273678917663853873745664165365869770382211876180474037384609736358880544855768956589451825919631592069677461181560904647251177702285777152823885974103446617959578579458752895466996816530560604399414469383602660654692089511934495845106340952434707910066061559245448749823663391852248415860377 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((999999932711401570606337573789765829690273005178365634011039961192804436231501009952019020763841950620052784752189446527360059881603312614870099915444044514550527131753235815933264934580722109511794340440317180762808966118327282095101212559627872955098762630913858484703488388931696865106084559376562724485346024094142854600668869777268125129578851231589796336295327668667 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((149756836073176290722958828729731510524286310207231968240488976519114901922434346467355940397108017111011221206067846466501355620175957045316768809577155802958223342845116656571477226056411435236085345675933306941589121212333024655751146456542313894807252959005778899760769329185957616892060313315471891657338977502075807265538910123424193882368907722782303859272582445093441778541370507182728707190908669254007956151274837809903533647926479920653600007771315611 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((54859227642929684253504530867906070959328723936639837207842703072085368110822753255500231490271551528768616954875190998112898658900011742027912519568560825885643921680700098682874223819794987251828315594280814217355502382874741237248347803620987415719845289352299076021039294367552572570637775338129205512847038166116146322525496133437355743261037787255917692589424813297327168379105601201489686983176747366249569126512612486438688707800889002770633325671068803 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((9999999436592565350686864505341709291996655872358455453574437595067351544566357956328255260855648652541701966730082235773585781388664536524307346592012984720331563674169843486809227297244386222942254012506775754526999473308754332982282452761764180253041939508641737092422308280525097851533246015659959692115802259740258121571400446645066011709963721362101364723800778569748791 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((15024838154514125427786325578437668668634606672593081131703721006819051929220258766143064738499702134216277918149580489688370736923005919987484157296706072159274164964605562410760222285056861357676928575963510811836724739609584807241210371196340684920757872473192696204366911244368430006018846933082785459424630626294868301630413924899258805501645888907630582845693491050012512964153411941022706444031876471275721030440258230993467451986535320230974766368746311555731 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((2203009388291090361954383194433530638118243665957260393321100733370327675391140361882590771637356769603484364653552948757201411837653196143636612448403392405251897548016589959211565223174149561299190740357607376916004392844162377892648622638118509798668531535760957846199265236491396866229330365302710489634190496317098083356121138010937608031465257867833474800286420074125125065101029826031057385436928901311724367962946765907777792826971230784106574565160168733479 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((99999995282589549681301116503226131901887999619257347512778765983498934482654115168336481299144346167731670567430978560132233747567288164318025413014924721063336182643824099515053660159827245844695492846719233392654566590014200030060650976974251481258720159505857264674851987232836644310887868889120842502085612320805181251917335939759137716047526238964874726832383918964506627043 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((1507346232645354649124455657078350794881848441671835595493339602444214764633731397551884566814440060006489085015692149144681483890048108132389982095378676228351227167003647739864239988218169729109936584630649755828510476935084086227435667157492012890102993121533633049518748896412541692324227022410640612048526992899065719049128154540604162772924896678486622097665136922058207610335222787617907144150077252415065600052180784468104793817960060412568254863962753885404466251 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((69114453679027218113189321573870666609995665562532419461230708949686792307403977368600448466158501477034421753322122098026834770443898904143117631610356609528716975670847179913565406065851662323207477629252439051594511169795354682787921124402966071124996674040226467170243717470468805187365767573208965452264872929793153775988344505679130991971196861365694325155385504850351311519538524286778414898571413371611995875509895236441149162617348575781390880357057657911938409 : ℚ) / 122070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((999999960501122299481534248481512402414508220812041770724496607579836578423262906304481357917735610462417277661099583483987193168380903799834826783173964689463313857276739185239544296518233529457635361605580141196696686058188896851697830630205407652579263895542542877122535689100541222815064126208608814269962831962101782622303853823603260096465937198852896087767550553489813988231039 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((151215618455095387482488010567655761564924070940595794995825714948075484168012714480875189314354677314866408195678260153243823790809814215683273430978889651771203221904993740484812493626725927114425178231639325840661191868399853710743918365342423995935435976561689842793478637984842043371628455239573632114525588189844823559895110969822825276199864657688885688082745162759160241166099421030200992606469791886150704222761775380369394309266427136071664339398059577098095206015171 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((111016360543153160754002101724529303895315614198344222055927760791228782640491137702427682851126622818502554270897974069869711678350656684622710218465362970389434365318570918058990371482329201756493731887828959461303453035450176218256426213615986789456513865461866667803593590473569047333048386462931546364456256546747188945646697708289876961340510199086580638662514915143726439400740031163398243091443257869487539686477332613385003733573910720623096623411023820695261168791853 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((9999999669275897013558886262535703345416677332859225746276210095265971671137980314487422409845200266401819865856386812511424768398853307516017004655515606344876326926978137198010704394747169342148780882723522522239941352365215633339265935866709878275046176597377711510146991324838831658630531928744681601882398792018678225896550168065030096787709292165995298942877700784370212523458489547 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((15169142372372410934752965136744238066757067765705339345885929423296278810813419454924868544585833082259397668756784182497786625520987279529609344600832412754564450877345448611262485958600756603719800820534107222646396488207885409331237812534051915284963056327945327924211047224766427737094829942663841565252018892079028038135858072690310089311827504427766142963079559840458169375239629241986324889624598283169913812419817582401520854466944238727345108117595451426120675874226730491 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((5572505526801150869020123234047331918678534472329655826397462985829057927498654775793356572293242676325916012737317667835465917402204549719142684776419196164077182564056921015648249609013362121155290609693933665726836151872885161920018312696655752345721071752031687993086722506810784148015233270251575723484975231758810621156721904369090873682892131684744975507287959975774848506089412949003052237935519708576366761591192087542038265394281648637289333453326196825342387402674630061 : ℚ) / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((99999997230847085694528554676211444111173839308030297173570707127661980802438309173203187837633861830582437736815526781158159585803598743831610379980632171925649485359587942758943627897218048901811742331044054078715028943353950497949673681011961810796961636649843578474460758362875537477713443839379219052561325085572392785431814557208497000403489903305878638048714988667531789458917932977031 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((1521620950670476052853319232802181508000317687252422062067647709428750538887360751758693094697848184735352899516205163294011651027502134863523842125741953530309351210773454376052535338436394263762540117304887781511827813414703770991246523983368800993659250074213106640464804056504520382867998188287772354774011969215123270462277797719813335193319074358950439252190177981060649016738414735772335885031554886769451044238380775068740844444724591039147705440100659650523283378154382406900211 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((1118843143053183121627277670252939274329229493193839829160337789890129163329056537744373184135247831465429765876564972172819359799624097800147075524360624780855532995334805106629433221495751805149018669888423525987964179769611654561248668620256009372174623415343306224758487074147982132939955102161246529334621398186179882164036765864622521217538206994050875112570027422595101942897625196608765105413544031731705889850325608154903175504105302763285401680731846924408172817788244802728151 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((999999976813882648520287588303918421542858556526137678234307530779913765258815962707230291764508325107466751170356405738637270211933532282102073711577833175533463140915829844720634996383406723454869718537831864801080937342702627519332617731113156241802959783669140282566659929772356875300894665267122201127095974941497644792420583287506745384378420960380121836381890600113243673139519852816680563 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((152627687877916427356029682267392412347351702749551621916057114865001964816765498385617895239293475768830813905816436297989536964750173117299374557233002248326180077111213759049057304746691132644659208873119861546473189369660734241695560248603588967661147957957351542707472459383513791749514405148901646633117883119372424111920093901429701185803538139147420835845095288892083797338416904735191028102737690954120866747104864650574913073316601270183530169840197353289413715050409662072975772331 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((5615945577986868561776033293564227990152702674038659657267038319609754439856653201067938479851091446386061182442683449175085123109864509100304554179947646590310698469396940661232542466687706686387292831530235876525333341883210992487641727398119981968852212684962556856219791171938045903283393435302758714955562112237910906618873932991700150501684412764590707048182644235604725979121836578681700170628111844287815800330863617029517419759872924418909779691477182068614774303672977137385837637 : ℚ) / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((9999999805862639416060367976868708943578354693793350779855856955220217956512066055747639232944228206124819107549394185249609863484519465798040663187041197178741686878888243289845876824718264495487624153317266203979450688370449100219372008262610457212616182268661711585930643591983944116894391032281614190037174598185159779846937543866293979103400518701262760136025569994748189275197199727634066353999 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((15308825695185077820203271244060992004789866924893806646795554966145141969591264245444547948718865635823621658102426789133420957683543336134103488688309972046596052909685598993746009588374327253945420402950061812734058414736361080808188369752871697626435251837884133355558349182845390658585289734199973391089993287333055963764900305965362583944181233023588374209948307782947374035911496039792096989286266689372590259490360316099520976125551514247824987930762162384742094106501574181920836374754851 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((11275384325621052325106095815819856353200702511638331239177679579221667498938489798814912556270193999713679612772629724282502619647983578887790561227946432393146440369027294989009619498765972394605935170130145593443894561578446224004189655827231807222922973266819604050063722034060480157271657283427348773559517389979530541489674347829082059335024493553861613720142364825319660388942375764204720370896923003515396950910713346161508184807436403899387515390469859492388119176412083453523629756138689 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | _, _ => 0

theorem risk_table_passes : checkRiskQ 100 3 2 8 cat kernel value = true := by
  decide +kernel

theorem lawful_rows_pass : checkLawfulQ 100 3 2 8 cat kernel = true := by
  decide +kernel

#print axioms risk_table_passes
#print axioms lawful_rows_pass

theorem full_information_risk_bound
    (σ : RHist (Fin 3) (Fin 2) → Fin 3 → Fin 2 → ℝ)
    (θ : ℕ → RHist (Fin 3) (Fin 2) → Fin 3 → Fin 2 → Fin 8)
    (hσ : IsPolicy σ)
    (hθ : SelectorUpTo 100 (fun _ _ _ _ => True) θ) :
    risk (gameOfQ 100 3 2 8 cat kernel) θ σ 100 2 [] ≤
      valOfQ 100 3 value 100 2 := by
  have hRisk := (TMCERTProof.claimQ 100 3 2 8 cat kernel value).1 risk_table_passes
  have hLawful := (TMCERTProof.claimQ 100 3 2 8 cat kernel value).2 lawful_rows_pass
  have hK : AdmKNonneg 100 (gameOfQ 100 3 2 8 cat kernel)
      (fun _ _ _ _ => True) := by
    intro i hi s a th _ s'
    exact ((hLawful th 100 i hi s a).2.1 s')
  exact TMCERTProof.claimS (Fin 3) (Fin 2) (Fin 8) 100
    (gameOfQ 100 3 2 8 cat kernel) (fun _ _ _ _ => True)
    (valOfQ 100 3 value) σ θ hK hRisk.1 hσ hθ 100 le_rfl 2 []

#print axioms full_information_risk_bound

end LasrA2Certificate
