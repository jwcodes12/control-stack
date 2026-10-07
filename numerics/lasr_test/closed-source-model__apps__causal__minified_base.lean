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

namespace LasrTest_closed_source_model__apps__causal__minified_base
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((3487 : ℚ) / 25000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((3487 : ℚ) / 25000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((3487 : ℚ) / 25000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((1983 : ℚ) / 100000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((1983 : ℚ) / 100000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((1983 : ℚ) / 100000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((3487 : ℚ) / 25000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((3487 : ℚ) / 25000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((3487 : ℚ) / 25000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((1983 : ℚ) / 100000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((1983 : ℚ) / 100000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((1983 : ℚ) / 100000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((3487 : ℚ) / 25000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((3487 : ℚ) / 25000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((3487 : ℚ) / 25000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((1983 : ℚ) / 100000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((1983 : ℚ) / 100000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((1983 : ℚ) / 100000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((3487 : ℚ) / 25000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((3487 : ℚ) / 25000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((3487 : ℚ) / 25000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((1983 : ℚ) / 100000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((1983 : ℚ) / 100000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((1983 : ℚ) / 100000)
  | _, _, _ => 0

def kernel : Fin 8 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((21513 : ℚ) / 25000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((1 : ℚ) / 100000)
  | 0, 1, 0, 1 => ((99999 : ℚ) / 100000)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((2439 : ℚ) / 4000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((1 : ℚ) / 100000)
  | 0, 2, 0, 2 => ((99999 : ℚ) / 100000)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((2439 : ℚ) / 4000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((98017 : ℚ) / 100000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((1 : ℚ) / 100000)
  | 1, 1, 0, 1 => ((99999 : ℚ) / 100000)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((3647 : ℚ) / 5000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((1 : ℚ) / 100000)
  | 1, 2, 0, 2 => ((99999 : ℚ) / 100000)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((3647 : ℚ) / 5000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((21513 : ℚ) / 25000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((1 : ℚ) / 100000)
  | 2, 1, 0, 1 => ((99999 : ℚ) / 100000)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((19029 : ℚ) / 50000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((1 : ℚ) / 100000)
  | 2, 2, 0, 2 => ((99999 : ℚ) / 100000)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((19029 : ℚ) / 50000)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((98017 : ℚ) / 100000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((1 : ℚ) / 100000)
  | 3, 1, 0, 1 => ((99999 : ℚ) / 100000)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((50023 : ℚ) / 100000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((1 : ℚ) / 100000)
  | 3, 2, 0, 2 => ((99999 : ℚ) / 100000)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((50023 : ℚ) / 100000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((21513 : ℚ) / 25000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((2427 : ℚ) / 100000)
  | 4, 1, 0, 1 => ((97573 : ℚ) / 100000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((2439 : ℚ) / 4000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((2427 : ℚ) / 100000)
  | 4, 2, 0, 2 => ((97573 : ℚ) / 100000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((2439 : ℚ) / 4000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((98017 : ℚ) / 100000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((2427 : ℚ) / 100000)
  | 5, 1, 0, 1 => ((97573 : ℚ) / 100000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((3647 : ℚ) / 5000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((2427 : ℚ) / 100000)
  | 5, 2, 0, 2 => ((97573 : ℚ) / 100000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((3647 : ℚ) / 5000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((21513 : ℚ) / 25000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((2427 : ℚ) / 100000)
  | 6, 1, 0, 1 => ((97573 : ℚ) / 100000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((19029 : ℚ) / 50000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((2427 : ℚ) / 100000)
  | 6, 2, 0, 2 => ((97573 : ℚ) / 100000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((19029 : ℚ) / 50000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((98017 : ℚ) / 100000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((2427 : ℚ) / 100000)
  | 7, 1, 0, 1 => ((97573 : ℚ) / 100000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((50023 : ℚ) / 100000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((2427 : ℚ) / 100000)
  | 7, 2, 0, 2 => ((97573 : ℚ) / 100000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((50023 : ℚ) / 100000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((3487 : ℚ) / 25000)
  | 1, 1 => ((3487 : ℚ) / 25000)
  | 1, 2 => ((3487 : ℚ) / 25000)
  | 2, 0 => ((162190831 : ℚ) / 625000000)
  | 2, 1 => ((22452793 : ℚ) / 100000000)
  | 2, 2 => ((22452793 : ℚ) / 100000000)
  | 3, 0 => ((5668586347303 : ℚ) / 15625000000000)
  | 3, 1 => ((110554362127 : ℚ) / 400000000000)
  | 3, 2 => ((110554362127 : ℚ) / 400000000000)
  | 4, 0 => ((176432673089529439 : ℚ) / 390625000000000000)
  | 4, 1 => ((492810089227753 : ℚ) / 1600000000000000)
  | 4, 2 => ((492810089227753 : ℚ) / 1600000000000000)
  | 5, 0 => ((5157705471175046821207 : ℚ) / 9765625000000000000000)
  | 5, 1 => ((2094635807626489567 : ℚ) / 6400000000000000000)
  | 5, 2 => ((2094635807626489567 : ℚ) / 6400000000000000000)
  | 6, 0 => ((145010452176388782264626191 : ℚ) / 244140625000000000000000000)
  | 6, 1 => ((8679504734801008053913 : ℚ) / 25600000000000000000000)
  | 6, 2 => ((8679504734801008053913 : ℚ) / 25600000000000000000000)
  | 7, 0 => ((3970928217045651872858903246983 : ℚ) / 6103515625000000000000000000000)
  | 7, 1 => ((35452064048179658643493807 : ℚ) / 102400000000000000000000000)
  | 7, 2 => ((35452064048179658643493807 : ℚ) / 102400000000000000000000000)
  | 8, 0 => ((106709537717678108740813585552345279 : ℚ) / 152587890625000000000000000000000000)
  | 8, 1 => ((883997486481250926994091495012842574011 : ℚ) / 2500000000000000000000000000000000000000)
  | 8, 2 => ((143598592213510187431481395273 : ℚ) / 409600000000000000000000000000)
  | 9, 0 => ((2827716259529784153341122665987603987127 : ℚ) / 3814697265625000000000000000000000000000)
  | 9, 1 => ((723979851132285136398917769222054467784659 : ℚ) / 2000000000000000000000000000000000000000000)
  | 9, 2 => ((578760998408751347145383123070847 : ℚ) / 1638400000000000000000000000000000)
  | 10, 0 => ((74134509256498621490827571913391324575063151 : ℚ) / 95367431640625000000000000000000000000000000)
  | 10, 1 => ((9279875627244395330212904416135563166507228335619 : ℚ) / 25000000000000000000000000000000000000000000000000)
  | 10, 2 => ((2325694203118944535687589437169795833 : ℚ) / 6553600000000000000000000000000000000)
  | 11, 0 => ((1927401931765914219132173554572787565583333567463 : ℚ) / 2384185791015625000000000000000000000000000000000)
  | 11, 1 => ((7621051365099641801495598403239231738205572689126747 : ℚ) / 20000000000000000000000000000000000000000000000000000)
  | 11, 2 => ((9328752673407105722542030637257132036687 : ℚ) / 26214400000000000000000000000000000000000)
  | 12, 0 => ((49777853611351596971190449679524378898394255036831519 : ℚ) / 59604644775390625000000000000000000000000000000000000)
  | 12, 1 => ((97856139125082610463186524042554323818425371947355683312651 : ℚ) / 250000000000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((44559375954199114062217913700717478599084277753189506209 : ℚ) / 125000000000000000000000000000000000000000000000000000000)
  | 13, 0 => ((1278712361072794015016220143955607963241155608607356468247 : ℚ) / 1490116119384765625000000000000000000000000000000000000000)
  | 13, 1 => ((80438675977983725611476760679379846066524309325107586941196707 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((8933080829614715808379730680891492422604218844140151622061317977 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((32704973932053695379418943956916994113206980607970059701397711 : ℚ) / 37252902984619140625000000000000000000000000000000000000000000)
  | 14, 1 => ((1033147364064644456914982959441192352025289337835712172476671211988179 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((448015289556408739164208611998866225475596628810395764203837264977973 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((833482976907638092056814741345155294357421773819259894356168956743 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000)
  | 15, 1 => ((849072415495356996211415869676538414438285117201134545861286893201899179 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((89935840348359831909871317439694522275026156948760765243922907942886829491 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((21178241099898191858402630530558325847511214620173738107284262766412159 : ℚ) / 23283064365386962890625000000000000000000000000000000000000000000000000)
  | 16, 1 => ((10898826051120022707745593092855845232594760711600758720658790621646398615564891 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((2258224273590354451916878086501608365855335489848082084998989451984105694338617 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((536795546224214141049425165603901263957508760123797627902006344893824776567 : ℚ) / 582076609134674072265625000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((1789793672063362882575477884068746278309963182073939604653540570118306640811449879 : ℚ) / 4000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((907818319014194914859240736573246868705918083250842694533464476032516389094783496621 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((13577783721974127306386517962636727891517885956543258369055862497700852418285871 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((114742706606783690346835835362541838708871811476665206421150393053235090081646366417215139 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((45646725058741577000033687202529098115576985269421440685761284336109464009463089075504479 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((342841389612144612992049020305203927130224280583115117293498769913038438074583942823 : ℚ) / 363797880709171295166015625000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((94095385360871981294940087960279473056551815016719199211028500776843807849658791822360875771 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((9186256357247847801720344495249632423408818253840382920047703596994619027218839712022978201287 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((8644110024758947365541847058200852084352514948184555518335039037139195918298524361951199 : ℚ) / 9094947017729282379150390625000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((1204825960415495391433258777299851301432787723629761551365701721794856654831946200743568559020194731 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((115609597384949848860326452827492771198475003795333108714807544311591369068651760398790847840150447 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((217674819213461242330999167872449930890675654080294342865941694805975521790356154598656144087 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((986601737180293161743608530595791031544452724429429700633014893811804524698167474187432360960697325123 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((18633422914212420027559516581280471284353557633565146123640778049543070866872319833666879212639601826637 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((5475690392009741897669220401174390363251105346229372198075003680360951400275931953880889627743631 : ℚ) / 5684341886080801486968994140625000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((12614079872114346842055899204917145515600641863833753556481014079931538713601861745169770004197661760812272499 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((938990517205931373468929079489589522733594674017303824903954907655048646614697087313350431958087089616145013 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((137619827560069332229618821058824034884621029313432484097187554175605147474136124123839578561648733703 : ℚ) / 142108547152020037174224853515625000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((10313931656225501046567649954634395784668384611371648832304852742867936163330750073851960791585493855424331330123 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((946815589202964938820507838100711097183213089082428380955115343218254460419270107459782448774652041044652558889563 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((3456147854218865413882311761647465837472852203619873030382795852979793537611090438276160853596749208152639 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((131671005257686207284835112743366568963859720200736552984616573103706134613956601295883394844708823785889958445909426171 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((23878156625377077338883968022996973426657855480628664594858488521175575650009977124707047869859093199809810161451848931 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((86740421385787798389513224533546541936553469456474328502625087185154298374627388598635048443426865714987722807 : ℚ) / 88817841970012523233890533447265625000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((107502344057970798208074613287911662237934708578772890637797592742249589752106754579038663396326819120933300251263627094291 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((9639019035392074693827996466259685415512435272172710376150173624829352560301766663301272126511153518468525356681587200294869 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((2175754500221886575270174289520801991056074788417132229076973500614224420933359010922435797163442162126530880746991 : ℚ) / 2220446049250313080847263336181640625000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((1370421608479111948279259025677468993899033687047634668245463346961279317156713075240250351057865946443467485274108461364442856259 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((486560763984448897503626867504288242789614144513396547614671367896827193328684832654355439853966715504171282295609805382050892531 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((54549701937009287606701666743726394092964336923217765644132930918713809967539352401974361304377131233828058837510017383 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((223458440490092482474462129547647880343370403313371791973960450676051081781569352786897052068563385559287655821352144624348411329567 : ℚ) / 400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((98276400092288069250716530341311050675614996603675892020644398302669264372058872986774934267759629315795304641619332316817206285995119 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((1367095122114276847105833137989420437606316780229183792302231742854290193831674088223674434741065224233343029771353003960479 : ℚ) / 1387778780781445675529539585113525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((14223435140739969623563577206570549363873654401854275278986894505008166195521498810683572824711876556479774342673503091027599257305213243211 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((310252553378851025479800429929697860189613501379263707783776160443924472414134950810850472723894137396885616335023020203933242668091834041 : ℚ) / 781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((34249501970629338882359292830857264911334067893070430923797911484024344939900804659955908114584536168931908599471117174201784727 : ℚ) / 34694469519536141888238489627838134765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((11580751423045279699862151788645247277047142403556562403050241951522841567698968178040065137486808174065961642206176367394045664997575112515299 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((1003232993593284101768886957065319821299118420675825054408865714659496180856191143388476652848408449785818660094699028813392088576798937273512873 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((857789151108771494140483080002503915965264177583624180463664469755815732692086010649631451269057126602232149700422143768602994831951 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((147235764717844628893104967375174646253905474827541771438512572055959875628156955265880989434410535962828527078982254812880319894754572919655057702419 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((50700881673421935695420643680307351408146529243640625076430810764257131457640906452428368604731409050379472617312183546933637431161321028173900195677 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((21478108388168564322551402833400656142354087627356506994314813737856863857404846347105521411151225964593820236505181578893956227819761863 : ℚ) / 21684043449710088680149056017398834228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((119730311280597969846711277951115420965488258824888962722737993462301701565789880236545624802054728590768888622019993975459438766386063487360546928726507 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((2050283091202361195508424537491361452870478236637187460089287401956307358716465852199175916219245984265427479719738660576154429305195300368005350525870951 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((537670805263809403498728087487618050545297471502320534968694587942514712164350459465281082118096324176306854747935971306745680329086536958719 : ℚ) / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((1520404472588367093582219416884627099960828785257566329612568968238755629517858565287889791124792514352174254072655385167710112553328024170163846283236201789851 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((51829227173709567687448178546582134802003043271900107464123541856101983413636505894995649364531289769993864448958780865714529394436573861225746812940321778537 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((13457218521368808678160131304437870495251834113804421668781526670407319002791671434476591919606606222004889366192346550722019820919638669592921847 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((1234946715275823436395892240085214044815584089542095646543225612898098869525958359325165341519645838689949072230309219247608116729541218914500938685518889387034547 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((104832685315379239895471669031292162752321790285202297193908231876424236465214938531801918431968102166884953632199437128009307975234123541888583530509934599687782397 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((336762804243419105610558753710290492311123947524649523360496983260472653707057227569894921966496919653991184934895951345682812407444186698952527694511 : ℚ) / 338813178901720135627329000271856784820556640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((15664664990001615998618095998580617146861327254525048762830853955406332827880630587656479024807404403172003223848415940300780489563252888878617737911532550371343478186979 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((5301745782012150754668730485363061003539110933331438505435629489595651384581427407311890311322973094521014440271232869140247659740171851820440741548082570881563798759303 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((8426219762518973331932446692517443969758490488957160196054371600882548199199922136711149456265248232516312361504416601299674343321346788454565728292015143 : ℚ) / 8470329472543003390683225006796419620513916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((12710049391541913156408441444852976450507535777881497033141530894001749716026796194326302324176645361291392556063832477636834359562157434073890330016198910398750711639175739 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((1072632624307277093199230198285215060412075783442629191929131834926404154868793523263528421286640477989896335785450114968352764055825590956660134200053410877004899694242741271 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((210809304621828126113175131294826887338146431035419762297717696249786259409387924927066958252634285226123427833044514343759894147872133460023072512746121771359 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((161055609317697084885288123683108196858718281295211094282044282648694244901528264889613894943639084543719937397925217626158476615578967204839093511442111996823434648084827683770091 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((13564486785711621964819237382576945102532524260557807163316311558030226677889052467605750077224807643173741423536198655713769858881404987247045719146309475493027509376235241731801 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((5273541542098324797655546739513088707723844799527094721310800799421651798674162428955991472888921378069593302972286637077306602803173207125476358966707317667246167 : ℚ) / 5293955920339377119177015629247762262821197509765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((26109935994355073591280441491086763481858500416503106562187297353378153781008188182497039628513252938838107054020910835715527627524254495737513539833983618582766376841748109469197287 : ℚ) / 40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((10979103316951971544803053869220345709691357186106732672592621215201847393509357230260659741308661307526740063414344594650363954271092783971392415586372841434539861269841086720486162641 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((131909723489384669386534030506332024379720588888779123114559257597957995144877256334130244556259365606411160726842802423444096946104665204890372910450774524975466790671 : ℚ) / 132348898008484427979425390731194056570529937744140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((1652706517551636239363741026736368696665646162451660461376858704652394119789707156831213445059511948024383392979541627441078268665747806992199754649200602611851205664893076992827321271925939 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((555434778553196035897420947434114513144129453769637688414698843251897671371727654238774274962605525155453330922547907128872976540047094874331256508372415579365045815777015509064542491044209 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((3299274488782717592876762935762394515742366921678123634938513308704870349551744415516143951138807732290723300716569208535552857601549662552806592422527512355797217067705223 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((1338455193585112295576037044008929292638185045691626183647601938027253421139418355700977578544670931033741112705602932125864319967729062127307708805878755748199473907509807368856838711555317131 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((112401994013639814774173907679866877608831809621599896283136456541426183506236784083709199693012053309841274210972881414370542837935800303916316187116453273189734106914316966393501117684277463467 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((82514807261072233584664209474048235098701486908906932742807236810167875829906677610998804820849170744770330368315553383225348625582137890498528222785834373310265530777542462399 : ℚ) / 82718061255302767487140869206996285356581211090087890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((16929653518352694198273292408650661845319063759289100168472587016135438258694565117125188304248369492205848824134444166629819063971059006218841985745360985828591887964120686106600167971763776220847931 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((2843363401561690272407712733068464943270163887111265943374641178016398752473053194265135453634313655325875964663579811944515266099029911819224673871124290687512985352660359293110006999981524819370679 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((2063578928204687711334541349339995728716763770942451318705387085497141512728782355445417288110928210232244117213572499933326924982148532438294837656791654873023742363617270993589687 : ℚ) / 2067951531382569187178521730174907133914530277252197265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((13699223941936222475441925059280917744494070075822460578256061963254748842491216479771631688371575946036247594388770882361337223960125107301463215583050181997561506909718178901480494567871174322204193363 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((230166051562271441723552059738110495187477634314444970736091684667707402110812917367078215696850867584406075419330437591171864620916068510368393182782566554723362118269887570881441891940851993937963795361 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((51604720472398465489631493321471229287843706081063367084543367370300005363334294812697262119130398586726267693615585191065662137140961378345036842510558871283359769468498350885094936431 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((173138967717776493613517197312100164582557057020766867577504963680636589022668978825645208421939837520409058788729028235256063903781306424641348794126430596632550916628549568746139909074547588354684507690375299 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((11644596280881245840994791963899262515537466457406933462609180253851348116088251673084033246440387536669501659839933730185343241360212071823845754314572468118362328198847445229231129365125167553254340418529439 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((1290446026270983656970729947652808085068380825841376512720640837237264015381410684305556199968852264796242196892752084215395589556313502132336777592929652997918918720575805022591047367440103 : ℚ) / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((139994675948731267819124389486284401599265262371024755417975307233793852825120683290717473775320427307629060790396106557244039353295488460722807994983047963679864870365460675214784468806597028876163280175004984283 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((11782190203795301554433854600811894513727238123875068375082259995943280898868807416588124680389327316816565640235863890080711427986876955533285571380702641375156875568118907536864571414757506733673676876736270366143 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((32268207231874558134718504159554798569051056129312040333930630706485260762900288051465430529929918772561558381753775587725805318124972371372961096356695624944229698435747293451001202015738935839 : ℚ) / 32311742677852643549664402033982923967414535582065582275390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((1768042562830983698382401852899033066033486939371137291321536502851846733462797618581057398656802802476988498539146072541315128102705565185264474656419383000234327911711646124372672466951068087053861339107452826198047371 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((74505908098179081684087584789088782107692806527041980108551850838514122327884195834504656440388479307387170345751272885853072912610597749626315933237955062679972551553449237339860754054770973635002981813555015346407879 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((806856988896989537209878949877000837490369856084552609098136767763617414792273896851175806990382342554116805466668974218745249808822530625346512065921592979425213502448231524011388858964591726704407 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((1428580335166147268449286251098112021268416155946835757437159421113246043394887978630810467564848746538797395284770051719868556548537222201266288903440999867946651528974065239996427593533942079829484888062193907591412765731 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((120607278833808838030557735866998109036765836182062824208145044962282847348492524062858191792268461864966665040290330706719241948739728074293253272852361671835536102205319404103248209763468933615090056581917844207503556612089 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((20174690570082740115438120096016380413789688853313547414385394019273701444426188342959345135784095335366714836004449642367866559137199101343079514074171229766374618078168804776057008522905261816591907791 : ℚ) / 20194839173657902218540251271239327479634084738790988922119140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((18029905147780101200765221389853828397522959919935822788374641608540313147371194050552737252533284687202838335265235090893990401981021483635949842970370830710733618293629831841300074266629413124233172317952717960950895243230431059 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((6100704788416129840360706089088748113748329342551393622186917355742527641374692595451192236672248309015800033885382776243615859003646983589162380994052449370473539754041068629375076896219656969046726034391668944787144688557501061 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((504437522432735093139470133808411926763341629785498523897102424896010139173940589822084391906123242949744136266963725156259913286718564267193669586277645665964017158715645497147314424353260897460341712307783 : ℚ) / 504870979341447555463506281780983186990852118469774723052978515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((2911754238237281217615890294473906814794994386665218636729566932068639255527944488733271186739535537206317844185045878663628131369976498531751408202962608098559610975170936851920926647825187062112451864287336381786289700516538824559 : ℚ) / 4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((1234286716433916379441287542774488080926319701607218501702673429487658639112375649192609853529540850447038602052285632818436375126733633400275132270354449290985379880440737980626864036234790764534106307923067874390659960148562358230099 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((12612449525059057684610667393190654153496869818679534203884100550772241124048983908842501523076429325577845603511190619286619514537176473080137413809590991211883901135449681580130175211111701687064331256877335679 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((183630163428427379110341836385695153548689071182136320732009554947466139826866716369756335817630557704018971463947499126715467706977347397266740632852939470837175180885054755706359731773265228173168190972731552946430646767537714373190152411 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((31212456248183174709548963250391308229978987338798483596556029093870233391210195003754450492455855592167182724486464379547795838003153478243848974583290896707204770243051635455240640054114267473182045051154588770510485620261674952272095713 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((315343754256686198616560447743967752130105693836855430810302057248372598301665790830928735265943224081156192468336243792713045616238277465372996183285730993941258365126928999833340459316646038393814958329202122462327 : ℚ) / 315544362088404722164691426113114491869282574043609201908111572265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((148189181357688779784660921089861398765321293115126120399137181835944113363526408166352540847421536307063410812689085618846261358027592756960530493208596947513884667597956400914498153427670275771364828715580025831969344025971187977767891101939 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((12627642380656700872840083601829806609357627302193382610283632896962301452082014949034730618630970154325768123648271736003006773330760799463914683503995854753370188351709136797196114957014080389419445926596046239421065633407983673255913279919693 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((7884293375926357457026343915172408484723152127202336170075613210074474082263736158145769881776236579657913168571317612712635750342134063112569266891025930872658291208975623573414653301279006223966141198536125260532040751 : ℚ) / 7888609052210118054117285652827862296732064351090230047702789306640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((1868044299848650531446103644279755267328234049767427092591405165455836718262692604399484453813730988905443523840615834802774743871017837449253153273207621881061628557368488647107155645397960535208477794828332218816789296820063041477133475003580029219 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((638536921451102553916398492108488211072640558027858154104646577597391092487829134349816486365633079722591767692016184723319432216846972219367724175956272817401307074536922813920126200998427167874480701153672555027902668396198100051677280212327474607 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((197122383161360409627714711718514779560553880104755490203176293300588020306739755970189947466652177538180685995474755802286932897110330099740702638626640850863497818778692589934869436470415260896183595604107662729825792676263 : ℚ) / 197215226305252951352932141320696557418301608777255751192569732666015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((1506678936637267726140340035403088454790898197144118763236966474496016205532422877761859439538959644361205459658856837699878520745164825750490740450577227760381209087051345589852269030118501150152539515645527306365881281099267553108524034255361121190267 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((25828333917845906765277838737134001294357427675137990578924940273676359569970691840541367363542751617123680906077473003016645644552755906442014261007047542705986408575263132278357202874283983664196877303076589343708688350045353486869923493629709218114427 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((4928383323076763533688700969985677348403813332499895665149422255581946565233892370186696339850088295378881097820648421574598787415534531435721735864774924624626428575386013687268846186788043507659597692231168148306742277844445919 : ℚ) / 4930380657631323783823303533017413935457540219431393779814243316650390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((18982862345460506358681145564261046423600457096050511136244593054777580179543688817382151152914683848821217260656474770537707144994000779239160004560495336275559236501879618056134086074250016637560184803018257216782354972922912147804338577989555450057664107051 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((326445721230805610011502461343307287536096879832244820089605767270433651948928759133167957407122909994903132289187301493847911840269865982709710395759927897351542713158873749932554222431868899419023405525610552668429711888709166819902342602796956695912304487 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((123216547782510839934436883386933599189151678967227525554571787429494328567251726559826398359194949498485869057415609493334343713670394374776681703658902953449588357942279312454214688016371179980280925152969120374522946623267565055447 : ℚ) / 123259516440783094595582588325435348386438505485784844495356082916259765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((15302921981851790767991322629592051864938648592054017210601304965741851421582414906807103078159173352014639421972713281391636269355699201696166070235793693446218695858546073036888193997362619215664570639482526553281069927543141971297292213137490083600236590088387 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((1320162941218568480358612326710482438340461543606979543751789768539066095960265565355810365171532085578396427365728167014463907320526505232450824228887659970272065353032093369109001952715994555299853398410941248485798466643964689147454380720088949304900002216214817 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((3080563526274166350364337157793895579179731138250897510010809524099709293201661393481545307901360948560926501032182007030101736312191194184570753490813979237560994344412254848827520583296193194915783542815824686617112150706355127037831311 : ℚ) / 3081487911019577364889564708135883709660962637144621112383902072906494140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((192709385667163789959768970482534394910782843739645210101557788451022571689963213095515046989753599476638800453048242458309435972462622386942191213058068912495822757071244644233408865419366152636742509230458117090359070662627855778165984653776762102803424153070107745779 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((66727391309881834679135124028437195845359808355489101246879776989822115178076778565407544828609219700904157920998583165922237241100758970180249327021519779014301414773743430605819301693153810674412417380451890965803229187559983654863441157580912552319614845880396372633 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((77017311486461406966757897412889902090481332692914851951745211820181991093006716557968484208881978086391211816705331517238578653284169160492670619847881135337649671331340838562826450308451004202223251356596836483193933698145817847964864993543 : ℚ) / 77037197775489434122239117703397092741524065928615527809597551822662353515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((155278406998694444630260456565452358700437225917833194903941214045501845156587297472524611472089134083118939936554875148050842873964127531420708661843734711003731853756977300086854261380096831108665417037154993669478273624471870179940831532684283870649193441646444292356299 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((13489289183572407028526862205014515996887055123096395076840081713026458270032511748107835762167906773682445170350737594943377909757015494527903633245033432046152225718848846260557696764584995190318259672027986564590938427533778376285589932892000962558467469133676982032845051 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((1925502130651375904860110450475246126062219328115759555509961405093198801092837868311576000785677994572534139812781796930353542568102331149678823044787466864518857379351135460002085425485706453402428806434467743262951095648210979363268140606090559 : ℚ) / 1925929944387235853055977942584927318538101648215388195239938795566558837890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((1954531838189361078349074079047800017455048411345907635540513599179628111764231432850582988357853877188448566003998894393134614990324318723169079363946437722781464456932802922491513147873817787667962797464244624735328822043659588281321455939796998553556501192711063562805657415291 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((340824500057984849533539197985106369671251443234676800584125114699046183764065485042213253206838552170245857752471213649862534311402535009353974674226122520747492067799690366148811389489259652960628730468108407317827401612644377781288354072074826134743886356534938551271095592587 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((48139045052781341260861751206867611469718884853081393954487466287910576475634830435986934504902290697238926949792374797362695761267585450023040520162512774656394178801980977151024863758474002932046450912824704560815866920679962799041987508858826195767 : ℚ) / 48148248609680896326399448564623182963452541205384704880998469889163970947265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((62968219920666574170731195267604092884584551537867272885955584686620154115193212739731525108392381630358016753678628954464891558266556814652722559246916736107289854969579271680981723227904354542043432158878800956364220258092884737937446990494986851875012528494920345704870022499979 : ℚ) / 80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((137764724547916602231297283449852145874095470777284995685036185771329090580896435975623859933347943563565960983619200234524285952047435315411912839169359815220770788362652665077838797236431884243979854181304688213122135281302161313773361461064115357270942522259443988319627771568876661 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((1203508219122442280035073730858183964541621381027516494062930526755334998413447341544386922003962979769701035470883359015663673912149565786345670710256137321183007968567016761449997894036051225077115298487597869216831745064588039695790277278079927949535471 : ℚ) / 1203706215242022408159986214115579574086313530134617622024961747229099273681640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((19806628151743325728275366800868088215879467535069085346090527204767661000308661959391608182393708622795990284860693845391488946564648431024387185988721432690087637100237701037987675185229359883333370258144029854358863148171610550533267614009181730430527642600853533345543927942031456396739 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((6959846030637336088995254623580079110672319164111020490885227570936739043308613235161224085510261183377784047185428787979878907555676161435909157058280139685474997313347005639147705359928502665158828483906219374511195494411234504276551261179472171829843611435112194884633207066094140335939 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((30088395890530032907648413100573137604022876049624373984776866034675390988196373518019395853071255583785578376085113702503972616872073608761654413989740282190610050427782231589073804694397570005083981416363692960461701331574482497975536235083333489978356587623 : ℚ) / 30092655381050560203999655352889489352157838253365440550624043680727481842041015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((15946057186365651305946861780015863441416129808545825405766602547310363305080941351489900634894621262517961176141668113164124901148552471238689121801867641004816208338589021746229324075407188554234042681283425412145789004809651491128318315622053517434016421701883199946203372662737732281502491 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((1406256800019034639965592273998864968231199863307221874849250329083991990593251760964215668449654959718966914093404590221886592967172381941668116063689763056200546520952691662876314197843159237531934832936878646514890716812987267377696112913329560503661551985708675908386266939235317454672037647 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((752224750106695901373587109248155558646318514445054448734530759318668415512265604977526262987121921373979147604719051081967962906768919545289471408161282690766594014852879148175744760390574923519371692210232126658412580746161841978947711025347753369904385269533599 : ℚ) / 752316384526264005099991383822237233803945956334136013765601092018187046051025390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((200554720901204856622193677773399068703268601554177391037012069419395372534275191561322017080745892692118778051238087531411329832073134557460340779982705960327561588857699086631701073400965456255546767085133015218835154228352615520122131049627819359561909554196715147926395640176431608468606672541131 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((2219536403862046037348505689740680689324413791299111715267817896992228624466160697735463500355458423596486643447621010086739170741747702018069068765766294473007688170213069188970201975273863001739753596134131552512611885170745854077578068660846026451176770997427522659260198003805713898993992930279 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((18805938281888431512033649436643711767432609750993588635626611233089931852495295496990897495641953894518413402420320945926376786013319766177812398403773674526461737041529989114704797030282438329672243214518723740802429849592179706493102107288306218246753040303476315287 : ℚ) / 18807909613156600127499784595555930845098648908353400344140027300454676151275634765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((161403215028009991322605834261923280010276513381733710139359887922164258346821398561629148619956722856440014153713383171241712166788463660224034853267820932016116158498337849417133235397607068190744553176725654812166505837079422263390076956070342730881224041264874169853343403981142772121622584076597603 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((573880925672209397566529271140814220052307944596455803250069728597085075117721381862737634525867661862435668601667889069564518733466104137101426194426934600202434323096736915267202704579261111245296102895749495129126000220207346077666960209516375811063188135443326017746602456301185381552476968566741937 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((470155331079342891762971649215219702109636722316553379318251562654149159682229430454499552823745354132774627526268364509714143797504548129783278126860383060087771348974434655824644298512466095786238968273941303835882673354276562025786105634093331673142398156048685970769231 : ℚ) / 470197740328915003187494614888898271127466222708835008603500682511366903781890869140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((2029243127904681695613008659710683234954461382485280837006284335920209478954634337635743889667180701189129922736114201834436698928040813206198002484633118291246189705626205635434993395550375600300464039357280768378947449058548136695700430954412179283536886513588666360322825110302716398717563930524845200638099 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((28976955787489694396729391185895552448044274283998660331530092934169422654750053032019134466047830101383167532112926422483818481762233092743108060506612148377783846895447620418021840652731103090015980900323265654689925883909625084001218446192527473026056054840180448790379781837993364386957862655866111465653 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((11754031158036830246611602811684609722906089525781720524273952747295847265731255198061008254897233803458380561972611325697480375515715343916027662343147420771668225030487012750755572793898683118649358924477299269421343951870551678860736490506249844284312411531075381289158466503 : ℚ) / 11754943508222875079687365372222456778186655567720875215087517062784172594547271728515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((1632530339711371529908003809209815805619607669281539678839873884221165145807016001282741055219963898648887493493554977635695985223562586194302056847324186018300741869212756413485681103861512875735729174173227491567263518730800922290126275373352056076745576146909046535552101140412868724880296899695296314219022443 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((146293398424061260043856616326187165161885676510921840817833539976564002240019243762102100783006493885899008603023277658902858904347673531562606691420787935776129667072030334429582981871447357672035691442882220411108712372400788743823009318443532515399712395514526039747689819206631019866119504305425004003856674723 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((293853960316019494498225254340710715754415571932784845513715717450503972064862829593220454962604190813800141029716787449729895318469584193665503099988130463060898525080867105307004637515142369931503658542280139183061372436591178267331024120260952900088412909268024677673666089879039 : ℚ) / 293873587705571876992184134305561419454666389193021880377187926569604314863681793212890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((20518063262184442775651039352343705393165575476934909741509381501573613066034695931111767181292675338489355386651540383410655339141818229515928282080276212035523819703782746561538596049093753145814279324453943202125010030875555762743156845506918716484951872186403331561602985733855016512717194771011494989308816627308571 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((3692388664060216666036265570103522034092629897717115968546629683939718841668650287747184961831912293920357552440349378088089480347778462270463652299514379047696571892447908949559729698756679874702466339842787445606832240576804722475202386754970369534344706682776845317256114353230340637701859616384573608748625814098101 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((7346417448607856520212065972955202297663163898106067678411820529460902196961052465972301256985503956977282433972297248406039237986236164758325968190044650651829109970064694036469590766863257804336438206220072634245199305228386018065092321899173879739602026917083014890793578591567766007 : ℚ) / 7346839692639296924804603357639035486366659729825547009429698164240107871592044830322265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((16501439474288881970665041310359224942216850628829952698204843141617761560795627651032104826519861016765114583594564172334036873957481797047965766399401228411186968283159930280419180439427847201740361854683867099984271835055551451080539220751828487936118868125671961336564323781153780757520648359846053078649582198868933171 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((1490907096010711725637131234394981994719293559722329651538644461508519905063807065130232572072298036065277855380452127983294279971992344439498957723890896393893806747468360005646420196198292640542266248630370917872339168184137242580469331595416187191207442454430741398262533829527042233246298825107212901244771164190453937309 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((183661908580134045696115827184272583770588187417857516387554852548997645111464582023795857175904146626452277002046030704959122126797898612445866553672430569472799642786001762806570306167529265144689795130412422580516972653378268406634331121016927674838058405067206899345642256240397350108591 : ℚ) / 183670992315982423120115083940975887159166493245638675235742454106002696789801120758056640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((207329020511403029000324196991521337414620483808726522042762849113358400431927655148092102446833072720466763648975045243688105560214929782764984590034334531774978642003768822631959085563615466904208369107466104304882170474749466319576346934837601766574287935941194177815679280383879428049803456728927262380750608121076498928565859 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((75239201139782782386721156420575904018795333781154078994699025165429550555148610152292023778277899554479236409917428194747905608172030032087329208187312390755322126136816967339880163334733715480229263477637949875507739062595400545887846338927564800167651922111898230861575207537774810030926970979177190382945686901568512312901591 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((4591579389490254434480381087917439013180677237867910810592501480354217742988974061161263781284600906374867835145016258555785594313803192849547927169154998841068338715255255923257746996582057081057711562640562446974661632692126688231924365406437165068791150468210822025622801858499668192886118183 : ℚ) / 4591774807899560578002877098524397178979162331140966880893561352650067419745028018951416015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((33338295216944059928850161291979194582665408143235831632930268931900583121603118799171324776117496069715903971246866087752736609874520787320153500381261693936513539493486296656223105475502609363507166526920585737338731206677214167481432404093676280026246597248228264187225688486900564357912508314303257277378378915947716145426684351 : ℚ) / 40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((15185816678405226003022873616948127651557118120260873168497321399731035910483319095823598804874282853950977903825808877298705820006980607224484563260934593714955964791238430841036019054782840379281333562430955601553782274851458989685441455667209419980992398812977770429271609063658278450172147668183618460268400742003341566713123217079 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((114790166161249611384472470786922438453656248466940916781952332783551071397572711679845855373259994298842531737474734770310615490472848087772324557190031490067903170781286320677043911137469793984794548847086419921765895704105721443933388872988682732124904020022619414237223336381903361833559060470879 : ℚ) / 114794370197489014450071927463109929474479058278524172022339033816251685493625700473785400390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((2093745842273255966745232136032781775102639035552759885921427458432629046756929987891394799656226645227299574777749481161225779708282337904756823358746128145649025692282152872012199724266398754939223658527416405622344580007273803007444895205620524263778411858955218196824651072443273976235132680655773056330149413450069263520228295301301611 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((191536964664904392212190679479531325015995409665685628722248780327754132989521328120661126182221453469913634855797592447690819415080566563497611266493749680567418415974336179836601988793809888113235936614074786800091610725401238405109497116472027492883773017072448280291789584673987062097381937559617369675798999264702529827124209185621549 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((2869768813505607083101557075102926742531015349486513730572036746089803826292254563920613577807051632350999385268293969113692271046542380912246018198829147445830800913017812616725245660300387677994885129347370151776949714282426385423338994824605531616203060182746611458485385635583887023125356067910019927 : ℚ) / 2869859254937225361251798186577748236861976456963104300558475845406292137340642511844635009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((1682882726897580679073082587938160473481795892574348271505038554991899755753331987569341380216729761678992717754803205649469752200292334645813249164388595702809179905440229582831583063767670930345870481740870987833843987892957844780889702243233867213285614301084965312003537976497549090989548527905005186101159378445721050612457674113392344579 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((154592211185186922321851327745002041174459865797766099053659146384975622841971585470350559698588813103325720818263505893966585549653250204496064203136433953665527922170080017621947735551421847481219656165206992996008140162154253799113060457828242120893377282340164282986979709315979342820545449363987926098727158668481877645139517775645470214513 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((71744535706912230013448817633285871114007445118933714581843631791561690397932092872426402178415836141767049775276808157542861827024266240565148589511411449002158020041752202823610209890042240116703963787649974075177519203357838829612291795661738801659376433711427852306396101178316161528495785088948258689551 : ℚ) / 71746481373430634031294954664443705921549411424077607513961896135157303433516062796115875244140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((21132220417682446065200302656452326045627734996242464348475955527053928839536381197899367888748506535800838111800524172686859164957198229725498403974894180377275611060014372037764988721787439854608943965086065940036662872530608942041048799570983680183308919596624499436600667087612896920637563453047177602942114661817105372756601421550856516507316019 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((7797285184622398555111898016089411798579056157197587244915262480920947017980680300413682051346828326190082486574644241552954768955040134613234033478938830191173145451857073604558918956464700546389361984202939331766797339934451546050630530734858071463880012404184250467708822255353998186254017707722787430782272139597876435599376257403602933888665537 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((1793620177211955425146449920659794147824084964479379619200387182555160162603383624934565247040578242292834541815529973893219586484773039633278041606158994502383425485158215139344326445364478711630652372963713892279293970621837186741449233400070986840098165218433947386667499324649115582962529824618543889188310663 : ℚ) / 1793662034335765850782373866611092648038735285601940187849047403378932585837901569902896881103515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((16980859979131634226989067999837565332572055393558127954930352574986739185607493612902082256251698297371368705043507026295513412987524703738350056937109866203018132702830930695016475209316882803673998164163083540610867642418625680079988208661893116364984620189563356426327773504383943476688317513021957487012182653314354160754531596242243702690709718027 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((314579382718407577007221516958998830031649401137672164293996991233191802412882527014366032691624157181015694204487079465840783707170276442555590664745613026452464510078151073314182085261207713870566868154506136174686482898096053861585994197468678121139043929697589480380827129372989566176222781218363315201955558247639461928231230155477485380440156172303 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((44840650386089612582853714816027031565850609781738859182887557753891498504903354697468703583991918710820749498077496328364832964046922401630710509073298448729774632462208682292714494819126030523310224499568376964604451189987583398368797358135727139891031828344169510129377912971176423536272904117018734688108127293119 : ℚ) / 44841550858394146269559346665277316200968382140048504696226185084473314645947539247572422027587890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((213176539751029915689140757124524557992608948272151436931718689895347115868949511755320117788069011437663091929630167281858482212191846346210607039424863607370464542683917069663949789658751860649591953572892025842882558739271120107605959357941042583971222154010633704090951676981936066201003462552025486604882505639570050026002718228303062770608189993318264251 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((7931191947304248604512046693782634279807984119552556375080891892020886034229730370833892687179478920704063031698233148385240766248185861182200259408970710240478611210899925349101203309629280532401435216262555579699812147504919094143845874097542923787336343795596163755091470787922301677740162274230492756181218466846693414356771756140600704421611542585352211 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((1121019399599166223536885408659011531668920916756897213477200737349026255506404938962929255812617121835261783952141178512112651555541441626281475181693869527523641668159495382163166927043858294647972859659214493639535558450202881649107937565573897960475767723168118671413307041748918399535838986269424039345270142456869047 : ℚ) / 1121038771459853656738983666631932905024209553501212617405654627111832866148688481189310550689697265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((171256098630856526585153039443124306302733830408677186367917482558361780974227776420816325906254698574742848339056471258675157097829929510755518326274519955084181414062693356110889131135369198432500889914406976640088381321449361925281823877358282531502549737000602763123622670738248743565219647606245273689062014289492380577966608994129889445866600526713875158227 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((15994783299462098587138623258590280593922150607398543201148638551979085710571890094497670149194909425356359167951046475740932482031674391744869661510914126180972508078716635049831440350110946553556664438449135658281671383430160423959109132828114024405333537631137897721339541303834013664712652475283603249967450430499884841793774408378228183994864138007394853015237 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((28025552539657372667997851842026865120612914395249858150428537147328563038969766185816622970551806507276361758162413173331079472914363033706193375583780215145616103207115224156476210101494523492761840129848681401667328468939214592917259060848191266823715191028515736978114474389144481529214504111614119358434796574674623808111 : ℚ) / 28025969286496341418474591665798322625605238837530315435141365677795821653717212029732763767242431640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((2149420365482753286328595284688661024957589153548618729085489015577832945554397596998944547022217586666827396816142206186465309920956538635998788373044644487241562719339332691294790155236437720487453862767722057592063241631337820394805353569638048968855209986949787392879706953912374943141461904161180609751572378142720679750002052171293259560860003152022379697692664579 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((806306904900275722097823845275743642407678938507965248590021537851699167670343691931043161169602458270204322354674357372785290426915360145523811427418978262614847033627943914313672059719784009322322188365290365061852167289412871610522264368115569333148097646872787978813446045687106213943053075281695839907246614720120007313092285176141506903785329236293679934691417963 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((700640266687661800732858687816162700335231095211478408312507061768953406763868498303151157221855372521895745503347994597871512700806691944121338088933863768427639228294669817278272707913451683899785466713434682994069237352289323537428994176027138723178584904596459049610176687533665231137991626953154549758007778710975181983891943 : ℚ) / 700649232162408535461864791644958065640130970938257885878534141944895541342930300743319094181060791015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((1726342424779019239605135003544507436586485149901064805282092692425136982518694049727441929766534668802088691033120481489718004394938678906096722504276603137848949687554364706333115206676990323014260492601354398015804775849351054835575004674985394666391443407984899016904697733817867307546232105899589711169392434256699664958627559183737547588819868521432284113011468640859 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((162564210490695848290421432866119649148860983009737884056838824866415086333057413073491787145226163404437682782298059278284109592828986390227958764196483284206772211944195303544428303472835804630836936295670215014136140525299021133405170395493792437933930258034964216916047790808801363213135363470321001714406614037924922036873962063603039247200299086795724780061591546740831 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((17516037929801986882321511479455076947198963246946240246085412972797345392373900962687644526723133607335027548013525407784009852732454363793882346307234211250183802718303231779107480765342086075736084745406120335251411503159800217260709951708871835351740897052583623534263731078911740117471613870643213828944021343409209090019467369759 : ℚ) / 17516230804060213386546619791123951641003274273456447146963353548622388533573257518582977354526519775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((21662293412675834021371611113479751957661312443094813469464350697335512671680762880890018286678087984135140119490373256988553253781056813052189516721136587669806979072774827424057760092895210848879718633123562037864583361450270652368158169665678693422432709036020401309366955077102376963050897264657211403016970866505685573508227632637102037443109985885951627474550624853304500491 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((1024100427707875060441031143796637966873514851722524381023774345578449696927938735822242302660254681063064479922458841501997414055276075672928107105542398622928269384218298359095269480036289994030568978882522861254521900834268641581905328627674343978340242575696436392275187110474010681701380936563557445556613186329067167422545421012456607935427063150538048322358407893066481393 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((437901620797588107878270739669166289737269713723097097615496703107835560242709680377598138738628747751385557015414972097657403961833290728297790916107529586625204147878857425263939233704804297747310391127921866772263615667476782073929653191112959793922001918292231493092615646700628265147166829199147459102072731160762315153588801525625367 : ℚ) / 437905770101505334663665494778098791025081856836411178674083838715559713339331437964574433863162994384765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((3478926859283297416363553421573672848937235456241429257300088381940718723196436656804783301129832404320367657204825612855121241613878637686118773742970634569937837594419098507256357027321161169297780090278657184362114338376474286725129935208671997171325806575249520384398732766016922330823255557275712256798336155459359990115123124019286368262781079337210223511089751243646033517703 : ℚ) / 4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((1651367202636412141528472608871125059469235439333341055164513726680450445707765471838058445541272199463358233061588360564701517652773865391431491070827613871634301996230936918830231847354751454130946388746661335324896790699873313514437497960787702428913724006245275723633302910856617776819706001634378902239848883167986430517624858295585104342209225260344388423200365300121782646038681 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((10947554988562462066757440002794004875422343786113553641038710919560023127915662078145739809564969611795235222447622294736903731430919583437870375978221283997068016833317859789703124734691454857437888444334983119871707163854428012756448629100413104046644027268220776110901440407470615868110999996561259287662890665461479685899155887220778520271 : ℚ) / 10947644252537633366591637369452469775627046420910279466852095967888992833483285949114360846579074859619140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((218223274033934971898707006291711772894468336216411494734708463573118412981393518937500419423906015107640591159902914374299815080766570365147187202391727014022826858960977015176265421899937306869400633040184830717516563853532859655741263719348253158289062007033885412639216830215230990583806261677954350183548324687925922056218830175956552199337519030490472459124843649291598836197642627539 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((83202974621258996826902061480865925215161689277379152390117084708873959526146197618722816188349933423270855282270465478439616607653578263189138146587615674805124103039637839014608349303881474991298701081809712294092718372991776626610195729498796412402826812655100952207578546342732342699098349735456924328889875616581178334951043843610940197920493393023606884702656754923244137607048979669 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((273689185977542973991457846287388188992572392740375023980579046652523695561205856391711076795192425294042838699890698426675009974273372998498905398419474482628924246135167117655883322417417268348061294102978491857800036216000309838429479357837187107355452958621233556473822687485915359170671942926022371055491766886072812482748540601780608306590023 : ℚ) / 273691106313440834164790934236311744390676160522756986671302399197224820837082148727859021164476871490478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((175195556560370706045769184441664328524521017830470465994594017005577510584460940398372726674556550507152442724137131844031938729533892676091834749382901333866746404342389648653419742977181640527955150336910289372096123103916462826822097954609100098404790309636553073028584972385823157273609658620420403046892874023048517210517180082877845996819218878551486293419896026950455654801128110631851 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((16766355571520568371580791594015046314852817667720662770042926053689876093995167950964596205833556006483858039659036629442003073718185650024519776094191569938554148998471456948177557112206402162424011657699366699494430320088377491960957302875630335109929594673463570315975502251531211362505144354567872162981015451090946840182799502742347088051184762361985165780480650633082110852916858843523827 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((6842236345649850188210858634862601162487497656766541503417028496636465212867127041168924801895505496238042172935123595253059489576543073316706951836198154544796047307105850202131017915165897693971842620037376295336852179114814665554133389425151406240537859498818597500421347475884497121838665508167519268516794381020084414941369353966106226499671164799 : ℚ) / 6842277657836020854119773355907793609766904013068924666782559979930620520927053718196475529111921787261962890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((2197469079310928795957877709282379096407583154134218916291351844922592933476961835267757333571264268075242200994507546065259125055470352188756433410779414569177884079937374348958069606280886003922925417406401142176917656048223253706401865773127655341134414505962178837087750111882265362452620901766099081916064093414027541425963161372893765818865805399909226635592133430648467435587557177643463274331 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((422273391037869720166721951133205007436315135519206801520627095936437339348237840068206217886672788432689213203771570854431938830994218280112957119983147936444092042661306982116189998658754439597341620802540116502007427742158478483298410220115853607508678400314962558742681161796550996652898945073055257583224436566509824986474236347180524737925820336306633933741274870349453821631737227125522042249 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((171056052696839431817295851503849615125850731383589947676081320698158349880883140352018189433191281012751465865962688904679068799260171136262316654852130898722197365717768155398444588408963957090416250284864076241581700929297007900066071606703282202452690971398084488026564448248703186582115211077207842023601797518885076018633678911872843250687425768320887 : ℚ) / 171056941445900521352994333897694840244172600326723116669563999498265513023176342954911888227798044681549072265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((1763848910730866241128940204947591350586743575322548867353329459215653746264609309402609723924857209448236669948335645660939294073402089351508277721518626495819459916651237393216454411138304085297654823431236564597613041226633872404749381687054481606941617057938172209709026322124731145930237184133885817936875298202181295479077048979054110903909409414223776109459317021603875922670313459428418711337843 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((34028636758087974602220002590421836565863102237429202057785540290970227019690205890019037648000550864317950244308016749243666833347204397148791624832084882714006459235274966441802652378193259614169319170862064544372972427914310944189788089972167511138942066844339515002882097104287547924065149199807841012896423870226419491332363049013158906131386316080673692862466351906922572283692997423882986856049609 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((4276404416488961814643376895703578678133856641594454052182307118429932424899254906276745063526575810231883900164689701406360807078484061654411218195833892024210631928686346327086738430442041608886124792378280872185147132091966530954121398475007710021364740867686991590915480975174351652941044535903972305453745470023774640388866334431120476852038590553887242031 : ℚ) / 4276423536147513033824858347442371006104315008168077916739099987456637825579408573872797205694951117038726806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((22119750568392630752543661597006213121661680663091185648109324521175575736753663524707885890839482304372371997452665196270656046413670240921520826401580080509110747661323452608773011688269355878338215495055815879765972925800471023673552189153721080673528870118443116014122572738517359867352320893622172316472444957058960628747840198824216992990858347108340777713708338957604563540098938599683539322587295060899 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((1713648853527756627521455379845212482218905570522687592455485893874373876023418814577415452713749230333683559568490691787214897799045223207200904980247080461843798988703149064729709285946633760354389092935107251172532104992654535982794181018358165617930588451596569048100155016425783487937062972010086996577331337504009889565482829864082531063526230217573800924555436707449985658522399053395676990907876061491 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((106910177082473413467370248214802635800979404364103577720267214695044432354653068495826060407905519950632558718998828921355040042679427618371348537046974519116843324681829368534617003854099641131967202658433956403319070252694475980416013645392840865689619670286550250095364742218925827109720691100902156207226426296621463838685681452616694818517906198585776237812903 : ℚ) / 106910588403687825845621458686059275152607875204201947918477499686415945639485214346819930142373777925968170166015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((17751721207481022139147892728613810353347938821630007255372704150141857673528151051554962531079660505528764331504197947665546483341499795157025091027981430842256779551559524490132218958354461874295737290932067515716175951984622576176395856008826860919120697752429529134798387555698740751992074321022436241004809717231692672217221991455113812234347958745735491978876920865444029436531297271980342684499232808644603 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((1725743230482126889007933124472303254521725631295424272154552581842935944365431581322087618733453960066196806415581041128888074454108373314678670062053118674430461771821355656410211340944138685707314918656072663326766767095400553568947477408118694001178067637653781759869039738213511355082894536488223197382478129853569666991699569745827622676603261818625227843627646397210280782301880552351195860274461274591415303 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((2672755861338909992647218176283337796443613586922012459887839631141023275690536404978067133961728814325809245090718290960110976438162526354022821077491562829760650443880195205285215603913245579672010430790889704104603158346216261766689701553336185543580787966874555530301581699355751318611421227653708086486062108919217551561645065090142955630775716050175804204068982239 : ℚ) / 2672764710092195646140536467151481878815196880105048697961937492160398640987130358670498253559344448149204254150390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((222578563328467350235344170668024519999466589325302112755204448998505441544075196159961751271274685346937734522965500671816931228044182999400427456693325153580678522655333739513973926233350359347596111838578183414354504312664880451531447691352026326237947247321893446053154814387206785923646099599785255369478629441120548913905706238099447784049005096261001468791127538612785143222676591566777192757303994809559405209771 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((21721421581144015254079381338834907521174408245300054494754356648713759371409357313700692747568199406425476233932196872305253906636805476223613045119415351875246637119797438275638426637054153606454288482333186745170376080654106635928803288244880397338535729411179469507121409400177131115642358019488197954101921589020939735226875230058416722526350672176650857658171515972819101150231134180556283767058745587378840224343 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((66818927389075456889911655287340663326320050616379558859360370019900143791052633240977185663080106073287409523859034702799867436114190429454092949840075991156640872999194639451300843286985652155483960397604410204402327745502150439386795549516921359599053491531372313123377927098240278117287504870514222064574654149179127186745670285284245404484877979387432075842136014907607 : ℚ) / 66819117752304891153513411678787046970379922002626217449048437304009966024678258966762456338983611203730106353759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((178595249206993968621770415689816112728480058980977568571253700438384253296341990420701014376959099469984823689750308667477946751271018939718908208812639277502984246099772375292400056708346942718762148253009711836109994654606613851438868500189455867712243225001476631937685654883611596573909076509002327049307883735089511438036371293683247284029714230103721052236379525650660524497215487151793645384788973621757529528396611 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((17495592316693910262111480105204402962547109698041805965390215927998953851799672270437968718003159026802241822274967233502024007548647397992077602648888413175927827764004458544751360337026620760877130084125797493438711224508142839155715809498253087969883071775946350419317864969745616584209263476012854326586418995297920794496384323619786518708395848458964283639002221160340254794853455730927914454847760660981325294122670529 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((1670473848523467459524970706720490122924838036933331069986251541117194544904968387930242880423878174222038921942339716295708548153124578708845901629909554797752815100831674278515835041632922334820926440033663676727307276788987762402528132656757529209054437763314412572223229345664443103137206092279372459275194534711290563168459604847319971386683179970561826247591872088707349391 : ℚ) / 1670477943807622278837835291969676174259498050065655436226210932600249150616956474169061408474590280093252658843994140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((2238934108500206861945681022563712264201334637474255930937302209178996998518230962438405817043266842499899875891727468821355449425470345106367118981227898041956579329163099668885818909007213114786153432201400749590679366590183919033466416769647464301035312480457582091555655510004327091197113324502642227917804484965405445100400558903408583288036450345845259709870127142003799465490311401002145380383106821224684505054725969260659 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((880639381422473350617816524082503586731805886230193601663161815056568373512713586893662045979166101261940893605856688883244555292105508967559105850554261789813636892038862738970678174684296610624184340212331630077787619968637151361060462705709012363176301375389618111339098712121652357540830065615460408088300219928168403106954995874887292567363411338122119210865287681936074408858789492224252397135735452923215771722054326694121 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((41761860493342534343068226476776164834124910389125691814735026926031275032741912154970832217909787468723895349134561885028952996418169061763401881764244252364056311264191808753711159250649058189002590504444206677434561445561493732565587717844824725874388119602182957666238332913279164477790714663206139716387260025243993885443071479080394544441715250706696568064443944244361207448583 : ℚ) / 41761948595190556970945882299241904356487451251641385905655273315006228765423911854226535211864757002331316471099853515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((359243204630118499199927149533847843818849715774913004967587556727294595664084258464590077518711327155800639040953860145367666042117830360798885421840127079694378172888212727023147747207593072986614341104576268953628675649844707035030989103767712188618488444072441534254648007146181619421758110481463666784523831651620518253793838440813406412350106472949710198114256344973805970271354039105234812946964782125804216038623306214748943 : ℚ) / 400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((177287145808399986533606591250366374601581630639427379734544208022706517532915752173788584542614356623609974622397731975639071662788838180556442268079702079782800602965694750955557845569102252606453071635028467902416521709114041910999728048668225322483015211591852967691585333198472472814998218023162549483955946203113390207968511781459328226990764733978545520839372228552740397893902320019826165129640030951266174282239833564446556059 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((1044046819544707413480115047772342154567600939715734520663414572309137539484409936825575441787665665481786461180657019041612240811944071025716064682394186601107943424226558381718588168959213188820012729522108218251649720378364414668683488573995714327735711617001761968273785255963374665410711644549553683718639124923074040457536796729456527834574620188453163268770382572528942655841366079 : ℚ) / 1044048714879763924273647057481047608912186281291034647641381832875155719135597796355663380296618925058282911777496337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((22514521973347072633072496362474564456818571823026272646244221322596079696523762095137703393925273692883649262170787321364989217176994024722474214247492282370663111793438721667989489760047949353689937964434090449089844014347075811270264026312577338976074982234540063658442823119753872176505869896020937756194518839176874033383630856740937646480047253009816416952401969885622502126029949741783074515183702947207018817758008407012471674690811 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((4460841428496580721129371355755288429273210527249229721812222846127564506259286624102887158353176465803737787044115197166758929445233197929992637686898628448664653281042885403822470726189882959039004046826909206652880692524935650341434774122370599454186478224813563592210893728003604708484550115252652410087952031503233674097083782184309967235975863786161053440406157262464670193714272807340562866770823485973743423361143501999560279314483 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((26101177097651027390139922312162809783489592578966434559357536145322143879553940486820802686272361653187904652747604180866813511587352799976229699512346136349635186885385950465911987278819553331084933850209114099247740434499753652767387889692369802332578364016558905223473942211540079176980639609194548397839083494470091832362989108040798283305203804114192901401057240282815143355115308457527 : ℚ) / 26101217871994098106841176437026190222804657032275866191034545821878892978389944908891584507415473126457072794437408447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((18059874738862394815732832731186715655870850459521692812315957604321281771567268136484840786786171677995329428981583269161716040767682939349729372697238319650203474709395764941422238853311297184528926835289850971474084999527479001582636453267793807947264467871574903363032460582170123853416786915161738147274837080286400031287090332521149979523120749346707693304997733385353398965920965702713873689360000623693386006885180337382994643885043219 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((1795673467640100828091491553852168799574598556915641130297970804210760091700412665699263240945034588444101045140310309361561504921127519784494131466073703263799824230687465607516890236313738172930656446883849585602907162669762537837012191653628891203868282941202164096030214866601625536656231779819831030372331071502142350409721095605588961400470566511883194313306479511194266871905005650545870484246069087040535702861166106086231649288682797333 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((652529569621409972342635330937468852179131444222850852083596136375206981096489659590280883367135071036987205628762451998602993449778720785888629525609102431289701775465307952373164582329245050811630181919548671617116639967393200331984815670951951557580758345088231728072594918796861723334384499912602319682712203216535085589624984681281693468744849437908631887840944410204202178998595630846778351 : ℚ) / 652530446799852452671029410925654755570116425806896654775863645546972324459748622722289612685386828161426819860935211181640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((226337010258456748570826972451753306507334234481287216844211374030085831520538526621067432425301579535451364898131138490500557113081034637901942237330677692142020274021311675478114658124008659586668973911457601113774148899556246702894213942688529750538886760999094147022083718335267876345797697456074036928839686477770194266270082387651730108994873118874811544782690972747605325335749279030894328078126750805000105054998154349891783395234563951562819 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((90344080878474968563297026756920718071496062126043622781750129458733731642466792500590150391210557365534052171496392819808788161768535649828835018990617061891310364400415510955674751369981844765359702335226957077251705559954194523237961455114824373960520664681228896824858063954018134906094410591373782718474481669455211083009718745576367802882970671798518182594328406355769894451836694655386521094925644609509585557555676027002723358066635785368467 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((16313242299256478237470993430355525549602650736354839016077840213862120279719925494198336523311120653017601075546647711236327057460089620266822086984428620604335354295585169979403889659649048778110600103635250572499030275618529918741989339529189333858234854277883129166025734488076886254092613746619813703334187627797319296289602295448413071593107945957728397803122237096723001476796787806406742665063 : ℚ) / 16313261169996311316775735273141368889252910645172416369396591138674308111493715568057240317134670704035670496523380279541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((181529042290490663942605363372958442050761457253158530798497126899693234939950202053759992165861894701077637104713471309595792505774296016510293856078355200321619745895631142236645982793827430270407524428492679651225446380208918940260943854999339595225931563807187064774716941819105185357798338011305200525112708611174304280078933922382196691559150484325003191917338144480191051416000647724347732520993209605236072573560636448421436789557011395457509787 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((3635921186201630148806911729129291144734694145346998577329662353625014221640234338685899229347876472237409721533319869266170125345986065797537170485188902383734067115266641747468297861222689219079546014318661472740098238516408851035943896671748515797091528759765579158921269786554103618055190172198023978001143023789810976697850412855815324047186150355660559375948080435512301989457597423085607715967194693434218567636648094914532162146701198736391564579 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((407831123283681753884310470564682374465426724710917867632968489821373105962393343342504410611840735353340034959612059246586625471513908000800143557296012915061066476960923761766915878248029986363493340029505145566171638319381434141896416661291450139292206420080099757748711626041998053984294399531032052199828378436803730021078214181981710409182531241388611021938568686661801930770329296079228254953500319 : ℚ) / 407831529249907782919393381828534222231322766129310409234914778466857702787342889201431007928366767600891762413084506988525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((2274716585239054775756630247819415341754589786654663350692518743328382353709417412633216472500759248636548725836051654444826843203682117978476656288998802821068391215163406132974077655381124135785367052388801863530044898494572326943812065286080638807133596601956473700435214125084964143968570563077767809726544214087157518225821071710551286112777247294065693476279970318779542198950907105301164316975929491782977150431286551427774203394080068310379322012261451 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((11430687891944599360757949330280830573019633226961815188812061187652887489940126988694097907182000671456520762203097171113054448458492306527026762983402842939612450272504045461904147569346779203278297493744173413047115918308773030588452706198581339431560785415956497825894718979009929982690108900959804270230210682975819604422910864041281512422388928259040229020592704507830544814437874770731462510649323462976709593856608005675113041698326491585166204281031 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((10195779497696274010353095875694110754795347614198881483390198954041132438188432649972687310138744658280713747620559906440806110878053702821213488348109125841708723118860352886891661288749869096637832224054744196565050455164852792694617611634362966846593236715183186088448033211041504135364125417111092538974907905310958643943455621696972536032743794595993188914964428156155344936662094146552437448814652362647 : ℚ) / 10195788231247694572984834545713355555783069153232760230872869461671442569683572230035775198209169190022294060327112674713134765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((1824147322654250225670762850370948904291219511820565605424627368404314472562033347993544399328834886785733976813562685483731528226307680581520356617567978141203094963995197439666726121107733313603703216572061553163216525573157892881181531259673589818490089896728496156910166619915340997297967179194203423755123216444176358862639910481840757510071845065685993318494401585341587869279017156029919984756471480256465085026557752088793912633006133673305095494247044067 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((183972978701288848889119004012016358074637537068906098899004222392114814541401237767316690794354438939005239810474945409659844620365811672295616019946130589510221883149447543141427828995029714229786817253283659311786817608189032783669767226755586035561822121415528099649520331071810951689575240083525899603673898322789474698711136818977501733250071162705790600663138201074485908785517332345298884445554410997041523176316062530353256762458362047939598142573844583657 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((254894517896300653760724269634709875490927875361583172277227045911135202383234367964997170219170186799200734240921747163985762791053944308792765774832871624232679760456042771655700309304875933875969684636089711900703930441961478129239308679090050505770760301453735882320782538469135878464088430098310933790967193766954653307155560789566970167672417253143601473127629742923369935622411631374782586836349616277624911 : ℚ) / 254894705781192364324620863642833888894576728830819005771821736541786064242089305750894379955229229750557351508177816867828369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((22855190319435412555332668909734213480398294110835280455649642471096354434682647535987743572706128732100703741133762104897181985977221735746043073111405205163774835877184378714276011255348170511809585872036657720310814930110849706451794209243442940853426873220069528283102692096942603985798792895091203424010856796621121958328756206246969053920240719907859189827017999203632332391825702470074665016381425568160307715499513392741859478954115434644424914197475415224943379 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((9252098072415545007435438129097879365127978561911469439209117659677738851180824919808966501511965477187090154621643214082683535759304717448659440051529242689434184369621544075098715297761546450278756291591097831859932983964792635776919322331063135779529050437648665394352634530993313282131097846828957032855491893419144708823647567840260108214013619777747297250751311387196908898885902249319212513690787539768568818026309563657048087664193997953374671455462467277495293 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((6372363602562133738754414164174075322011720436086804658326327834007459614882686367184352825828892552751398880433965594156943238117302878915058770113979567252117639686690848146629080754075795965473735825576197972119843655597917278994325247613264256530646366365174220036366994750086520153397934396704963118645077239508495456596837579265954229217136712366878298491394698659510457425044941425765697790610389294980544710343 : ℚ) / 6372367644529809108115521591070847222364418220770475144295543413544651606052232643772359498880730743763933787704445421695709228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((18325795522514015674439575664997363503935280993712177738506427442708225188703787807528505794594899111205079652328717120674047991595755541511694503704176867967605885901884220973351143025703432364682796911306044205812064576699774015493201528784427191867437496447684373816426079380623262504523208890712674080036270751644071252307875737301314670503141393138338821884104972063107807703879268005393052015318022223753342876794754284489324054773587434145788883147018708845795229419 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((1860979477344873692292788396584859702704191164249772840849764157092822878065508045370882830555011789443960303293526827283964821949251995543891741626737106026804804869668092327218761774813704753418260040190269345783332829924172455938881202621451482712283243098010495202189429451904500813628288890773669999843692170478571876340963419586316792971396326072364648323005288096033143654696949260240518257191460145089602197388079525113602799070738440084491272902604951472085034028611 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((159309104158394627481822535701940926666822868077362075442732850576032678845275367046071199914654073590845681232501303012551257961451521209099659321462042430294806782579780216178431414262432598605236478815620746974214196562877994423004919051904153950743795279613992995642363158058611308060049762676313871571411546653546262757767766842748473333148262093148652835445374152262048470584991824892497456569401304902916458353608959 : ℚ) / 159309191113245227702888039776771180559110455519261878607388585338616290151305816094308987472018268594098344692611135542392730712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((229580351966191176112402481207922383937474869005951799540197768486964477637766417190852069185882483101898147185125202634781313443797633877739086748522628270108344532484683965888194896818290269913463167308130328683761068120402153037514796244176473450674083785934760305710452768042769283089055825850308281790337620108521758876780520951976353260952783280027746808039409429948276494901329110782714347174703926864325328115982598123894850994228987743109522708774795200186344540993025691 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((46785234689903512570829337121835772731240602585202629330413356381362403624527207034270527717794848212319344928196129418765697220376181824652564806451718575918274415295902224545376661417330098174728882603613155509263842326286893246318676399294465280504599182321748573817446865435693610037615690109169815098444894947346428451596431385274868694690486061000544842727421330323471814245477450775146051266022361432239731400248673021241628649711524725549511418337649932695461538249662557 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((3982727907171429730016418805257456261992978519343956499703475811517946023756012351982985163078880787747484068297935561345338664520556185146360970982612918802932178313638811790646595015027712493794452368760449129656270010657194294022104823563614063942351267850335831315254158619314905070295850544455540319115776603157740750707857968088047906816018562409906968448936334137613448747694929128912297783177530272376441768561189534967 : ℚ) / 3982729777831130692572200994419279513977761387981546965184714633465407253782645402357724686800456714852458617315278388559818267822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((36812149361949104753173272493231894922523746586084657052554172298244784796546675836723363536883615886376560790359128618389251572822701843890009946479969366145539113661508817467220113108710103600861692791819139172663897404365927100865752240139233709954566732864380915390794126069218675825718021016176867443626154853741899235584676737323709062699887835688345363485352713311882620890792627131112017204980634630822922535559798956810181028079633953714972528868373896202149253827660410711 : ℚ) / 40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((18817094331813767712718924465847155036637608771261349624109749672912558022650831782341710775947723684970848573933822609903515747263157614128571586978318565243848110275008599007474796952470589161891260156186217997737091661539380164314257259718051744323487025415183557634318240872667531498858241413426803674307404342793114562024420722572145661952471590740651989260882372541092928378621410969802950361311405918611426819003344856453130532316204161436696722100034495482429332887527372048701 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((99568204202276120506842482625043684229495400846538190445719975060079447903003178246231345796189154951502147959871863472130356989726965445428663568748951722207479952061311758052180198558291178879000053809143542126295336739268220847297541069324029357591802825264274739085062714377321552777274632762872038885137702063732476769978148467478174619333007333124328612241967356302478122909161010350290262209498208749634391767056870465745071 : ℚ) / 99568244445778267314305024860481987849444034699538674129617865836635181344566135058943117170011417871311465432881959713995456695556640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((2305594877559798812357678480016071332915745686210633842788265922535032735764115199665058722533458084622372825329161030717418936836161183032784397323632464064182065611394541320158685336393521790130411482403649823466787540200316390536491882113364056345490911894700911761215137969733597317932493444362174133745932556091920269408762596388974014446785456328210518014733719882758481378100513075986501024885062804207506352065185268090357669390154793597200266512885436292707991937373502438902618339 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((945939887150735652652796662309637794500222304370525415519926857469998540941185674204128748803278788980654026776660438369567468993616756871408887146901140449405003153449357609225963936057593717346386503736574252712867897033314753221880380765865331491331466471874681535043372278325017564915615606280603400358373393791561155281693154844729934929085701442048697710694460066478511125625473999418044408351021404926151134815870318860656374388328641698702104110096940240754356223617270329202575399 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((2489205245385994998588683950401065470460145907408867447748751321639836040085809486561709591685247104588928789025182792398642527417402213486881839354496198399849516208694999850976552611584518131223928157596105021762991579271877235087912001024367843569872454179910342461936954174399318564897509174627666172535967384497076772752539907980857970585710986757503681435161443736135211858144780815665794410912934964830884670084694454329573712423 : ℚ) / 2489206111144456682857625621512049696236100867488466853240446645915879533614153376473577929250285446782786635822048992849886417388916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((1848250452286236356578936971154883694167152710539817220799676185385657856466894347010461182461281623857505839786362308823850462859492190792568296465491316382978059711238292721259459920023877401639368760550007174174858551176726826425310414942611407518322302243877154760376946166100981214612786426024321872403052954605081310925710115927866103112419436155239293518801264137223715384141684735244816439875047000742177618236675199642674966803129586902800739183155540859105872823821993262990933905211 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((190192063985755091390174743134075582170526896589123761073498767921832859720208127167826006333553345325797209556432051727618789063929698827648526423473625944423358618621882891794035087577322260949924449325971177241459211994529408712069134582824690543957876799288895715682043066478557318413644884692701627788936512618483083702456359216765707814733706596118602090672939842288470366425958694325852932099464470511530307271240033890036946899994686796995325855495750454104651896046021326081782433522007 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((62230134153549630857762898367190638756784402631019249320668324636746464664078572308165424685220466313953202037410242250939550629765723965227664010033276716175962642197655531794058576333017738557020366454365007333187237844875894958446250878037225418718666106772411197383649695153852540286640114873764982369766266342685612612225391040392197521210400458114176698714628139095476812704268669687418235161969969898406821907532031795992119275355999 : ℚ) / 62230152778611417071440640537801242405902521687211671331011166147896988340353834411839448231257136169569665895551224821247160434722900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((23149167461584902016562851965965949147689191850015334245973929216277559002864862219665877425292338313694533675112251858285030996533069184882865178460421338463842730942294042539547952347571450139177020557500475827511855672966959212344142100057662893095683779102743054510160845634226100959695839096510946115158919823632491469702622320328616567204655357832676960649635442500353007623380309404585434994457400419229803327744758806995057739736683373440486458256222733623142157352369662388898400033281047531 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((2389790405030552310861331901930658702480347604306323723573074630647296446710688958083823197151623984513972745274366531082297967438101368386480634457226316547863292419961237056916434281677413596798665223976855512930774675613182187153687526972896033275184117672531456686459168021081644800694715802014513072036272316978320808600232705534637098454842775018334510308062136592405395464743006411001418041398517395633963100788656895680521442240885126658732762993497083908310555452603179506992203994942022017 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__apps__causal__minified_base
