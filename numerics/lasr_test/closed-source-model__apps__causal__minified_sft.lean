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

namespace LasrTest_closed_source_model__apps__causal__minified_sft
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((7443 : ℚ) / 50000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((7443 : ℚ) / 50000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((7443 : ℚ) / 50000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((2371 : ℚ) / 100000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((2371 : ℚ) / 100000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((2371 : ℚ) / 100000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((7443 : ℚ) / 50000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((7443 : ℚ) / 50000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((7443 : ℚ) / 50000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((2371 : ℚ) / 100000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((2371 : ℚ) / 100000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((2371 : ℚ) / 100000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((7443 : ℚ) / 50000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((7443 : ℚ) / 50000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((7443 : ℚ) / 50000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((2371 : ℚ) / 100000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((2371 : ℚ) / 100000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((2371 : ℚ) / 100000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((7443 : ℚ) / 50000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((7443 : ℚ) / 50000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((7443 : ℚ) / 50000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((2371 : ℚ) / 100000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((2371 : ℚ) / 100000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((2371 : ℚ) / 100000)
  | _, _, _ => 0

def kernel : Fin 8 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((42557 : ℚ) / 50000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((0 : ℚ) / 1)
  | 0, 1, 0, 1 => ((1 : ℚ) / 1)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((1113 : ℚ) / 2000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((0 : ℚ) / 1)
  | 0, 2, 0, 2 => ((1 : ℚ) / 1)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((1113 : ℚ) / 2000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((97629 : ℚ) / 100000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 1, 0, 1 => ((1 : ℚ) / 1)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((13633 : ℚ) / 20000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0, 2 => ((1 : ℚ) / 1)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((13633 : ℚ) / 20000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((42557 : ℚ) / 50000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((0 : ℚ) / 1)
  | 2, 1, 0, 1 => ((1 : ℚ) / 1)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((16099 : ℚ) / 50000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((0 : ℚ) / 1)
  | 2, 2, 0, 2 => ((1 : ℚ) / 1)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((16099 : ℚ) / 50000)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((97629 : ℚ) / 100000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((0 : ℚ) / 1)
  | 3, 1, 0, 1 => ((1 : ℚ) / 1)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((44713 : ℚ) / 100000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0, 2 => ((1 : ℚ) / 1)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((44713 : ℚ) / 100000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((42557 : ℚ) / 50000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((831 : ℚ) / 50000)
  | 4, 1, 0, 1 => ((49169 : ℚ) / 50000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((1113 : ℚ) / 2000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((831 : ℚ) / 50000)
  | 4, 2, 0, 2 => ((49169 : ℚ) / 50000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((1113 : ℚ) / 2000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((97629 : ℚ) / 100000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((831 : ℚ) / 50000)
  | 5, 1, 0, 1 => ((49169 : ℚ) / 50000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((13633 : ℚ) / 20000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((831 : ℚ) / 50000)
  | 5, 2, 0, 2 => ((49169 : ℚ) / 50000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((13633 : ℚ) / 20000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((42557 : ℚ) / 50000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((831 : ℚ) / 50000)
  | 6, 1, 0, 1 => ((49169 : ℚ) / 50000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((16099 : ℚ) / 50000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((831 : ℚ) / 50000)
  | 6, 2, 0, 2 => ((49169 : ℚ) / 50000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((16099 : ℚ) / 50000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((97629 : ℚ) / 100000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((831 : ℚ) / 50000)
  | 7, 1, 0, 1 => ((49169 : ℚ) / 50000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((44713 : ℚ) / 100000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((831 : ℚ) / 50000)
  | 7, 2, 0, 2 => ((49169 : ℚ) / 50000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((44713 : ℚ) / 100000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((7443 : ℚ) / 50000)
  | 1, 1 => ((7443 : ℚ) / 50000)
  | 1, 2 => ((7443 : ℚ) / 50000)
  | 2, 0 => ((688901751 : ℚ) / 2500000000)
  | 2, 1 => ((23170059 : ℚ) / 100000000)
  | 2, 2 => ((23170059 : ℚ) / 100000000)
  | 3, 0 => ((47925091817307 : ℚ) / 125000000000000)
  | 3, 1 => ((55560275667 : ℚ) / 200000000000)
  | 3, 2 => ((55560275667 : ℚ) / 200000000000)
  | 4, 0 => ((2969923132469133999 : ℚ) / 6250000000000000000)
  | 4, 1 => ((121382586817371 : ℚ) / 400000000000000)
  | 4, 2 => ((121382586817371 : ℚ) / 400000000000000)
  | 5, 0 => ((172909768748488935595443 : ℚ) / 312500000000000000000000)
  | 5, 1 => ((254186819127733923 : ℚ) / 800000000000000000)
  | 5, 2 => ((254186819127733923 : ℚ) / 800000000000000000)
  | 6, 0 => ((9684458528629443632135267751 : ℚ) / 15625000000000000000000000000)
  | 6, 1 => ((521085929689167856299 : ℚ) / 1600000000000000000000)
  | 6, 2 => ((521085929689167856299 : ℚ) / 1600000000000000000000)
  | 7, 0 => ((528438376602883232652780589679307 : ℚ) / 781250000000000000000000000000000)
  | 7, 1 => ((64563884923596922984804449043239 : ℚ) / 195312500000000000000000000000000)
  | 7, 2 => ((1056320639744043824060787 : ℚ) / 3200000000000000000000000)
  | 8, 0 => ((28303595743088901732004383554982267999 : ℚ) / 39062500000000000000000000000000000000)
  | 8, 1 => ((13137298922190344391293860490051577681 : ℚ) / 39062500000000000000000000000000000000)
  | 8, 2 => ((2128388872035120776179655931 : ℚ) / 6400000000000000000000000000)
  | 9, 0 => ((1495258311538634391008910550949380379233443 : ℚ) / 1953125000000000000000000000000000000000000)
  | 9, 1 => ((334734069383841960357411734584768143852129 : ℚ) / 976562500000000000000000000000000000000000)
  | 9, 2 => ((4274304814575089423887957051203 : ℚ) / 12800000000000000000000000000000)
  | 10, 0 => ((78170817339149663778166206316752780799037633751 : ℚ) / 97656250000000000000000000000000000000000000000)
  | 10, 1 => ((6831927714391371175311111964687172965054730547 : ℚ) / 19531250000000000000000000000000000000000000000)
  | 10, 2 => ((8568117258622074528787296197988939 : ℚ) / 25600000000000000000000000000000000)
  | 11, 0 => ((4053570942252192241407419242222048092464644579541307 : ℚ) / 4882812500000000000000000000000000000000000000000000)
  | 11, 1 => ((218069402269172502149252054800967449804735063121787 : ℚ) / 610351562500000000000000000000000000000000000000000)
  | 11, 2 => ((17157946508846368950540260668361689107 : ℚ) / 51200000000000000000000000000000000000)
  | 12, 0 => ((208850592026926545217575540691243700671017879371539401999 : ℚ) / 244140625000000000000000000000000000000000000000000000000)
  | 12, 1 => ((89146552974395113818022159650356670280430266194679986141 : ℚ) / 244140625000000000000000000000000000000000000000000000000)
  | 12, 2 => ((81905416904446003659811954772388430775277994880053561851 : ℚ) / 244140625000000000000000000000000000000000000000000000000)
  | 13, 0 => ((10705193316764912984824362285197258169456507892414602330871443 : ℚ) / 12207031250000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((2278400852586204655197068421081405318138045808141984740813999 : ℚ) / 6103515625000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((410128822929642789353207041887301314579268128146513265113499 : ℚ) / 1220703125000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((546437845575314401895170385771139715917560606377488231394895999751 : ℚ) / 610351562500000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((46589879737570767214631671890260431542775501347932605995824240559 : ℚ) / 122070312500000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((12840183947704645952125993633837779937764111128843192872680574353 : ℚ) / 38146972656250000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((27797602073836155001452766107262392890303626725606766663472589061403307 : ℚ) / 30517578125000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((2976994708439042883464002491609223224140283998195546060333142249005109 : ℚ) / 7629394531250000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((10295005022704642326898122292418748921219009489606115183621948285325157 : ℚ) / 30517578125000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((1410124885440620248396825367226765654232651442561647168897402972686140535999 : ℚ) / 1525878906250000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((608603218600315042954373402674870635322856809438086440059426806475354965801 : ℚ) / 1525878906250000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((516090632372215937115888119278046523704459781604445072568054940076845626849 : ℚ) / 1525878906250000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((71367801448915225911023697153069465947178947441096018566766778308604082790509443 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((15548112717580022886720673858143078263428439906015000484317849258944455549442269 : ℚ) / 38146972656250000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((3235176197220793401593273404300635877747234626294001200598509628102430325389889 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((3605055361222422769095435479743177262314094466250723262145893784479263951315710365751 : ℚ) / 3814697265625000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((317655390285086568673279663639254951294226325760250781811166370640105972523993439211 : ℚ) / 762939453125000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((649201995432905762070623520040348759928724150922897445531380612350856429237968334503 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((181813132755589520784394447711430394752300918200232029867142801786084035976142686035265307 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((5068111901863308799787546611941200862869505222373950280325589632807445072419032648547961 : ℚ) / 11920928955078125000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((65161083973515621523338452716148920676498385936989730997090302927368159854240522818277719 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((9157061078081966986021474511255343309473670175847274495055996215610378319036704289602785669999 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((4138190618963367377799893855848789141662053299486868998152858334772384102148517232838580580661 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((3271290953740964148483003601352696487415462079572532126323142144393572841556035724546990854967 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((460679027670051456524115890775493645221270981673532460686098030947730870123245024452625749758147443 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((105540106149847962582213413158541151798277059299299473437784712158797789150829972543050041731144939 : ℚ) / 238418579101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((82142470654424012253856257934560538683226010641187710128323800686941717117677069180369926905200857 : ℚ) / 238418579101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((23154216349060239210296799963732683059681629167080520929418273903042582639834938505630394032457480731751 : ℚ) / 23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((2152285446111512340956248585683811000943569128629043418751004097597884268517346891051717400361270307303 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((2063283483908948957707838846359577411829953976747138190863176025890099125871701760856441760340201191071 : ℚ) / 5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((1162828933592249568822600916056571792970871092463445729193253482491783189403455477984112678839293007501127307 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((137092442321338452561536393579324593787391796566412773043796796996845061041837495082197080433197166296747779 : ℚ) / 298023223876953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((414741088509869778982820125820132481757988558060173826231116430093480344815632391850521425455170487581923961 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((58359258348150013337883427184619525793461361081966859897277288454402817191442854776569883273363792520225474803999 : ℚ) / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((27929104029806720887684313104850254967687862859332921952121372490102171055858702684990990627394938367812602974721 : ℚ) / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((4169619971843583235824165947741553789061565948609488583911068860896769611428579381710302212713045016937201771161 : ℚ) / 11920928955078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((2927232328585452539495305010695853159192335143565263656648429564754020691216233570726484522464542918283235531233785443 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((710871329864439660205165559521400506220305459994827450019246595335721194865802782318825795579273518095642622613090009 : ℚ) / 1490116119384765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((262072326856663776417214435403163213287497323668001344763457396161610307317269420006949190173950936493144660625767299 : ℚ) / 745058059692382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((146756094760772724817051695340183422895748206704706925435987216987236858556089252069407001822523552973379654502716207097751 : ℚ) / 149011611938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((2893527796050551134623046770244149478239249153170963035146700666417389682204560164197695988953705375503306917959252840327 : ℚ) / 5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((26362402553547951802946525728638547888934985652119617852314867344464418713899122336750313699452363486400338656008182446541 : ℚ) / 74505805969238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((7354592552392285904726768998592185928174356432732212625779307993325838989571490300317753776561134843888117956672093625458989307 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((459843877480805106597498078122632133351875975009773561489438562999163707696001329538198758817016945340491367390027467593648457 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((2652538982273748684219949243754679727712509020215265737416112131264763278135211629762559482747259749701717703975136123185742283 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((368444066635062563981832108273087656545316086707784772715290010271967729879193912710622647469112215551346635882094288418658207937999 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((186992175305867639877167009063523701424540008717644918651016242575300814949971423416073611566513552538843986367596594235653227971981 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((133479731316910341403070851589533105954419627496829375679794604948975585951393237462565232555815543285707344397162370645482337254963 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((18452607712933560172093579031777791399599016702023196572444596967144130680468855343225968008343008557218658783234286632232837355217423443 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((4750197643493971487894663575309666358966182678346026075639111814860485476902377529703725413580368557952794510063188647824369268475405479 : ℚ) / 9313225746154785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((3359227703400170292592758243168770741278325705817983250099407714158127781433740172827813545374333604987361884667774686038774436466995979 : ℚ) / 9313225746154785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((923924304896573652079723942855367468592735353788001176533524713130752769368713076841667520531053415169554461838101536207932859325987889463751 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((96491810575071591335919038168841863012216651020514557715580087545889438684619124061245145827119864672602122395892307488227662593104020575007 : ℚ) / 186264514923095703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((338234562380452926845867590978895242644429788870139932185987759631180096633242892569909120062391790590564737490184646608365102257497574489 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((46251280566346491503353686836095873360901038451155966069737211216705445606024322411150844671240040189370729232444087076400998694336066611908851307 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((6122452567049382019214316633782934544659741412284057604821536414832711151191397280423059646357397129610442134551401677758030479075388468601743249 : ℚ) / 11641532182693481445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((3406315734124782484417041436886567625279945694789229662592213483411732957818902449048867021051884997852427879241964285340057930194649089107759017 : ℚ) / 9313225746154785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((2314907443205157968498066600683732082619865493365844448029806497749333648655577088851346496673962390339050123945123013710397301434859986803004985071999 : ℚ) / 2328306436538696289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((1242574295227638192450281852026688105268408064955289921289832118444720523670325463448152030928787911260630393247192512735227632417624373805212710676441 : ℚ) / 2328306436538696289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((857776723988779295713375940542072692263397229789890373878409510872261420881548277146544963054992655355855241627489568906294235161150096581329210094041 : ℚ) / 2328306436538696289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((115845100867639424144864407825297586240053615801170242174804475124718392085835394170246752858953817445658956124732600094473377957163336458375483149709061443 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((31509911803675614278204900863734204404299732185386833438106262315719079845189508636558828073736817777572843229284802941535873807917270742330900456922379349 : ℚ) / 58207660913467407226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((108021507452846141322142914598868375053442563733792414294548419326264461396237219247859709065381891563624075580926128979091388527944087383598769234215061 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((5796499197982006797307603978821189377617961727650401996233154047882640611996896869703191061418497609034908195800245262220503545723000109659085436402168527829751 : ℚ) / 5820766091346740722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((638977797154172183670899172808143297375102323675468579576751228486364771527915022571479417348184361781660170004212348468652427121074260571249223126048234096219 : ℚ) / 1164153218269348144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((1088446636698652819998877266200114950460516560691424302276796549954982015829670048316583193136427740831529467171247038399005207640475818499710555175126564100819 : ℚ) / 2910383045673370361328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((290005578386414054471750171276693356343287597243618157753694336815741536524751940083958702000787002747698588088671037624317969395333715666761698916967086038850713307 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((158111706420791511858530103559978903628889215780930719731363434356465646098486025412899130009768706968086184770894129513848724992262026055923305915110869294933089 : ℚ) / 284217094304040074348449707031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((109690618106847706436202178666604739398979827700144854985437020483833867098356580130140655025731737201093742749053593569968624943637174592298077096900326473216128767 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((14507965500285312476090795476522239165901290275896657939523969891867512569883868314153030481047492475933808813289573348178099823557216937630377620809368280555369806205999 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((8201769796475101474155820654158109356750818336459611228968042506659893994340923270941251100575779173467099056557781329229830462731522634282220633025048052837551557072101 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((5527922209604128890028569963302031119678020653021910685150038186454655714112724780827839904247236409022829367641899876386819809293511655028835754406120255922871377830639 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((725725392840376521041822154969356932183261210271334071932321586688205732436547783845410518181938137298315101667164372978415394191124481214735980408784285915594872842708699443 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((207664469226810679525199498392645029854472479502326373632437050495051115376661175438985771846980476213852394317866592814618767487711141840096675054050586375555542409317659619 : ℚ) / 363797880709171295166015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((139309038912448111359419121744601478499454263763016131704707335456411669358252935993338119958255419744197328246792045653326766158841284937600675277219170897689834060240802461 : ℚ) / 363797880709171295166015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((36300190795344627505818134042780922962923047325517164099223809764689971355302164037109135422268741309004395781649514220842423930591684547055519118256632855709971003567154122195751 : ℚ) / 36379788070917129516601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((4204877275255292298426964496743092511294680951007049908808470782024047109512975575738903794499511332402543320383155719629808709955872542032174486236985260919048053755954188170071 : ℚ) / 7275957614183425903320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((3511127654106820431058359790112299058074366662715086698138655083008846423776972023323119598316150754568074886122332615678685980523177548983003969837752725573299053325061495674149 : ℚ) / 9094947017729282379150390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((1815601982289317507757167760146127738533116125032033952570667672155911110967594194927253476165490823887300071279658376696391035214190319269041727115647524440449235998807377978284575307 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((265978378071517180141027989022839131355357472681958237049368371330289806958618394683092123723659421885571478873536916052477594146355793738625768239050725843434588669899215616553943519 : ℚ) / 454747350886464118957519531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((708025807577798754598798007564094078930263537107586683814217323205157794982786163176293015384572735391563263799187901536283099095243118035924973762124528813972809275115784375055573729 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((90805311690878294927225059852913758168753822932988268919549904123939109149447906153519126185174792992171829133448421537068313285610297417132608780860611697612198136401245584621856671339999 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((53820328732876135770363027177737341149167305797098438444507798635317640206607302168676374164167963333417002538165142612571784256591664244650535269416643648793354476356107061701317877622961 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((35697033061502510071657076269430859039547336095237758836413352030976286939839060401141749492701500744815413713517906639595939222356495529095587088536505569957805631986912994646532812938357 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((4541338556158298084698080446379200806387656442559181760409285269802476668073054542175313453062483665367856532432164475353016208495717427180912431887085052015282316090827808344752354362216337443 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((1360875478740953291388751854019969330000820842797423185675074960713463225510932825172611517568927421058637693904468767707422914226348848199429683279421059944118091449651431598806430809363454289 : ℚ) / 2273736754432320594787597656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((449978027944509246634619614669086409652615249896033541643748521669255502889159357241477186934265916912974651497294296268334972085318550414351379091284168310350655672254112500512291758917688981 : ℚ) / 1136868377216160297393798828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((227112590260908215964504388267497148717439495225991098177737953226983999563184982151354814621980117347059870450715623577598310784952246548538090363818678558614369525877359039727625944592840672561751 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((27519925033719082095394236934311371968745772508555936255163127509169280956292564097274391378837621731597000464325755671566182201690126843244570885045975174201876896329460077859583199881237028857363 : ℚ) / 45474735088646411895751953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((45380826834840882480699276458019213865649560564640805085458929416264135583513738050130823779841620424287829202575540052400392926648151503500211983883901444116824911492785254733985890991028729527737 : ℚ) / 113686837721616029739379882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((11357572770057447165501822187046751157968072598332503165149994075480758069410463285415206845867607853938826906771104792591851312075212756366135511613031503418951723912762768653688577324037520502210437307 : ℚ) / 11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((869295816552685308151087415720758671530062082862341593904534915202918197542094017582774824935150074014983916437088760783646532454600568832412085290807636072983620831765024775425361116844920994792152727 : ℚ) / 1421085471520200371742248535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((4577005037799685487493368502790757203650385171578697405634062995737180927384969576197940045041135587578402085052146972488307326668748399584885038098541127060369126650626423003537272743782323059200944371 : ℚ) / 11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((567961337691533589957281493591492339029647265567236337199288297870234621159901086037414957739587787440074656671457906658331416287984829272673628967715781691000328514555445145595024785179064760012569580473999 : ℚ) / 568434188608080148696899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((351377391004549609926378551386027715175964448747282100775776263041622788795257860994399679826807134040565118657888526314412759274416544751907217183460194443921402103987941886214331853789458542680819732873021 : ℚ) / 568434188608080148696899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((46165167858402997532629973010686068918923528245644363930779718310734089839170282024193360222159294679538813039280556114393453018546774928157417596256091568208896939914844895473590392848763615454245893021359 : ℚ) / 113686837721616029739379882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((28401586313948535534563050861640326972084698680744876802190112092463574772701910518494268356523637470087257163967234133658610082967770379357171627979080521423900980593936079061087469782865458991854923636231975443 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((8874425404962182091862303957137063430610316429070743504628375826511857936228955784865364843642938712501624179491851235393217183849551241016058873682863057599196346523289344759630974257728844950321835383503731359 : ℚ) / 14210854715202003717422485351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((5820735152036932827129118145506952822341990629229715038153604961345005426999838633362081388876414264439464552623316841655167730150836015450847613215517126584607476670889511517574469950201665545158421383926741903 : ℚ) / 14210854715202003717422485351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((1420229092053204854081950872462186769951008521756459722070804600318972351601875205935560578448576439814503403126953583026109469300859404034303152971905729750236954031136137716602699451549405338316369985187124178927751 : ℚ) / 1421085471520200371742248535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((35851798548002491823151085672118706214126387264226310695230608207054412654759933664518359399937217993905089170645057534046739856173735484971320285723040130859721281571231538666894177357844014045879203579387948238979 : ℚ) / 56843418860808014869689941406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((9174199193813360109232787021400383219767828443786051455103774458006372680786291500656353062335365469947277571284174817623584550111419785155845975569506899934484287012244369915714764143426198854487870819687049168373 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((71017828635033090342043139126541251118805069660389656392167231375774506367121003138999651537036067549185821326873763632842140685036673657487839281025392140980834052703060612805461080559588042982729757459608443682628299307 : ℚ) / 71054273576010018587112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((11312534361416144061263748615081548462972199116612051198346420749045381604932109438725007793519648452510958890946167318695825192173543541566594274584389416569621950284817804640077459601733341000421691869390912716686980589 : ℚ) / 17763568394002504646778106689453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((29614337925113734373121445728373334443695394527575348900437255010347337076763832296809791234739621130500990445278332933164798860155426917345257788393629583542844815743365114376494597777369066766287244155686105940487639093 : ℚ) / 71054273576010018587112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((3551162691447345794030207664166614461362987349537202607081460865658835667465568530586408170461643926690700998207766758922862981133105720841709976282597613343721354780884150499162007205374388345216030288208556537801612533607999 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((2283919823661594047467346871233934405183247246346575585947871616512518087322705109579188343225547351179418768358360501150711934405189325390523889990691473762402039792013069914633212602575524238317585098553261766167392711046281 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((1493710245657264468251649065414919548352978443389970788268902894173595065182195201976162551126571742821749626557395412158124918093767044831116339566244883413895560108032253691401480353831621269316979211664785536858104250041553 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((177569678571236823373737437181858533507224652634254731349565730059843069500332199956165772510336180588176162380727929959480279888081580161860651460658506631068749695410086792792837540639117844807358600975291540579223224592755613443 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((57624535003104831037380540440311888692923863171540095175977796745833247137616987490908208418855281906610406975461440828872127120045182397073065068621573845056089170178202681848702029221851033994355931440133319131798836112431418829 : ℚ) / 88817841970012523233890533447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((9417772055273102661613837268422697345459359443094434750039545964617924786313565479003280248695354483954088048088296574607385714405393019587585581589369910909298361252375092856447448398785905854136058009405450073682653901646572371 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((8878975206521731913175838595044349704216959542155978602043468774156741508725637433534546780722376837291012942436638515285602271197087806948303744211244066698392780787567063640884787216978938121466759981705482092430002768993900641293751 : ℚ) / 8881784197001252323389053344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((1162848385205604134955500679223502990325850108580395112233358739614295889554751074808901031289896015640205718418262415605191069863599787935575454816383109557108765562773975490489701629177898781994377716674059521400833689052172155915467 : ℚ) / 1776356839400250464677810668945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((380027145066094570733525257542040320523876941625118173598003058246596480728873304150678773477695255550109493828484454887254986080630524818475139783339088892647754919618042038250185949512595005803474624816915417378026894313934355337139 : ℚ) / 888178419700125232338905334472656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((443969667642225666072008887134102195049861147235531981367163900621788448386836952258929707347202191064593637791276025295009375855334465800298962442397913746483501571976491527365133889592972669635260904541440201407543627840073429591538161307 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((18328680603593206736124011647261496703803932082717428411581762618237551572583673918353842650765298819803450412481410635666283378623841864537224256298328086780860554413414764646563497200159376477396666706283213666099830661629074693997068231 : ℚ) / 27755575615628913510590791702270507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((38337436399615464932941427840603892024637792125761179293546345854473284606135941126735645983251499629283678356111080392070794600253695973373671498966413687567152307468064191590043727957016401568539415537801971776404501528646031696709328059 : ℚ) / 88817841970012523233890533447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((22199373134764213723175718412005977349111940842902534531042394118761450997998620177283271555574883645135911443483333808479714008275468861063322944661128015309098376398603549930078002939408137901667798314570070651300834169990004943127089530741999 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((14788185139379879640641543844155647426955803198554858877621132180234660972967328113591812015533188663509330966305326049741360590432673831278940909116552565506177911405563513465750515763605942400740769096173766131345069935561340598056837777646741 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((9668765188968839253202490186335252694970855086129568051582292512365071139704562974720757578637040339469352582142481394800463402301552488004937203375140543261784880960967003892195008558366016313261038693417667360274628026787003839608889775864231 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((1110006521941861446024650858571737889764906866451403162037571166512131070121827278884644187590600323286048983300320236887471189050179128320271834555943624947509299604395371274374329571092392124681276492873158496707409599772264640364659549159787251443 : ℚ) / 1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((372783977096579181827331545636832997756550955155097931174524838841324405579583704692259101827217040852599118345900613467289800605930527116848933463682585237047561238343695971794690965011694372249154408044587817811668368428438624986797634044579604699 : ℚ) / 555111512312578270211815834045410156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((48769249742723353722208636290641138277082224618790381925555290138225318613666950656643972516891271623074485114436339364827905567841458623650755724822814055357433465634780989406537505440585519424174759063557368609249093856554166582671473358269281581 : ℚ) / 111022302462515654042363166809082031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((55501937526564837688844157093837424960662641515572364366832916133256761951174603507493802691293177958084386582311728321220111392408473163925808463197292846891153263264253815323548343556978931650061083707203006144377230337508266299998816433593066059659751 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((7516249231891418088836522879661599503955669086812627276698729048269948063031268164156102975074531646402719761004348128799966594017339006250167262693521443874432661005498985600670277598179555806769497388773254307745540278385309884018947564405530474567879 : ℚ) / 11102230246251565404236316680908203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((6149729843983540097967447351648439430432486677570203912647085222554572017806792771390952368516776016561628330152022630468717134314755831682760752438692474885667376874023171846605800608482732523087645477532656881171169946664295790440448600827378590892907 : ℚ) / 13877787807814456755295395851135253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((2775165453932271804042795318722438073347795034978213110359308411883008018356137601468413761133363774362197239783440222166164280526727392437190630768287191685146809424736849618724246856754352394231649539327438332486261791473339288929049630964420112300940023307 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((473488600624730265042361115473846207548073030436722746907209299044665437684337054332921121485915715873261191223503752989940424968321037297698679382451432431269111476667373258882663267405075597379111961525911600848419957037526469432984295106898369353929366459 : ℚ) / 693889390390722837764769792556762695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((1240734282353815574466961427897802419358675554853503891058461352426704640376063694328155555891840118824078114067952269345229272306630961523008098723123862789911784720553229631273827443894385956087913023589565696409903740286838001448764396146430490864282914377 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((138761191153708291490581966642870736052305863303567815337561088084505172237182147905691284432552562145532027933463865534725453286375937639949521673605998016544792768688526109224047773482894974841316309445157793115617843059730900118953565144952826719191104571875999 : ℚ) / 138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((95430006508687167476630977656792522754676829008239778065430881389183399285258624844801846324865784631584503951333862947669605538187218794677490880391464581142640767416988625097166529918123515029740724912251291262759927019026900851301659467775776804375493237058401 : ℚ) / 138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((62579540037531361381966834796142111951336513109763599230173049947493108377513412155023710335465070642023816990234071606374140062639436875102335616384545770918711069473324096452628794289697534360574763616987485887998704943356275677629536391059170985038387831112429 : ℚ) / 138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((6938183758463993777261333067620646862420168124609935517320587225612286614897760668422503991596139387227406512764421725561311115508300778143331793863650457590096745857077605630247801096111561444321898181057580201621348547092967916362306871873757446688615837265326889443 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((2403754269937185463943571077343528566492085588955703251122342135611491178792989844951845719655388471846657794997921589766661843194052882547147800804367253170975613341953039452083882404654250417295227778179704933088860639590585032978250853503261484348993217436076736969 : ℚ) / 3469446951953614188823848962783813476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((789068934878524635990751910631076522236100364499953416530187938825675012655001719874097786945111381356628945094094376730830883735538012632570933710904259519307909763164347511483762643198024676991203773671434629166590455678174018350199588457427512171947131536990638183 : ℚ) / 1734723475976807094411924481391906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((346914473535733683993742367018731715936124469879025025810612230560382081470204000766056502370356903902236738963715495374712717142686756215445771151455372523661747213439651662806455671247219720386007020891267440640399730118635435616630693546331495658727424186500516434025751 : ℚ) / 346944695195361418882384896278381347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((48429203620073304596437412076600133942873974471655360544752457783249325943425014897666741039297596675048521811322569549683088374600834062111705831240112094516954052125641896783552150123951677019241921327818934571527943643738641462302461888466164057221906955399280161036931 : ℚ) / 69388939039072283776476979255676269531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((79592980716402156774595668952911275282408560768618608476428287842932378564044533690134011965641990839952749830306325660052543436479595031658440301731332259994781964977218581368971957085075032782733330978968873362381015421980052778926853588987716985458950384773965146061093 : ℚ) / 173472347597680709441192448139190673828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((17345948616599293430463284696216158005699117814641668023422224695958180241127471660601066571375278759367488900078840336661649103441320284260725682892486288489472976162351255814054334001267929640467300788069668471333491314658768233536952425251229460748462991104902477882833885307 : ℚ) / 17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((1524295436435639532488744434870540748141096461056697738696660843414826005782882789019184113034485530215007821847930585949778141174914343051860969488510596555460435109899597830818067876253667453054537747899786151613682435102939044662146106163370696942515275618639745043349962597 : ℚ) / 2168404344971008868014905601739883422851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((8028237878730959873498386340669662545254134412794144743418451431987685192525942290920203777695583609404100120938708729237180248652996881751301840120458417536084812958511762935797623499597127791803380484926928741854522900406408485449975657380451024573819286337586193602464211739 : ℚ) / 17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((867307003593569882557305545966870654778810794337705466072779616385892276521661811460199590078017738162402225120655208207309800895152267337283702886855538979246501446541182393678710292091959281709366919637880881134539389877933199714632084361416572161072339512451334751259761657009999 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((613999141813225694224227590527752571665532542053541395039272804801249886807085439776233595551153808930168140015492708164282961792394643824356279112728276282018225114540140499529427786815186249525136859166762576809223344495092715498013702616957962065614241440751354951412429446145261 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((404873944320746697632027330987405992581242544215780229455997239746424256517752661283655035528967410295659570846080412043257040728550034231438531902042438377732455140967677398169511865093025557623086982011409937644172797318647037590003800411513484820543962042245492578287753378339747 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((43365757567779241093845229077212095381935522849629731519659282134534417611932361710311713954950200882977351494459723695678483196694995041072782543755911172339793362060453099127784873900557511151705527999029296658442592815035203180255597614168805061458755552631391453009361676837374527443 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((15455227961900375365858083653678767855171880665162605047496242200244666083103542476840527759504757185850196762748512722874951696457061888178528322396356784701153976679449945395254721551322155433000969069294814075677752429233888108642347503038771604135018875767575215392147302687245823639 : ℚ) / 21684043449710088680149056017398834228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((10208740127576792463884742482524163818140586099496095500699781990940886462329034301555042279913403706024127581641901110119712288415778291071820621517100925092542115948211293372852841692801196708062476274243297462677398435317989118920873124654199300808925752146216500273227137364666866067 : ℚ) / 21684043449710088680149056017398834228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((2168305215604365543323470261713914189494713639661692484282140069799381210311005517305735610780815698976867147549722461316989209401748903962934406714620311761264586109206702539581140878586026002083132155054689777893341422429453141742137467666181837000500260053334126065719404881168147764391751 : ℚ) / 2168404344971008868014905601739883422851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((311174630371236732415347523139725184920856164067760512410704465788291614863150390533762570622148485815178165669411854906637163892529618567766320092334819135631289608515197051130749607625056282547503318020701354419432922603059268534092714074240199802700342413893699565736752201022047607463423 : ℚ) / 433680868994201773602981120347976684570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((128699209442290630146444242659859416715450577689718411117094239495243940995328832842853588107302650010735460642898662439046304592217805305696676293821426968490465563419555997118314511700622688025886925306213170859818303983710892001625550360286886156127567748260043526481294881404101604273083 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((108415998600094203431851866321508998478610708050582647053595034950452266167205461799980190387999173701358535198273538786267109784510228105950599546554096607624136991049509639976954612369985508570651855122662432877806930914330237353120144211469700437230289567089740402978820713527872864409219747307 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((19575647159445980561788228903442500194584497672449362407012024447431459460449913336413481366790238085270563184652594208719157897542949353996427363769975772368221316215542347211407766339171737347655509009912442920668713394846995358387934881803044756760570349212004307124791167579129006212263693129 : ℚ) / 27105054312137610850186320021748542785644531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((51917022021736392572549904697386579427202072997107661378797730349283546338150976929069928070118738945584880193161880924860819419931518717755468073510897114418209618625589834325931514426145444434343550129425577311663993302016358051382568712298035273465310951643312962924106509585312782053036266781 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((5420831329405169965681066994731956064068444886883645710659843902386397091277762837821756962342080835208715182432926990127169391099401777504939664902702689330660397928093981748499257438629473288241230998455145155980829558921151911036733977207516041507209433106638082329569673105605685490663164786143999 : ℚ) / 5421010862427522170037264004349708557128906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((3940153675567875956022130608726631146005826162616684980463034394266855554028394894108241399507264179004502227654498929325437066888085106702646296420010209287227953427570149190971683135402398572209706581640472105586897435234736086346748320653226951643980304631871733382950827687734438776127235719851321 : ℚ) / 5421010862427522170037264004349708557128906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((523555501388951025157418067388168718900579519491601656595002714561436972229416179311135541068575805322180465248672349268852822182009121497200546852725739937236183278660417865220489209626110442467168985652535034221101937998262744319942203312419083426497602004426151478179639762166653799483060943463157 : ℚ) / 1084202172485504434007452800869941711425781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((271042902734543865741076524079182735009271258269857310508550976953857901013507753089180511046391934103977292018798073918841947777017241445277717319264318349844914554625895581270882898815754494727682067601255612403076163539007461877990287868020260178422311844719196869699496578355261157426152303803930165443 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((99119063454366294561566553286550991153600672145350046694972634207295058359436984733319000704039470795765406174072910092399046452911929744284510305104813957638745016379221382201944785508050813849753762936198299292111114678260107933827397056628980907937679318678058752561090822464486472413070571523327632709 : ℚ) / 135525271560688054250931600108742713928222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((4124617810730111553102494853528005286888869172204602327636350748218507168848075523742189553031079856005756182195023197383455008497500974942161484791668375587109872107518163251650894950814078591932732045221584618994672428620717814534073088368890661306357831185226019393572052348074010061152339079028008763 : ℚ) / 8470329472543003390683225006796419620513916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((13552202004126385669922361434456523693325079399127817563312403926225330693431849448216255008601301539662961616443989631764156771546522744186683815955931596014350028701214238252144963524902064032125965750906635097037712291729540555141632680799338212413118325175714861183801475885064849076584763592983856050757751 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((398896284565915145081046652344106088834219492522067372676912990581025494587701565900889315836535407054175345680544121283715803547566186993379038299028233740600001256623759660440438000248263716699031573511860470787783163485266307792693140038924222429321777999324983768322913238245035709839106657076882348512831 : ℚ) / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((3327221271903200070052606917031019744865263091802835358364349938052754657258148541143463579712819447270433464088208117761137196607387820608398636795086778146679481935084102071336581778142429110896993407903982292813329114583267337258224001866218441946853142738563517184378974343907204269724051407763535868668331 : ℚ) / 6776263578034402712546580005437135696411132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((677612520312226713733854325527103480793611527035557532041885973888371398320379216967739164401045589623436657511006866758987219726705368424352703155636580931582694171437574337296533212729257139015184724461333669824633921999134057405162461996777436305665076564502897347399039409240704782152217784226613961952097609307 : ℚ) / 677626357803440271254658000543713569641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((15674848914405189709498595424366161819887393646128546330434093078426697293462791382374636786603528666113394074919743839655361652903506456479858831380698743002405044328876562518513433298261424449064492609035003155304721814050116418681122556940339917818698871545039756945639751616945090937800556846596884038402011783 : ℚ) / 21175823681357508476708062516991049051284790039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((335479355748273775627892003209445223666091151878853173138196311587552592135511311270556897038303261887230378798019514004063905458677991037776154665817555145349131920638659036436746878354127872621810918686170711991293353691295750955692431879828839865138804288560835690664368101555687270348031208137422821043460397903 : ℚ) / 677626357803440271254658000543713569641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((33880729008058438195320058029503802930972531908395971891106541390767421598320378336496075619415297157604593833695919228662219109909400364035177988194425974705364715853868851072328563934118996065069216318900976986726945818517148080991498895196857356860188663355549802413260920139056673414051932243332010378795417959277999 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((25226028685095901129555598973974136929244875440934372133802452766642429567116938792659503762753553716469219007022971021541181647164492447837698820487376446584073334843873638753422603158728924002075283693023914524205962529182245975787917685989708398985291032705039821592013752061193367316231391525582626323476225668800581 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((16912010025118736078602808555329957177552481418569181974050877847589896137138718212302118411905694118022517870360087312249933544571748185027128154807658909915591422344675711713050716480061481167891344048339786541805766070126541474546009594133461746423644708456373427290974767460389391253960338880573647028235090601826143 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((1694040833452493251225656684463936346275338348042794875769821081966889160959720340866263490135456801136178699780597234614178058660414351292245069643590186205536206212593096695085086695344302115541150638883468877624138633198634270882755218482892658535899048946422132941301144978357834850481808080479480365690396602092993803443 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((634246745111588462389715107086925999454839727285589598044221167989384673366888498946951689675281797311522223416056885518588332244882820435122523106366690243536229939906493979554070505670397674994056071331649782558326531786274801219410030142168280366629295783161282436831571999866186386589429222807790527161890766116707892179 : ℚ) / 847032947254300339068322500679641962051391601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((426254725381188914043741098302195586125640225180522285862648725568613731068623905958691453910919638613717551081285610987458852200920989866875995981781395384375539793260309531511542430916523351694887028130860918721831433381901182083916252665502814144730481759134656569106450884611368833402882094388342406603049956665981453989 : ℚ) / 847032947254300339068322500679641962051391601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((84702228202065270139781320265848889335536589458516596528136275785264902022962818546245575349694635085952356926562876513475575642411253547944073428822267554349004327789324416052736034493767465131084747738963785025050467813034278665957413832976462869312255826012886711582952826843974377731954306480965245922686208195271537293123751 : ℚ) / 84703294725430033906832250067964196205139160156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((12755660870676481621249664981100732007628967053806774486847468507370918980462121762541040043918085197152927381161175662018264276608818224374586866021542205981133273438637933663000778486089336324316036424704787790905274737397351296283582626135965630787384759679798196949472875759971279529036334685470190608786946746944819710351927 : ℚ) / 16940658945086006781366450013592839241027832031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((2148557763745540772686255931640989027975857604527542522955532297808234720648105317470781695146616688456375323677447547850831120796258177454601266312960014924673952317487845585190046237594663714740596088144290148193969909586909358169740796235824970966692200241069895455140211987734519505684212538313368171833689454595262636958589 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((4235119348236667443707226083809588695807281406629059548447895488593518435391228668872572950156954585352874453723736335783980072614095717239855932910389240310430577177730279173956287419951262013583573609527081799311072758719299797187149660489979330329321671187630419784835723451999017593138779420910437970731756962166170812583467471307 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((801575749596843965915570541104907471863343577795788441358474285093039677583198106730958015678159474262621960156885745252894596110434667017427958274104336991773933051228717847780062507894238413043851850050656864952731051642020828751561995404399977786330772708724174146592148235079370480927797932358775282394744790503229962295513832599 : ℚ) / 1058791184067875423835403125849552452564239501953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((433169700925950133236100543210717866364519441849772382843372516533357605590950784603555064951151912617680155813330610896247239127586801253516440339031625468495495996221747641186791180747108319245828102500796087840439509244692183854603598002796099429029471909906575060200168292656210491588577379308945726959464659918689019565769901501 : ℚ) / 847032947254300339068322500679641962051391601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((211756305234976643520276042311477541745213013274061324703297088308074364054944518461210087039829516288862278127121047241958839950238071438576548936867434899890994072952667490806057723730865857512076142100644020133281323392817241468893528101472050360824942360731987774783253882946722191711207035815685508720431381038905731271114625176411999 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((161170096306093554486131456617994550142410812355473235977379489645979885448163181863251006813098122020503675306860085728394785024958162111345981401766278040892097866418153173423549248648586732857100556130079994546670833775241826647004728376022942854608057362017956553296355832471081452326853911843371061393946916452573344009689340008897041 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((109157042915800119848132494524271646292859036234150492239204484850792564434793846147634699387030144049942533301489752253008524140792661987336679808452352779462931766653419806973587605607013293229948373408876597634235729165919427174505213623721632590291514010174781100538182674641469895783197806143368331283029721001342838409816989414072421 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((10587829638488340374213768625789193524938157128511649670398214187126720711086273872153717674154024724705111970255890407476042351762281606211502193106267427034661034762646670406233398548814458298141424379377107564812053279628123345191701875414346047205627072045671203731450935496563656312653837823208128194615398282872711205704825103632565441443 : ℚ) / 10587911840678754238354031258495524525642395019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((4050270977462289785646973490805505936571234623368504250300106003393597392065197191937727168161659944831094882143320572718755490445407855109113835854991481697216488034268920034461163487611355297721656259222769216298007502817148251033613005686497675534034549767414593804936701951749665035385546519094773187712827206349954707149355706209528490049 : ℚ) / 5293955920339377119177015629247762262821197509765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((275053749657866991829540093185673302387096466883217190600332383576221444275090111268070606041128484609533148704047517988423609491718731498494286002333075543269711268078774188809964920285910609491379106714257495227301001511315913634345388897262200917211137401706036691407558781311495099632383426550255941643682911974355723532217169702396015461 : ℚ) / 529395592033937711917701562924776226282119750976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((529392093755320269101484406064692897885149499048441368773136801161551853301698557177245763058972830209275450118179928070957934363947418315542898832023422892314069656393954352478074742041896901794004597313151566635706551421134045201323256712008324730929871305047629417199357461927259521697609376242268311578247504724213970781180241935291087491489751 : ℚ) / 529395592033937711917701562924776226282119750976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((81418806762254092758384744173372532521953135793321030368422548030244377050364011009706390729980662040206031313498500681725913722746994734096358942555892111801335664040339288291284369847758054422621551375742211115734455617480739041999548002333625996378753130379593819178140224785760591729111842565165552052605879558221813800718810219670254907255539 : ℚ) / 105879118406787542383540312584955245256423950195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((138606953351547784024539203389323081484002157773828287478276817769412401368425235675897887561104804011815993733354223515657290363543317018090329082082647835160671234958129953444608878513584423833222889331747389047055273667939971771480216674620331137352326859901562708250084976504952997182651996157863100465771810397147778065196974762831215017249809 : ℚ) / 264697796016968855958850781462388113141059875488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((26469630725453763081955324601744245107516124537523074018378382847032162220960385497792047938500706735216135330679383198915756812726510281254559145594420808028209862367157515378409426797077006449647453647855791221315763708829201561632713835892938275574182533128911965107753055507238383464885162224742212535835479058548373954534687556040182810375329333307 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((2557041422297128572226053871592816257000265987852282936046914750282584808255056473461944857264262785147294958414405802540734162828146903128016939145258095081164044776307573549610010751982361901865026639792071605452751173188814335167834813120173650116392160799083227815192818701664608167021776790886306263911802017052107952944609584937882588922458246067 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((13968625720781671740816224794939616059602519470383975015219581392874142112412463291641776520466993867691017251858173902415277791288136472045137152680163154538564637587400193104686234451986299787037465037071583631295198165048513414783329669298510339399906838005727085922582029053528903095582091704030204442381645720399129835717326760690025931505958481987 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((1323482644358565714968945385718885311651454577269297195375128838821147727637411125629536184118774576530593071267722510796257862679202098039350273559061766327256527112759122381958969976203206163477646684891798907005534956156644330858403402714095774193610486062367106499090646783221543885115117848798354338887550482294643150383132698322402059861142890437545999 : ℚ) / 1323488980084844279794253907311940565705299377441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((1027813620676272195263367617242826928007914526344352871969198446999039026302361054297868125331506382360223374942017918679301858328152970682934257696654525907837481736477244566165655182982137011182068992796859112652963979118203562864654944608073577327585234919671111670566268411063692048373669514057471120139514430109134466262886394813555384033248694682924701 : ℚ) / 1323488980084844279794253907311940565705299377441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((703822569440545328572351763080735024511134048126551644482171486766107317330488023022309519145934440476158844140153522383147594434327902805982405271568617961606263235207772843722124813248893116152443815509110387600203488376629593791677302347361369303927794402895900386242837645261628951401036639101273286269948798235667228563561004017034928477372975020672219 : ℚ) / 1323488980084844279794253907311940565705299377441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((66174179374738977106442040612161375838495495711145867462329357993711583845065305273416171387542689653412449333940466891956345862038803686260629591852991589589056024337689971209027885277279844699118209968940286085434551129158312788341073609303773862357481455356156951281800655153559243118844070291311565600037485875013128550854978242506464461510657988350645079443 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((25818190996246797839021857993872475458601754049768136165605125252778061822963739662085011211713769493683372982373778225007141678011685179489947297007193356090205656765776234386603501871136779512330537350986925300877592718914561210717776099544891655987464364841567977615408589490223888647507809634521614980877669732411440514824122209446810394637707405409162674319 : ℚ) / 33087224502121106994856347682798514142632484436035156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((17730182517802077727418911164422724798681263491863287522075146871129466058340013820052732579518466153756799916052012716239741957506081885852433626471838643791815652167471786593728407199846490742195904648890819285264509193318863828941754769043360155032024526607117609944707326614731481001818044937076132356721524475935106351353094800301827461217790737036471381271 : ℚ) / 33087224502121106994856347682798514142632484436035156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((3308710975589341447444285513937890353086079974294054017531850488138383873694444196520772005739654243580273606304504449520986210850785368476193613540487763078141457227739072104742599713745198350860373661648191754937838192403590317333431069591140704260347338295591971375699590481370020709408647099387346297240795286382933711738735309066347608088509072010238402645855751 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((518780001849865139173836961430027518993953809336412238022894500720092673944371499914464934192111327914364255547435426215593604348733468608793004096784643252429429886251504740636903467933853634925705522901108327594939364956190135653335219649275398349222867559838215641851845243544448898570076481250333297000635887381602429434507003350420662511079645524289125025639791 : ℚ) / 661744490042422139897126953655970282852649688720703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((111653782616961431097960950879551122841557137780847913165816344448952910749675375897170681564909700595414872252589252868721600880380531328704306897975851494438843087774347540725287445458020845884722139027497853545274991509464151996417951522226847553611899604491088594096214885023263530105558805164672976737093747563110893907187395474011356734820185950405159441009111 : ℚ) / 206795153138256918717852173017490713391453027725219726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((165435634185084343915158038196961733832645663631773023620977961223705202512814461671334494248262465644045703863500795858264610175176872926241371611442537733316465995240891691561530816017854406217564921918762096514889579954119593134758826028590174951207601675845507525835647472115663971330303794608627296371676525002598509970465358547936555157422680577539715701399683195307 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((32572252093873709470754537261211875572620776678737156386326866571293545106223523630945098320807315521880521942974576388881137300582845557833108246256541487877862185335438087970230158359080126676968761197613156036482802928885486863349569573376587058101261128343015763171068313397300881669619759568144768543532107654078566794695315820129575659339481623189842013631780136869 : ℚ) / 41359030627651383743570434603498142678290605545043945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((89994008307580215343757564475488150885364244598536969528185508093861035758651480501952365671408943664699445142400569784760549725067873080486527985887334466794859893701805309876092868400871993394010752109142776476638989981854456245829595971984689157957716881162685147321763051894268697361722202037864024340016241694960150774660329367907628241443515495080961867361164991749 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((8271785343861071420810959610563447210533969415464412906081709095797222303337845045346982071723305750413653019319003369340167015225002181122054051668160078316748843359466627717784066937271829965400910382096758541384155854107467525035931359298712075398541904518957263776987649470826311627903738587159351851689437874535584788813094263724535977834437017338357681104466317742679999 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((6543657264822510773663615700127782040935692420545312352066255495552628300599766551288637122063405696531575513567036947217804450785003714334090977249860302526252406405077802385320618733541280005886304527416256378835164989783355396231124529843172071623577150670618584991402454655055664963429618286144209781352583997250715564698952647193139699712070135282420871620907126934147561 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((4533185560435447818518003769551545165285866004345586562559503751950033011150221637349757374515869867844337873145141107663532369818999630128679346348651092303542480017479061485710655292788057384264358832675307307245131335353417117484969373608418956588751573320500250405444398572321925711248335032804249423412959313741652809464840964476760882495180650293118848909593158654259137 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((413589421871017466296130957097515958129597531828271437036306793989842389563148671594831516026328722820353831543158826389009487666930417822011254276841888452925880526848821275785736536649477267837566543130891753245685520683251495462954130857675289792735747830613264274557263398529955343948699403053740536752347407626610881857518852581325077608700136146868487834762773084175232717443 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((164309468837403291290480113897980569901360394605021695081849808359717336323131835396497170378168830885677391042815865728836952915149912221302673088667311119997261429681493616558654031067182043655335931918026158119418230448710553495296510483718078662157926621989449345820472014822344327774829454138677036064039562717279752280093242021497287646361596821554763534863097017134634252989 : ℚ) / 206795153138256918717852173017490713391453027725219726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((28541247501014755030203273998985763888494788246142662532381912287054425905380456711371384724500686958231998517055956353230777323779091362551083047838932433609024493712755953496638580532333599651473222313261886755093485591812766822985815451906503458503939840100370107039143884152606002860122424752967247278511974224884833952855199379021919365233283459585256553294094980044193016293 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((20679477676180982805198392588737353389666451932733368395563483231825722572638918017061244827532471457065798008982210174637076766641557791251332948259560246891166697581105287033613589790191804087363319376021360342876638703717133892416938946910087307709455220427408687732333458451239309572424800495758036022569648626365679299210429809303451327793451694002282236783999334143245378756221751 : ℚ) / 20679515313825691871785217301749071339145302772521972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((3300311471221476074683063653169529808833134806723583403027223480056688489014222995063208746093249132059891462876158317754327032004246249045710723699484330044534420237966017949064573433808052683710288534059325476818902922710616080470036626138119317059409918920087618476290132575555617879108509613005376151701344642845913984508681480081016282412147304275220009976411019780787056311725483 : ℚ) / 4135903062765138374357043460349814267829060554504394531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((5749919562113460095382648091673745952121631461015127324831762171715641375851129259380167610660155406663234452297077256148679868804066149876999330853452410853206225573515311105265130964594071323330731631106974576842002921758246197632149640031133197572974109014453623578407474803915306354898321287103826942717837919271509076656506677188379259110747744656101926373140657916410586736675927 : ℚ) / 10339757656912845935892608650874535669572651386260986328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((1033974163946038709842525365775813886181293683437215001290463905896807275523794434052075396125299387798349165868255918402030075957964774922282976279082105426947381148959097700289493540701192606545920782685341032111801113314090067059587670763652585554191285815729231523824914991309391297473682234697974739012496536592244213936498261394526978156905923741655125150816659663134093583728529057307 : ℚ) / 1033975765691284593589260865087453566957265138626098632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((51784357474459386393223603003418987282462178007191299428371313188761484814972787068343278039685894790755355927265834892714746248510190851323288159243963730310320254318290886013294559309386881326459675191080538893342104737286271785484664413613014128448574300317757323988069796688153171484007284688830101746860778233060225188698791602628038500188169523578584993213641912792539423043910727701 : ℚ) / 64623485355705287099328804067965847934829071164131164550781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((579148384062038671950046977517932225795438669735242079908883942001808282290302445653414554837115812524157998598240421025418109756431900211389288254438160569817634326537097468047925751413724244694513735998814163293671424963725024397103333482985462145312976145376304490222419758118856988615686976173253471803305832296346432185881125171087462235855183763255290377133893805373154497486456691191 : ℚ) / 1033975765691284593589260865087453566957265138626098632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((51698720119091800604853220610167228453080239712831610933941709943250427224466119729954172632904366046534345451855367119435193942543106926367596621508897160654599699556252320831219976611620653756774750748740058303581919979307730983854872504688763083429718550459988905959416907285153765446587494862041710968154815107756137012495556510166884609423445396673617161043304585283997620642735011091813999 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((41598193692826255280973719956161432310478780337905749691569801076651661995838624652511204861113175966726829686240262041630348725809029911459853241317780472099843459088001723379143452119254588143090792481935342667232713890406068004454444787251607965502540154870051949207008965691534956787355096830875413372781746300969566338631324204172740319100422539506682537501473591541606366034415152771909621 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((1166586868517071658503846434524506738601741642839829333769581580977787365361270365087737298864072441725528313819432392085292732189367663962119774141911106352622771212116741641075249029273560614460046149066652017604496276745134159769639116082732432962989838719561296674379661324148470553651842951547415399516920215022633059130261127067429673222930617297640009544922600295555289506228137043387311 : ℚ) / 2067951531382569187178521730174907133914530277252197265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((2584936513310201319844981940449182586220881982798677472716929225054908431391604657347659724738511105842362139394608858501803548612807001465425809421554136465977799414015430017614228544660740161927063067614130661225535768559399107479911809182039690541518532351925747870914905323334288796110424018843909093671764466540777922840773398403172108323233565746239125522519913235931086741692873867034328355443 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((1044151611050769716106414931425775216059220414817925437635450555050363336848460340517457674637008638646330764956619627200586631332778756786190498407413920786590587695114601207719924098907942803839755496708240926027720942390090341079301997397885337089062246495118917535705849642020522534681788482153834930970421167613458978580773693627459074930139779484819924773618470566440122717150135720429660794059 : ℚ) / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((734282921205818013781439897380978473003866868690294445398304211786059102652374730805605346217887248204206268511978719958819389258311385295129908706562877639308847928858165587939395598359946554528279338069471798048178660512482490027268143042501430564131897684374874037177681820833034632701489368791164581491983941243650915868398932166564393636314669589010796960760603951437512816733940374555612129513 : ℚ) / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((129246847257042815643855067986810655568959385608948447516472950780661738114732519402744354905696817131333405566216369191261253618315227561364126171553079385582617209662254655259608724175127119071130022968454558549775125702582347817022606863360063110375404181300904052142525625845137328296071314969940239299389280402575886062334793515843795413911850857462698464861879947581519258466223633159379911822587751 : ℚ) / 129246970711410574198657608135931695869658142328262329101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((4193114534802854785570552460762446157039246803202834106640908194742530349019612657442466321588474329446315108085639234442651476036001600122326803200703265188598910563009059036375972798360894180742210617779293550527697690257182584774888261341740930460168203848858176364278885136828197560204219124708124315944420522098708619582272247120404261299867709124533859027892288258465900833658272986364700401181883 : ℚ) / 5169878828456422967946304325437267834786325693130493164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((18485823470776027776852024561170074871836171115673391812232139600277795975617841840975408297905326142833859441072216295929439020539725825232783392684775549410416761094333688698503699550976356304795901795651203523879966330932208312793823642547197777264406002040236001003080499250529267040810048501381304067507889198647928146766965017551111580985451072886978616625257542364471404831971438530100970457943863 : ℚ) / 32311742677852643549664402033982923967414535582065582275390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((6462343281723000009116148705670440681406070126709275596461469053872621588948671828222591511721739446658155740681470023672505170234641139328973117482784399412239440591596571363883168474720884806310080387468520648202780024524796976049031080284014205788246075743622573747029463059091509280295906951175746763864109606092421983154781807653764401429846636941040058569127024929226715082547079156363730907433866919307 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((1315421336028410438398251477519439383041093350277009978655464849445279193161744023117099055770306603162446187190523922688926590596793505253465188378236270030218662684511036053127497503213675196317738223931634463200568080691307798451464452337813426922405555312693435777177787844348737566439016629077341112781143202072831416055954704094561280521322658202789158821965280067738247364009755612704898389341842637939 : ℚ) / 1615587133892632177483220101699146198370726779103279113769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((3722829771398875347210377009965025464405741142682718886628033155770011869301497114874046640229828478662239335802798367313764433218319049646024245876165526290136269271935685759947624447773773429206958207145860927774829177617515970325736362350987337871564309292225484347249754109314699928831599751373480641444926952379880587765361317725808819830399326868181597324693614690644407106552065265637865116621120818713 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((323117203190537156575986369335003924696491404049829467333757222900657156960888626993668826964342065631431133856181319797430802529675622966423108960714855685786673873256575287532776000778696694702138091049497833225565709503701784909718615683646792555730388245421345870952332859405757360441552912121186255029764912506475202337118049388321251631649983328299841772526338799913101313767956047657371296227663074484947999 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((264082013951835464389990027167025396305238520034376622582701685513267879134695513779831547438921586963750193732389784608439177928679946226012896050106190480374856677270509277588290611944545838185031159731964480343091438038423758855336967455707809358401067485622244533696000085877237353828885933216842186258115195493538994252222571064662212625399857679989764889139787980318674938797579317663286856006273786069234881 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((187420277550869738244222815114244953568594480540887386105664527395611821639754948774083236514840935616255617028309094441468475404055270963507884431654440123740157058595120416971460548173270922093237089943503588913439264134493549866998799040006588246897021589448827820393262126595509684471564219450335751518090133325256440246805044067670615558693781018647692122782072931669456787260026924702779272165316174463808733 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((16155861823692262031805773363179111054203248565521733930080030353733266628784537298969564269121505287076814763517508426619262663255405486582068248041142113420023480024180074511532348265138995236438890740793479288580399899349036860402895127648956550794218132560396216230118429497730815988311167281141323455301705381538065185860732827818787505688128340502456366313403400307901852610022905520154750253560657460855931993443 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((6626579469924567162853032159346429986177528574167836221561605713616157223304171083036138075615851882980176273931179998082005468238712359335962844717012662402220026976694942366839198977674235635508636923261547116699954010754416991209019761231403881478517019916252639948030008414332033908469711460155809617027500344757349850764838347860035646342093369206616959173541811373508357628739674472894713485068831901067600825529 : ℚ) / 8077935669463160887416100508495730991853633895516395568847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((2358679945123172357659568327232027056585968805965864715198911062044090816441510762055984668029989450520637211164136443900544106000181663329633971559413852683342822078218817247936403297914368889983533842292347611612501040809710874254812242488444281772127735403040375077104420393484649979203536329164188605793366873231166203679688542079507698774280450159489967151986726947225084911732263068422286352609411124608636444747 : ℚ) / 4038967834731580443708050254247865495926816947758197784423828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((807793162006500208257634369186280880678460843371565495300282062701326627921183553832247746601003900502128005891014606111635961160160291292473078431886884920815939239389031430987282145119520220277129873255948098084116078516596961668166007947356643932149541067372781774105150004134930336014558345983531302287274675922115440114675206953484139879569677786763035581199508506903379141524744790221225706540780899561645897844953751 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((133014018617786071081814414830122214653353740896893047850364337577907602718761105291810290797510322672413081498865485630781772201764747590345922587580756058312310504946864176877863306094971897793225811193058680330170077965185381542501478226210015558108880394536428272579320676472239571715476213115886089182121209214961280358792588486355519561443122478399567954322838574500786262402786228560553786431081539567431401893484387 : ℚ) / 161558713389263217748322010169914619837072677910327911376953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((47490911196605967723971499977551992001812905337240935252669642073461365871958210297812890205113975100010989711019132039739570567990446875823546123833895393526162255989103109526882680372150099543261685653315045016945557826816453694432884344682386081283228977522918069625821485929360685966571137152147491381651592873259955972687758503617263540835094099518924616573056799957521169047881991021897260449799294096310253397909017 : ℚ) / 80779356694631608874161005084957309918536338955163955688476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((40389661114292060011323949457933928016269917819796566005387414289255357304441808500438967352098922993669061546703908592292891599092941516533776798825810161575163926210679010608525766249851422014333816016153383210165727953430816897712140800215656695820488019204183473960592868725970230309771559530021141631439548383217466784960232782319424540854846777571274505229107483528287106125868564037444702393256012742644964474587696781307 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((4171513440589627289771344871838149409162193923954805284420919370743187127274540932962462352317419939839582799248002306572289283833368446676579808340086121815623502699574263585461091993689085939503236809679150516909820409824786525057815233390856830748861746152724373790818058920094233077202418449873416263397414241892929237567832376675802253352863355992867733287309380114672813343377505410142898023410578752811362592451603211137 : ℚ) / 5048709793414475554635062817809831869908521184697747230529785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((4780695874723217879108897143516339349851214443738917213640680026747285014975916962763818348643229161525655976927756625083089543214711070122313340395857213493033273959067265715640093429801418135951438292877126660230763600362545475464959709093357005390018650799508489025377448765469902220676233218367181347599197064828270374420325436760875898834200718338042049914603538449632870105887334589045152994636591742223493193617062439343 : ℚ) / 8077935669463160887416100508495730991853633895516395568847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((2019483183979998730327103497504962803450231878078725120585937717251590240805130044353181133603273865841574252243078237962208587782598312119127939227630003046154251207747866654467031034294926966664004208199439529275022884514155274715935576034777702004032508633272436101340950714371115091292948258919109724409172860544585733967552626517167750185159714313100729119035127176513314375398588479741534199749796134288741753145028611922081999 : ℚ) / 2019483917365790221854025127123932747963408473879098892211914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((1674436963268787775555548250026822840574287606083721514588014417594945344807686367926515273078355973183518563395111151335018527293269379637365589290013804432688097256564009987683976369655215864169388606670336675575159397774700438046540526689739526802953091116625114346227117786248188030771145868064055602735625951583521216354083954472287609754305884478668237737875107605678787059434825284805645770993393720164993063944405402332427341 : ℚ) / 2019483917365790221854025127123932747963408473879098892211914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((1203042398674369341711926718955754464736282080127445647918323253152386992528875453833005371640400880975328440097205046827644727910544876467726025735464409189025030282413661644177684108823574684958798865423124196420848563415645173234267375353638769200927568094228476121405277347447734572939390233424238169719590612282810323770715856640618268729183911190456532452149739669152337814288645428010435624026066424415624622699404973547918611 : ℚ) / 2019483917365790221854025127123932747963408473879098892211914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((100974164657590382587790052564502133469523167306478438011509027800263425877943919297538329502754525908619875452708680572957710870264036368853727709710250039635186468648125961214153439726489206920320027088343548047357148896268906026086070309312034664185611469906175063164766839551491544940153999054820552541681169426195935080457137126691107944629841962022627729118777907250877119873837729932360470938752074086925982788592982637568043631443 : ℚ) / 100974195868289511092701256356196637398170423693954944610595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((42004290786425202540596287455997738168932144997106961862992497570880969574479097045718161492007002713987386223594109107869060652465050662380311988649424641341097618380817142137147768454538196567321227949193759125091278223107754435799646810246351531869875775893794820844927742237839776962925455595001665055946007530261352715920495095041837942206666878262912643615749678273651422585653575727637005916983128207193244178972994001895185035399 : ℚ) / 50487097934144755546350628178098318699085211846977472305297851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((6054384881689642880412038544010778105713548659844194764111867601527111561718746456126197531011498473039142799732081231422786402281428788552027176408705100689873552277620202168233793430992982806786394334613264339121966047413463358677236775644223818961366161434303541243509081677702990547042770060359759677281585598109940694027257172132903065885107191932533054969992476421287037003714874686151860083343317020354895630964484403371585730463 : ℚ) / 10097419586828951109270125635619663739817042369395494461059570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((5048708465180752742851556718046688866217079894615909539192453514455185615087659373545338688648724359093136039640923319143361301505826595749308090142139110936754630546258296531390727934440201178908059392798636374251378185578515833752144894153392259203747067324797092163102982390792825678018133737775998254516325527270620409219014384700593480799612184377796968268107831398875577590470912272731464561740472016917309049534151562106983232823319751 : ℚ) / 5048709793414475554635062817809831869908521184697747230529785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((842905495637187835073522249905801369793924605351437599534104045645462338583939368443617383323554728783630940591399683001151108835059513251934513613315267632627539510355877759450359752539017940997604171315645874654115981727353963323068638490608803549391617436267205313947685111970395492165086285103165923486751108060801945086009905521700914052541321229011821438156659260599962496168632096695631887842877967041040947553833410546037550053759199 : ℚ) / 1009741958682895110927012563561966373981704236939549446105957031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((380836454220627399311533282682065965954382495692997986772807213994708706901784338037834206052844915339907894887985053751943528117769079405502790111691444339014103895141499411791351685407047774870461263904694496321097648782441360837538695401892230723885232681896024398283156284713634141423480214772147875380695635906246388507515242726748330390624479444122517326485622087109178986086740372161667598526637688102331725576797556540615598167523201 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((252435433145081236030682471802871516687329392252874594896246435132638084221285519959968978572823762549926590438998773692784026908183462435303304392179014144135466812157114325486395208705971641570790283579331568179015901443664898336990030260485914374933863944141389851185173621604970282379417717478533157717451265464055792755133595169703156762389095730565905578585864980841947955517670613590632937353989267623949921221024888028586885439262018643307 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((52854894577372412210739930290197134051203446998762499371132684493055236968826604743609323013361600560054536159658565586406531898276636984122378880543402393082940137226845353047414847069118668221057148713127656720336009699994270442751960459191297568999624000391504368498751806179777679477439676724319920252275848168592434937432776544167188599447874710691090130523605375953665846212064671477694367129384666513315748892883763690950376139860652247809 : ℚ) / 63108872417680944432938285222622898373856514808721840381622314453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((153305053274964744228720724757914616531582020181067367319121465548903555294046941011741390847008023036879436828135962546304273529390375199875121400077377950653443222027227748717468012930032675885690724411255898126084254247948029885774871106653592318449426216336855227192928722544914410067154722955657565488834840628986461494040506914494576553701229428011024553483313338436362616706772165232306623709637145843483914056170650281183012790864955631597 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((12621772077974419239415192580162732066049133104990850766841219085838116450205247872936399821123660862837225909312470812043809833131563610859202725017962304931973061124970314349724520896900035150328122098285613546994379717738047078527284717795499058054060447870825127896887433814642720307220879802733935592981573504353822372280220409637057242336992747005693243707878655989690779142965508302576565914973721262272436797403156159832572083638673727403215999 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((10605063090842859051100983663822997767021659866890752114675672642951354034068829581640841434169922698428274950391816026210794593986156312772990034659654969815756907350129598660432556880600645625189962505957519546285567257855758664116723290418371435526140090838581008145195389511767685193562221982657005689599806716006716097534044777186649308254555545151981110046665464720142842720639215607440833320480023752568390613791478789633111879483260378982671001 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((7713545834051927407170468843906519053827556608106787931623528382828954517937373676774069836252951444961946307597322214448450137196466899537882631519330866010286842799998795130218791679414527093790321190899477585899833593360137636405372154009402353825194587808368195186738963362552477635174940058438366252439085198199036578932504233711595569473500485284211249864081497807247498773664183560299140457517223455468522119547800334184206606202935811521710009 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((631088621803317213454664282016381835054175765493358967676544737930934596771384733728554367187559635339763823022610820348148415068579952587335090368589421810989977562295361667781226435809374795892513892136740855719439817647778069520885655735223053413606650480038704967907838520849750248114398981764948097030516823624785618697129339972924245062135400334321287372476191962953270487987183136832750915643536655758528092787086116693994770163411037817098663269443 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((265964519855224639535769145400314103776787411802699393856866600620803300635625421341054340364027345668018792883226932718783482681518824551679572239335250943134710495646686283879714733063788536977443967959550311714433693023475057439105670533534482415313853179311422635386712782202036706928780721890667106614850292000726125095508155404949377202975141286169745142702870698976068235599456964800849729905012725129491796534077621688145672701908083720835511471669 : ℚ) / 315544362088404722164691426113114491869282574043609201908111572265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((24255008908936852159664356250667284156377633138336804426080796938850589993423370230977986188157285959982989655126770942499813443963473554955781614248509539423542985227568653390284201428307001199319322592361694510254514021450171430893546280926623187384575943964782287931589091141101357452485427137559000124639676218203125664161443242325471758162630063685042452938487635429186935593946589352883235602811453738769756043506657094105523162015171268227847439647 : ℚ) / 39443045261050590270586428264139311483660321755451150238513946533203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((31554431852131763347133744418890984080366698449314044167014863276872877384799820113286088204400975401154329016373248681556152100073557042259219440816060024010300475118603706495765653428739563188797713707663280596852200319636491304600330851123887484122858224479007167319253883931802821309004477466970896165327704463000001574893733321227737097109296232027711026710469301367402332157270552754191380717041989459115680044740023868146335433844283536382267812757685751 : ℚ) / 31554436208840472216469142611311449186928257404360920190811157226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((5335770719648327441409858447746340328426348112595766859047151289813832325564630679513006080370116635053795158296511940281808290571437621872628246993609543354182766415034256266017917317636885520934912793114378040895366998601558754843725881768536857828768164099207768589397995077402005628429100836626218759784701499039920507755879093545882380606560792295436277529928522863424553185579349638258795350059784064943860226534838744908315763233206341873106303255578651 : ℚ) / 6310887241768094443293828522262289837385651480872184038162231445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((9761772780347820346162518019740138577717965089439101890902789782606644817921274252230068979926551471181352563709387184863495691918262392991412334058767317885074424747116981250279114143403423809982910117725043568032327998267975605416735028908416238891223528702442834732472790500544393660107864515304252182624206512435239296203599299396721899472459203219445877161846073922190652193533227552884832616388156525635168762145249084903444800840277266271974556112983683 : ℚ) / 15777218104420236108234571305655724593464128702180460095405578613281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((1577721625033571087471150589690734725806472605768116106595858979711183730364925944561116055714692310146924779949796344140985164922830367047425601742809066441806357319622417937340298912966869590625664302257026232360239089002770160449876280031279279661816477459153108019605487538485732666447303547561880428107851118831891067022752608951488807641680319746403298163717442058292541049616962913560122589175155945411585995664001195756703597058111174457820171307528832505307 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((20906160710016633674607418620285897590824379346132598033831816566052546393518832498734620611350758354736867470375189806452411274854628250803026605272845063529087842251994631434643064702401917154752102120535507119373526222450283380604354130322967098628431320117371700389107032458612878409827109624303524464260269725628472789655949814730120365436215049229477492383463713949920634623928860018069790315801711041978881992338068610568976461837378324008241932441708911159 : ℚ) / 24651903288156618919116517665087069677287701097156968899071216583251953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((982123339013982757719987658875591791520240727373097813046939455251148711417463307889177063611955053191680367292775724096977352799182410520870276472929508158819078175236457036975251973088787149965583977812235575153083320572865661711846570311544106744363671087373031760410857941789139917133810094682171490081804654748367431619795225537757979441742953218181406401478472229857913373893752728842553964509876939207752964973091759496329006821265158161136190589065518713759 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((78886082631673666504868747068268153541061405676706633597410342761434080388140153422687415983050160642922677860323483017607905663620891930437291333368725440563953148451171240159391100839131069168256395711152265370554694910690889718265384849291152304567923831229178817990350733175337325085997897073590945378985820064128788139287282779148509186806989367447685159953323181674755669448549090712378137027527111568880865217472898887818034980002037251401453030334504524928349999 : ℚ) / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((67098927691254600687081944773046587670312788851872902099011660491259203511800611868268371336027257312551744837794454047962509710343813888695387644946547545647491170336658967418567538691229059963058318021710651170449880976187412949953718435672391114836495225815023377495940395597763987431916215047536242276283269216672589706749884790228465647030764842065368585446210944827474553376965015747790767154014431724912845477998096706510044922888541894016768407235045128789629861 : ℚ) / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((49401895707180042859684394151155257974729120115352562463536277407492669619078158973215649103330296742720057538962923672790644501024868491791378790872301978519706262600531438529256221017935118938616134404228371405338715407862027592023845985715408866687071835024166895141135742554109087910900553543686648640939471254410302942158773479412628812686418927962982102309217135232596321712820960415660559609141737423962610394642456563659501380541145690408959694008742336367896527 : ℚ) / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__apps__causal__minified_sft
