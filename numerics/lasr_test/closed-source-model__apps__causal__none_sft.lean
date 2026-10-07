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

namespace LasrTest_closed_source_model__apps__causal__none_sft
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((421 : ℚ) / 3125)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((421 : ℚ) / 3125)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((421 : ℚ) / 3125)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((359 : ℚ) / 20000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((359 : ℚ) / 20000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((359 : ℚ) / 20000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((421 : ℚ) / 3125)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((421 : ℚ) / 3125)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((421 : ℚ) / 3125)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((359 : ℚ) / 20000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((359 : ℚ) / 20000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((359 : ℚ) / 20000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((421 : ℚ) / 3125)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((421 : ℚ) / 3125)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((421 : ℚ) / 3125)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((359 : ℚ) / 20000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((359 : ℚ) / 20000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((359 : ℚ) / 20000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((421 : ℚ) / 3125)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((421 : ℚ) / 3125)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((421 : ℚ) / 3125)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((359 : ℚ) / 20000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((359 : ℚ) / 20000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((359 : ℚ) / 20000)
  | _, _, _ => 0

def kernel : Fin 8 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((2704 : ℚ) / 3125)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((0 : ℚ) / 1)
  | 0, 1, 0, 1 => ((1 : ℚ) / 1)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((7409 : ℚ) / 12500)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((0 : ℚ) / 1)
  | 0, 2, 0, 2 => ((1 : ℚ) / 1)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((7409 : ℚ) / 12500)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((19641 : ℚ) / 20000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 1, 0, 1 => ((1 : ℚ) / 1)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((70949 : ℚ) / 100000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0, 2 => ((1 : ℚ) / 1)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((70949 : ℚ) / 100000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((2704 : ℚ) / 3125)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((0 : ℚ) / 1)
  | 2, 1, 0, 1 => ((1 : ℚ) / 1)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((18029 : ℚ) / 50000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((0 : ℚ) / 1)
  | 2, 2, 0, 2 => ((1 : ℚ) / 1)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((18029 : ℚ) / 50000)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((19641 : ℚ) / 20000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((0 : ℚ) / 1)
  | 3, 1, 0, 1 => ((1 : ℚ) / 1)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((9547 : ℚ) / 20000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0, 2 => ((1 : ℚ) / 1)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((9547 : ℚ) / 20000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((2704 : ℚ) / 3125)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 4, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((7409 : ℚ) / 12500)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 4, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((7409 : ℚ) / 12500)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((19641 : ℚ) / 20000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 5, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((70949 : ℚ) / 100000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 5, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((70949 : ℚ) / 100000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((2704 : ℚ) / 3125)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 6, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((18029 : ℚ) / 50000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 6, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((18029 : ℚ) / 50000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((19641 : ℚ) / 20000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 7, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((9547 : ℚ) / 20000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 7, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((9547 : ℚ) / 20000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((421 : ℚ) / 3125)
  | 1, 1 => ((421 : ℚ) / 3125)
  | 1, 2 => ((421 : ℚ) / 3125)
  | 2, 0 => ((2454009 : ℚ) / 9765625)
  | 2, 1 => ((8381689 : ℚ) / 39062500)
  | 2, 2 => ((8381689 : ℚ) / 39062500)
  | 3, 0 => ((10746968461 : ℚ) / 30517578125)
  | 3, 1 => ((127881183801 : ℚ) / 488281250000)
  | 3, 2 => ((127881183801 : ℚ) / 488281250000)
  | 4, 0 => ((41907703109169 : ℚ) / 95367431640625)
  | 4, 1 => ((1769737315781609 : ℚ) / 6103515625000000)
  | 4, 2 => ((1769737315781609 : ℚ) / 6103515625000000)
  | 5, 0 => ((153468117927896101 : ℚ) / 298023223876953125)
  | 5, 1 => ((23390304085125941081 : ℚ) / 76293945312500000000)
  | 5, 2 => ((23390304085125941081 : ℚ) / 76293945312500000000)
  | 6, 0 => ((540445568129228322729 : ℚ) / 931322574615478515625)
  | 6, 1 => ((301777766872948097469129 : ℚ) / 953674316406250000000000)
  | 6, 2 => ((301777766872948097469129 : ℚ) / 953674316406250000000000)
  | 7, 0 => ((1853451620134549839737341 : ℚ) / 2910383045673370361328125)
  | 7, 1 => ((3841859023589797454148776761 : ℚ) / 11920928955078125000000000000)
  | 7, 2 => ((3841859023589797454148776761 : ℚ) / 11920928955078125000000000000)
  | 8, 0 => ((6237004443072311688768910689 : ℚ) / 9094947017729282379150390625)
  | 8, 1 => ((627147041431805570712663316717 : ℚ) / 1907348632812500000000000000000)
  | 8, 2 => ((48539177866128371837788287022249 : ℚ) / 149011611938476562500000000000000)
  | 9, 0 => ((20693832708531558688053448956181 : ℚ) / 28421709430404007434844970703125)
  | 9, 1 => ((1603186572453316057927575331169580089 : ℚ) / 4768371582031250000000000000000000000)
  | 9, 2 => ((610562323314539638196173418547842841 : ℚ) / 1862645149230957031250000000000000000)
  | 10, 0 => ((67921663314069421822566258643529049 : ℚ) / 88817841970012523233890533447265625)
  | 10, 1 => ((164196131807783129283275412957949711036317 : ℚ) / 476837158203125000000000000000000000000000)
  | 10, 2 => ((7660350684742355820020448858020967608969 : ℚ) / 23283064365386962890625000000000000000000)
  | 11, 0 => ((221052489070618988889687077953401376621 : ℚ) / 277555756156289135105907917022705078125)
  | 11, 1 => ((16835558387832776838262517190168596414510138001 : ℚ) / 47683715820312500000000000000000000000000000000)
  | 11, 2 => ((95964218614567759778344005589077349014851321 : ℚ) / 291038304567337036132812500000000000000000000)
  | 12, 0 => ((714576903788751471837301091852556160273809 : ℚ) / 867361737988403547205962240695953369140625)
  | 12, 1 => ((1727423351662914269202753844020403710428436904653653 : ℚ) / 4768371582031250000000000000000000000000000000000000)
  | 12, 2 => ((1574586777961873815991458855848935675629551605718347 : ℚ) / 4768371582031250000000000000000000000000000000000000)
  | 13, 0 => ((2297375239537901873221772255702308225788582661 : ℚ) / 2710505431213761085018632002174854278564453125)
  | 13, 1 => ((177309419963645886638229592654423829288584221712499802409 : ℚ) / 476837158203125000000000000000000000000000000000000000000)
  | 13, 2 => ((3155516273732340810791186453706987274703256951342509199 : ℚ) / 9536743164062500000000000000000000000000000000000000000)
  | 14, 0 => ((7353225434251480081984516252334655093807962280969 : ℚ) / 8470329472543003390683225006796419620513916015625)
  | 14, 1 => ((18201653891966573454736344552923639154603146560056780295424077 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000)
  | 14, 2 => ((632724544067461556384426923148830635581585364322567910224097 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000)
  | 15, 0 => ((23449130282156606569163769674174200033893088650318301 : ℚ) / 26469779601696885595885078146238811314105987548828125)
  | 15, 1 => ((1868291539121773461947202857651119621999669066046138810070667425281 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((15867572062709849626422030761810475509789701991443043843303724279 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000)
  | 16, 0 => ((74550225495265852998886451098533576454885532468517326529 : ℚ) / 82718061255302767487140869206996285356581211090087890625)
  | 16, 1 => ((191717705003772930948279476379345709305951566395562464045929458289167493 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((6370396174710555296011127286586206185810598802530069794657934196382623 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((236408113527681331621075269706580226869131169663797852887541 : ℚ) / 258493941422821148397315216271863391739316284656524658203125)
  | 17, 1 => ((19665693303267323684955625075314531116575651563941346905221779297612907099929 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((319866807461922140315298418039219967308948433874294384578845175609384629597 : ℚ) / 953674316406250000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((748073488317858024178657235337047421376382838611306275311426489 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625)
  | 18, 1 => ((2016252936041720089402714666356004107547953601775581471756859272244288620903984637 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((64278166785588639046602512054232336680133329854087687012900235324799850995866557 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((2362871804095887170739306995759046502158777182606212421890583554381 : ℚ) / 2524354896707237777317531408904915934954260592348873615264892578125)
  | 19, 1 => ((206604450166270354610824464379204843482081133161278430203371138933948294410338039310961 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((807723559521278780757372038777281238791067059363613751611759357972162670538157914887 : ℚ) / 2384185791015625000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((7451958769789026013929766839681431350453077211146074180818657706436849 : ℚ) / 7888609052210118054117285652827862296732064351090230047702789306640625)
  | 20, 1 => ((21157883551243376762930459509491927224101540187756496768180133131058848316925462562032036533 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((649918805892770236278023685721596124477934668357841122719532085566909944535650967785285563 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((23471200924489986042449466794339120398549319870747971435016524736300942821 : ℚ) / 24651903288156618919116517665087069677287701097156968899071216583251953125)
  | 21, 1 => ((2165352724901836997757083367475573743731346109536460730035322698618109053616960148875521973143049 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((32699701700901362829424348781787565224551090117262690587034565264508770364479217206511373894507 : ℚ) / 95367431640625000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((73844578584134858823731412148894637891815483092405598666793665068506821653609 : ℚ) / 77037197775489434122239117703397092741524065928615527809597551822662353515625)
  | 22, 1 => ((221462645936585315869929025448147689636379822499644228667637284682875906106487880214763428017951821997 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((6583960854288384380956596628413567269958032726557424192063651391039345727333462382251920901010069017 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((232108400754981710024832407003741276903650698037811876002850639662583296581436861 : ℚ) / 240741243048404481631997242823115914817262706026923524404992349445819854736328125)
  | 23, 1 => ((22635161893667225733828021756357963679903066558974179069232689860124743050820265473169586976964245654147041 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((165778941567231655430594708487398708287614970003901558746811739274051657638991949459961179689225252428869 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((728973178964848830674217667766648212885539086731578116486209908764315392800199412769 : ℚ) / 752316384526264005099991383822237233803945956334136013765601092018187046051025390625)
  | 24, 1 => ((2311943874310060577111514154459266091587870604936134792864513582726358353882165127746132665249792448920287116773 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((66814329849059019168071673120291785021690738274923097423872471532036387970411228637739869803357563765682191703 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((2287868673806508384290180946230178643073958938138858488774029653038365568519220901580501 : ℚ) / 2350988701644575015937473074444491355637331113544175043017503412556834518909454345703125)
  | 25, 1 => ((235984468003412794794998606142119164665878646397964048663474329893487613844394766278455123704574973449011426149899769 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((3367342296018419739966837132562346066925429402890771751520233201070475517687369634976802880854761102507406226604217 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((7176163137365164752830325442947533911595301367529571046755345118502167829736853597414690329 : ℚ) / 7346839692639296924804603357639035486366659729825547009429698164240107871592044830322265625)
  | 26, 1 => ((24071651437635466864045201298798050248797586374137896815491502253147590918431335074158402243868436610689906526167326040157 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((679080699519490768040489936722131367874613276207188663574306041810812102088156108611318619482884684722343457850877580277 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((22497364634036549496995938011296165636714058644056515401396356127574947225548703000974996477741 : ℚ) / 22958874039497802890014385492621985894895811655704834404467806763250337098725140094757080078125)
  | 27, 1 => ((2453861587439871528460710477679618525211980429011264454928256080042787132324896179727848266955930544244866086196228512846845521 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((4281057785610617325630045547582184523110731546352649707262482114458439071450780484182407699943910186882671584482442194372391 : ℚ) / 11920928955078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((70498559941063404856573072674938687943425951280580552929656693616291049216446976894529121188702289 : ℚ) / 71746481373430634031294954664443705921549411424077607513961896135157303433516062796115875244140625)
  | 28, 1 => ((249989874594362921587338226035512381848880182618370782106272259103039476319725724024353788274994153144948946688716927374144319944213 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((6911231850252224562659394333599175048402488562433266511097902231577033669132049245534407790429460715980093723721377396708950397043 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((220833374738849743659348764426765012391996074472226487885169657811352221826782887959971527172034192581 : ℚ) / 224207754291970731347796733326386581004841910700242523481130925422366573229737696237862110137939453125)
  | 29, 1 => ((25452485812340882186584857524803435910097572221672761679563789493783642268367060189041948178170783439928061821300930895058051909736378089 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((348765769263640606395085131439323372154135373816801199007041336766366649292146578731489123652314727661690720235289693272388973092902727 : ℚ) / 953674316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((691524909850769384752301483740381344110995829777702525627054874324712735149340499159902957841252966504649 : ℚ) / 700649232162408535461864791644958065640130970938257885878534141944895541342930300743319094181060791015625)
  | 30, 1 => ((2589889257336852338925368116978968318169723346560292159767166976454104871227297555166813023650372899735338286818884471158694043704293590863117 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((70418332232708305983963966166950167616925511456419354044932840333676950572141373440252626566094014438056156689249463691687198688753118464337 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((2164856682976854409799668289316518500110627862483914199250419253932824258749190366341314936652974614446149021 : ℚ) / 2189528850507526673318327473890493955125409284182055893370419193577798566696657189822872169315814971923828125)
  | 31, 1 => ((263380425448726813934439160285707820731007722186479066484017980899012986314021542381319643466124657741064767507793570927988015843785897232791678401 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((1777668998061729901902619235151962383573879436783592373527680812180251522272202422803895984361934328631170555400180285778660134305901373415459859 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((6775564116833083053565318920819763979406935048797149525882080143130609992237103427502344771991601460642318593409 : ℚ) / 6842277657836020854119773355907793609766904013068924666782559979930620520927053718196475529111921787261962890625)
  | 32, 1 => ((26769816036604525022699439763367906647904359087437902842143918071991201866392083147435111009634265259989405586838472690043096082362642134607417538134853 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((718173521853023928131814404712737414766562216329610895228966066545622599138085477029935587482258023117337882253397484326524179922655797437157336077583 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((21201724265865621356425046944733822910028218961449509602700602458575960658319417283327056461221409422014115853531061 : ℚ) / 21382117680737565169124291737211855030521575040840389583695499937283189127897042869363986028474755585193634033203125)
  | 33, 1 => ((2719413225247791440944011836249321435802480348304622122348374233801315415919196097116545384254297122847854726738727893939232663284407863269042073866929826009 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((36274518429247771869595989540927173796395833419167246425597223633227681387753781619696778308999880465172216391685770942974228646881084130603023895531254037 : ℚ) / 95367431640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((66331333958491155083974653759926448116565887163953277980438234521585620242940359382118598789130563178492689195926504569 : ℚ) / 66819117752304891153513411678787046970379922002626217449048437304009966024678258966762456338983611203730106353759765625)
  | 34, 1 => ((276109435782808365697947687379204012974930046269019269349556213310615064436848547047267742684985886695682973069074905410585782371296863740876924723338496221234877 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((7330075732063742810258727533999280667195729844053188848608131309973150579312871406278287298710733250300350522630972654378458991544266179629932722070751278705197 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((207490775597480442522696610083610462481724106054435301205154378251355712833300278794255685244521143151414606360718129682701 : ℚ) / 208809742975952784854729411496209521782437256258206929528276366575031143827119559271132676059323785011656582355499267578125)
  | 35, 1 => ((28020230648750045935822356335004675452337087682273739350807991904379255906844866674154081451541287943600885837610349749975442818934493028756962259815867480773443077681 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((92589343654039388630939443977419186551507629852404639669495553029237727603433920233090563296137797766425438961671401791136152085473738166344243320101926769196113877 : ℚ) / 238418579101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((648963959008463239005212715905986899220988067655898171790141789119753959052461288312814229522160484571332516771047014312414129 : ℚ) / 652530446799852452671029410925654755570116425806896654775863645546972324459748622722289612685386828161426819860935211181640625)
  | 36, 1 => ((2842199808880967231493296780004952529772449730017266936773674208256959228339445719245874377297520706678916982842121396232390567225890458234722097439319508635142101033784693 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((74860170962420710866151215987715578806995055504002515083199879571168314044798257044557936046672277669536562407095035192424023297731689400900908084532566431892431386689323 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((2029513863261622480844598565809489227588570750206252148181181992555090053875409493763933603568469804936843816510364850608238507941 : ℚ) / 2039157646249538914596966909142671111156613830646552046174573892334288513936714446007155039641833838004458812065422534942626953125)
  | 37, 1 => ((288162708379512211274724172528307268677030451563863174330027567776674991163496524587869829578428982059263116468748236394734816539032076325084938040356059004997374000874612931529 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((3783292412816084195890900729168729557323052068910439722637281583145992384394521657892871730343038504721858991645338698552705449255062296308351679132657543529891568963678042147 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((6346290855330483071249117590697923409196429731259904220121411716541698970046464052906688735738354398349102839723569443255522872738089 : ℚ) / 6372367644529809108115521591070847222364418220770475144295543413544651606052232643772359498880730743763933787704445421695709228515625)
  | 38, 1 => ((29203090978999085610750302283681064584598757208661634946704518169831236032932611315645083925946483590819016909908288821757774318808811455235516831452853392100224824373564280444419437 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((764875323845529603301035014127545187101913275175910263147903886184606632750237278239112124242693696660694922180645687732310352009343613066972726215480532797744045823608937427806857 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((19843137251160675859174248555088011579082566064271151046956721058631052341153628742087849690465297936260590203236103297096827433088870781 : ℚ) / 19913648889155653462861004972096397569888806939907734825923573167327036268913227011788623434002283574262293086576391942799091339111328125)
  | 39, 1 => ((2958251500311973061622439303469984716953364110761774027934615349194871393736460908655806445289933220456167863706780141515759825354695386889895004487798812202309148288820634350439500435361 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((19331068159707602627236532211996347701869138579979982054833740765680899275700098052690899183079834595884132164515529235848096622244026165091963027915379501440851086924977758223718321249 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((62039489309472997631071651186210566686762446359490348792684798045983047799691880690568556028733127004413061298999084323268238832838175732449 : ℚ) / 62230152778611417071440640537801242405902521687211671331011166147896988340353834411839448231257136169569665895551224821247160434722900390625)
  | 40, 1 => ((299546114521167401138177110716418462308063278569517588351265780922639145215386630250509970039168736062366496328751905587576570085095863776157057234406005909984374095205301684883106223797869733 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((7817514272683361713203212129626978126329270802971386215196949331900382571971854662657457144971435668505676501528395553427507512437424765978383203406941452127173030056485900547316944969368263 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((193953673412610392181494254473927695373890616586378016765775394864602793341655809674681783207053629747321747094520589659862372347012768244995221 : ℚ) / 194469227433160678348252001680628882518445380272536472909409894212178088563605732536998275722678550529905205923597577566397376358509063720703125)
  | 41, 1 => ((30319458887000597900066377636115551357251348875668938590153324668650577758002110274901505455533504936975292989035200097414226472376283113478992515743629976306358074084401600861090953300463957022649 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((395196206328887545029946623991592282696181547751121477478158161571462006206610479075761909217289421465797395303727271366578764236248888450927105472040220095041061009091710925470654826350305171057 : ℚ) / 953674316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((606322277657059146043374556805045247831265732344304012429518233177212928481115322758415815871120684609848095837418254595721150273254841160883093209 : ℚ) / 607716335728627119838287505251965257870141813351676477841905919413056526761267914178119611633370470405953768511242429894991801120340824127197265625)
  | 42, 1 => ((3067714413869809147130319342757241906506051723546172118394799671334416822388249534065100679911266920957018128276328833040028557698775646967417206203977259056435564105645787078867616312667793838929600797 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((79915692097133675319820555652550939328699018083737663267080001891268831869478837479804794873015414103845369188324907705229831772876576301532829985505798393647219518779616917624898296864645776184393317 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((1895344016126439948353203841311919723699072243680053846780859694584080556379429624607744722613159299225935787687612023412621538610544577456577932865261 : ℚ) / 1899113549151959749494648453912391430844193166723988993255955998165801646128962231806623786354282720018605526597632593421849378501065075397491455078125)
  | 43, 1 => ((310277608027158331406260599132323846934504794796565198901929528853375136089446275210815625043949642316637240804322021260436864473553445063149433294350435396026964806767500528195085722867161831088510116903441 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((252511388905094041090788888053903181625089176215760717539236798685101779908654370985540246699145924392452821325426621255529801457748034782059312638924544381237128849914455843311380558575683266296496013543 : ℚ) / 596046447753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((5924537023798868674884310186004547725267696670101664967856202089383156317470270804529930344001135770234763296604906233138327228751860934184930633055556369 : ℚ) / 5934729841099874217170776418476223221388103646012465603924862494268130144153006974395699332357133500058142270617601854443279307815828360617160797119140625)
  | 44, 1 => ((31371407944720388694796760547331622422443421521445654127711550133338702765371379928645510263730509326657182911782442087148073610093548976953587920339263252303479247628040544719689969901192441345765825349766645973 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((817022729739256828668815689333693889235943340557822695989812583254465073817183377762786613935091488988471051892115588130944445599304177733302465048765038410914905043053641374440734233350735515247046247741330403 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((18518469375455187942316071615134787025328243430926150092335537559778937473128028191669521069101424326239277849949676835126657415135495705855877127369382624901 : ℚ) / 18546030753437106928658676307738197566837823893788955012265195294587906700478146794986560413616042187681694595680005795135247836924463626928627490997314453125)
  | 45, 1 => ((3170818898845188642336591064092360532424237165564122064336129007897935914460547696984795882183487136692024665777925684638833413779844977429530939151476802815832435595147088967649639858523289782767768645743911321267369 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((41305388834564258604530953751715249382246277805202388398701227938130302341536753400749228260741733166654286969106680830478012472474813084810395843644237618165015426947077598401921583651334873981132783657050205664767 : ℚ) / 95367431640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((57881820138427850212987960372882245292126294096509459909838940780663755648239488030963726904982605139165000731045208601934420989871579575571243926116680002497929 : ℚ) / 57956346104490959152058363461681867396368199668090484413328735295587208438994208734333001292550131836505295611500018109797649490388948834151960909366607666015625)
  | 46, 1 => ((320382107612421934117014323131604099337140437742154923934481949795665223333016191737469298973991054257915013277870337051014141503684697341221782877505838864449974572558681892425369216723049951421111028998859902977765482957 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((8352838371853560705011324350593097515704145192890709899225534199338348394490198612386474413087497873034680150159111272474141916077919275786767093927296512151332363521982356031331262266371368121174580476830027419109808577 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((180912063364299600778936015865641657443780511297227673534215893430357010025656137512880111095236569799470891429187751683855484792066498631522619119062844554146978141 : ℚ) / 181113581576534247350182385817755835613650623962782763791652297798710026371856902294790629039219161989079048785937556593117654657465465106724877841770648956298828125)
  | 47, 1 => ((32361582675743647806177096429772495047283554933093976420713810890521017201323976214665136161836457942716098499931679049831703808602061392357707797003201410107206585262869860861207859542568890035166152776195067807819228672193921 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((211135853123897738142486531462938053617577768586605406392055609575811995016773260758038864679108621680081999951598552333066130219184018740185143912915873894542142396853123202859854875605607342308493252150121451740870634997039 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((565435037180787038640669771329970248521329415236035172792805393208942276211925951700934675227030951935171569963403391878847763488540773109568335669331374885015235533889 : ℚ) / 565979942426669522969319955680486986292658199883696136848913430620968832412052819671220715747559881215872027456054864353492670804579578458515243255533277988433837890625)
  | 48, 1 => ((3267841602935988858379282239422939815190131260557342958020410067362573731302349272812872978062934990856295395525124739731618663649757052045380503137960499514612825644671163842238786928982322891357787098674391574465755705638660049413 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((85387925030717466798324673377703952690929747014820137726687428574758802875779976264741029596239273121333555556535482309998034622968351236096210617840413521531055323424186557011685407116749613855155597547626763274948023708132271743 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((1767213896298476021654454763017724573230883840949275180845138337528407793322522010480911283143614404024586048740041869533224766881742253019307697060451547722211842635588981 : ℚ) / 1768687320083342259279124861501521832164556874636550427652854470690527601287665061472564736711124628799600085800171451104664596264311182682860135173541493713855743408203125)
  | 49, 1 => ((329888234053670659598893317405485433072891691519103339315429148886353685166318163131746149912762668524882125025416334409341953810454462979061495980434544854691786858348942979022853680227922569486030144969820475524029403420894463327873689 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((4316421705838347505735712033191881785960038185526260726200780239387174695654424582684116890195477212323830472851161229302140944768552815057244003256236607777820728537410587597137556403506619368374404109520662647189971472593430747267277 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((5523163737346166253710157245892067937357588350148827819047105796837526793286206507220333863775716817207112311914945396132903564675506060073692129759521953894394090461486120249 : ℚ) / 5527147875260444560247265192192255725514240233239220086415170220907898754023953317101764802222264464998750268125535784702076863325972445883937922417317167855799198150634765625)
  | 50, 1 => ((33292918161874028037381438971361726336599124635678115575393397906450372025900835437941496251845945109233017879480115619326558745307333059702280770191155492544073172192894803730331722682419046747988626822012273596168903367066365370423365889917 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((872751914514895023745047347045285338725323489031403740389603429241545520012723462058619223387543513521187414485009482514799686199188789256223342204110006856225607993294825848158287277085688976563467546882116878920650353391357652308509716637 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((17261564001268680709896363838805091363056414036996142079084160737650897824489986742023625749385111613492505554298862916502945598342802786156401384207437890997733083029275705481421 : ℚ) / 17272337110188889250772703725600799142232000728872562770047406940337183606324854115943015006944576453121094587892299327193990197893663893387306007554116149549372494220733642578125)
  | 51, 1 => ((3359081399663928778481893525747958478043933290537050398318885400348939008501766691478636963710364215999158871570786698965813629019143460424294866217269882964217385189128667400116374597392802515049935518802460690190068284500023228342156730529378801 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((11028442929538329940917052611754073760076878751020186858801195979339215740674464295429928954891051500703577255930175396458232955864508853983870011157917290909631342004425761236314726823907109238757576944332289259598338104414400803506994171317667 : ℚ) / 23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((53946922982820035014135076088606903484584215862892917108033528956489982015683687733243893344261008489647715840326783342972634771232171232882965172077194956218156076578090371147153009 : ℚ) / 53976053469340278908664699142502497319475002277726758656398146688553698769765169112321921896701801416003420587163435397481219368417699666835331273606612967341789044439792633056640625)
  | 52, 1 => ((338826245773798978413855064262365963477453213384022567338202728208781443785075203705095313808730648214725701965262759600373732387934229505254647732316484604115554150084946543508495960934507611807305432880096767584886681682712889070448420526786372096053 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((8918485947172433764328416178685221937321873276663789568245324418443303548950021964432533211249609975579112608636074701599542228832845143426180240637145805984635236296964820746738616085432431986391830426250519643255113738611743517419778242444198768283 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((168596398256137632098769084082586618393814695652185413254466282054230018552479827826979016721393225352144863699439428461737597775515642573453212291485119220864787218776309062098747439461 : ℚ) / 168675167091688371589577184820320304123359382117896120801244208401730308655516153476006005927193129425010689334885735617128810526305311458860410230020665522943090763874351978302001953125)
  | 53, 1 => ((34168463228606734296812478531010786596203616420973573962656259504691954661369244522671142759200310336333376599762408488094180278485207424661353196096079142868886308035339331575599973912845940081714976656623256297355070168481166908059038288979653437393289609 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((450732657388042945790105062315763366590436528664087733279747110058694679932546071387289362878871350330203417731902212100483096273327450859472417913087385636593498254418665317367792072461767517023713172709815083887651303716610076868089501647535716634042587 : ℚ) / 953674316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((526896906230196961634283598168669064172809236915143624297400638411766430109877755057549789709995588840129211653271109255349693616568833642797718743014462558377425851162241886780155898568169 : ℚ) / 527109897161526161217428702563500950385498069118425377503888151255407214548487979612518768522478529453158404171517923803527532894704098308938781968814579759197158637107349932193756103515625)
  | 54, 1 => ((3444844266723147800189249658257157465583975918597530529736112479531883625963300135815165125213567119067423614985724207914426865306945748035051814061209410775240308865396912053565987149775627452312829877948944885451616308717410288439324800315521070264586143365677 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((91111973397422569879627512172616150634221894301802389201738941043884785301682795376582326568840579720086009620573328144391431368245453467074565363554139045784954196694828766927256875226403381235876567937717014452076978656882020407984229075655181338080883701497 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((1646642501151455098131640333227315049635570863717405444029308237943942864342022889092485032923791533123489076466654125347750662887872551558188258689982044836474563287764896383307112869308407101 : ℚ) / 1647218428629769253804464695510940469954681465995079304699650472673147545464024936289121151632745404541120013035993511886023540295950307215433693652545561747491120740960468538105487823486328125)
  | 55, 1 => ((347226747802381907688210427526714782025617793978143710938612568651421604980761138775115492703595925774641224914167920646098417927394054916384932780257094025663381158488862272250395616140656732141930623975686435392315426324460691112653135750733487974645892192295690081 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((2302015517270156605719557962784695155124912250186898499137095784380890985405560412131120758661609959993004663034614566949107086638978131962546528448279861788209146336792262675449401609994232046516294448792675266428030572149679225598079897664930470340882796592111229 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((5146000281566667441199635097856765832065504512675792707933802324395816621821184390283799533863318120877725988253986023444333702913402458751038636525433130733520980962060637075004843572297676941729 : ℚ) / 5147557589468028918138952173471688968608379581234622827186407727103586079575077925903503598852329389191000040737479724643823563424844710048230292664204880460909752315501464181579649448394775390625)
  | 56, 1 => ((34991270438618798714009597489059165862219006430899974523539058219372226429534847216169932491713970765576526816751321885037359222021330201392655868394637255142975286675662719899111186276812761890705053444404929841408353456874192774678430851327433760475245049093263473281893 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((930519298182318040798472319507482419170554405298394070119905261940062992196761187950094587062151083168555148178534463287591414524461440847789424613952560666571583256276104858570313446774415201388212777382072875997421755495959590029118106182664144734419400477090510676023 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((16081906506522308935540312169636275865689252005975119692498479138276897884905590398132768954683242871702782089389257171468528052879699871393113426376401440177483738246238079071258129437267118889888341 : ℚ) / 16086117467087590369184225542099028026901186191358196334957524147198706498672118518448448746413529341221875127304624139511948635702639718900719664575640251440342975985942075567436404526233673095703125)
  | 57, 1 => ((3525433934255603886895689452482813176440275507655193298247422828516905100948694939088934598835204975730834933504868619707391758043169863283379289118978370538721263233143166074211093086112413694514984138884091942329042607889203101270431527646199309212424980580104625357395403129 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((47012688860454427219226599239681063331920358836304968600972732303844281652259615824477558417436702196411807305586673516947745041367828500867684921199029697725444619582458787013562086368180033916434627830512547779442209371931200426949850154298781687618732565396914563115974697 : ℚ) / 95367431640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((50257730647280198907127563059920180740149136810718524305533005255871387316725678332817804175703584577738732198303798154385430230617519773904181683708134040096300421107909379622572708303914665851549089689 : ℚ) / 50269117084648719903700704819059462584066206847994363546742262959995957808350370370151402332542279191318359772826950435974839486570749121564748951798875785751071799956068986148238764144480228424072265625)
  | 58, 1 => ((355119898935159581373374443012412809831561148209271864350166654359276813753437193472031621925831697057587021603017399642678433753963997769405952551302236322434615190227135897585347337803469690527803456169548183878014263027772715464142683772818477230504008739634327725702571990774237 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((9500046129863214693497871685647609747201145145225709144255045716474805684973787439168311387758300138152911760280054103729929382269472310547456572813705171054242193593575436220765655341355389979178465544133262113817067241947529461023573969514050936184760046321134401090927462867157 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((157060201962882768924330927242848202469255139019188516775339738918034529541741740137773082873102792237750561328573616343003610767436058848815666581454121150221597566457292005667845122958611432629123162347181 : ℚ) / 157090990889527249699064702559560820575206896399982386083569571749987368151094907406723132289194622472869874290084220112421373395533591004889840474371486830472099374862715581713246137951500713825225830078125)
  | 59, 1 => ((35764329089499118278767033142684992340210407688193222897755802126140374506266777080603601678192798581849908579747532962933381214856896846546944157549095794709981761619177339949070201479151806595255585680111828020507258333177095795174180918420806640537015422681484582719114339311707319761 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((59985435554904596507173072724192027981918232102974820793264949006100957640162088877420969829129723242775225432404671392380977797519817989076273684658760280640546241777482929463628789271244659251553682829457636984838218343688559865891082732362960721001528766336670964253899079781288181 : ℚ) / 119209289550781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((490826093272125979294697067042236644939027999292278333901701443741110049872480621350768854782620886271955734908588515258811161714666744940256185275962339545827953656517720843227129836557667114349569105449668049 : ℚ) / 490909346529772655309577195498627564297521551249944956511154911718710525472171585646009788403733195227718357156513187851316791861042471890280751482410896345225310546445986192853894181098439730703830718994140625)
  | 60, 1 => ((3601146244020758063799312522165198796607191571377039597758498224789949055850133618138032922925506376065294903079509462813067498633115232494914317850890466972731344003043201642012852167862452291383329588129835718810231903866682367200768155439630284672306199489122853943437486016917787184982933 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((96953619741852948624576434095106923806306949897060986719401253679228631514626103350833274467570452659073765619610684373505986653987173263548101974199920558668536337831351973099386413752955732062740523868643507353546622942544934548877605441295213808829767551178859287158695568364194029530963 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((1533866591096862935898192868587130092484388283162547441561396921709538706078971837689449104250178551670237735555715397345229750649957758984260921360297153493258642427277677347277648528294375003827547593832435607621 : ℚ) / 1534091707905539547842428735933211138429754847656077989097359099120970392100536205143780588761666235086619866114103712035364974565757724657127348382534051078829095457643706852668419315932624158449470996856689453125)
  | 61, 1 => ((362534938993241833140291402499735974469932173045432030956758172566332189895851899794370964156783912952398342744781224376938430039710457404034411281043130145973364909833882152370441760326623359001330882030728048574897288460391669751602161341900983980181411121263428739371975068602519580954556742249 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((4896539175737336456678495124051528506925502484546995705555661559598014756352661130467902567419826802926608987627987776344529172739121253065012887102575564733176561217193863851022240648345386801214341077825845911128651149834823676088251634870161562928728201003393496286160287435733938339086567607 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((4793427871354149528310376014487481659356712708534737115392005457032521196311865591477802005761144288687789800576692097188389900049669782374092145027290338549958418311026840132012166152515624781056915983399572142772809 : ℚ) / 4794036587204811087007589799791284807592983898925243715929247184753032475314175641074314339880206984645687081606574100110515545517992889553522963695418909621340923305136583914588810362289450495154596865177154541015625)
  | 62, 1 => ((36490525811480808267803164519872431468675808060935659575385489983784046509601580052295100180087855322585416789487104074376963675824675370101803542669192291620474537121889642947912469529636595965118605663942562468099569303925881279405949009538930954123530762581915246946589887811153429562390603810899597 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((989077597504596417191127456452969943962364031961299967502487244770276761793024390085071507854186144128225432674758247620361928174252865377317630075366004155108418801903630453869452497085553743814939163300742349726262802637362725551267062080698923769946475289579480833012366224982500948929332475437617 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((14979718367354845792181452048886281310897197385325456764426195820596963986934552504248262960667701297147617882115743126943933334397382098041578327869564436389672091824479077545002786438926108066437986099352025135825253661 : ℚ) / 14981364335015034646898718124347765023728074684141386612278897452353226485356798878357232312125646827017772130020544062845361079743727779854759261548184092566690385328551824733090032382154532797358115203678607940673828125)
  | 63, 1 => ((3672265887182125032001057161670970757176018371304996859453292388545285210938877593704975246244033597543721634856339221341773270033820038116640815717452186667129933290688365094016982666518752221753215668508450102137707677821957638184155592016712014406545965169067731920069303589704082652662279928420858219841 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((24971034344497627809917204707076623393603647474716989765609514778195856939719711135855280180392117538882766272050782759099307450389289974448069654792939729273372824439382463139960717687015671957045690459083106820449137300122398261449630205511043344841065411506592406517325730817434285019395825693383327819 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((46812312850368832608403006670538913739655541171943558854777849326334898971006242299275697849050361621661640819979618465714292750782630588423281447671087738968249988516711743894318438163743254519336080913396569910295167539969 : ℚ) / 46816763546921983271558494138586765699150233387941833163371554538603832766739996494866350975392646334430537906314200196391753374199149312046122692338075289270907454151724452290906351194232914991744110011495649814605712890625)
  | 64, 1 => ((369499920963488523106971454539762601692732363816442040102700906243089392276022558366602111396080516669071784526800860052681570252726603282442013065673886857892848583511326253263886200530524186396582417739522907909507059054698641411377964583007192515007217735747481629235263923140324991416899261377650782985855173 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((10085952221375837190800656828180603956120158240664959630523870206868575835796137692192026192097847228576508444455367762110565909730291946154990071486943023449751919796033245114726022679325095139980313853309054300047356817717165882979105065636062775369988636796164867382202240959134448302268314158157180738949103 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((146290351400651478330447856069482251111370831585258894905098729039161780412398417701580220744472481931768333235783166613972375768654074971467970687976950942953200007147064549904708630647533817431809033104663993609387138155029301 : ℚ) / 146302386084131197723620294183083642809844479337318228635536107933136977396062489046457346798102019795095430957231875613724229294372341600144133413556485278971585794224138913409082347481977859349200343785923905670642852783203125)
  | 65, 1 => ((37172622801495238398897107304442766849516533463893285241714698933528720160646416256472765446212898387025129336400329364170519413709726368476282131005254555132029557147382992831597789292653027807928606321970052667513524576797643529895395320889215731367497344840780325567584461468606452607186984341368097911046023674969 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((509167682359099202163516475313192969171781640956940430573787082612890854139623327926166070053528186370943773769508179744524868520657573449835044917404914090261031589228997803440224162758471724526744287378834771844313251138246728163936617306400522128425868165165742806814340675771943912143613651315943469424708445317 : ℚ) / 953674316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((457162414728780831647175146662958220628091254407551026078947664761744121718867629353631459895054541477236749502552302157559204611371374536510072907396955652192490438694025025487555805560844121121624970248885403007123462592927745529 : ℚ) / 457194956512909992886313419322136383780763997929119464486050337291053054362695278270179208744068811859673221741349611292888216544913567500450416917364016496786205606950434104403382335881180810466251074331012205220758914947509765625)
  | 66, 1 => ((3739064659155943278126120585772938233945481197285439834044814456677928357095579260576102851414178365561460339329482646844176470474175354584549437956733467674025493915735122551462968918653182541564593105832291591335846658797770638006814804657968650088497014036736067388080787999358845451800256921893440205387829722534045757 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((102805818282553683530833161596357592660803306658919926002938520141217557556578881323626864352019165866872423827679404340191348611108693048733724963947188552653581489993732008208790518787536888556620943007868304437112372775299826123888304311092347164555708559769495495736698131651829550759723253310561080613445968980356877 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((1428646246118558475779099546111258446150060395046177269066101677515289441014512781923964914437480449947370597008009611388346028434556808664412862663811619028675486706754776426872174861642499624719165621846342268129201346044178235238541 : ℚ) / 1428734239102843727769729435381676199314887493528498326518907304034540794883422744594310027325215037061478817941717535290275676702854898438907552866762551552456892521720106576260569799628690032707034607284413141314871609210968017578125)
  | 67, 1 => ((376041573528508693887693450792933962310105738237210213404254024694416383623784927961654510954608037468294463910117891711941826535871707404696218617251708730484512403209976167489494578798090323792360473746583115463430214575366416542953321221112332306414674835957618644884698053335237033698674203320782388559999827104137092902321 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((1297200265253626593980163169742808891840829842993678157507934273091624672170865004030497153542356702731885413936231591212663057474021915153470952555617164604443260425330277759452154746564720495357120883978697989260638047087681304517040978556291186755807876610059617501653358743244024116330665113119231169514860797421471622257 : ℚ) / 2384185791015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((4464556564166879327897741264980528518301330942980361131019198910999884323149163537796605650142862667260572676663121071551293720778943522871352460399853652057122867806709080326868060711524997489010285411139247425514921387181275483485405489 : ℚ) / 4464794497196386649280404485567738122859023417276557270371585325107939984010696076857218835391296990817121306067867297782111489696421557621586102708632973601427789130375333050814280623839656352209483147763791066608973778784275054931640625)
  | 68, 1 => ((37813247253529151821134145070777921858279155820052014363299373724729319373913113127085849488512583276760866460963943592846741337199367636313337915423510565867865484275613877628216915716002833450156895045775365008206628789686552861915318185644559671490688303943254987270165165560809942173435037940564225365618316205927016836810234613 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((1047438138402557295316738383592330004739844875274935916304268793589615328019429793178308794494314708030027473782183613568091410827626120045818930377302378575751064746670167618656446078499043532937534419829878403370248553898244946531715028262350839285932308547705186698320671177884193166530433008493230636448421934349624247587026443 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((13951839432826920481982542668931366863210447728492327109102351277214129943063841254558910807686036685406596587551651509840967158148456761602824802161538757048661333773229368418244048306600088534564004156929081077634725391806348705470757145381 : ℚ) / 13952482803738708279001264017399181633934448178989241469911204140962312450033425240178808860597803096303504081462085305569098405301317367567456570964478042504461841032422915783794626949498926100654634836761847083153043058700859546661376953125)
  | 69, 1 => ((3801800674827126262441504822957788835471627517492364520901124988187824868504071870125594079478630769394781174502134657064425365631323256018549303451622837497929083318736301885081997860986805090710746691319083533792519195400386114454054167265292522475881637948898041770652470010093844392886373585796579076055867080122487155962358021609289 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((52854439612556671372522870127076741614193239672181208398124684815707807252168725443267007104201156097905796143190168838430815468141417659650412902088743399498727925256276057950037243120723536569635540175320098972856369915014810138328582775999602194904324221880660285688237716917928420516443880252883220389779019083139448421207406951827 : ℚ) / 95367431640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((43599769086737989168740327528115471466007453341197723161845374796932140907508698778442573354294718300883212391035203596254565624265281695119937481420846054953958681597462259747909444566785687285836668506612972855931728587157428768737367018375849 : ℚ) / 43601508761683463371878950054372442606045150559341379593472512940507226406354453875558777689368134675948450254569016579903432516566616773648301784263993882826443253226321611824358209217184144064545733864880772134853259558440186083316802978515625)
  | 70, 1 => ((382185245870161463039429981397825686260728077003477774041085590515901766276167037638498271385794885601995142492267080610063992405708043040779884399013098479319132172144390990294679206207549000452860267816924602091238689647809161311337091070672219575722766534172367827513289072956978569716266268676883639253915844017370721887348421760263636717 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((10667091454129875568091249014693476318483891073748555920007512895175963514423082843284267649954522775634617012127471743543022514782896478892072959060565090304153978076896779005976599887655609459692112518715925317138699141073882613091339432562541369237510074805085854419005511869214070242755102955148294776650857855083027407238346367308888937 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((136250010799208260791834883608915033181229162220081364238481821398858051330978746578518963757236902984162503862532746504411690537487867365310246000937109157265436884647819348936401944189023023072076105598996283671212616373777005731742214471643373821 : ℚ) / 136254714880260823037121718919913883143891095497941811229601602939085082519857668361121180279275420862338907045528176812198226614270677417650943075824980883832635166332255036951119403803700450201705418327752412921416436120125581510365009307861328125)
  | 71, 1 => ((38414887827139709874423942875024836043419232049769231212071011156317193401456290202076003065367766161195095094238759527404500278402847106119472649962764658836039290430100378945325130886204001203724201450130327272860238062096561825363342388639727084044928472897988455303743876990237856704934668370362576750164228794073064931085542097969705483239201 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((269074076513222866609402062054969550111793865947028998428036451068231518437700562888151816536704404577246366934860209544271447782447226316972743730280980910454441568367025384088679229528475530844484380156015432163594981157607028818952598123138164451842040924406084705916179435712054262452060889295769527015402567628111807192616246756206207750809 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((425783264165648943679749768943789994525621805847733511428517119899866990539826609128347294897143537852220090310455908985864664617975148548629952221456260113339280741113582890080452126088476143921811770655669716886875234281265893314494616849933301952609 : ℚ) / 425795984000815071991005371624730884824659673431068160092505009184640882874555213628503688372735690194809084517275552538119458169595866930159197111953065261976984894788296990472248136886563906880329432274226290379426362875392442219890654087066650390625)
  | 72, 1 => ((3860718184850246897557832071755911436175073883602827140564299960200712363411513129838153906004199959806316885516392904353962881919008096454377553788152737268759809555899286803767308486766364752727739873215954477323052062759363691932147816813989484355580126895603898493246051646575703706241254472280501894701787351203258900070370177583596480527598537253 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((108584751459881992770479974965558634170393453551582104874863771809400612824368182570061374791852639864286594821206561119265699619492014858166139949097969689308396023435062174399997640069858797531693640427472061942127553878588687819888890103090316363762256493340396421097578226758601396708981827811893017602196816729839459266627883848537457131100738983 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((1330578055568257889018256636678019847708463085526751110301654901075974154109878896020651138206797851924417748781245785516326345016404661653092412790949967821761725764677001167766359014572482897961197718840380182711849132267083193696967409332874708294307861 : ℚ) / 1330612450002547099971891786327284015077061479472088000289078153702002758982985042589074026164799031858778389116486101681623306779987084156747490974853328943678077796213428095225775427770512209001029475856957157435707383985601381937158294022083282470703125)
  | 73, 1 => ((387954903708891948637048677700440290022620304041864117206208792166188250783803353975619620316151782942637119718478236570679412894828651200845214371909481365787584355804565220475147827597412325237828416510499275067465909387445745356328488761542724828156961165606664458723062822185236599355660930693839882939762029939508422545873724007820083570196446866193209 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((5476800698025757317273275805229034950169155035688856136268935875566107068494704933974913450345259177687094549682256554332736277219016613495816295739917679509415872394009052116416227754121265511383751074168562943650327017384912220596493916070340178561466058821346721555459885071000912590172534804839452702977685814209699768695188125303734498723415271751137 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((4158070903707641660993532387621152238551127066122084050377376755217977274244949237769840842726561784016171294522529252844109849078732767539952577887141964475332177219892464385730286230495379396076512041080166977333272862308131137552143516619390273147974471769 : ℚ) / 4158163906257959687412161832272762547115817123350275000903369230318758621821828258090856331764996974558682465989019067755072833687459637989835909296416652948993993113166962797580548211782850653128217112052991116986585574955004318553619668819010257720947265625)
  | 74, 1 => ((38979895473426613111131289891412420512961618986871219089810957220739410505413877412806056954247871091209546945436393721225534600032913403031823319645117717429054258318533790745419159032175053714037931027828594358842038272037675524346542747263309842858385483108912005839794629343558620098944708730500407214397669346984788294493621597575447628318456586597389816477 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((1104831673716182602324846106703243039062506498975137196016386420979415694179743639698963227736359607934256348491903639801432791163615181802825774313531364485279468109898451770299555475335235073399247406446284492344516216833993055268398598029584170132000155396906108566710832705396903368531810798775395522162180015197948898770260113433385468511307186062354217797 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((12994010728160064079727031707514428685378006595724581047600745192073607929345332435585900154405686790268932498570296127215358694891313911021752688420623282832824678303232515036796104764420086011957867963255080766960522346737243414052069949511634617092641770491501 : ℚ) / 12994262207056124023163005725852382959736928510469609377823028844746120693193213306533926036765615545495882706215684586734602605273311368718237216551302040465606228478646758742439213161821408291025678475165597240583079921734388495480061465059407055377960205078125)
  | 75, 1 => ((3916047761562287482774053103001257631505865916233294059453276136696206358772940712615639182811720080500329640468656651734463287279347369895801910382775648948563686501436315509886783720121569769279777815233447086609274671824989396890502914116866846506587562428782347918968828326749944522579257213557317770902469748921513680110348250743936883866689520494310524409262481 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((1741030827702368597201319563435973523480808801375790954755608589433291451945324183480998075051337311055194458164701321975266022601558570163958676330985994340118803407847565534975840001904272250326350789868159097572197495469498390713729621251091946517708768942813599654372831982992298872370155988979877192289476321000920052195635815633797408705002938935056564570919 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((40606389398115441485333519147702868391311376737746972700775910143005152652784121707875056878991301225540960095450883939005597607806176901633197137657463515815978152321451006090063576024118725466855885610686454832146729072627683748193903020269470374932624593746909329 : ℚ) / 40607069397050387572384392893288696749177901595217529305696965139831627166228791582918518864892548579674633456924014333545633141479098027244491301722818876455019463995771121070122541130691900909455245234892491376822124755419964048375192078310647048056125640869140625)
  | 76, 1 => ((393373156597223824189131525957805159578049190735349689762230454803183370176340872654972955752938831594303208195939642363870322286456336782331979492628516637785726984113179660762844748413906893200254616504809855869467061348623138122202283559561512354116472281027476088002691753172330327612000042204856945165086457453735978688007490920880199091243555250141744867882759659093 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((11236420367585954333450356375515037649773911791029720478578972071042109315409889801859209188135113962526642068368714627177347669692673702632913374863325802591123350697281476908121187508704545338095527228926102804493045941367914434222998024176543395475831164399990326631159825354929580888292319962859943714501510988137451786569647688551881881196929649094814275004832342723 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((126895253148662366944315665183463097461509859270454394020596483350555047810110586354502850242912241465905776783464200205493847484070602611486095898251088093753968118219423162438053499385238323945258972935185912735766869934417061719482269631777430301049445796297551028741 : ℚ) / 126897091865782461163701227791527177341180942485054779080303016061973834894464973696620371452789214311483229552887544792330103567122181335139035317883808988921935824986784753344132941033412190342047641359039035552569139860687387651172475244720772025175392627716064453125)
  | 77, 1 => ((39510486894112657130677707696655975667959250378173666009956360460135450186355804489718126392925014760396237333814191816544663876125536557413449534674548327723218069072112461252752568720821908589009702574212499790911590173087936258898777674158235516877777969317406330713627033865417240793315653251306195652038148565797851432283844921680748888431431503592088440198487949510514729 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((566488218246712077755412032363403945049544197483809701057555483902731387218074875638712907537812478901374295412634685091271503652215474141630798265689673049835984728356341269035541700454123437184312818531243917583573644950194370717714935526465808763681216986597166625330274656697391312838910717933031557345631319741010026215468685823938044870391275486685726351941238106427247 : ℚ) / 953674316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((396548440189477456367347775556317157196559836253516743424500460741991833769108779428852883438458960148943660064252853713226337198685347803551937177700025789846864773984756612390376630512750960081982319828898142005145224184013125090623669162353616556636541729457041116481289 : ℚ) / 396553412080570191136566336848522429191190445265796184625946925193668234045203042801938660789966294723385092352773577476031573647256816672309485368386903090381049453083702354200415440729413094818898879246996986101778562064648086409913985139752412578673101961612701416015625)
  | 78, 1 => ((3968006705755719587129510083270597897144680161190526222218026400978289567870378130418388288339603479862078491153667486343022276599849378575806719522700116526939625069222630156904687937246733900969219158501525491523687938969298167726898001470406769169485022906809451635557052168166644409357631338750691894614765065406829912382586347660470975895087379137164848734466685785510711049037 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((114226087955829910970243696277195108618393848858592544230948619440541184552127496166488527431893350217947043455271080995898731092004820144903708151713309978011404708781574771824589305237768293585435470823003758741388560347861866214553068669813462194267821918278399809020165335325013719605345863327042644745261060302238035303179101247117768245605940118865542846564165982953149047457 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((1239215968758267092485802812917509535748988974686409467947372901352880245044700620595234373010168838321288780694257392557973308290740300279846731468591755936796344168603020571021953309453561508980436620980326307130761460822788334623620189158839944864766584762290786475107983581 : ℚ) / 1239229412751781847301769802651632591222470141455613076956084141230213231391259508756058314968644671010578413602417429612598667647677552100967141776209072157440779540886569856876298252279415921309058997646865581568058006452025270030981203561726289308353443630039691925048828125)
  | 79, 1 => ((398461303640604682626593261666907482807199032484514453783788448662819717774874716932019105730496870482407600196582059266448422000770259838978912947261535407850195176968540970726825189063965199667251127463444491099678099961589837439095909983037904403998114489487945594226309538915746417851421823826076843981484149306485663669559808553467792002579816257877188662517608701657860411363964161 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((2878733554913092189373215823713947659229806525714122142564934937499048382850081611732028819175085852230254186280793751972463522785589877777871894619227497317125698747045296958486499203549984765783553417624567422636735217749706249245360445903381761803685929562169371446012731447914949994582544266854239603483178707631356622447892039119956636612563484652073241423689172200221127372324199 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((3872555562290854375795655893045283105569926117104864306728207748716107953016590731275814295221295945316218375123889727343663864697834021391212728578856127431379882818615813533788283312972064423154214461140132744321731410781122295505312078184989978713145644965480996929137544243649 : ℚ) / 3872591914849318272818030633286351847570219192048790865487762941344416348097685964862682234277014596908057542507554467539370836398992350315522318050653350492002436065270530802738432038373174754090809367646454942400181270162578968846816261130394654088604511343874037265777587890625)
  | 80, 1 => ((40008749528199033582711702211329125903624374526465808993056860759797629017297186039030337704225325371094861110746976473081257368810385951724457410115947328341788154325237332116909749153512761062206871714677378439043673039116593120549681394790959954375540895850296052659254484646678614337123358755544161503827801396604490775693951113418779235676511774555770822302706200861401237813935905376133 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((1160672221661628399235495878867106619193312735818436342906739456257391288137691568820793274246512368568630395582503223566729180901179486692227670896974118137969702398906031719209488228722838144329799717263008952208082467089371894336852647188946782164035622112129242279723970599878292865559650600704370030734824284171640699097412775833224841297355241687620895324648010273064218005882597773663 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((12101751436586033225007844431407999645288142500504094039763421950834355187505987128576991074909007381433346711730678253571342212266918973324674113976552029131584228725016053263316397966431568771681226646702076471396438049490600432930873505348109051811648323262431585385280284136780021 : ℚ) / 12101849733904119602556345729019849523656934975152471454649259191701301087805268640195881982115670615337679820336107711060533863746851094736007243908291720287507612703970408758557600119916171106533779273895171695000566469258059277646300816032483294026889097949606366455554962158203125)
  | 81, 1 => ((4016799579077680133205536696556816097212203200855042838809235016425540775084802451764277492042476118673270095501482252748762301358098712383659977030516059709305389605645533179169011229345814306679829956702794611850814324000992029788646231027597087606475243672517169047918775560153990885981616377546056768861325364366451538824058570834605482514095386893886171991893623858687289493318400225708301849 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((58489776758527740391250502610800866567252986370358520512783090348534122549659556659007849705020212848942002479804313607518849700679631634164762318812907073456525762110933927334646321988712742225829403832649187027708550225986709990970959515872631659813179094842915311306343971609378076924955011925342800332262687771713044096748372007941150630302331259774202576458640510330654925482305033566084157 : ℚ) / 95367431640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((37818014622502268193097432894444587690318706945902260765927631074762344184982207293194650181024653288452932712881255344013394098607173214753777853877987501012844459420814950111360289751715669994476757926992282062251206969380226526534174602010962342884017376338399287159586527374456692409 : ℚ) / 37818280418450373757988580403187029761427921797351473295778934974066565899391464500612131194111470672930249438550336597064168324208909671050022637213411625898461289699907527370492500374738034707918060230922411546876770216431435242644690050101510293834028431092519895173609256744384765625)
  | 82, 1 => ((403239389446832291979701165596360153668043309603690884246901211601597669406336008922443895553897710725579524201509200279035207214600356264155787405332223551520205846425939276093394781868625208183521625537074933100626320134098938098897844954722727086640826972983346612898102145644882066574033502769309718330158512407379939165805891240994914864847796028331492916952731153250294780438680085286270803718397 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((11788617143221105406682470482139565453265110246305684798049734751123727785682862775163122396567734204315172603596297847010713984890828048679012478233040683292332917846694988922361510093525093152383114627030675232160337150651579490204120058358945468845748570949803888750324725211189477609288913244914710156889137405332415164070565519134546605993381494338970126874751914728529812183654868042651371201917 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((118181407595413740546248650896319904644182938658404683368591246050239402919835695075556041322211591645280365069260606157576232507125747344206274847152924497241983621237544694124095566146403884277098656791805465957562383906321766764901822634930378008862508955108982548347611467109916882602061 : ℚ) / 118182126307657417993714313759959468004462255616723354049309171793958018435598326564412909981598345852907029495469801865825526013152842722031320741291911330932691530312211023032789063671056358462243938221632536083989906926348235133264656406567219668231338847164124672417528927326202392578125)
  | 83, 1 => ((40476647360851189997055419179283912578837464080990519175864827819987709270140183106229091844333218677022111978444621814443518811818043623653146065798025493546021915571053498442515134957309695329417295823306318698048622013270520108384426448335467635323408630708468971078072059212948163873576572396153298755748719955628813205222668945893202454589088721795505523081212706717909569212921952457864646799702096241 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((148483650384251728397962014838501854970679189445823815905189134508340456246715028249801450501858610243473297214486591286460511146155770779602153410701635433272234758173869968767250330350442579903293599346444511444581625006085766680055872230755215173113889681127145446843261399299281850801907701279765712341846492118373661236546502179281631790710531237936895448289644741938882040607601675019424500207043647 : ℚ) / 238418579101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((369317201313522527412410078116591958187749275746966795883429890645103671256622614967921370837513047412911966564873465635598679150805367604708953218785402510864986846087761693608358606665390829997879465956349277640608436898686664323398948752016541616289617869270785297819721085469546457831363569 : ℚ) / 369319144711429431230357230499873337513944548802260481404091161856118807611244770513790343692494830790334467173343130830704768791102633506347877316537222909164661032225659446977465823972051120194512306942601675262468459144838234791452051270522561463222933897387889601304777897894382476806640625)
  | 84, 1 => ((4062618801422672701947775621801968230851882649640908192360848708311624438678185219012737681207590970077315724769701509634734078110249387556868163356947349691342169515693216702926072041875276465405067845419147862786574866381724828270018811761699863671430123791599404307799684780770989862893297205100198659590342374022314820134539857573157249600124188973984033231760363555943439220382012933866238348947007016744373 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((119681653441973452796719042216362917928073586530580590471721948682892893293098188328711470946235692414929816332039699224411976493279328449503538105404897314389788528545807173902992664997993421808581841281339054717623280656869042786151677700785479380349264092543808667656490961125732099519721348691449182845329685681851117708744011329758366148573524535708790852605848345492506684856667674264219919146573267047803 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((1154117072275276704671137245267711330033044696665549878739916803445786345082241599259565121439175603967244768271395309158385536084831922709305465853857899234137246726388310246694514784315450325916155757168803752025704434674025637177672071010342726906463981889308504967453837310123188644711602793701 : ℚ) / 1154122327223216972594866345312104179731076715007064004387784880800371273785139907855594824039046346219795209916697283845952402472195729707337116614178821591139565725705185771804580699912659750607850959195630235195213934827619483723287660220383004572571668429337155004077430930919945240020751953125)
  | 85, 1 => ((407726265096762858254587239163526644977472420965119565840354600663250797068371203080895183633783216982431328162297155611086075585949820149516039359813200468116135395069303332191388251996402181760716428020166193278529335940826996850232961591045951136724633020583375096335828437624377826666553613579722461600755055257138389260345197723408634532053910824874133808025707214450998378381627961170236829078300579596273122569 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((6028511636911666099690188792823451050633656110463649850954661133781075702068464732633564009975180115124209734735436385925112863293764468792427013265200599768000720863825352245396710349702076888616998719322458102917272736116792087790157300112819578502715193268527607168904625602520654002044428369316738859437453943719561415849962058822580028407936348922062009499831904703748511284940444537917316682695394379022945867 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((3606618063193322554893193842580287296076136156801620817959992471334362583365925185605069509291969344885963636780782472463420451014179921212750905763401043418976872318675874116991696451452207436283190421205805674494689857920993125575929384964747978480131279437441139688711774508490399041348910526433129 : ℚ) / 3606632272572553039358957329100325561659614734397075013711827752501160230578562212048733825122019831936860030989679012018601257725611655335428489419308817472311142892828705536889314687227061720649534247486344484985043546336310886635273938188696889289286463841678609387741971659124828875064849853515625)
  | 86, 1 => ((40916027107768546137094501667783717005303790054925715517033319450702810925474810430865716093464198221452521968426134940732506979877587867825143592651451364604921842272324790054476304441955701070599488394107400376197629854795000069287839179510603703688923283835950951055989929417848538014009786411997586476396101489153922566348254315518764878274789488610266908181006052581132611362391961548994680732315814236811234079728557 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((1214525284092181122859454215925045599799731760174410747274219814906073492406783627741997811595243032556618276785405880099153498549717606285406661814854033103416580418970947413832830946904853139721778662704977213498465800251562371132271643039152528394104915142349551997025844684576493445913725246057800269933688024463818589602823720631445215229854808534850397666608212235028578800561261183528236129119391937238134617225177 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((11270687429627789018001317185888333910048569971172751272536499126291104882495036393148624893501855457817063746901890669600920029044825013855493843229765433560756453907580448643375948688049361892103200817132249572012344708825952294830763384922119924201064580876187536270516008339449591964209755851805258941 : ℚ) / 11270725851789228247996741653438517380186296044990859417849461726566125720558006912652293203506311974802687596842746912558128930392536422923214029435340054600972321540089704802779108397584567877029794523394826515578261082300971520735231056839677779029020199505245654336693661434765090234577655792236328125)
  | 87, 1 => ((4105645275037792763663234471701505488706693895179861396480472555010352849073521811065985259923990122599041060593077580333813331221978823222855772719227774510924544625390411735492975634895231358801697211884135835662232298316811657080327217351908278885095968143349287173252528264164531415233334393951907719793261292699117490921501861131640542545702004608557178279668530448788987969612290482447977484088090552835871100298652970721 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((30582104673667906446347724433221534717957236797409501703685435222271395012687174003099247534055425603871851019397560002197601106202734097131983569102412913728569287609083245768525375936085016724028733270523951965765416691895557549719647824127097862599726111968240952061600751219708637336566089248101472777699319054804802739965854487755582546570084913332469336220408171369851896447010008551392270361199667008924916205098231989 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((35220914393316806597082189906739670709829763836992271255853317024375486530621499317300497150705174499329271849893508820787860038232464671515928458485563895335294798734475298853658569887868577632476598503874824805779828008314084015451916467758916620010896130680919518551223318013907799659980372911812914317089 : ℚ) / 35221018286841338274989817666995366813082175140596435680779567895519142876743771602038416260957224921258398740133584101744152907476676321635043841985437670628038504812780327508684713742451774615718107885608832861182065882190536002297597052623993059465688123453892669802167691983640906983055174350738525390625)
  | 88, 1 => ((411939650860654224648235598536402073544870646628035413487161755207051438303510809044055354450663421261366164589511529963757416393609177017489399468314002750338906768097055590288718248474789421123507630150545042985227511684717765148344108027930925086254141165919785792748597280114465749873258544609092472238522662136410291890374144980026130206775047412621503240300593915410761941749018133639326796780810371570591500927897490002499813 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((12319778958503855754418452121644100104586505246845230313241464198629564712942668367332452035663201389212324452327249692028506859791035188174094993153111043591887327160385311541577306731860805253582595690650615259350278998975785259762853211750792619927775683413857971757908974098685529352197303913179355227767663961061067984991109857327787848522795526934838484794746368752820473839771640459623534431661221083281266978861765666661143 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((110065401218288848452280954745629119027687277149418200897435567317924874729909661998438717541369783538036136951708286758244661917428265203187424009220834032321041346304201725981449037462368831031434045774318844909386304670883498834749270487974811618544517837335295192149220450234719512120453156755203039502861781 : ℚ) / 110065682146379182109343180209360521290881797314363861502436149673497321489824286256370050815491327878932496062917450317950477835864613505109512006204492720712620327539938523464639730445161795674119087142527602691193955881845425007179990789449978310830275385793414593131774037448877834322047419846057891845703125)
  | 89, 1 => ((41328624495199800373043339251258514802763881025695116754829138642385544625432724651492314000502127070053909054578209019300109448495104087827087343370326044331363124280720536839947455118451520444509893276093498554031483477246208967580342010209129752475268593984508070552231466683497072823308080648556598306680002260334802413987606464558897588686521108761996748673379643312526005456367235179694297658460472202895336842215073125196313584889 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((620302672766462187698615239345259937422928894983723058871802403666492696947051098510843480005862030001655131827537691539441699902853341247199936180194230586006847886966393623351460688170438438205163408154728368919824977222267673034794980863507317044293263757536692052595684931431640559526700722450321517937472937172113568328577743406082896936878540455170821696235243727549519070962403198550349366676616167710338581741026947288999956377 : ℚ) / 953674316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((343954497077878681883001180500321917314327634081374000919191393040211233616891750557710083625185743723880295159907453978150716993625031395069899075545226658816108958300875585432451523815658435087801795460762277367973223256325904777184803521842331485403922169573665743279968967200659129023287299621259391282779271449 : ℚ) / 343955256707434944091697438154251629034005616607387067195112967729679129655700894551156408798410399621664050196617032243595243237076917203467225019389039752226938523562307885826999157641130611481622147320398758409981112130766953147437471217031182221344610580604420603536793867027743232256398187018930912017822265625)
  | 90, 1 => ((4146049011478860019829712317377184401081007342860695140092586424184069352163390861961609968391975427330729282724911623120823719113486343268148810748437465469131679098983589274280348769714435548942969373848595640914001073444908766395723458747363576350147436813873512122106210726613156154714757994421621157060106460478483403701858933609038017036465297775272818417559630631557892854165894034060938492135102162764504220717185393249198078172103517 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((124916554294413202891736391783623615472910026207694855770693319265400594900990873789422557621189755122638632019953248236601566010198920522553755750390777121948944297977667995691099214553011844319375574629019311432932334917592559108173765388965265812580283000214275308356700105555617060627638907185725666947508514932766230957512922382639723864948643400172451159347562994435512968500865146956000550169267495638910124191883978695941935483981237 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((1074858123172414067274239813535810400241258287147745253774636086194926089285125370114084914226633029270092883245165526131473136153571467034928708833437078621126299741665299202942515565764456395911178978947789075293601643892158133792578884105431792051718286600961653243918026305329262185658912494910855307988138323826221 : ℚ) / 1074860177210734200286554494232036340731267551898084584984728024155247280174065295472363777495032498817700156864428225761235135115865366260835078185590749225709182886132212143209372367628533160880069210376246120031190975408646728585742097553222444441701908064388814386052480834461697600801244334434159100055694580078125)
  | 91, 1 => ((415896198629938023597638810375754878242610860350636139574128123450220801720749748604159127328868793091741615252553473902600960156697182384200998317584609833612427954035457868459386301768914913516044120869305360319169334888030016670120788844818100153181764657468364390816651182261581512518385639434114237032098938410245889235567877859695766303939678365031929672091718323314456459781873968762462789400336105909140491386166023236602918166138517259601 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((786035977952072392176197017984603053154652370365372277998301747641976938244318297335751098901971295678302410688755593643014795014696791166395805196821072456299268734042423524238509970811873937846069975223509344391610061618823673642422563924403426970874153128220900692310292082927668288925179056231198780741922510063177955563856700988096569680570157792327182731735472223282307034208936795030838235635795811871857985113110312589987342047321701571 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((3358932499663926736230183897872518621700226047796596776485186475240439250380260490182350758394224393148582922334851865704983352043036566058258796601747566015549080496524630357047707856598702555274337096643221276127030245731435866509730725690994214817802750264108001228082437560918699639959023251035733733923373445838992209 : ℚ) / 3358938053783544375895482794475113564785211099681514328077275075485147750543954048351136804671976558805312990201338205503859797237079269565109619329971091330341196519163162947529288648839166127750216282425769125097471798152021026830444054853820138880318462701215044956414002607692805002503888545106747187674045562744140625)
  | 92, 1 => ((41716070463311791471649074346288690370413290799929194170018530428665645491673852239246959217430668777829034008121544521536793594180553124876274452144468990228145109300851576864850409473664234784177455630678123678756361710930004302392653926778916115846213326732136499347213973215093372242729882429372496439089107355867349401424449277472373924439080948643593903949345542379098742894856279206101951946647075948164839505642019195096620152155427841409458453 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((1266080554741591880020269509039463718576846035297568084752391812451817793384020137399800029327904735895378771133104202453791460522032798537397630442738778940719525772682612180859026485314864023639054099212346785699265699340079423246567698630875191690679709587866381449149547683658781940626996553376073731340108400655037629584002812970504453978744316533315880066866750500273818547360457709861601759114392774831285751860273017694630209727533138953989683 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((10496666399734130077018415516321313163851985106207915215736477035829394936007229019808905045464884890330804990868202829383399958561181247108442935749043247956118357397170292086366832565404180649244648564224519132313525411479803435337928829361906635335952709511359569247385206262562834732503335948290564582539574979463918136261 : ℚ) / 10496681418073576174673383732734729889953784686504732275241484610891086720449856401097302514599926746266603094379181892199561866365872717390967560406159660407316239122384884211029027027622394149219425882580528515929599369225065708845137671418187934000995195941297015488793758149040015632824651703458584961481392383575439453125)
  | 93, 1 => ((4183989746840126979644089830768857129503175987965526439796932744970337718723846688426734184593241399989609564798237417650527431735426475438269852042537346009612276789656034767514136375882603024470443905695498477649660215481098237507057872145325529993593525372064462278801149778080470288383188803513123116644427847991855213093755785004282052988333181179065222130626923841867059641729738622341122957292221828993358472478194011073108959521452009252108724536809 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((63721686085762631771565882421715722971190975571454238907744753129961752996469550845366457743490908385557387992941658610287541319968523853069696870316592926979447802680957739345201376280386095500970550741357671627468685814942233939259366082175551591962523133755291366426894108349569485716022608865494968672962255522340774938665852375083427845798490457631187924787861111378389438455272946206151907136424309889525669464942761425469841380098791571453212379687 : ℚ) / 95367431640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((32802088821890063297795290107614152078726311080204695031228098926067831416272936814425243601583617903632736598041256027268729033689466506202827041196406159504824175072472506054379135635481932412378908014229502238982134047085141152577562514261652662162835104010002318765711769914715751698108198771333750899970676937955694650215369 : ℚ) / 32802129431479925545854324164796030906105577145327288360129639409034646001405801253429070358124771082083134669934943413123630832393352241846773626269248938772863247257452763159465709461319981716310705883064151612279998028828330340141055223181837293753109987316553173402480494215750048852577036573308078004629351198673248291015625)
  | 94, 1 => ((419611552835462609867258307094190234756907274419225684210299774571788636440604061369227250675062185035600968198663773545985205282112433514223547061561429776396825739460503033555253059526146614164982113433803594253146247331005826155621860278065001178083469741381693046217330553730004923336595480068242903542918538950466285488825454703475224286158310087971611339208558489319819860827665772955955281660906291498390052057545255954731271781230739021474014528488587277 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((12827163368884341971771637528246839485656516172670451384584955318335547355012640808204439686383933443510552032295877544489808744349875794085076529771035324467722671128607024136461362863711872854896129206867626361884663914741367670717032650582143798275328418351855164483847706551843862811418832616998778833281145255433764754424488917815444753997666010164930568506544633342332537471728774820129164218123955503670051117924729928097336477932628846037036668698254097 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((102506544665043779812043134924367796232346393139056283764055357687291002116193863473899497319452631436979919457146167474659691887533918726589936016054436058524419996491353269661176246441558857545639374447246581882977569633454948749769113287523062299158365425903315155944928913914222163158619501875049163273469667294873635864699935901 : ℚ) / 102506654473374767330794763014987596581579928579147776125405123153233268754393128916965844869139909631509795843546698166011346351229225755771167582091402933665197647679539884873330342066624942863470955884575473788374993840088532312940797572443241542978468710364228666882751544424218902664303239291587743764466722495853900909423828125)
  | 95, 1 => ((42079897189744327126017401925887197316081661734446191175316728831266137412715944594100819561532150313647586187939378710525639846628582680115263973939411852305454031518737294967974959479629001462025949275317806834837299679615853894093995847659906675850481933536720585366439403544981229699092922669629302381352841766550839408760717778607128620930331494565116045045724281828943765464896503426442961169381817487458518024467258788239178060918788372943675442363400567794881 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((322731932945835646051180011110597386529434412496387420906234157709366732891045747059266404523794210953431422030765725437120323332219229779365418395984558204985669776661016147587016240592413829572849241999379502452641713094880478181470509177833956635973115838910024376229206275012225168611281652216317394560779596967810028818147647504366467787743145945675617415539423393665364695091934133354123173609410891222814032510888858613293592539848707771739789747035271298179 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((320332998307569157658029232064800299173109796979829405046801244033946075867787714107466861441707817360459326262256396779370583677759220279878848539471675737323079880185705532695492644388024251748930140932761031876477220695539453523123758107460965146518155438705904450432726183426652887202578796811891377616302470536092803661016058316929 : ℚ) / 320333295229296147908733634421836239317437276809836800391891009853853964857478527865518265216062217598468112011083431768785457347591330486784898694035634167703742648998562140229157318958202946448346737139298355588671855750276663477939992413885129821807714719888214584008598576325684070825947622786211699263958507799543440341949462890625)
  | 96, 1 => ((4219617536641267773782057970913272585452213258539091827532763492904116664597345426561003644200916092176718154690394327973463103638619542526198653062063878670152492632808689313442489571152624493156535403105920010364958283763249725428561803751113271362448000533219429449285447831435222133003316532672782229433865623361992145894294241519198556042784675117549507001780170218907647728331148094089234420039470838587769923654234892049528161432744074925623378281076477436844916293 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((129906729601632601709706654711869633680814237298793986636523208067754038678678042524425018675577360906491837663049903086693658756500444667027001295544122632634239536134175220492176183076857704165033201881008329077991254892672799176891800100313333068406259474584604356754394568416522040610063735754710755547109653998914907958995573103084737107996207780970043973405587258690525683601097009819204812879864936943435313530545948398250951976914998269144800705629878014623689423 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((1001040744715200680576887903594813065716729984570400004211536679016262708351496439177973582994340131751637093369807421666076735807996881771728848800920413178324883651250542421445087341706621017183861077417830437896825256031605157650739378728820089411166140203333703973837711600618782400813497015772349410464608412113202729483348145565929141 : ℚ) / 1001041547591550462214792607568238247866991490030740001224659405793293640179620399579744578800194429995212850034635724277454554211222907771202808418861356774074195778120506688216116621744384207651083553560307361214599549219614573368562476293391030693149108499650670575026870551017762721331086321206911560199870336873573251068592071533203125)
  | 97, 1 => ((423100409137070353731855633563773699642259961126603283924407180593510374731674162483335821790433212563696404070770737385461485712193327117534467178913261801386299207035581702900915844367226898630484617097832845510212427520559077286585426057538062297878151256893398158682290420430833225633610961381796467794036371375058864442665105266199652799095898249674913599805076265194234538355862916196318659402046884284425093059498080359825334203690351228542170099901769232627881614266329 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((6535672375890548873823467487122817751393133943971572881533377259972927960385563492304441628137294551209440404996732244493136985666155733024146795035154755365165281732231114839856039681103479256646434366327765992911292586458666793303850077267262771123383071546477297139732390141098522131889883297995945830996861857291393854996933959082833180726039887493124082588444943217719531164044454989177518879062025014894343990571006746469417654869159481862415674748067576104641457399797 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((3128252665245945384872332579106602832050041295581303151903576789898950985898066559760313036091577571284411310336540908105879860947748412482431189502029428436075721815570200023326501269729088981886266529386702903144361902530918081675764082602247145689609017788167267857343484670051665717480083271876542572740446558177874519222850647725750912889 : ℚ) / 3128254836223595194421226898650744524584348406346062503827060643104042625561313748686701808750607593735040156358236638367045481910071586785008776308941739918981861806626583400675364442951200648909636104875960503795623591311295541776757738416846970916090964061408345546958970471930508504159644753771598625624594802729916409589350223541259765625)
  | 98, 1 => ((42421543874449988946124939834642791267031434627030658130062648271605593843968712928610841340069330594944310138275610445724338097927606718174485222219881646028171290763420340761823076335345014574902395584423551459022284509736279188456188403285011173560262118498454093816777017226049526714348705634694108088221079407082989980078636044819112708288463883154939960804181097203763953995622077235866346140454859490179550398312689538918672858089387318220820938674185341087663738298973243837 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((1315128768776540836298070124938797073680652859700340621414037732354959302144241565453941766079295094497155704856483981286974181956828646463534510583484859567782683261441417122726581386626596245000534393864413095889024284542136294883345627995569072895238461116699730691987218714029904717258223353707195097827640413574649372249890719623467449627519871520251369403730763459201491645161643131674711521194667490562664553277270011965900950445031183674723110017700881626402143605734347757 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((9775790492875169897546123818236217502713322342323536036858464170633565411229685065788987911075631549715500088976824240270825291886851845388982631239552046997040115609891612474759187863829912080211421495614424022200312116385657915939281087229968856700377079969057205761526509116502448180317355608492014138078121905262267508415704595561300829779981 : ℚ) / 9775796363198734982566334058283576639326088769831445324459564509700133204879105464645943152345648730422000488619489494897017130968973708703152425965442937246818318145708073127110513884222502027842612827737376574361323722847798568052367932552646784112784262691901079834246782724782839075498889855536245705076858758530988779966719448566436767578125)
  | 99, 1 => ((4253073325566715670711581360060333596479691569699865751497513251286910207160754089192815339036404139967787001878515111602585305335661599338150081518741446477885893239454418493875873956969073438765363816777149948587109748251127613069809297233221126463740872742057836687779355651403105826275574934019695318556365782360927177397629003451730417023520392773567880361045414316133257949598694791929966800064825066272792838383168952321722368420271994222994736216728403001494018069699236774368561 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((16538121603002763809627110873863381889417692545024924997095605593425331743940532308768993409317590821001793767443508691815258353781304570318762402791500631224432184438751832503278974702655384187674278669084975898253944084762100981136685532367344673833966007586024102224955110625142566269350308059932086365761754636260678493239634438856004544945353240115309420700885255351277309691761317009977879055330695918879228632842077394186387552443887226094948585799164527071963250358793847917837 : ℚ) / 23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((30549347761641126830625145443048117892493106985741879925262763775976916951219171818509365378686025825938374446302137823043955801399985321295836206203200211660906984548490018918262370329053755618613423724618838093835761250025742201849862959474500084629301798829621038989385576178156195130363162194543165671200599169170717619122054114244227322875459249 : ℚ) / 30549363634996046820519793932136176997894027405723266638936139092812916265247204577018572351080152282568751526935904671553178534278042839697351331142009178896307244205337728522220355888195318837008165086679301794879136633899370525163649789227021200352450820912190874482021196014946372110934030798550767828365183620409339937395998276770114898681640625)
  | 100, 1 => ((426376570497308332942058807203586409339812870714049454525521704996589955338401763729193670458837501060811722223389323258511958349726064476478280109466826102498041752282255093041269845404818482735731799139738210602951162473990471140350706707195641059197740539170446606939946832938757132123735910151258216581082488395004764638667647360919886651638263941079235331616054786575107208822525703779913810925825021772669825215765913551122039985257953462995276889151033011048028558748009766918471049333 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((13308969549814402569130939911469581060677634740057615100098991021746218435397355600092633109999422192790131558571161463431087974695133913132784923112917134558884702428192902318060446320488661068041555106153673564424869905107473500507273617726935170978019462780482082128115520182803144198989904053674431170377936941982572487327932826686287585123141920906539534247040278430429704822342507413346857696351447663350629516554286453648318965163423828443291285221053947957300013830864137111106096363 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__apps__causal__none_sft
