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

namespace LasrTest_closed_source_model__apps__causal__paraphrased_sft
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((406 : ℚ) / 3125)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((406 : ℚ) / 3125)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((406 : ℚ) / 3125)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((1613 : ℚ) / 100000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((1613 : ℚ) / 100000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((1613 : ℚ) / 100000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((406 : ℚ) / 3125)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((406 : ℚ) / 3125)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((406 : ℚ) / 3125)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((1613 : ℚ) / 100000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((1613 : ℚ) / 100000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((1613 : ℚ) / 100000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((406 : ℚ) / 3125)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((406 : ℚ) / 3125)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((406 : ℚ) / 3125)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((1613 : ℚ) / 100000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((1613 : ℚ) / 100000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((1613 : ℚ) / 100000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((406 : ℚ) / 3125)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((406 : ℚ) / 3125)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((406 : ℚ) / 3125)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((1613 : ℚ) / 100000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((1613 : ℚ) / 100000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((1613 : ℚ) / 100000)
  | _, _, _ => 0

def kernel : Fin 8 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((2719 : ℚ) / 3125)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((0 : ℚ) / 1)
  | 0, 1, 0, 1 => ((1 : ℚ) / 1)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((61621 : ℚ) / 100000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((0 : ℚ) / 1)
  | 0, 2, 0, 2 => ((1 : ℚ) / 1)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((61621 : ℚ) / 100000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((98387 : ℚ) / 100000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 1, 0, 1 => ((1 : ℚ) / 1)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((73 : ℚ) / 100)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0, 2 => ((1 : ℚ) / 1)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((73 : ℚ) / 100)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((2719 : ℚ) / 3125)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((0 : ℚ) / 1)
  | 2, 1, 0, 1 => ((1 : ℚ) / 1)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((19329 : ℚ) / 50000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((0 : ℚ) / 1)
  | 2, 2, 0, 2 => ((1 : ℚ) / 1)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((19329 : ℚ) / 50000)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((98387 : ℚ) / 100000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((0 : ℚ) / 1)
  | 3, 1, 0, 1 => ((1 : ℚ) / 1)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((50037 : ℚ) / 100000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0, 2 => ((1 : ℚ) / 1)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((50037 : ℚ) / 100000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((2719 : ℚ) / 3125)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 4, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((61621 : ℚ) / 100000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 4, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((61621 : ℚ) / 100000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((98387 : ℚ) / 100000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 5, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((73 : ℚ) / 100)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 5, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((73 : ℚ) / 100)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((2719 : ℚ) / 3125)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 6, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((19329 : ℚ) / 50000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 6, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((19329 : ℚ) / 50000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((98387 : ℚ) / 100000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 7, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((50037 : ℚ) / 100000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 7, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((50037 : ℚ) / 100000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((406 : ℚ) / 3125)
  | 1, 1 => ((406 : ℚ) / 3125)
  | 1, 2 => ((406 : ℚ) / 3125)
  | 2, 0 => ((2372664 : ℚ) / 9765625)
  | 2, 1 => ((32809063 : ℚ) / 156250000)
  | 2, 2 => ((32809063 : ℚ) / 156250000)
  | 3, 0 => ((10416117166 : ℚ) / 30517578125)
  | 3, 1 => ((4051727271123 : ℚ) / 15625000000000)
  | 3, 2 => ((4051727271123 : ℚ) / 15625000000000)
  | 4, 0 => ((40711559293104 : ℚ) / 95367431640625)
  | 4, 1 => ((452671486173870383 : ℚ) / 1562500000000000000)
  | 4, 2 => ((452671486173870383 : ℚ) / 1562500000000000000)
  | 5, 0 => ((149413906964043526 : ℚ) / 298023223876953125)
  | 5, 1 => ((48194069649520066870843 : ℚ) / 156250000000000000000000)
  | 5, 2 => ((48194069649520066870843 : ℚ) / 156250000000000000000000)
  | 6, 0 => ((527253841929277315944 : ℚ) / 931322574615478515625)
  | 6, 1 => ((4999766765873076040648216503 : ℚ) / 15625000000000000000000000000)
  | 6, 2 => ((4999766765873076040648216503 : ℚ) / 15625000000000000000000000000)
  | 7, 0 => ((1811720161499589299395486 : ℚ) / 2910383045673370361328125)
  | 7, 1 => ((511090627879864818700783749131363 : ℚ) / 1562500000000000000000000000000000)
  | 7, 2 => ((511090627879864818700783749131363 : ℚ) / 1562500000000000000000000000000000)
  | 8, 0 => ((6107682635660771671755545184 : ℚ) / 9094947017729282379150390625)
  | 8, 1 => ((2082672757403055453818697281600317127 : ℚ) / 6250000000000000000000000000000000000)
  | 8, 2 => ((51793915580585149993160995405223719423 : ℚ) / 156250000000000000000000000000000000000)
  | 9, 0 => ((20299337575559726821438385949046 : ℚ) / 28421709430404007434844970703125)
  | 9, 1 => ((212654852430631557745059951373391915079523 : ℚ) / 625000000000000000000000000000000000000000)
  | 9, 2 => ((5221592871991237527728573697865290814564683 : ℚ) / 15625000000000000000000000000000000000000000)
  | 10, 0 => ((66733112896690924246038029500924824 : ℚ) / 88817841970012523233890533447265625)
  | 10, 1 => ((21750479768839440452402604396723219587415810159 : ℚ) / 62500000000000000000000000000000000000000000000)
  | 10, 2 => ((524759774364972047696162439836157085284290331143 : ℚ) / 1562500000000000000000000000000000000000000000000)
  | 11, 0 => ((217507377805927707457936958792604440206 : ℚ) / 277555756156289135105907917022705078125)
  | 11, 1 => ((2227356182367935294001738729706481167011175511391147 : ℚ) / 6250000000000000000000000000000000000000000000000000)
  | 11, 2 => ((52636222056143942551085225705143835752303254495362803 : ℚ) / 156250000000000000000000000000000000000000000000000000)
  | 12, 0 => ((704090197253770825431129205268309734638864 : ℚ) / 867361737988403547205962240695953369140625)
  | 12, 1 => ((228276852919365076959740458207750737494153630048073902551 : ℚ) / 625000000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((5273496639321645883940422693176668302892678845258751283663 : ℚ) / 15625000000000000000000000000000000000000000000000000000000)
  | 13, 0 => ((2266570111956294714512860978847091236354164966 : ℚ) / 2710505431213761085018632002174854278564453125)
  | 13, 1 => ((23406763018324609198020898131346991439337542220875735108079283 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((1320622550376910591380381071247130782670686988701767632868831 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((7263269339481952329278033594368231908744142511304 : ℚ) / 8470329472543003390683225006796419620513916015625)
  | 14, 1 => ((2400554131656040133184723653259956001610252278225618248711486864639 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((84708817807742683146426977042101980701002310960249867101125956921 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((23187783099903887759924362695846568925803973390579326 : ℚ) / 26469779601696885595885078146238811314105987548828125)
  | 15, 1 => ((246194908005856864504095678689169936120045000026327122178173981491556987 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((4247178488375326789084096895034206404139651119937597275260406370626981 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((73794312766927606371163683897379778302788034593809406144 : ℚ) / 82718061255302767487140869206996285356581211090087890625)
  | 16, 1 => ((25244711417350045667831665688657436290138116490197792706998913784248005559271 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((852244084312793871395960318223650428948714406841963577500539028151093458771 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((234230269282929085322973249415016109060052637763143458899286 : ℚ) / 258493941422821148397315216271863391739316284656524658203125)
  | 17, 1 => ((2587784983570666796500430390045384528189835477029434514797016960397453464527223043 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((21387828250992598411719860603552383866721080489671425030355298543947102852892417 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((741820642397949569242474242965805337580445533648536075977627384 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625)
  | 18, 1 => ((265160275857421490335487733952487790678216720087698152151690503576067404505787503384719 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((8592398479550166141980205120785235676434403572397740249118322847377068825033719251469 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((2344974514860229210799381147268951391150488942148335250678383700846 : ℚ) / 2524354896707237777317531408904915934954260592348873615264892578125)
  | 19, 1 => ((27156778551478692705728870468635960685955170178200235899919371846064003097721626202651927627 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((431709462003058001575628534185475345120565478797163830261751038313106529632703660240516751 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((7400873793968101761754435091439674702129609234194966234392071669319024 : ℚ) / 7888609052210118054117285652827862296732064351090230047702789306640625)
  | 20, 1 => ((2779799460140096422777099019070604818112229780217445308144870106313935942664319674206348440454391 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((86804310753071641103162344669122131078797028147215155736457248716845226085675906832925315676391 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((23325751120996576620181926988672587607563625634318746590679375327374520006 : ℚ) / 24651903288156618919116517665087069677287701097156968899071216583251953125)
  | 21, 1 => ((284378782991912287806432116160876680251369689210712756362885676076804786353751923795197447498413074003 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((1091379435710771057264708977538330610724314256634261510758575037427640680960118963696667307271037891 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((73431390032981279111435965654226115993944304745158401353080135447931612865064 : ℚ) / 77037197775489434122239117703397092741524065928615527809597551822662353515625)
  | 22, 1 => ((29074901774469193397930381293111326214325352807176899959195618793681533802210816438775345925115600279962399 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((878590088924146766149106878644880964902291472851769626306387195435188506731518605834970556658499368951649 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((230937051796524808157623472401420029040593335369103597569721494322926970907452766 : ℚ) / 240741243048404481631997242823115914817262706026923524404992349445819854736328125)
  | 23, 1 => ((2970777095289293540413488391929471604517983764686680907765893240538832064553492716239850116262490326130403959067 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((44224575652589007563589756369314104281922948381002611676333101236433200913633728620403922736284072763913553721 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((725658788512403172923169102045646120377181937515523632700499636939041294920313289504 : ℚ) / 752316384526264005099991383822237233803945956334136013765601092018187046051025390625)
  | 24, 1 => ((303353944490038871719346774956858332925578503966489398152573806382504874890900421159050474719399159225882013598235911 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((8907957640468568495183373321460313466789602092888356012154407016120165460293105645754015827551022347881293024860411 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((2278506698082887413248693290293940118229959746376367978901492556196637221585048142755126 : ℚ) / 2350988701644575015937473074444491355637331113544175043017503412556834518909454345703125)
  | 25, 1 => ((30956856515710154945900193188457109436970180351899467496037954619531569603997649021325282073456184906988724593128698816163 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((224372532333889449060884403706355109467048700193827720634220983245828776828786776329165797328660998408005956647027331947 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((7149761124955068333093811124533686671856016982496279602098264645796731420166984364506656344 : ℚ) / 7346839692639296924804603357639035486366659729825547009429698164240107871592044830322265625)
  | 26, 1 => ((3157139352305438671516873625081856770788049539737909609324375606203320988245953829516810846438524314056887081411785912290069679 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((90456140005988440057658136966421236461511500835129973974595509370812252160967585156904241225733376423695997359870287925381429 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((22423017413964385349152741410808542468241374025716556323933639026602796527300400688204438443086 : ℚ) / 22958874039497802890014385492621985894895811655704834404467806763250337098725140094757080078125)
  | 27, 1 => ((321783735074327510196522323531688548472081915839564443892540404416116100335643336899833866545681140485758399206834425748056599427307 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((4559980038163884701191036786659296846234460915539174599518094215225832717443582472169871561142169202178576084611238087906526109091 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((70289487208605271737692144405992953244475995508139479412989494059212640619812196349699242638469584 : ℚ) / 71746481373430634031294954664443705921549411424077607513961896135157303433516062796115875244140625)
  | 28, 1 => ((32777278392049636236496979611843617495683771231390113155092445026376661025372639840944200886313503483005327807267258078674221682805111831 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((919780140485566002074575907520353436858201969323031194158699605618516974039184024137155556172985372906992073305278236853581836217938831 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((220246187157810571271490692233658984475879292824806753174586964177873035039276883370055286083119892646 : ℚ) / 224207754291970731347796733326386581004841910700242523481130925422366573229737696237862110137939453125)
  | 29, 1 => ((3336768853126501785021090952698688693026223756214525790693965057997104754145230443080494442468296418677261206168771484874404313520250090113523 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((1449843505681080790012220235183025477445018450908800141872864559646602149185828510475458226746931459859478765412852402569015026739288817307 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((689877731124627060214388665913831730677881612934948026415041111321117611003067350555752339576006406073224 : ℚ) / 700649232162408535461864791644958065640130970938257885878534141944895541342930300743319094181060791015625)
  | 30, 1 => ((339492692766243948248347636042987274613432022330090942763780132558054605832956053795225587196089388510736545145786980322486314755858020273947018559 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((9363411033613969175321337207013048433764596207301437889773215868030944683971478567627472837393237447981537998707436610625106533602651633305852809 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((2160241139185798842120439888027561450363053279771056385489181643311746374102569828262878163544672099265439806 : ℚ) / 2189528850507526673318327473890493955125409284182055893370419193577798566696657189822872169315814971923828125)
  | 31, 1 => ((34521759301630348984970729009442760650344119806404342747957253639652393463320227393920148867340579590531189822592216570296745349477946862931342688828347 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((472544959483123089598977399894160355834656470726695426802717957439624395231021195599962000669504098169991620885263024731114960713887938437106619430861 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((6762644370752242881092717009946480129318058037075417004853475080757224609263730182114851827420184316503805051264 : ℚ) / 6842277657836020854119773355907793609766904013068924666782559979930620520927053718196475529111921787261962890625)
  | 32, 1 => ((3508496045648196092325442595787872967731888167070829389560961897160957837345266798460212201281482345806237988496075643291389275531361900756014611440817050151 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((95413236336804976063712294277055054824196031735754859787392764016641586463451080031947930187111645732606947705653917368923494919821622332530632858706879651 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((21165594773156772860463725532543043677181162832114042250910318096430725644084466174758051183574921402202202867980566 : ℚ) / 21382117680737565169124291737211855030521575040840389583695499937283189127897042869363986028474755585193634033203125)
  | 33, 1 => ((356387289537363733307892747970010350791277324729786716404915493363488537247812965496684165703379315739893079378608913933116457835290938018867628969816309850710083 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((2408636585017606889175509538132752424995285781397668371003499063448496713733276039100174669069817735766863276780333534186254637473158851168952858859614751246677 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((66230391966592716866265332168292548900647341207099279051205527878732117812191862934128919495700962060176405015519627704 : ℚ) / 66819117752304891153513411678787046970379922002626217449048437304009966024678258966762456338983611203730106353759765625)
  | 34, 1 => ((36182967711712461091345501749858494931432740390907809323536579017824438493162952008376562742272006276418342854841490413604162774337858342286847384623682055209088761039 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((973043095382997808354602184168109983986329458526038998383678569101945711360892700651763203628028090306291471103281185197204607498565469858444848019805851780932317789 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((207208997564601382967701883307174981530834369075169184024541495847700674537369048458402089382438261990334068416824332570926 : ℚ) / 208809742975952784854729411496209521782437256258206929528276366575031143827119559271132676059323785011656582355499267578125)
  | 35, 1 => ((3671761970496165104433864702916017403738323705953260900972191133882919421066712902863069442635379413397797174496941967405546096297239725714997273162450633053467081199778187 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((49144215717726097326853047764950212630585114839303858545287629968893731089973971364009583211441613632093157382370326882382703349783532939149010037631626823115075793327031 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((648178020026387990940201561779669840626008175556217024751208532039360778460916983822475147510935091066450904461678062897066544 : ℚ) / 652530446799852452671029410925654755570116425806896654775863645546972324459748622722289612685386828161426819860935211181640625)
  | 36, 1 => ((372426621907120426260058222517921306274642187562402852185029367878487515499475432847008742166918524496388717248199779493179514073517992216772004079393525052652325454930446978871 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((9929650891867837865132180175107528588210375608871781350875274193520119545919939462578911635699576521157462038820474703209312777047775823366678389542637515850525361862680610871 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((2027323397852489043150845987314738127423583498214954132137536638707092720365891219838559508832499564843219298094842348756870026886 : ℚ) / 2039157646249538914596966909142671111156613830646552046174573892334288513936714446007155039641833838004458812065422534942626953125)
  | 37, 1 => ((37758101697228998890711834285423039154540759714910445464234156415000862889997692651688416246757333906501000729357494248912536742594137184787395507775018197703031955640760175220029843 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((125409059150556127290331697014549025677662041633306078189477332866796521290083316599917705940716908545943091710386945876213231670063180107146757204319055164879104884145278239848621 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((6340190323138230507653518804620697439594308746888960416028839120932306243333164291819948250610150855038523549218437895456636146071784 : ℚ) / 6372367644529809108115521591070847222364418220770475144295543413544651606052232643772359498880730743763933787704445421695709228515625)
  | 38, 1 => ((3826396967485883620202169995008750739641193510784594985523760422381981143606407542846331731440452270874987830083070427829231659925351681258201124797070491620343390415607739196485518689119 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((101379379379415677027174933686887818965707326471869548627167977550293466398521078714465669382438484869131401106453805422085186239962808682276123421008874326575642418557594067640672168369 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((19826158752291951248204819395738440310536879280423896279766404195714069227680080162830017249954576856817902648132937478955051627946524446 : ℚ) / 19913648889155653462861004972096397569888806939907734825923573167327036268913227011788623434002283574262293086576391942799091339111328125)
  | 39, 1 => ((387603187234197281012669715637169653624060033426580176243482615430541930784812649325034163381346512831254158308038146452494566518578727330685749822854273117692845494212971767519725309663412827 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((5122583337015304256681442745437107991803554503076473466556948158335096065997254229585148103992423084646158221623191870733759045161081114878160039680225434617204142620873920713510560069365601 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((61992267096479010749790471955683956617724630381075114324009823714081330955240908129520998016831421604838368293423472134055216460065799187424 : ℚ) / 62230152778611417071440640537801242405902521687211671331011166147896988340353834411839448231257136169569665895551224821247160434722900390625)
  | 40, 1 => ((39247219320825678973066099923727428990724202165389815717229272381028788038373657516866725092610497096700634849217365027395572853955398746251397069548221138853930612708226176888860369602660775985991 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((1035429011094885712995112148091742681445523132201933483053387353890663544780701690758229091727567821692944182844469294038763758015839770717334561006669056038547937508317834028445180390287316220491 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((193822416263442665559685193305851982460389693811151174407373244134633316133483685975374409589655032628400807743412218009922480691416405549199606 : ℚ) / 194469227433160678348252001680628882518445380272536472909409894212178088563605732536998275722678550529905205923597577566397376358509063720703125)
  | 41, 1 => ((3972475698759313138720673406111478532026110937144934260122347829864752355979037037728837410714847030322937479711323161779048443266254598739924776574288547364757294558000167479414827996376570973502776803 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((26162976278773803699952710848888319671695740375150422758133246559342154257458806660349880497527187549576927949382424229004943387644851910858463210837642416774920755339201667479317425098976571324604607 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((605957656158163843066174353280946866612288401863169851214868267852212290523766069577064319617679525231763309859318437260936559801515886558879197464 : ℚ) / 607716335728627119838287505251965257870141813351676477841905919413056526761267914178119611633370470405953768511242429894991801120340824127197265625)
  | 42, 1 => ((401930298303748770477060483382036073194563368356063360888031418490029715522498578701500232724923440042372600576077138476751406026832802315672574312659288566428892078550234139733423955319733260897630922434799 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((10577753291392721899785292732216807533561388712729450137950947547173096268192874642990541695970731666686086488589135392928897345731587625178673796140770484082011315314679307052440066134968378378648355036549 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((1894331699399870099951272793703192425014089740886739475457040623571866167799194716336354447363619040089981669523051257449853177355180070149234627748366 : ℚ) / 1899113549151959749494648453912391430844193166723988993255955998165801646128962231806623786354282720018605526597632593421849378501065075397491455078125)
  | 43, 1 => ((40652146415057264022219043531212140825175046668650867371851095190489738255772049110384298667640841122532029368150442705658571328014041449191802692387814992747023095843455235995430277008461582737398367899548788267 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((534593352909421719993035405461519935899573874633792331856276573145798959225577315723536657447051271991875972621452742923066319640496420393911227577517835302372278047354820288354033832279158156691821766758074571 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((5921727991623942460062337998367411124536052431160984165029611590747219578574369099832036999641518954332214003231815201935421636900167031347150483609525904 : ℚ) / 5934729841099874217170776418476223221388103646012465603924862494268130144153006974395699332357133500058142270617601854443279307815828360617160797119140625)
  | 44, 1 => ((4110222392638763794274187786513801577483103532005567814140057434009247764924513453961181055026339841935294281151999742731052199491687917997738944374296260307545496448656614907312428201931643878452860963792411428519511 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((108074236319759996774480164772729287134421072220526250185915407751415374439558397360616551150419181432779067675468006446052200121816389374430433544525056688367613572529448338061758239043575436355297357555231454156511 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((18510678724712048481080832243462337475497096640607776979909008087914550872669830414047962530962286237852895636658051886966382829704780472643469448564672026726 : ℚ) / 18546030753437106928658676307738197566837823893788955012265195294587906700478146794986560413616042187681694595680005795135247836924463626928627490997314453125)
  | 45, 1 => ((415433865766942964500178777636580962081002162635421103180063024097662424423241896663438748098110421231300824803252266495875506519085529763651226099011833557856548687385209205139962105372153025978309498374601103268670534963 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((682769878137594692441607982603135060848080068146968448626836941942507381655155667388572112435749034292844976715988781867271189342917501667807033576917672863370302205949045471375287943693903190437755074911925643552716193 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((57860223938387525233094205450915803808012762266690861343352262280642353943183396494560953649614569408920791241919325433486505535758630337650616191992252908636744 : ℚ) / 57956346104490959152058363461681867396368199668090484413328735295587208438994208734333001292550131836505295611500018109797649490388948834151960909366607666015625)
  | 46, 1 => ((41975764231129537870131041493444202454042309216016222859202132106853266189084082553633951844018820270064292077882563915079658603536514562282565774356324959381134018905372202054554674220883390572050142832125716500685684880670079 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((1104244855924639630171026225686428233189495030271410116872473351635626546804426977087480201856474751892227477977281161548798166503567240583503111974532592027630683037333936808577418004925496219934074339737096989889695385594329 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((180852225406899010524518840186482908716912189668377188664386267671074966997747303814850431498077367748476781405047653206227654244825629114737721555229778370985650686 : ℚ) / 181113581576534247350182385817755835613650623962782763791652297798710026371856902294790629039219161989079048785937556593117654657465465106724877841770648956298828125)
  | 47, 1 => ((4239949122110210591333393864847305602982666213632915350113629203319184384089394713612591650001523148380270531382217721576904654754325002259402362508633437142502112569524394676703874263711856122983839343047523732847148179685965280507 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((55808582973802043713859309797149676769383406252128591096025364961893775344758745291621558384924426080730856011694755274808836059477676371404497599688839522967184380000035827375235848046331269377262195786910828602252666239710141941 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((565269315001431314040340775109055898060426397037207378077877094703929105973848821404263318633195342675674462447415217044538759682611864396302165312428650866967308433984 : ℚ) / 565979942426669522969319955680486986292658199883696136848913430620968832412052819671220715747559881215872027456054864353492670804579578458515243255533277988433837890625)
  | 48, 1 => ((428147053212506588760956412222540256186038811832616297090174806076100486887824389888624282885534837235303017063475300493387360631767327736827702893297125102777577257715598571065060857921279524449779326541188780615635841949582378991587431 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((11282026752554277740440017514554090560331301410210916540215998951662388205150420026593927316637575269226700603995141891462193628593311892527101250987275795855950736166277541549606362403762063165744459710339430251577497981961166417426931 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((1766755124114119569201230469527800703261118602696947492554406673332096585102188390184707573957167448508802906541680250071618911923680968147702776246240012570588249815596246 : ℚ) / 1768687320083342259279124861501521832164556874636550427652854470690527601287665061472564736711124628799600085800171451104664596264311182682860135173541493713855743408203125)
  | 49, 1 => ((43221546868516333462752635904077316916072588727539188141482707238005902711939536235699676155175276436654846465317873593249121633044989683524065621022088121297690073362882982793673430630021228983626549968390519081601112965248063050703115368323 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((285082168790128923649937024331795039845970977994252788714784051561463926350261076366241536990308487432388701765623179915596615503109188819468272335768160923181128687868280734410900772398966559008714475309476844044206066191340639720708493737 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((5521894234420128065925470340415707976025791571835439705882490659890324821015642247870081176694254891788072737721698209093225647603798892562845063493984440627254883072336661624 : ℚ) / 5527147875260444560247265192192255725514240233239220086415170220907898754023953317101764802222264464998750268125535784702076863325972445883937922417317167855799198150634765625)
  | 50, 1 => ((4362015800466224848321348752375769162132802901907136281309364048707879393577038639003222099705574961813167413690211554999032007087264196147896802563158688683154202375517745120837326825486727532687771080195457211291610170290218403060622896097906959 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((115254073905180355071088801210802534411700856944734569955323977697379909876488245120219883159983382471509006738215983081178871388110603404318219720465221947677756383127124851240624727290966963169354463626098492895888408503263717811809875572353709 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((17258052460744068702711743523620365811372908818515683915379051213930400082475256318702067229133918423561262382724264959113523742345074001907254524141574464214960501522841097799406 : ℚ) / 17272337110188889250772703725600799142232000728872562770047406940337183606324854115943015006944576453121094587892299327193990197893663893387306007554116149549372494220733642578125)
  | 51, 1 => ((440106820260150374151392755639251764757076069942831354819736196820333668061396872722458326926439241881263965819136972347616974280095738657259737678747962873214893359744903176066957847635481314376479994342587433770419175430777242641727329420951092985547 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((5824151249301741466373521402507513511361414528585712537111888866029340832161002805217399746358467725176506190088043851144680318634486883324068550369649515193523046307445836951383837273241669126786060425120958932683538023408093847087756882899431615711 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((53937213507499811838486948353317699092869131373466405050554887468453654368418112701623784888834622233630236821311549950670431075781083751901071290207912124917522836294222803803303664 : ℚ) / 53976053469340278908664699142502497319475002277726758656398146688553698769765169112321921896701801416003420587163435397481219368417699666835331273606612967341789044439792633056640625)
  | 52, 1 => ((44393262826315312962740818871874579451697373002218977020107402051913447686286638352090615051405125723609470103730157707904285454286822936854649693772002670246620342412399156844717466718373841562691318670445303943117012966999264026950702272094229489257957751 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((1177188888257338547243819765399154417674970349228766802843401538747934096427828339837791781459200361051963646491731756951537849269812202407571383817231938469128324768172094130542082031318125847574297773790374563969015713445229691091400553857792622654799751 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((168569561235444141625763880424526837745218019129212219346956386582278287928253507095317771402802269228138002675534459087250277158626352786154157335159597932391510943926547612562178756166 : ℚ) / 168675167091688371589577184820320304123359382117896120801244208401730308655516153476006005927193129425010689334885735617128810526305311458860410230020665522943090763874351978302001953125)
  | 53, 1 => ((4476804442040133361512000858497899383354448937049965706573284366924008394865118469819917284656563982715799027305314586000511976825055356082618930879188937663320909629881480129692958708866899834853949201452078333795600908040921474149058754276776456137653995420883 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((14870107837148006026844817311634723305664044175926395532638626256525032818832110145229910156082352598884140762664054423654424947806520778065045460610689224527482586417935180968930616581806562809177061118508673675493071976923132051795288440638520452634959513751 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((526822754838398099945820327911338515303331703152193849449679563728317170191060844103427458850659780577861569144741802918787800667985009677850480347687336980487413106669269861747176830984104 : ℚ) / 527109897161526161217428702563500950385498069118425377503888151255407214548487979612518768522478529453158404171517923803527532894704098308938781968814579759197158637107349932193756103515625)
  | 54, 1 => ((451351705380487196625077505748624117342096368695371850418740136593364855765546658752044542750491392765941195545797994788736446872302843029378468111862714372899728736532751584565386441472937229244255553163198769841926010811747328859363335184957155965526942040367297439 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((12020817248311078990435725953189967886475631469195885413914682411816403407046879920768164750901409836531247192737361346128918998188107972091013985105386620320885493699090583621824760603023213991002187463960217459086307462088978131730800841001189368453652564692466689 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((1646437688653184055206961524831710808966271116932895779920257323186989714856180554839901880635070226349187918598189239200416208371501105227504601544700588632179322643699328826561238781473122526 : ℚ) / 1647218428629769253804464695510940469954681465995079304699650472673147545464024936289121151632745404541120013035993511886023540295950307215433693652545561747491120740960468538105487823486328125)
  | 55, 1 => ((45494784278679879322922596355186365289045344018670160882345908337747778183269797733513556692576344349512061640761124604252012754591298441824123203508678425810479182263572776708981089920838342815954938756284475482196930437665580034089738962539441198843715961572905501119387 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((607300360293721423729149948471631703511260105111361471371175353257185293331803044458821115140155671920947750289553671693569758993985804569225478672364795043936694727807831891343058378346651010048081209160424896288953258561219105922532914587696456425481331793430143103881 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((5145434757471693763152341052394863520380891842134545823311237753650722938152349052743076401009650579687136675961089907211657227922267329843051091222974398560376973289048425305890836303160869366944 : ℚ) / 5147557589468028918138952173471688968608379581234622827186407727103586079575077925903503598852329389191000040737479724643823563424844710048230292664204880460909752315501464181579649448394775390625)
  | 56, 1 => ((4584702781886684889688776242747917167772440346418489812801061700397945566165446154427821547284187696246604390155749106636249537894940569076917236685239995537909700488384740751615455725124495451841900660430566014733788170831527715052764820297659717470373885575809527948573358471 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((122715842658655770821156592905649537451671055139609767521279403327452805288245019469141740605683324926727118010392259943338554357603197595554212223873865418697271434569040416386383413862621182771640964730840827403213840915541005037757519655891124610434547256553844683488002971 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((16080345486889555082775629903891139633170647028745086961420936989380371617143718712325247195479285658180870638477620225913888369471131822122837415856934571152794349813016262864438521584342682617314486 : ℚ) / 16086117467087590369184225542099028026901186191358196334957524147198706498672118518448448746413529341221875127304624139511948635702639718900719664575640251440342975985942075567436404526233673095703125)
  | 57, 1 => ((461920421656040113992696892755014553168203690228246381463579606219367723240333220071530479280106867644750610588660395234736648402311395145242638284581761264401742579712118296652480586775270091975758493875687509785981200780651080251527571762723145325194412572385558123794850412516643 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((3099369805811365300876481947108452019970000155824755284745943422993461359960781390583303534309031793059555298887647307700559161778393297944507590666930797688894202592677304064255169656920628111353954806520831250670654947458342429667946148096961033506711018150206857862573569922067 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((50253423070490261959955733278772214041512870864849319160096282477887905265474651297302417315552070617129868567706326794901713622687279150225687117532715041049227085391883701408787520425478625313333556184 : ℚ) / 50269117084648719903700704819059462584066206847994363546742262959995957808350370370151402332542279191318359772826950435974839486570749121564748951798875785751071799956068986148238764144480228424072265625)
  | 58, 1 => ((46529966949243071621487545299869726029838068894909240320371493835232452109140645000477002392758905948024885141291334237835551729239167537216772493910354627911769816466256983134059292142290950500035195973913440543460778977620187225144622525430053726305598450531048453203886145809191433519 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((1252362547933763117814711820781046864135209967325501094696463146102746335725585727957417024169096623355942111253150263230792165485988500601918762241857079639685203789667805820590905843318157448851332052705891664199931982584226769361811294665885657886569842052944027549045039922712525269 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((157048318865030402550022124941519791788004375861811010396279150819135573287015827247646742027998245359651366703361244432343544171634436152818931347001795765627783595962695792506678206279535354967127279108046 : ℚ) / 157090990889527249699064702559560820575206896399982386083569571749987368151094907406723132289194622472869874290084220112421373395533591004889840474371486830472099374862715581713246137951500713825225830078125)
  | 59, 1 => ((4686094025077951272193322975790996155122409490364036391232593035471782979272382564759707316557726261738211478061267637359557187605746726258136578733954270503793759279124457163083997473441368435397779993228059238994743710474805160125518571352411439935464812899124723953402962498942806714418027 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((63249794881600464128294560654936600715458497884313580822370993785217864225493327972634826645178888017908348355595960134307836799371137413515943454764206978916425237934959607290745687977370358535134806263529628390942792024851440964721187349883773753912858227214310459678079042266893462974451 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((490793321295165727911330426955174007025117897906656986017412257207724495236740566693481083283540245856877235028213416977185174201260669847499949565092706339913615943616832386001235974882365919968660758906495824 : ℚ) / 490909346529772655309577195498627564297521551249944956511154911718710525472171585646009788403733195227718357156513187851316791861042471890280751482410896345225310546445986192853894181098439730703830718994140625)
  | 60, 1 => ((471850984588730107995746919545360739843826097139863169862553216358715725670276227501974769529245823183563672238181730592689031935809016509117453452877717241633960047153238859433985894782524122621508568695262506581692671454625330462881364668790875947578738078709682530657252217342601965469167677591 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((12776418131642920855118535511259985930997706798343029824533664354779076695842476036315586505732576498031621578122554006205033083728114240716522861650488141272596764869729169032428514780663618299244167546150206637202709546036563541231062583896987239218476863270550055616084226315383337680842924591 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((1533776235292643312246595772263560916206089314215677997324872821505599375890399264611855039539861605747302855047256635028601106148811004902806347969345892454386597832551237651836041653231119467060543875378383239206 : ℚ) / 1534091707905539547842428735933211138429754847656077989097359099120970392100536205143780588761666235086619866114103712035364974565757724657127348382534051078829095457643706852668419315932624158449470996856689453125)
  | 61, 1 => ((47502576152587400080281618563885966066488879133852415471886366796606418403258650145215259807909591552330385651095730681836839795006729417407229266095799644171272124034651821202498714101148937249570651805867666282929598155098099584569244750372120130247339239101821937530374824493316969252012990461759603 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((40321699289437425740660299508199970740624625134073432458314093715609827833468981023089616076399686152936947744794380771775657949210866731013195308241028180161708027618185865713549473098857322629095947442452055406073619500823887100108467399863191190753699440509422432695299993624167165797827634619179 : ℚ) / 78125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((4793178817170346222422519971573505853366837313500796138299856995916838682238813299768008771546120197472084128515816897729124587292314758541524163571960306321481772262510160157525575497404059239268104021877639945369864 : ℚ) / 4794036587204811087007589799791284807592983898925243715929247184753032475314175641074314339880206984645687081606574100110515545517992889553522963695418909621340923305136583914588810362289450495154596865177154541015625)
  | 62, 1 => ((4781350600636047411063050710344639337889413892565593602590315583669449699715565289611082095386523723902442089291872071375236590871034457641824470498404141094669289897078485771142857129365459083406310947316737716793297105437045159744003303897838613411315484728291202630139096692290657000537332519061379147199 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((130294790714045871507596488879697963496339902288242258435539612511353289226428866896006487501062552627686641462128617233028659452632730529947748846990037275820943861639223329959786022172974667982249425005554777121955450714654874882419140758492181886156321723625777355909013170453635539191989754050985361449 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((14979032058291324680091913261423624047187182118372313648704585528907615561984888672345387471825264852692745700566775229570359064328108941633134524012500150194373353643650578537635096784531153972602741162747227755113003966 : ℚ) / 14981364335015034646898718124347765023728074684141386612278897452353226485356798878357232312125646827017772130020544062845361079743727779854759261548184092566690385328551824733090032382154532797358115203678607940673828125)
  | 63, 1 => ((481180187141703678601943022081619847653786148447042154423205051290475413423219534431214707959591907968138314980025909229578566766692650979884473427502800902093183435044331538438874227695429762419852059977707103244207128310189986717475145033725028628445820307650170157452062215057678419948365115856650893587537467 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((6577984740262866951249809691251514070211953142329533713157606374309417586287219354914577551229315967575058529295085112234238056970677998564702368446433471972811739356239229452658451681512938733042249376148120390080665585491926685559823316499433758057498495009251208697845829871066192353210097632262417994555421 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((46810422086510215871810791716296026383935546501615723775413000418755216666091772644720144854615907746240791044629402738717022894284081690921525030978550649960577445000477963885464381304294947967234247994203227090065832002304 : ℚ) / 46816763546921983271558494138586765699150233387941833163371554538603832766739996494866350975392646334430537906314200196391753374199149312046122692338075289270907454151724452290906351194232914991744110011495649814605712890625)
  | 64, 1 => ((48416242930262358097984918158180323072534916801548150300490181639890958003217235391410574630784580310892660012398508403693393972508477369250776188278795409470157479725435260547255921493922972828341579545969915732156046133492695120134644996858558531582257473148374080872537489856359957685963994061592143909316950163111 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((1328236266913243897726236498864383478006275273246343676539043227665608893588479132017810834168907660610930693105784569697130544499342776050227370154716727960748913378028132605993584322723029721147172261296759067966567546568339610264441833574213278891722083333096813346541626944098101081231911925894696588401444812611 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((146285143653271602163706291296875122611775745693397537209676799281268590218399968397909812355710067573807509240310911326306637119483272738306352372319937784686798499341899711434685631351236527009558028960905808282618916647858326 : ℚ) / 146302386084131197723620294183083642809844479337318228635536107933136977396062489046457346798102019795095430957231875613724229294372341600144133413556485278971585794224138913409082347481977859349200343785923905670642852783203125)
  | 65, 1 => ((4870830522414535912215539579534454694194208045751146208142140768029850555196313999358085460498624976196754883502481769289276115564036345598024877076704941049957609452886598876016938304570159059195944489392491666938691043280430546726404271939229846459345641860601317352540719926438425012674593869147816977624989305993133763 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((33521521150172796101743614339605929724696226056794175250006623286316425104729712385082800907586350707782369725853257546274515067454086241591582411506943901135590103340154003016835996571662073047022298697450158684098769706696137507529160521873523923398303095166205123918127357539721106216892496712587577840921197534617597 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((457148074343402752558907245474535417362215111151299104499138877066622909626630884626778462595205093769991362593041509395399783421390189265113490266241843859825868952165625714234997664721695127834763620321787998422721832595507257144 : ℚ) / 457194956512909992886313419322136383780763997929119464486050337291053054362695278270179208744068811859673221741349611292888216544913567500450416917364016496786205606950434104403382335881180810466251074331012205220758914947509765625)
  | 66, 1 => ((489943300478678899065592359051496883587938042353204961108136524419257642713161059974845582119622993738636672901781965665934468860829210123910707067723886733772261772997207917604494589420735467100634501061003300777778248527301205361787903057035486254660773059651374713060896080892471529971471385502282655605755564435600338310479 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((13534658767883090713766863521925002412781631014243623580703392024996621309603922403183654208722959445262684876947426967726737469513580597516058895384636436181957125062927910688404065736399357214431897792410803964917399450705152797077463730988815398051241010651032456378991365702203146581208782253459823049431707186707142847229 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((1428606766483953541319512048690049171622853070379604767714495043684315231346063658277903398546454587575633842917467806231004627039994833017026449302361364152561737157360212563392731878746048461632020219833332523031008782295873197018286 : ℚ) / 1428734239102843727769729435381676199314887493528498326518907304034540794883422744594310027325215037061478817941717535290275676702854898438907552866762551552456892521720106576260569799628690032707034607284413141314871609210968017578125)
  | 67, 1 => ((49274439713844686952741078023409567474940513653346465283059788597637787996216956302259795785396961459177094980842202540864442276285876904358304307833618827034299544880816203505538120773549216023871296903034435400572480188384541889809283776260636190707230780674327676586439864632403064655203302854898449903867266613470709078247453707 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((683023376892341003384032138092890051304720037292561425456177497787296263044078234654835760852562256078827630212962344482456663808783102226022328008580802806010624599472991955661570594079414049496298127454945626114545967919034043849419515905406846606652310065976708696048391930551159132976251063583371316265438819053225895697334791 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((4464447899145624232322263411153204234564381820734715683982388389215676676752616721162909211741847328665108818976932284469953505663105039739491382117026145061112861694680781229826629316959753920456519028284302865495150752402132237829438384 : ℚ) / 4464794497196386649280404485567738122859023417276557270371585325107939984010696076857218835391296990817121306067867297782111489696421557621586102708632973601427789130375333050814280623839656352209483147763791066608973778784275054931640625)
  | 68, 1 => ((4954875438173251581564900333918869186879222767414871527388822354196963995413381068042228954223208656295231189252630874555994151319357565030079047816880815715862440675065629026373478385748204669200485797174044956054478823326492760994201856555115951796702319150457113743655393941313035905880431574179473020472639280399813600434835848623031 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((137859906860614094529840203721435510648449481936975911794086325395245909520868729630237146813162265654150090260618577977780886315881898354028212198030740592201027690031893219407278264874657826523831305905002959012781343672578734464762982743503563711741555081217507595277752068362933970559780644939759843632607175840492360525817557475031 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((13951540403638685267292078436066063991661317677991974196518977672271248517598707472045980993894949464912182129061833004373340846714729755446041025675899075703345553334769429382529203046092471388718325395897118664324558249967813226960489059846 : ℚ) / 13952482803738708279001264017399181633934448178989241469911204140962312450033425240178808860597803096303504081462085305569098405301317367567456570964478042504461841032422915783794626949498926100654634836761847083153043058700859546661376953125)
  | 69, 1 => ((498173920530515144429079140398607471418406603091094527236298542927459559231596110899491563168547588227616088923938170250962058820102889077982769661343643279344450955974960715960155858270525528448449421971814522147037893100321310302141307445638852220402264987672487365167325385019748545367946807450539985154662329193715366391321373267725103123 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((1738898255086751886013061084642104815345048876046725062401146958715975462681297622211059700609930147831893972184880326382792600880280196776963655057620172524462777390300448839955840349233496081236227618989107561584891852684171433953054229906457637558927259227214046463537158623946161380906824434547859868552785844306674866665846961397265281 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((43598946375811500803041674458727695736704508727129809877119049172136223574064456264005618719803075652195445865992730572952167714769685056290172916624347672094208066976401782299317521623821993702790908495169575564058609363495033140050088796690024 : ℚ) / 43601508761683463371878950054372442606045150559341379593472512940507226406354453875558777689368134675948450254569016579903432516566616773648301784263993882826443253226321611824358209217184144064545733864880772134853259558440186083316802978515625)
  | 70, 1 => ((50080468572420429761561265456100625403811320759907578789234954709749420930958342059587900449505502104945569752798939707986110985648460209807510281955483550677078375235087813821417052584153516434882436556060722225417354632652054988705857690235008106405804043924073018688353668494075656533951150426722832964351791725784896665307081730668698184635359 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((1403601328438994184490245622361709332469039037551565259645671306521074320880751034444801969200808727634397873190322115819109574411680045948545897254031165547849729236907293360646098265825974448901682018739727469083808422520106570113900412226706937997957002872576300450843898072956061955067945847043188239792089403752927465956504183539838804694609 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((136247747753074956812453166575355816406153890356158553170836534952884325818861164855308141041028025376754488112989255159297737618184820078154190684712782836851687694918723020472533774237348763368094048147507669445425782240069710657622813447477519006 : ℚ) / 136254714880260823037121718919913883143891095497941811229601602939085082519857668361121180279275420862338907045528176812198226614270677417650943075824980883832635166332255036951119403803700450201705418327752412921416436120125581510365009307861328125)
  | 71, 1 => ((5033809763442373221445734754347042301147600207489624157350486434052641760821614762807044647012452816377811957465035160855605873165650962449381350710545107539926030416316805443606587768806607648674773485091480297747822000473927798425514367477543780144703509614768188643132537458367146680234158224931487775546582889748259717300500928013884102604563862747 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((70802169489449700593208443801313369145273493687654678545154431965992702404758543719476514285649075664154447010822302593674576143036295348462690171001653510489691120334329495444223394022746644886396226959620426177370790104895778221233142027794891288140810620971366141100011036639615323221173271278561101758840776787872784263505579978392108449522160561 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((425777040381996701726131577799877501364752212650559481430722789330161025404545720596198034683941021869505049439702224563883028589238420824067527360518998772235788720014903437666973810095653670379740116754140832868207774975520529371284623542683073396064 : ℚ) / 425795984000815071991005371624730884824659673431068160092505009184640882874555213628503688372735690194809084517275552538119458169595866930159197111953065261976984894788296990472248136886563906880329432274226290379426362875392442219890654087066650390625)
  | 72, 1 => ((505903907952587231954071696208690389036052351451981732888656555269295133171890048946918078362690906535317726500810257844447551733339756888973239468035661223962937868925606860652932353665336666998526751839179286452219056699012303751442659406295178100828308429589873330647627223630748074196831408398306026758840959543145651893818886425175115422265640372625351 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((14284411104874440838559869703098027858097064555948807598128585874566040032120154812772460028546405052584006839539145881322181025086407473879716522099649083955219866442032726534570498504165878835840707249304253331551138468083174171897828558644265592534388151415267818391817162134913134227326220312575505264839332513753990354543509415793246820355093946479851 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((1330560942302979951221699940917507665449573093609884903007692297917672026522029231034234953784966328682276717740564222919674454750995188194284240920704102158071765397004571025148234533226027275955927126957844798462704043485849650901798496971904336622491766 : ℚ) / 1330612450002547099971891786327284015077061479472088000289078153702002758982985042589074026164799031858778389116486101681623306779987084156747490974853328943678077796213428095225775427770512209001029475856957157435707383985601381937158294022083282470703125)
  | 73, 1 => ((50837457488423921211004259310064416034096099203364124668789518951793489858045988337529671252964631404949203210762434878371891956772749056471062066347371016035179892880740494919073983227879949043913060143426983206147845331275655064137049768163156967574818269504634621317223040754737801819145422266422330302494647713518671099968389767148818278542854541124150211683 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((360197745451223589842040797865298920073536847952950366969125066463557741549658258525834337199877515004180060265359527957390930918863412925364004825613774106975957316114220028833002362843666657090144744447692722066919854048265712998616150583990551982824677331749015150615612165405680189842314282751503938320093859012860148643965031778710807365830155714991828327 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((4158023856822836609960390204603580652478676202190944779395281088441163360260489406473248893964231854621774421517887479401333905020630672867898332399184905318930429699718080424039714519516396120178583825396304612938989492136179361868476380639573703959660580504 : ℚ) / 4158163906257959687412161832272762547115817123350275000903369230318758621821828258090856331764996974558682465989019067755072833687459637989835909296416652948993993113166962797580548211782850653128217112052991116986585574955004318553619668819010257720947265625)
  | 74, 1 => ((5107940504380842856525222903163800210249800963677238111082119828563749339431103927807984782542932736600315241488498163156628949226432177573130810163075990065409420463722481117293332569332667090715773606521899520762013864168964865234476193850891603391435425179296667623671585303687366126360644315206783339568603225792601499558667949665388162058237349437472194186473839 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((145308965864783465601640734046572933523634359577049881089315818606774427023218956896584272595188087033748113472434609195814894673330937014552178841699747112033402411831041446372170166133778265352854480392065678839722777993201559151881321314506641239981136027214973908065464797572048167912223574601877146055087820335559369925138479298394375162314728920475603623255589 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((12993881412642024375571638670219877388218542345837390505542537186980939177007932968985651413385335184387429733298677798000786458228203412551688944967728918659463399557479247568781686352548918415935625568746066636077666172550003438253156864499519065701021708234126 : ℚ) / 12994262207056124023163005725852382959736928510469609377823028844746120693193213306533926036765615545495882706215684586734602605273311368718237216551302040465606228478646758742439213161821408291025678475165597240583079921734388495480061465059407055377960205078125)
  | 75, 1 => ((513163387096275594526781834328436519026524465971026184128848549574802179560681202962174833047701754146783848324386824630143770698706329855642159188170586853476084176789360200410010446225594873054367940818175485624241399116656996646691148919016746166490454495462543662439568607302718584099143970257104165629035937219354922121540227287445465986087711579528859003533307580587 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((7326669772086265413066131191236624966376314070783910184445533741419588480710748990053038815417428419958805088415852226521086881835862938944295985158491521560649956538521849784365055060952424001603842100867174630301550092855143381881219956906343423253320942877453971680037690941224434115646213510525491272314334437050218612191277512558748202610251764770441838462390440731 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((40606034017038450630583465869023914100219409613582526191966308322368098623721014345124760163921566277820749823562672874978387037663449494427646551287083558264117112159116658188947725736280000939085391382337787663171904771387621077775238469388311604124529867950307344 : ℚ) / 40607069397050387572384392893288696749177901595217529305696965139831627166228791582918518864892548579674633456924014333545633141479098027244491301722818876455019463995771121070122541130691900909455245234892491376822124755419964048375192078310647048056125640869140625)
  | 76, 1 => ((51548361676724421375232319715306995455829616306320702404752784259390046227913142445224902469477032489973354043233423661306539626294175436195712025555197564380771510921023384933964559763987697484488794315861137907219311635738646448543620482782436387522233051767900648713340877729254823701207250695504201176335058966960454228235461962001851684167900699798652744816690277680698071 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((1477520835992085955494724686052953230744002641438623982906352212871734984850736729547748163142462601643115035977168765008456798775546381970258667905908723206491808974743021176901926900724256615177625014542744716651370621812362362063112293920385749375981614385672751477517865965244931064029539865567757111429972382285491773733749539699488809158063088191391929360152432346355071 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((126894276667530004618944507212551233318662802786989205614069360175290500787386327387059141544849113432742519953778057366485761410847432974410034441449044658760872330342921268770218617976006234322612008733942796155154191724103447114111201382060941953125383721149756762086 : ℚ) / 126897091865782461163701227791527177341180942485054779080303016061973834894464973696620371452789214311483229552887544792330103567122181335139035317883808988921935824986784753344132941033412190342047641359039035552569139860687387651172475244720772025175392627716064453125)
  | 77, 1 => ((5177557510482183675204031633006598980530433528381656455874378114599254720326458842562201884844517578004372366607103970552092937206134269856275717804851727902370042422760986367823792982292163846760554094768385262531766934280605748070775272959500957187941031527810671143236769622356992952528522647479236509267386731941816264002869744535121991398344272393606219089914689529044472683443 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((9310296367730821510372824838631620358965019801018866989106188846187126389276574066494806611293265247660614267728289092333848425567362250977614009550449569864957151828634705606102515638364612995780093717332171926524041937921368247516211992639044795487959058250858746392446519843633626550768305821465591489650990964347781227738810438619912207911828979326583928775794514410269891723 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((396545757556521761791372813594286837393963623426755890371257614837776248608056203486241676670277160434089102952794881165160807324345775879487331985360778876673117811147037539643942396336326300402053394139360311180207318081276352089644381507180334612769127744658910804080584 : ℚ) / 396553412080570191136566336848522429191190445265796184625946925193668234045203042801938660789966294723385092352773577476031573647256816672309485368386903090381049453083702354200415440729413094818898879246996986101778562064648086409913985139752412578673101961612701416015625)
  | 78, 1 => ((519980781503652337899044457980979332655140546401498935596221257857728152944367746742231666015208739573314209310718017475104403930476219796010457891086957884594189790962916259880712521962818539684095030932213678268243493850695320200138733369380281512385537437449520493966913711035289440309227110887002133060386963120455774544903998506486957607684298378741429557247731480067481209465617919 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((15017109622330672387494076582707570493810419007092038284369150067717727768505632331316725755016382949009013341105072979424497426967052319229796514741447079480311579006194018612170796319719925241069376826181822951268005563880490047298275297722493965017133358084253769552573859169660796494803648940813065376254365741691274377533406384026093572642316219417561015790377764408921557584322169 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((1239208600100894167912188612923366017125810412875262516877583906372542922987657252656678215147209914877982618423875354343341054015682432185283706727761040420368913406460778226097248044574612927289656123639201462456305794061237524414168151284762809319060537734142335251197451646 : ℚ) / 1239229412751781847301769802651632591222470141455613076956084141230213231391259508756058314968644671010578413602417429612598667647677552100967141776209072157440779540886569856876298252279415921309058997646865581568058006452025270030981203561726289308353443630039691925048828125)
  | 79, 1 => ((52215967995646024295683966512806258706617243941832955832538086403712777843859598812686250559348264247572307777146958020953660246263520711264802031829566887056974566751259347395783646946914060729860822540782341575658581559644058568483949564254122710641399642340358469092982563759137185062184350970890761779584412601879439419285662590818925289025409819122277297817408737060086290155429356943227 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((756854432315767118795489069687030062608380973310406130325667692391724964212648284511897798919620812833146355400251933480288788030989062301823345855508211381265414563415735661083462184465743809012749306635614373899591827416302349729147561699566892444915391848854430292217524498602481260149656586366370302006860441597057936353592926015896815291218306275950100562262152146294622233415197343301 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((3872535325251554672557759378415195032601401390038817692634320802766410779548291430528467742862533494983529575417098564882259384933597619264779058153923152198904032045766803358650194523623815413352052953219616202535327004672027088514701571989330951997717100212929124469575695244224 : ℚ) / 3872591914849318272818030633286351847570219192048790865487762941344416348097685964862682234277014596908057542507554467539370836398992350315522318050653350492002436065270530802738432038373174754090809367646454942400181270162578968846816261130394654088604511343874037265777587890625)
  | 80, 1 => ((5242933987893747748409751084026913642109491230237032942374002752376940844957753160356934387579875760993346786432114989265418161856618647979129243817957355077447601395364613540199233317594768842536207461236047351751369381842919535469520520610385028896778380666985761200078798595144919494878947689057029873158204445925816845232030969439433355428020066270162060904118584946743548555522426682031529191 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((152563865912681610232638303518767757234500644870015175958382678726427494802087513223108142714833642125920215250642538687853712936309080070847080854443137250646560331285326355057046111524209792035725399975470009479014721668933272055637717772693268070319915663912389925665519725843304341160471543570437556875749123732739790306651884555251362073774214299131976210837887423027788926497267036311788691 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((12101695866787800373448668187025174143756719371487354397660750016907703946919464901341152779959696499204888277817158111735847827212442821009036320249082311128573052174939773838081682317312663059065100583068597161308027721389248715023280976257931088041766227084567148562682016052638806 : ℚ) / 12101849733904119602556345729019849523656934975152471454649259191701301087805268640195881982115670615337679820336107711060533863746851094736007243908291720287507612703970408758557600119916171106533779273895171695000566469258059277646300816032483294026889097949606366455554962158203125)
  | 81, 1 => ((526382871254120250424755097796292987258605833401173859803039827004165214669093529999868894205517417126984966309628624197343777202657225472996404310953372908728578437900185910602221072640674506345041650344755856519761728826714247424767491898027805788994761581480242870713547390673611219168017694272103536997863182818169937139835394582352017646578859090720816635323283811786533146596794649486008618022403 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((3843745022623631936287278803012391614870890855251477459985416510683174629656478311170622607379803523335796215423259036279276136680541503429992029977058668935248142839232711560699444209092152424757228752970123152106970069530813246873073429025412558296127586745995150412600639859150651481553532140581707809132465977635096690983286091384115649893716400185730555375335492112643986289338308986360131122257 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((37817862053761101774044805166503507403479235570986020017827178527802775273322964134666122493449377051165189234441312636500346990871853574786388695784021242395318219621473231021718479869459096326850722870564955389766757360976139322872699105754502845760479345210478261722887716283355382264 : ℚ) / 37818280418450373757988580403187029761427921797351473295778934974066565899391464500612131194111470672930249438550336597064168324208909671050022637213411625898461289699907527370492500374738034707918060230922411546876770216431435242644690050101510293834028431092519895173609256744384765625)
  | 82, 1 => ((52842901178641017710931966185172434227437766214225871496616751434798535443845079773808036998082660377984755473327316591632787826347594047356825074111940886689496619907488011426764294278861161455230188597467627982211736109960803266396246419474970038284149512731602720264302995207251244050832905223974176551798706028795834232631467209871630341608994583217367814040612877176513662173587202587432766102274099599 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((1549284703675768610228981780257046113487392232174301151439939952875945215253977317475521993529726985712171129784989740318971996245588656607786579699823010573361169560473168548905956645730572088804044959517011974771440399727836831336438563976790406965079740939669160574884895066255219916515464008090439542408009567613575478640759499745493317528034759257280486321250744816900931680701349585864602075883926349 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((118180988774067287469371188891416970713199777767235686586558346016566771723318074069405712324498113295327830800497365717052495807809387196290500054545398878187645522768948171260472501917202925004121847938820612792807781972365285527404613028887706416919358882650853471065017058812663499219566 : ℚ) / 118182126307657417993714313759959468004462255616723354049309171793958018435598326564412909981598345852907029495469801865825526013152842722031320741291911330932691530312211023032789063671056358462243938221632536083989906926348235133264656406567219668231338847164124672417528927326202392578125)
  | 83, 1 => ((5304327163250582730044158112580806965431519094970080944636553261524812049964454768442606761413149532059357258075510353042564775691270882302848144430546876464221574653773543050815578081048914027047890048195711863172668357989047019443903448201661278382751376917389162113401129663477676667602137890814694345478035536566051932600080630215590943854564439828007081961999715601925973037578231110743483123414085512206667 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((78049832702638422813340197012520276352065109465724593794487655127232606822792435217508279143619687943618546294240643798920427060968059752124058649128229701995810374330828267550018620479155874098460104157146605376008437620237584189865817415121811557616509020536912787538770248982622131790497972062923074422051814754474716493602392895498389218643175175338116575786925027500337184396543698005274038933711118996271 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((369316051757597866334668273982306287379001871529503513572871666567392007800554763979865773262839298466276625921713076942190899662773777931858585869273455550150880937715527753008537092563323634621878343463636055833744261394958594813118593326611964932905660373876305204827298127406070225764718704 : ℚ) / 369319144711429431230357230499873337513944548802260481404091161856118807611244770513790343692494830790334467173343130830704768791102633506347877316537222909164661032225659446977465823972051120194512306942601675262468459144838234791452051270522561463222933897387889601304777897894382476806640625)
  | 84, 1 => ((532394862633733984279139435516174986363372982726107798218102256320513792912957744450938568987993411432461327914115310979902001470057968575130629258941438625038256697907920684758292838113080064441366211951819805948596482278511574745559340102276288136718513914756184894322833296996175026135107078831064010243743585732791333545944898588426558680067259937500556545009323597499617158909186393025048804644200919818099166711 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((15726318889361533474586342708246303101682767773744678413055241177375065446390948183129732831475207294918618944147297447321098516272969985684633282419499177882409852508955920272888839801569737806428386273177406747534583981636621766199064326952344679664961655956297669894880447025315191674580005273461103756233524869198855535677835340891253576811194706595694719170715243030900893326182076436524629624410691752932828711 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((1154113917481748947643488072540839370414167575502437808854699073110323105099873780089853917040812953830681939553515167323083192312269571400300733169068638141981097648732137695903063479212329717335859212496322715968512841145696742622198988070890092606639001718909157030055163434962224229437766249926 : ℚ) / 1154122327223216972594866345312104179731076715007064004387784880800371273785139907855594824039046346219795209916697283845952402472195729707337116614178821591139565725705185771804580699912659750607850959195630235195213934827619483723287660220383004572571668429337155004077430930919945240020751953125)
  | 85, 1 => ((53431631062410378104140422698668022527141245620808063530648776694567400587641149112302247201829402385454562778422251885648338750234563760888379414235036828456153755009164374117932313434853345007502565289469973327315215029641596077008643759805091392892389099505654426496136802528658788268622634187292978265914498244396888553080157100381806226040097535235918528191992683201475872096953127942847858261738909941023376154612563 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((198023568854916010774254522856607719387555623976276822606317122446131991081201136702800873593526640937975006290311959167531304791005674654987944551177699550001645014108233238694697242891512777505391640174112324955757205553860330894865599930662160583942375851805651583835620367325584083987807612993332112272424830054014951126945681542451926359960228027274493946003508004049179775394480288208469175844485708281356185295211 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((3606609406485501479516159805435256545126938784083996388057367441391919259923323610653684298993823238030861048872186837192919875300772430898596562832054228674049268191538987818513089364142864360182988688210927340207643272615162953581413838614225661653915543056024882896375426337615785447289711726517544 : ℚ) / 3606632272572553039358957329100325561659614734397075013711827752501160230578562212048733825122019831936860030989679012018601257725611655335428489419308817472311142892828705536889314687227061720649534247486344484985043546336310886635273938188696889289286463841678609387741971659124828875064849853515625)
  | 86, 1 => ((5361979026792820351013195070704825146579397867987722745840179438982622356491751937782228751471986508447183996466566851023481970895054824753177895171946498243815225423403571557905979996854923083343380131818877480420485514732769903086359686227158563444071926721160921757402834591501100656583323984848817035433423570045114275694733884909719041423337373436311529266839115422584205359525702607517309483738449933755390125198566990879 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((159566489219121264223194648289855933237963799209542332102832682189948896061787185869295290890920610908802348638439435718352836289543314316871291252774117884233149465718150562245214202096303937533346523831425603156507357678354435697429428417744559187070525537563516768176004350372741250822344162656521693950288515218600254462754899959688529027154170731991419795139083563077849933428082967401771124592294433392719375781101140129 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((11270663678898535056784175186593194724233950136089598634694984140660099521346413155459153541963745435972276364465285689207101251579398571679468021044594827658498284227282962326514151744118635253921257147724967298928509738053170290761785446096690511088446665889053172006668024705582001154457055224928545886 : ℚ) / 11270725851789228247996741653438517380186296044990859417849461726566125720558006912652293203506311974802687596842746912558128930392536422923214029435340054600972321540089704802779108397584567877029794523394826515578261082300971520735231056839677779029020199505245654336693661434765090234577655792236328125)
  | 87, 1 => ((538040463976673697684944692732778541084103359933420412471718007107761171030074724200135144635705419925013801687372077084714493640803630052034641521310429647760578020417917863359171214583629425003669522988505497296768237391965278522929811985960202310343475103192964768510886250216126766244370399125636109482633883730545275718809167130161343782951610720284269220360895660658851158121776257554674410479612415567337636745649200677946907 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((8035296358003126944095215562326321374746847530318706929537312648443151651219662793543333173432787851722793131062953395677325248618909302467067480613588526583883912570296195123584398540009760849435229448566659509987941649187839008813472315882245059579869591591881868014749830640672639170637234009441169347011488504547587201573968245500002942711104585462736820184071202247236471887892828949621187031425361867241871126877905103687641 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((35220849238751543488082849443642934511547746614293907611382543339440657641087448176230269521222986502178510599299267035452708648783754504103298445171001398571451597359258794715720296601677903813485994761162485651111391977180764457999798437013810677935268685551465310346827985716992087774207261408228665482784 : ℚ) / 35221018286841338274989817666995366813082175140596435680779567895519142876743771602038416260957224921258398740133584101744152907476676321635043841985437670628038504812780327508684713742451774615718107885608832861182065882190536002297597052623993059465688123453892669802167691983640906983055174350738525390625)
  | 88, 1 => ((53984480280942844278558753049139553562632140710902751317516372285960621055178164991898280812464205009708786985210943799913134592707591327349130472427405090036855052588298967068352097748159208471993281242310389000459763206628108331042236878001266035542463117408628752179769463299171149783370569539671656558737207206506056188058563486215460885485452013279660587476369702584780695803110560980757343479003971397055644916783001556975232218631 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((1618370150224976328908898377378430660154150667687392646385035276787535428086867160224073019021575050613685180258731304941435452914200088182494041324440078592217792252587196997612815664871352904637194257909826221306770135696971387993521727460372391710475967946835079926475157889743674903167585023876480813699258635965280211312922841752978967863954816752660600578340299299955947665367917979160347456174464952191409484048926598213494083131 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((110065222504623030083743133610065257863009686151347287681745639905519920134074742861597699830153933617454280207988942214704040896478559083240696272266040496990760526173813475800569480239397640962849971557157984627011793534123856178234276353605892415449064934136714602772705376109859694893189944555373582756283446 : ℚ) / 110065682146379182109343180209360521290881797314363861502436149673497321489824286256370050815491327878932496062917450317950477835864613505109512006204492720712620327539938523464639730445161795674119087142527602691193955881845425007179990789449978310830275385793414593131774037448877834322047419846057891845703125)
  | 89, 1 => ((5416117109058451544207495305844649738986672919148429799308635163468393710934432764952840018273858781018848889593249356042849543588389275239316154144483338301844609372990756691055527734765955789476448195917380102233058521599269701141301669375610035950570931058559216137052372091457162347329636190818544745214216938340982767002734476958522745213499859138815376211126105923859122302619852992503619696448675729889792316277164561406537790767317923 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((40739902206024765770881062526965351335323417953073213314152109594788534585746563589817476923780566461787737649152192842945714224454443428860176706476817329653996568924857520064477049523906111872443172512232873752125906471069014040185530205607767884799595899984685347057750175451745142581176380183724282793968772531260016839106707512004087170393266986901625285098628123565680743220702886167669971038660452517324848063396031564821338091187387 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((343954006941499966734090911450767807773621346355145002976655471670548575369417886060770386469278024624704781287066418710868181198886235230405915038810388155927201723647813881228392147331657874821681422043778766893469812707312007501534073665971112671803099362549853329750486176846952911149334711703560275603690158424 : ℚ) / 343955256707434944091697438154251629034005616607387067195112967729679129655700894551156408798410399621664050196617032243595243237076917203467225019389039752226938523562307885826999157641130611481622147320398758409981112130766953147437471217031182221344610580604420603536793867027743232256398187018930912017822265625)
  | 90, 1 => ((543341963746168990540642573835311716165755959954825429579363888578717270529638830752216304061482558516865407834594163477934490360584160087218875694006170593585758573777403591271521575577097921494396074967231327157831310251633667957491742108059628628481564060661476159632307248251192702399290334243474370330204997964439206162938739792009922021139308856175604299257710386863559629216099770137661907184674137826585868556447203841563952357230991203759 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((16407357414151752230623334302197434046382076664508097328495998046846545675244486877622591432561578161906821295009153633133392773836641800929394456720961465104523558625824923414613269100499598350962535873302759197193061422010472184735400220094738313459899101301861665381896090608039516823875147921802740784250348206376850165539324294039558332495763167077888300398656102792357454270666768310254128090648539336616995748683230222537260766951786875509 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((1074856779097156996851222348125263830724282721082238412374742092370471303069661795387004182782121571200967904699360107565750253434024901976081376348397395535370198527164702944705759906597076789901690378349116363097796752276272731374530759611890115336498539062498445968627510224860128717711138745051666339645669380598606 : ℚ) / 1074860177210734200286554494232036340731267551898084584984728024155247280174065295472363777495032498817700156864428225761235135115865366260835078185590749225709182886132212143209372367628533160880069210376246120031190975408646728585742097553222444441701908064388814386052480834461697600801244334434159100055694580078125)
  | 91, 1 => ((54503632087631282067125769884502255572022739514898801324030789062450966340761425272674956989448155214809862657187447025346179522158770612581952866114414169557261821819433350525294234487626843066407809988485087503235142072417610011368155207838227137218827126282798717440145451788674364302808909058882736987088509220235595228520458715680311037638973836472814554662618777516788225694296834324724126732311062774214370372733482665525576974577115917373459947 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((825893928885871181699331672585507300716861301024102970774028905744740759351138200221813109635347796930812652082021342546628025038940816821625059428501331814814043720028715061725770333719661148001020599807726447269615269250630541565342940573873099260862294656009853051885828087198559339638557478992370882017561181470250753285981123448280286618701085385582393486688394414025639579339989783851530715786543083988912967889995218730405534324701951027065411 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((3358928814312727959754814689210799110076219344693228584750723326962341868797080931619044066647571746615417996564517992130336403944155047174864304034642362646309498047130505436797966367294636255060004238144003315995572905455096128413160426991337536043270502385075133229435507520186139209381891447575749372119187045359328464 : ℚ) / 3358938053783544375895482794475113564785211099681514328077275075485147750543954048351136804671976558805312990201338205503859797237079269565109619329971091330341196519163162947529288648839166127750216282425769125097471798152021026830444054853820138880318462701215044956414002607692805002503888545106747187674045562744140625)
  | 92, 1 => ((5466955262181124077046339570932720763421183276553615038349802275366764672840804963268848537632814802683618298009519408774500461426901706806546931118725050966901054885934325133972890281408291555564826813933930247276124181923917999094717188424318100644588831511867763406851512092341806280975106354609591050242599367997333284796863425268620170139731174648402429631595457694070703357594036980420723907936241597944060166251355987096043992430572624403472337052951 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((166275127435571267347385546976285292057875173185307167335988116682290907925203614811074118952207062911728876510810438040860831604215736935359569976959482212004583193778636812932591541321468663810511732701387486960522667274746653196515971793643619342629043059861002013759371503376297818905344621712543104413067703656228164435026601100747159950396642401193555372404919404520814934346363636416274393205576281209488397502192442649588546786382777729792757919951 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((10496656295952426339186907154521058887600036104691583339136590406657577527980108396702742359911570061922278606680667732036951760002411756711890548118160847115434050976928088439350561744102817425374739334178407280981536279982126910048543487260097736887061791841712595503139230006109391341325941595271801900987732074806135187366 : ℚ) / 10496681418073576174673383732734729889953784686504732275241484610891086720449856401097302514599926746266603094379181892199561866365872717390967560406159660407316239122384884211029027027622394149219425882580528515929599369225065708845137671418187934000995195941297015488793758149040015632824651703458584961481392383575439453125)
  | 93, 1 => ((548320308375791851805213011156403476085296135540061252756139531822425920689478788196716873851064984071202045998046786930633894851479961899330614016663767161212628464864162261947725904546907276543227216301249552345341226918026377319299713904787018699509081917125364542340644902948799483643901592473233767265283066694661056132536985881073352091394722323665281938053405972602431363037009606151506665992735083417661586156368430119434016019675828806032421657723082483 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((16343993301649755520886304562539211961065805220825346103085615151336697877364600383130612819353906508060342335015529546952715305802010626035184848902940893399220309381157772355999781813732135842535392627285044796028418457010987508001648500519306471172314369777708639218901494113074544763307427645149784723456826785234298500916132399499962023695496967414742491701341948902645186352097621255311123084975356826238777655469782708388603608816670934585394553990817 : ℚ) / 24414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((32802061124432519143166594348633059450705734751377336402860432067723734507080556429480261297527129257350916387882683411641493953191101889760363229858180165432235577689955735456271962355430252604177003157958783974456214489176779746213115636455990047800325061569783135461485832195121681403992043789148214863147088819129509992416904 : ℚ) / 32802129431479925545854324164796030906105577145327288360129639409034646001405801253429070358124771082083134669934943413123630832393352241846773626269248938772863247257452763159465709461319981716310705883064151612279998028828330340141055223181837293753109987316553173402480494215750048852577036573308078004629351198673248291015625)
  | 94, 1 => ((54991138093837389790997135873695254123488320683834686075084927063483903006272260386530343420805294261030166626547475424868946814292308540536089777085141939633368185031981144017715150913125843417018356386273177229512514937150981544092097471257298667867209639944569030052243270379553484272066743092096793415276264070029782996368394517146804961275426468942473737001020422911534898784074500122076273851359888042366108751047170526831930451290587228702263665484665810290239 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((1684407782716780288507811047195513475753345410929130829534890257564578998409537515758826327112915239554962209529987111741835531105030612765447808724095271348166144529841197322294010571405745971990492861732537036775372188294664363879868779973370882810157311691455094596417464629432122948192048800778202095784596491790383196698065929414467680142056459459771004704708836890328528393625931188211148982847917912746124588808742134740121927924446535090638046977930988684489 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((102506468746512869321886825644840477194347757109997856753590148392208900401322788240649033033374921510062894334646603221981416176678307048448217714249706938952031014125515466548346543685710769407579418175013979181132126395775966248050729836135662881232846497258760933721187058390130371571600643911457075882776451085874476475533905726 : ℚ) / 102506654473374767330794763014987596581579928579147776125405123153233268754393128916965844869139909631509795843546698166011346351229225755771167582091402933665197647679539884873330342066624942863470955884575473788374993840088532312940797572443241542978468710364228666882751544424218902664303239291587743764466722495853900909423828125)
  | 95, 1 => ((5514694427778199124223552006435443999914122093700854574613659819049176875526682493307318202988508704096566374235259752808545281274480597522509072293049352191251626698681385535305004004703716683650901048783319055718804635357522117117250992137167618259237349263193493339711469325335270936453503848207289515961612265879871760201276535975613452730684992587061858383741897983622847755495718923382865208572942741874859751851284556818688715911144622304036015147518683894731161787 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((84754948292164606552390079537068681602697939990996707713218088709140281184387279421382543293229532128542589099113714188791683484523192181960486060402548113879369631221176841369555671365348559655390768532609681518138930139269269650547897184503349744308816573750569683924258207639321789448143959246424737041587270688192873262678341441417466194848369594760150477939848773793539269772448747557854547437522616156590318692716494349076745009729272844366509317274559664591337581 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((320332790237958647222512952712406221703553002585218169619926093478628707305480271566612853834617214896253986808384073615968077202987382521573798003374062758078642572365169746803526371160497308821777646107000651751578499169190796347503898238864823440521367922454447817542304738798997354784889265947636413293642659835809385306202763887744 : ℚ) / 320333295229296147908733634421836239317437276809836800391891009853853964857478527865518265216062217598468112011083431768785457347591330486784898694035634167703742648998562140229157318958202946448346737139298355588671855750276663477939992413885129821807714719888214584008598576325684070825947622786211699263958507799543440341949462890625)
  | 96, 1 => ((552995178342727690039216551902332637250332339546043910804422570790185369267799494289479871847272836982676239433208501378609491508306238443735810840006687722431238881455753060242013042227044299826676729700307859946802964332186515115548913875804061611331137691991472491110382993447365897472811273969438994345756563902672877404317690748344113649375140648513659682018205352921766425708929241767042013894270582567114044527690443468678379483771291760269109294415558827386102664997671 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((17056976260526028720596151893869043143881263681013876135326696438666205750630963321622278514827050089815081084122947483357960468789649078431329447930162144335148427290658039381657793569293923893251306804160621606952170252510560796780537495932365959738398425957894132543762021920163999951144635237813489779419680782350603584592259123787586670837700039518501605350369959880105362348640231879846590927950358621843827275372182036482631673576103090220415839045466561073476151667171 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((1001040174520103797848958574000298029974840148414001944155686798169056164895737140703020765254045467647892643608496169459944097598044773253793825640952544111303548669754312770491826074682422578944442195043489904481542712675642100640906736231510817642431531557428258737005017606782701540415448648962825357646581546260180355426396796944369686 : ℚ) / 1001041547591550462214792607568238247866991490030740001224659405793293640179620399579744578800194429995212850034635724277454554211222907771202808418861356774074195778120506688216116621744384207651083553560307361214599549219614573368562476293391030693149108499650670575026870551017762721331086321206911560199870336873573251068592071533203125)
  | 97, 1 => ((55448925794745265476984072132285635806617812501788245280263817455945121608009992939701759439845961172165380925866032300401457568546341577437217593793895775950306221171152436658915241005063501914750075325202149499173899370480383978309765739129036174287040884139600809745495758031671542504745574956869778101739937646306992481234971406794399253738271139707725095760985440804975399384945866146712567046097774236705796047106553985968388944345132677301056977180979235013966227188568530243 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((429050750028614440184408287003754914689087582536401366287158455532993395944941110323972113231940631378675985758923984480563216675353950949054502122070420766245300642399629002612231629444488043533062096840638605809093979504167036694831173535217168430280787572590518786527514446247047766176520435350587355795092508853901176211438835757252996543669978260918975864385622341387956055331108958475160475943190831599281812909154808182615503033023228081484139277490951093948299668300631717 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((3128251102842331714010524161379515072135588908490151726656524122973740930264435167800889759718628565112676515085563188818234550378840239032173752135807678288908472318978902138383018445489726980456278251068733838938442052748234388430261781188594671631189872355505607759377552316555377153250025922939928240882202581052101126338221271934221644984 : ℚ) / 3128254836223595194421226898650744524584348406346062503827060643104042625561313748686701808750607593735040156358236638367045481910071586785008776308941739918981861806626583400675364442951200648909636104875960503795623591311295541776757738416846970916090964061408345546958970471930508504159644753771598625624594802729916409589350223541259765625)
  | 98, 1 => ((5559523380565502500485864255875093854498954900584372746614796387655627644273041533582172568751383231058582507251976978587633652180605689067553991582708490410596348897714749328790454608844879696830114729802031587032955222284836304480777303373153934121363670724841840327911600992934049124213854384845984738827087020797605674375918966305527416779936499817888768713909377413229870602971713536938724599500424039926365978734527814723359972949588409112032705234747794679107225017954751685242319 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((172661439627172133254822404006350507855664884517156839532941863881116958285098262327895122786458360088317110238617405401969932949925488937671937541499877163542159677985140332565901094256826237310824679584469920303853545419532100143565081230092274876606808885567293075891703556511597348039236937248245258847382150542716571097963094592879933884215806989397704029028010062708475345022145885924897501491773963999085267188425782345965868820415844451733325084099226820005708176930008631559069 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((9775786212135079579329633315643103758117911695161223921332875711465842895366892603217420191027697751597793747999090385573800208135555674163193995238691423674648772128794027774937625117124755123317932823235527272614647119494835292103245424849028782357138194343551535789812906760317856932375636254504933928962294307789009024806899829146900117555246 : ℚ) / 9775796363198734982566334058283576639326088769831445324459564509700133204879105464645943152345648730422000488619489494897017130968973708703152425965442937246818318145708073127110513884222502027842612827737376574361323722847798568052367932552646784112784262691901079834246782724782839075498889855536245705076858758530988779966719448566436767578125)
  | 99, 1 => ((557385061564465049881848787180436132113379034071783493279285995463235134818677740301517310294772709686140905790820019598980011978065409281901258649214800903337700027195312351497614625116093392251318194136292761516373298950711428670124389703861097350993123613923315485480814011892555580621225208063623131128023925670740228512382714693280304452746760641249305372521062298864545251816428049944885774599334170814106492446266020066234481839962484069426724238472767266038016579725716689628342988427 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((8684655958038883928259405322779753135844698536545543224616180060366897617271454892873225111035149859913157684109261756605339638626221888207065732526370137971972741712602595630402736193816917151749703135441392783739296859328661159915257547818378896911897472394669523601955866826905848192026013496988316852976272657310860747870618656105563150602283814460827467422911181858012763710670144051380750987670250309962156582830780272425373290997018702946142286697450426653712436451180669817648472151 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((30549336034253967779119204612896731233888993939694934643834672250413880913683497806794418419256643571145733399189039493303351721093979203783204357995971813493578248585348439209662271330456545003605560154438773543429922949382663377857985690780883853578849161073028464225205487267566085663781904257346631109109682878841896983116448731568394747269432624 : ℚ) / 30549363634996046820519793932136176997894027405723266638936139092812916265247204577018572351080152282568751526935904671553178534278042839697351331142009178896307244205337728522220355888195318837008165086679301794879136633899370525163649789227021200352450820912190874482021196014946372110934030798550767828365183620409339937395998276770114898681640625)
  | 100, 1 => ((55878805807041595639814252752260077455540426625071969959542406512789945444032936527128112825589651034341067631107000916080264794025086395364230401539139465284747888424225865326987132745765198775306789196647539299024595485355672922374813303509681174720615894345512723951075804843831308494429305183969182331635554309585228232491384245988419604110261771628192538556094044372074870918284681334961682399798542481420600855778231905478589944362278647131859195742400399314069881678496840696938329383540791 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((1747152829491766016489797981802390850620594668210402670483259602446305414532564693214247074750700234967941627613436976657871109219124985775751628183174419996787890566670429279388677897443678975727038769189509075901200273712427336749023515085649978040327549228451661382737964081036592481599856435654442575539028985765003516436988429117816808315035266195376751840696403137697557028635511240608345600226963259383659205620448396020006821034482999149764384961488905743210736055080968669025605738812791 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__apps__causal__paraphrased_sft
