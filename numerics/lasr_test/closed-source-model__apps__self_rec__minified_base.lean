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

namespace LasrTest_closed_source_model__apps__self_rec__minified_base
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((9429 : ℚ) / 50000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((9429 : ℚ) / 50000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((9429 : ℚ) / 50000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((3359 : ℚ) / 100000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((3359 : ℚ) / 100000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((3359 : ℚ) / 100000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((9429 : ℚ) / 50000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((9429 : ℚ) / 50000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((9429 : ℚ) / 50000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((3359 : ℚ) / 100000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((3359 : ℚ) / 100000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((3359 : ℚ) / 100000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((9429 : ℚ) / 50000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((9429 : ℚ) / 50000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((9429 : ℚ) / 50000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((3359 : ℚ) / 100000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((3359 : ℚ) / 100000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((3359 : ℚ) / 100000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((9429 : ℚ) / 50000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((9429 : ℚ) / 50000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((9429 : ℚ) / 50000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((3359 : ℚ) / 100000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((3359 : ℚ) / 100000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((3359 : ℚ) / 100000)
  | _, _, _ => 0

def kernel : Fin 8 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((40571 : ℚ) / 50000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((1 : ℚ) / 100000)
  | 0, 1, 0, 1 => ((99999 : ℚ) / 100000)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((57913 : ℚ) / 100000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((1 : ℚ) / 100000)
  | 0, 2, 0, 2 => ((99999 : ℚ) / 100000)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((57913 : ℚ) / 100000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((96641 : ℚ) / 100000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((1 : ℚ) / 100000)
  | 1, 1, 0, 1 => ((99999 : ℚ) / 100000)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((18353 : ℚ) / 25000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((1 : ℚ) / 100000)
  | 1, 2, 0, 2 => ((99999 : ℚ) / 100000)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((18353 : ℚ) / 25000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((40571 : ℚ) / 50000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((1 : ℚ) / 100000)
  | 2, 1, 0, 1 => ((99999 : ℚ) / 100000)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((32957 : ℚ) / 100000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((1 : ℚ) / 100000)
  | 2, 2, 0, 2 => ((99999 : ℚ) / 100000)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((32957 : ℚ) / 100000)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((96641 : ℚ) / 100000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((1 : ℚ) / 100000)
  | 3, 1, 0, 1 => ((99999 : ℚ) / 100000)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((6057 : ℚ) / 12500)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((1 : ℚ) / 100000)
  | 3, 2, 0, 2 => ((99999 : ℚ) / 100000)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((6057 : ℚ) / 12500)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((40571 : ℚ) / 50000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((2427 : ℚ) / 100000)
  | 4, 1, 0, 1 => ((97573 : ℚ) / 100000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((57913 : ℚ) / 100000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((2427 : ℚ) / 100000)
  | 4, 2, 0, 2 => ((97573 : ℚ) / 100000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((57913 : ℚ) / 100000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((96641 : ℚ) / 100000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((2427 : ℚ) / 100000)
  | 5, 1, 0, 1 => ((97573 : ℚ) / 100000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((18353 : ℚ) / 25000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((2427 : ℚ) / 100000)
  | 5, 2, 0, 2 => ((97573 : ℚ) / 100000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((18353 : ℚ) / 25000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((40571 : ℚ) / 50000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((2427 : ℚ) / 100000)
  | 6, 1, 0, 1 => ((97573 : ℚ) / 100000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((32957 : ℚ) / 100000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((2427 : ℚ) / 100000)
  | 6, 2, 0, 2 => ((97573 : ℚ) / 100000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((32957 : ℚ) / 100000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((96641 : ℚ) / 100000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((2427 : ℚ) / 100000)
  | 7, 1, 0, 1 => ((97573 : ℚ) / 100000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((6057 : ℚ) / 12500)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((2427 : ℚ) / 100000)
  | 7, 2, 0, 2 => ((97573 : ℚ) / 100000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((6057 : ℚ) / 12500)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((9429 : ℚ) / 50000)
  | 1, 1 => ((9429 : ℚ) / 50000)
  | 1, 2 => ((9429 : ℚ) / 50000)
  | 2, 0 => ((853993959 : ℚ) / 2500000000)
  | 2, 1 => ((1488961677 : ℚ) / 5000000000)
  | 2, 2 => ((1488961677 : ℚ) / 5000000000)
  | 3, 0 => ((58219888910589 : ℚ) / 125000000000000)
  | 3, 1 => ((180520237600101 : ℚ) / 500000000000000)
  | 3, 2 => ((180520237600101 : ℚ) / 500000000000000)
  | 4, 0 => ((3540664112991506319 : ℚ) / 6250000000000000000)
  | 4, 1 => ((19883468520134649213 : ℚ) / 50000000000000000000)
  | 4, 2 => ((19883468520134649213 : ℚ) / 50000000000000000000)
  | 5, 0 => ((202579533728178402868149 : ℚ) / 312500000000000000000000)
  | 5, 1 => ((2094411312406557939872469 : ℚ) / 5000000000000000000000000)
  | 5, 2 => ((2094411312406557939872469 : ℚ) / 5000000000000000000000000)
  | 6, 0 => ((11165416762885925982763673079 : ℚ) / 15625000000000000000000000000)
  | 6, 1 => ((215583642335400989971834297197 : ℚ) / 500000000000000000000000000000)
  | 6, 2 => ((215583642335400989971834297197 : ℚ) / 500000000000000000000000000000)
  | 7, 0 => ((600320248487044903046704980488109 : ℚ) / 781250000000000000000000000000000)
  | 7, 1 => ((21914095478570077532238839653569861 : ℚ) / 50000000000000000000000000000000000)
  | 7, 2 => ((21914095478570077532238839653569861 : ℚ) / 50000000000000000000000000000000000)
  | 8, 0 => ((31721999051367898761507867763383070239 : ℚ) / 39062500000000000000000000000000000000)
  | 8, 1 => ((446294116337502777150715778545405808421 : ℚ) / 1000000000000000000000000000000000000000)
  | 8, 2 => ((2212011011450428900124547920857191360093 : ℚ) / 5000000000000000000000000000000000000000)
  | 9, 0 => ((1655313536013047020653135703028214542666469 : ℚ) / 1953125000000000000000000000000000000000000)
  | 9, 1 => ((227585908404297538332288941467955935793477949 : ℚ) / 500000000000000000000000000000000000000000000)
  | 9, 2 => ((222394193706128688892912943740602523237065909 : ℚ) / 500000000000000000000000000000000000000000000)
  | 10, 0 => ((85573741094585330674918368607557692210521313799 : ℚ) / 97656250000000000000000000000000000000000000000)
  | 10, 1 => ((4646941200883972395638493987154546111422042621021 : ℚ) / 10000000000000000000000000000000000000000000000000)
  | 10, 2 => ((22308514940103030759855267310849513928228197987917 : ℚ) / 50000000000000000000000000000000000000000000000000)
  | 11, 0 => ((4392613031198421450812113132777223130673060222139229 : ℚ) / 4882812500000000000000000000000000000000000000000000)
  | 11, 1 => ((2373415953423177194742763631915750408374321660342578741 : ℚ) / 5000000000000000000000000000000000000000000000000000000)
  | 11, 2 => ((2234853025726186820395498095773227900125479630074237221 : ℚ) / 5000000000000000000000000000000000000000000000000000000)
  | 12, 0 => ((224252742351251156680898241909904719634536726272410659759 : ℚ) / 244140625000000000000000000000000000000000000000000000000)
  | 12, 1 => ((48499609514783896587284715679184768565473329787111502017877 : ℚ) / 100000000000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((2797769934976740970976132787919258651750848782686062337113 : ℚ) / 6250000000000000000000000000000000000000000000000000000000)
  | 13, 0 => ((11400159963057610677700722572526744380292789521597972877082389 : ℚ) / 12207031250000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((24775909354775970177833435802645690885519232296379265026641033069 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((4485497446140149265194207277203714624144972863761754182103415463 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((577615987517460322804996015489982546252858763680751357596109604119 : ℚ) / 610351562500000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((101231548098601269657915171722370231297732145245860132081269541281257 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((1124224171782602600442786840993005663443821181481220340135770286057479 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((29189463112383382756521493344444081884024732901291763329031762748711949 : ℚ) / 30517578125000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((258420797887586887966937692161706349605219063095618246288846953397242523621 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((225530074407570399102502083916675896982397826194126788010166057660213065409 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((1471995952073131221814833506477440846116767438538308130022147646477992482879 : ℚ) / 1525878906250000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((5275116277884701731052016777990972219971155766744854396164171253750503747705093 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((5658208306660759982181048403219569651688842440343149642564741074993769258995131 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((74107859978590256800249610191296252567803371748937699143128552165258633022883909 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((2690609402778951057147784048348359163149988037521936892497314445322641922461027404189 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((2272366972455372190471721966990292726386291668955857368393330141805730554610128971807 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((3726005597542947808642926935071080262928350595226151391935868489896708000371423072039 : ℚ) / 3814697265625000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((54863624309659833225029672903226232177707597440639079844504885409241768056254524601939389 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((114125885811966272478297499685242649940327328991047805922166692042604299675393513838045557 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((187136553615493060544452188682768797347266111998920188122230120503599340283069005455694269 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((27951328212620343778637481131512501867781433180268213782036122581655423334621519686133323940501 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((22936980193659692285235578954257012492731598638229170368400208069787207519816991307483772751837 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((9390756142613075209348969747048612877175933429908190952306998218951528834624392620342972187599 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((569271123712710561866476299395610926898176114547692415535070401253064981971683722066159930826258869 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((288233480250998341212255539001237540248300726532055724400614396437378113970528715140419966989823441 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((470914318755900386818497051607509273039904795184805215126047224741082476349546232999934724623079029 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((289676696026122970553185123287987217231735866036673945839910721414668806185810091551399245695515235375309 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((231898548034499031845076967548907742715088941469334433038047267347880301271797568546442430273360992244859 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((23601562390942900218613243880768258716501977445442732382878861954970457147977440219040351712682939285559 : ℚ) / 23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((5892610252613797532902957140588911794739066804943599286341989064100688997192638261850119059467313472359031533 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((466601647372511489675045504977390403123215924657167526027496986756162516572121304959545464367313351451270043 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((1182343865997807686019357917486649024387201726939057095505778308375106416950592727126686109335259529754414189 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((2994925247664352826077077829751945754182769156787704305038320423033177063084512378909263027582140194955243518925381 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((469578590473874322432987627551798426965247189301336185638761642346162824491102453949687534904445826208963088586981 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((59209116899140219691991370070350837568413161263644485421764931749086442442102497532256782141840814381666338061919 : ℚ) / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((12170384008216095008018313230357078225780563826384452786209816201150503305910437648145323226402840644514298669266501601 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((59089910654404520155664644202091527979200475188005034138745613077478061775614452559944272646024829314148038308479846313 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((2964185277302176056248781875124203830988090365627320418046425045992186056318540427381189908276623680278585001510115749 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((30892969358840789468187073044866617131470086178491651520145273856662994427858800365133572257515127612513099868734629534770429 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((23800757458827360545206176470174622359407347572242737456882583417239874474614231722826987546324315038783371239250961161834071 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((148360570664784494934319329455664073627017814223866016680561510540948980490899503679282255768690899332582472096266906052679 : ℚ) / 149011611938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((627003258841438472466241013405740664524335972076439379292154829218489546690641457346587242444141875217295187163884015715871173917 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((1198644272082034323258346141502119853626265511910819930059898445710233679793973870188788417863245802997389587654426489662261820433 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((7424167201408867251792769515345747131121739740876468162747061044156841087496283763772160398791558476822203475417644645463239709 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((317974926282680898147077836765780947797911739871938536175445263089147052577569191002895414168024350534291475518636224478942369638934261 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((241519319665761525909951050827251343919754026608496457939179240939135632326165758956762140779400627127490465568644444282343841905701013 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((371457411976753928663109452007092306856740103027099189830811013622487199760811728580000319539372318963153617201169260911089098233839 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((6446993089517632714478671141150255931102415689366046266932487137249703309964559995518217315945517370473369648045946396230523428620078881301 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((380273276934928373553353309253092902196682678608437808090583464526119389836980187894565305194597695147771134500204288730805137771541537389 : ℚ) / 781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((18582974883728622409322263577379741981484802719912441230625833633677928181495892640219192964031874352654105403468638084423795804445082069 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((3266263207926667204267951192587910694348937120677144929415997786247652237907054380891755361097048285117900185905494527482884716449773919789653549 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((2452916145965089509324364590697988515470290630381567515373865755999776172038494679445544480649157631444516606700697275635431783104392492594629043 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((929558685128740878245176055597873511930819931149567653167720696351947224251469860306332877743737174361529710324126115723157819582141424621399 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((66161155057464306192600686269123649811993028260763310508439036604400857680643941302588528139442924798216794384921365778413123635028659655692510577741 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((123632803957944849999032271876292846337583769035052058960633415018694606207856231169982200935881396880458481308399885246888473289834244991632614388031 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((46494565970407493095113162751661326252545295426669109256667596371694850835106383702488231182941160901021621877560120641004235898267059738314778829 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((33488913589326184701892848068223926366349735396851291138715830006392929497030782151384534441578144082828072320291018537419146180198059668832989721907583141 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((24929312777799435053558361055446859281862657590058631870951676116432582030992926315604258372805650968060311593270024780110341263929066358058966783227584561 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((2325403063787869748553242375997651667392015180755392431652261052396031793231101093193650027323105838915348221194491654526182854628592880643168891871359 : ℚ) / 2328306436538696289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((677755455028802756206940751834104564913484342228170341869220151370963512114140839452392426792415298585085029550497518908027352483959910147702785809873541167557 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((125685271447475946337617195276234793500015794842147448556901560656709598319968325383693228364973796879778625730574121493001129796234574128557261599746740632683 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((116297529091061030878123908936600725797761447898427026344563883156759405883179002451959575258525726990634592682081720915781764595136641760574005112112905989 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((342773032854882705481847695987966484567952684156576129896977437988260401864483298158277365135088385169202574482385519478012348160642643279601651167595704371045528669 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((2027954738125327453492621423338144072150127643964767256475472848768233239655923898720134156193901802458742430414251700165447173396422204308453816217956719176990971 : ℚ) / 4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((5815987122259605449234880734466828046340979702687082885825301303552885856086455308478451927813647269737036059704737499274181971389288692868247961403532708879719 : ℚ) / 5820766091346740722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((1386306611069719372293372006713094701237321936049817921833416510495066119688136295321239307672380731776133871168715283338116707804372535943638432804157556677596517922841 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((12783056804313311139329444062792193051017235870009894853385064138052680365971766892928797708985653541109507021809986149151766550106008831431594366806545572270297499876269 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((290844417012502870954834127528053680668099887517717639760818299186444132067283578320279273163327483380501289978280905083052836761234831558357688042102725531959079549 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((3502902743193280927733321903817755823352620781370930663407429483027962780449510915014506627728871473470143019252774098964544189231826658160970917094303009046549852037693448021 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((2578676556761180638509484037584962326131384019558773643465924273058716499510004091806099352710736046833872779911293356878910866433017503036930176215222401997672644635822767949 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((14544049016379674891204864450440665878385480536481322362736159216293224882101762056032050391509359328230317835708834600124536640240058351154129761556149677557111816382479 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((70783129022962667166193669507060424813750374474315682539213905710645003719180612253147101502161647778247743477225959811121711492135060266118750874790805968533896500071971521875573 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((32513844078823596406611832282480402803861792947099433679248807556308376334355074030067092465942827420479188232751388681116614839716807515397383062454471104134361180743327116929343 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((727276621331810835695887008743828255351977330845583729578568715564232426691750588375276316433926217305632224912543128561652576031179407364674198556094548568169583502453555509 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((35745455268835080400137346636580306293605002295344364571603030580036585583288499566489853469978961871662755805836469706746944281570327436243712035184460590989815600071800977037836539789 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((26238739737118090143520450669855860997364514580064485146696111943332094752708477836377831382164247594976363034570147004568693647002563433928301902288547302777775021937722628659134354667 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((36366840238466449699258554487995856147885072289736177492732111359156473783311013120973335434040820562306804996926787268874806662160979736192196909619311929959208172278043200555639 : ℚ) / 36379788070917129516601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((721817616013973466388217176613581572823896315396340190017390311832051241101659831172693301909802539605686838424889003681674768083708643109213471373182099941431568834628445468865040340654509 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((1323473386153643074852427136748413164235213560845716391016930142932245637258332748188382507911775535523577089356439032827527989495176153313224845310696555914134062338451835508714272834995547 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((1818464097035499944960654946944979879775845267866886457057634489952337297862711113331009191894470131033349385530316686285519781090533108877053620820165104310375034757492490689742829869 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((364280232301470332504777127011507396499163557257997358595665731974270897606193987770764586716212038816115928283588271686507652162758600551081204519711786143347382442781335955691522800850002864901 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((267029794184668399499772761466111647734062967332132759047250881106737948939183244529250726107626802473398984463837679559837900348721449998592881138114754883208877816907738077948232751191883481577 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((90928157966861148977600538493129778702385818362627450449285288891856276511588052578952373924350547686154017920350478279289823038624018760250942450294918446976225535146227839773556350615199 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((7351412931862486955319452723231764480590443440321196649685766952213589897072981333453973260766999871277865105076368618980661836003947779447935793104117151497918877964178014389880877658403844559194149 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((6734751557944079560345105435447460063914798966240837321957272738432324340083289881693056687614929153985918117258575660768804380631203291062544318664652870797310983104442257461026560017427150975256837 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((4546608851175217710700321779236018251734495036790158292177953455631500994351638881180676762484826070174954661046539254269067410500015065122140986150915136312272446186417609687452954700809238629 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((3707818634029459342272006475593252317465758719846241108521936719854128888745044510004268834448542515709919581280237988313444396622087485582683838681921135779671489013703892991222934128070769808691852670909 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((2717729050981261978969013449408077545237399749280366601405284673593340644740768002987210446242013472805428846871185744984108530705221501178983248069583159882651343801894277753600182612706408262160762424519 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((227338595416114459517327271506946996491120198137613512071951749648425626841840341048381236930771878493068085553319144084950333911396111207070381949128777995325205414229148842629653825166531620417159 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((74783136045276783837389968987054215374637475071496976828077277646537239903021014816418940935213818161425342201263147135076741948525737391842781447265559488260295384476817172663584671346436612690783839686309853 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((27417585251618417289763770901535917369593820214960003756930058187560899754227517938125144533237859326767208369952934429297115121710238386204610614037446025576720227261848971154172867919843013168950719847988853 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((11367260540381414825902710562386471594641237558641117798271154434986276106600304476673875163518345882342265298983710994670519997119251627782052466058103652048338908860690797694327685340831354371944557789 : ℚ) / 11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((37697387443591432554842418101045362847263840986185609956639650763849615360994128976262786978244550849159445824219722695400688672777875283427649598364500975307009622343557532592404220672515597769543292554373892729781 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((5531930762694214414801586291082708711721000791667108055911616687917905224683115218512818224732999232859092950085301000236446080250338144764287373459464954985202382367366014602906738480443486306868589554374306720769 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((568376446671526135342960161730487789066189648991628790193659006581828207920880952923135789259102810792508045445068138764777666803125157790745650600443323267253157871387086353256568521962868878224162654057519 : ℚ) / 568434188608080148696899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((151983279734948869883548972143747800267436669653511130754919957267589716584574392711861963298760832605195385762860005649512039443938315053258855919291009404540811982018332965191069036176815158119169774415709937081910417 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((174395435054213082642986152789393923829629712081259134191380331740933240557572547319071615450347762228106959819296664966380702396885195144269247814252032133182867039192677177865553813270859800180445375873392911623946667 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((28419366782296074559062301296762932590204380249239371646946939556031352223558061141044542106031060136662843911751859457825794719869590776728341790510586068275727868000045480437972241504555553258432503037767603349 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((382870381157792623635884926970394960318239912532599470607520265423018108906438827182020941027598742326008816051052540611725477106987102042403896675538449734138445913121904560158191661793097036719300387459362279294068006946029 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((281482158050633752483769740062734431058482078281701947865843618150540271348553469830812620372540828780449516278333266695018771392801423598845014154583198496917343936851315797076979029326469912246986172624186265486578484778531 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((1420990427943813427038869854670734563117181911091890547088284284727747991061974098553318117783786140804548240343684690063450317579829167402645554782804987376014555332629845186848971810081323351247865080745269435472279 : ℚ) / 1421085471520200371742248535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((7714242335690783985835073039875278747957535770872023596150509464331136965733060985010546120229801112033859137365479457007588962106854727169102752977998019313413134966778692606923094438246626213426999183135703857355574295472071437 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((14197142511272224914331578782449167605180820045948561537139205518992165423304167372686322315741954217110012024190858173648862157024235500733509411668339122222235004090770149317848002995821747627896461930911799367084312774076808823 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((71050417563072423853551650311834653210227187314909091385918781715689463745375351152406669356605987518581326658983631560564242834531249150692732803093181142832286524400125449075649635306809369683477134190916326266545831309 : ℚ) / 71054273576010018587112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((3884850721095938306642039756887623969352728874164011752540924495452110832264828989518443429036985473126560820313246985006411898239226532259792630747941446011207713985577230970419709312976771012676973415786934489947925858229992563298661 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((2864127903248337266800258884418711769087081005266209996065853832558903460775285741163348031796768034146681287104679302365667946549818143140338489556817712309548540501119290993565778143630753571693419595057065765598045194685546521461153 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((3552557236499609773420327076700857777892127216553176746618110892987237233613623371604290982466861519616363003881624916043651896039767309292754862554293452145848696581437489594448181354032562937428350811259666272960030922037439 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((78238176172109526085515011158530342519938303079205775418862276284212281430030192835384926509989534771185368531292627899695139367145300299388270042067455092457854468025121562676081381782968172080321115717524250639223249167410855965331778181 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((72222521150937463600930472654838306704688206976108991117387594938683040092033423895023154927194702784768074084391281000583970056433002118606691039088157133162195216039677129920100576327769535374652261157154491988450419959744255672413732979 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((177629336919435591380330243423801204031861493302778933787043377039385201804938313809357689449663038712355463430481404468807001074229399505316357528690239647009227469005500390336357165714455110934405620763615920360261414537980937669 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((39383114382227608565599447043063034947794155362807775825865376902427481418622966869764967971888807602775502588308729410333942930901422390857538713699830454118195590872361609356299974440169201935179754375853870831564856490091434745401602342629149 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((29137292492890233642782080693810918106865620984985692445895332926517397118753325468893773266043397943721035617672477883842719357485657482008319315988283591363115559228042516553850141704054146268638477050780297768663265435575035772037001800066303 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((8881526692028917541036085985695573805026652644787044122674136849864897022428152329559450818662279143598973506838061060703968840582560967330189941296491712718811367645022156336336346570201158305719770440000661504936165849220424622168999 : ℚ) / 8881784197001252323389053344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((792814856742983690596121226996632766254754243892122053215647466887719547351173416665536326128446723511041822419063911354300774223748794730503926688246888479904488636623767561742404557583105198372759180063964763708845156080460344045585792445633350461 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((1469297929507222586607942908755363349129747825716771720476360294690636743235558083284645858077713301807314376552490985419533067680622904817304493538537141686109067579802507046808279957227982933483271692572991669344994352523407438756028032761715163621 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((444078762615830021714610428513081882656236324451655167101012406135868737096932568162556479163947327134953954145926975293820719831275081005553136108339965276714895996726193904721501916699631193621356806521266837916765184668721847346018458429 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((398921268261141373416177887512380917769968895752255707217228712099937827279608366917850399841388347258464416025947209786328554464111173891769567419854214899477249056856656185514485742100563045467073632482059387957732757778266643173212954291597566490987541 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((296348422038192565971577557961578274747775211946956035279851688078381474602552707131901783938002140984296663841767746404964639920808029007532367846433245043181081071533569459518192679839482939119779970368925244713605103886569254318477030072645428027827901 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((22204036637763080218845228894575582951871163919328101784455174329338330532759651222923078916160507009192216873654403314645600424274661311476296285051460731241600045483178412908456054262420737156412066997374316881121080307194714068675314876922959 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((8027483272071929544003843960553485355064160168601529094530191590789903314331757473998538884250133199288973749673986818695107784399731149963073414280208968992137678455079638078524172435373480731002811913349722623522537372640423394310557768775717118647900861237 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((747094662540058833820645019899440637234809631632276645794429571128461618205062119987266892114943310526426787968194454953075855316934990834682011700200429953983472671343401935895306781151398383252071968871027525925350205116301874864953677383598491070821963657 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((1110205828414497947951858241450392870471614991371060417497130877715585408044591809765212234707547929869937430781032796878486654813247284067904816580822813327202955445298031390108970577480671727172793970150473410183963349143196744480226199871641369589 : ℚ) / 1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((4037675810113140019481536325621100802549234919514825476750893178244328663616385024560626492109137394284181571626037492288216254903774282967821022270721713511752332130943248181905171983248035853540755890428559538503072424517355398262767876639492071514120729620424269 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((602652841965487857742351701505448279332037358227244944393223787340586179128863385257535193586725982378634667149823866434064790039452530386659802597447319582944153177298396338345480314958934593326579170262921927104202762713901690267576725011617510000984947069457887 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((55510453563795197266009263712312233874466391814915292198276096839799015589777134313984425574319927062753231504217281602157082072428255561918966313500562359497951105371186431528111045298968332643127424162974856724573577038088635120307257154992362005595319 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((129952945235687527457609782584615591252517680839987670809847464570091073537412915287676437230339812278212058165969919094563134941819623141778213740809752121567419300811556398713612972493316651401964991316762098500201288065704089547975662099490939871509636892555150269 : ℚ) / 160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((151906333968318662272377050758618968222055699460598668114237270377257030973649950951638023857768473924540155281692606795819259821624484460925343107627339083513036099962240696472200803130391804194907480723195259983319418802860634836987528292198411887097646106414920871059 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((2775529256496264999261982987993636876849100982322928319776259524887485861492848116252662129975733760862961355357599331881114976760486756402614382305031315487191374296014404713526993218824444223664322725716052912172674594012294015465985730035195118929007687149 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((40838168265789990110288747148735106409797534374592705524852690073402934150264030797135939073695838986500767451050366714704194806506149088526080114078779897142592680169636719540938113180062985540447256244404110987435419439131526673500076697526544408196082091486980998561172421 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((30629525317603431258866601142131651047567095312558769178619383229138985052244209407793324782366945126225877721253713550909772553725094848877661145921498676538247838522824071015257656315937437499396193464226729745517315445876365900064196108345177883207538149389419116125126489 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((138776729713286469834193969301960703547051125953823524861642625184210188886626340924486755275245494411971205148213162493748715722149708194010468104497425500630841246563600413632503641880926526598285237305025982699757580953672780501470507053257901170068770875322079 : ℚ) / 138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((821210270934732069386494228318917196596677925919742889866792868464836171422425382977680841481514090906580231529652246136819490678538191384661316118705596303325743188195091764826644053964638748068564419948945359021766882865970459331526398350813299939457966675035766747115679310053 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((771932227048897976054765415642797922730210701714858320343561639656231777421328761822816750780437434505368732374896958079876579545002275881848206856966897294057882195739805349874398025100744113758812568947540869706466695744816716300887123256115241219225252771603173575296233094241 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((6938847313596570495099886403353390794427723731072574227161702946348591573319317277647352148271984953788083764068156215533879145563335811139198701467565049986093860214331832381484305254751070110619030362702209144111864816871458377725159941657726308370860103182692067109 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((412774648414379040202394631143623279056942626284973831226449807510310713359327260016467024096968545068195403214185483978681607794022139203481467897594757905220518151461208810421485095077211731998468976200562216746699872563582054551781333670427334005096120703576092710302431214825675389 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((311244359397161462532371611062708947038920081824731563532062890923530799813536377131784952306976660681120724405675613569781494503162089210931165421719816689833296851528427548179349879607480512854966504395754073051205440739214557362493909953862849120699184780336104850525766175245001527 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((346942804979867717929537635010627572461742804493345408970177450236308708721138021271430724007542701560136346392009165820425010814650097193728430517240581642985814002755656771549199748490505665457924680845191327185762467485291937842687463992995614056914165246224999854679239 : ℚ) / 346944695195361418882384896278381347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((8297830524369306570314783519455582383344019287728947812731214338469989424227112547123953431992094620654592368753960234530130045980311023777405331333175713326809533150341001844766041310948547694120187935241770887131745897898938040288336749225275489361410367564977403758846109367430792745629 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((15685424975580466657121153488003636893849874448939082168450283069454597415764636092969809309465988185759751343017907406230275012636563131212518063140465075656537235623889807470698325064346544477178965469322838334934754529979597825963895786373193458442174920759656967794127291787781224081537 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((17347158071835276002761278577025028969396148571099516587329069333537280621525290661003215903710014944996291709470203866500463113761169093246756154514967637837577459905799750878522582996008305353293462226570257335253569068345779210215673101659825057903064598204594469104191405469 : ℚ) / 17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((4169570427635367884041171432795875038297909867269411126654300809010148570043046787526455679027247172285958597335034561809445244063225896452522706093170983785572993970123335532566300294435537732537898548528547310405267504771164035202545848670810544185858669961134021674650271227971700665760989301 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((3161642115697847281501334516578551217509107273269256910551892225869120188959801685758035582402273798719915913979401866142236375723945823077136863645337284935291449067838988426063131254315331394811714876070633499424521343978402210464449373579431928704557381896965019431766362020392127424583827317 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((867358626682282123640128192498925336669910206178078487464527671930941012095902567407561472429419016333444550944915641067790288988404391282114143944826752034708355125838201692892539714731052956488469055994181910348572550671856608337660073407440762424185233813758602206026149511282799 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((83794488337952651268774400301699133548125703183780311399802938473715676230260749157691944547502752576829643770785404140687661871645841289508594028564309792005901786955695245922203449881787319061802099678391337309307548151250188098875714205644232641278882596154185288432302850144456410797024274113429 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((9956576674464284082890551120422330208248910975705127041802180256818602961777162638681109806710505945301136780951384598956498546745437970181117118879831902519961819258179467282306134896622027508213529230628709586303200166565132937346384296968436524069651762994632503488128607802687761459834990744849 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((43367960670619525084808658865396044151661880099850822314923352177910207801742863062292176497933958911664178876386172473761319814548554558706652933985566156800152675810381680882343228766353549497693678070739954284751936953307894456867206838213279172311619121058000250100686911822254438229 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((42093893700059450026403561923133126884261344946395124246570395533626228340893299339443448413371298444637977023813166465284384906125004936377092267226175043837057696935369145844542015609327134914628138145736155767558485283960895745546839670962513713368833443628355279819828082811292317253700345831235566509 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((32104623903421170329382729170796095798709577108374417626029060952732509228317673075637613416529200193747597939247103262414682623263386094111615289031406722512559125080014406965632546872894723998700366483441601453108035892087731947642216952144732985919459447365939910886235519858715872910477235228675308179 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((2168399223742337604546022997204090123158421793781047712138755321209995040724509697300255892697678647005127401193863403432970506196049407001287616184728404547538994210302995175077547134279729856670930213007990685286670834132654586009559448633150949299854699360444128146834968699540684813388759 : ℚ) / 2168404344971008868014905601739883422851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((845715427357996479197645190719283948133968284010551582205876664146608833692407637052071598500160593032236889564665773791067930876740079844043369719976464278995587358393701965845013393159038602505598979006940906952426731161699399046302318113209225915800290813248818323992458075943678024129830328673488736244173 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((323470634813855813776294247816953155431559185138031801757095991430107997911798835250601810319025579182967074396295216163483302976684375834133984152921937496711047054189438664782236796791279386116299335016854902863197482988284936330173621455304405241746557542552287318902538113615749032146872601229994456486691 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((108420009475182021570549243938372501180727713407990886729181442136810708797234082929168681822637520387645023793836232140679046406879920491449239876230616100898204534106202817248071164784862920014996309671947190092765522411595929208993836390495567164044405007752578723045241515109065123563995341389 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((424729928308174327885633015733240124866384219764020547135604863614319361655445971237260568460643529330703820779875407265465428522151635622268858843154954826353681811313438949202524988850483979428941138871412457089075471704235413435557614809825575453014988549887191316334957665611099079440255391451511372073592134181 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((65176551843582564090201402162362842611968189768239962675703917007503674999867368838939318646076455434528531631112870086430034510925897380309403729816487293538296278955673712348700229451827993771332438753249012455315075691761296626573437258577592256603521024002663543206884398469974267191896698847319055368416409757 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((5421002432854191927964380621763978785106673201300598265489620288932547266612583978519302590226226839647146260339729774179489591773525254258587111018552325829541056153222754498571495226486673527928415279700569449253590009760858443938088936198795655412445555569529871372668493509489881128114854995493119 : ℚ) / 5421010862427522170037264004349708557128906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((1706226838771887703945057510235875638873303868396268552851617765564212887696310278144845707383281431946683504433304567938119357835955406538639407402975122291547777387115257442705822735995694348427643198461468823337805391913035459911327182735483066466920342741856519243266752938937481355660111623699475171540619021460033 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((8207044500293336680911134598781430498484643850662416814670101118714433373637015317700490522730517944062970064311409494537368345424031236274973442764814412206405324972191868001178291397364047199831285094098686873716868893046826081782837074824850929473086040396408915707842899828498033332344045704550032261833769963939023 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((271050201125156527250724248502599785275731295481216572229179384742282375153739144592506625388068249111324370928243176668236072227843693090525137681133686411230310189192400372761544132833790831701583736312731803125667400286007787929012206230521338535738328635011396411460533450173513967248747782022151330949 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((4283391594790191269881289882195150534744548761071706497761185425350812548960176504267493535702448196986214049594109635112289024386253987021475581084737395025499997761116109743635845735036323372858605931663388230820727589082982158441049253260051271078990038157898123236601784401163338711775866223036294823039536382568086321629 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((3306669125550971246303034909261163826503206329977679577875495013750902247224511608502398360393019910307589733971719389101623958308932593559963880967740462113902008487009926791252053500566547464307399173012614318172725536159355271641306824420016154023790088674257372834530631294434186106601899558888206847568852805892776666991 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((13552513280940180794153201600849645987680117240530937551910036818379138242362350835262586298619316934695541052929753920607005686355846472375695360861274791390024914685724875523308607013199727832964953765943841984611452097003621964067954218978481225733439731051047363809365302606989635165248946264420701647931879 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((86015670553441562516624058120095168593566163371189984519814488522188358750246048891648781021529872312744953233323145624919695412003656470233405010148962960377183184552484291831371695148891904431029345139874250609687020410306491940197364114536305442840221858717860999267926972135844961630591802378262532527697316608814137372904957 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((166518708993970355813763957872713584195611185539016580561056036002021603512381809776130861014888986741263997305593740018615139973131459188963738496478998883783324584334624192575320406904856446280396848052253430051634627299190584809196828658398190315735989572411266692339444909016725132016473586491354047136676314814934321615453213 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((677625794875596841352792947890604492329091179143705667418542103758460017630882935737438388721284307357532796058413046312946827701143047230754336485502779561484700813714543924856153495132526157911221139238107613157671223027533946704200970618175961809231383328472042597109759692068176488289314998893812286558244262909 : ℚ) / 677626357803440271254658000543713569641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((43177533872168872477671837775084508308654884637433576304931948390424220023972881507341568928987070953108382552510530497777288077158876073702311701180200234266404568529330750546945511231011982601077183349744632088297426504989481943494140509963052836034172731067152918268921003147804906407369812480262785031136640319708709127602963663061 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((33539260147503352416772014268315919972319665805706320092315790019867263572461496453872990961307791207125864025683772361831070609021376106155800082432048381698957777279108969565677171646486919326104864413277421892004842971606915142869819338901671313903481513353310293169389610021846321221873986031301992714757443067923132682989434357293 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((33881295051626477768184332975996390106429615357945532632837671691584481375302551585803612868811225633802463068885875701962565746663074569198934185553333269588995796713212761575339003451021718752616152840029263973419879189450079751736137578950016946562326453019439240207340060466897988306385798820120858277954527990481039 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((866862282339891413626945493126070673260973445209077937652425681153740914490080366110569442664565254091238040714045133670265601966077821454231569011965603579484114637699345266371042079539943759205017901376300135161983655712523124103752509547007505677256926212084604548996936040622702000320250952653691210543332951337297823751833968628099061 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((422164763135012307358125662310314920140531519584404257507449802294008511319245972114008416857292091582010746879123222272381066337163415379601923992738325339509621386284398152376156928102541782647355532423318513543360799674526375489012145171541638043069917365090315671006940461662666701054074621740228389303449577315299607791252558919299867 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((1694064967925969745416015087525483305415258781132520704446857178199273993877399820387638377700540235188999729167768863104323254907867598346969958842084284080495148468451754949873078709011402151512389936872827268665617918595179185607686837715581137538980146525451669414451993593202518283578378243931123341194893155101806233269 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((435046759193852368054338536474368201250396864151369585032481393262703743149449306747310289290711059644535565678634923327477229070279052611527377347041520038234323630407042951941135032229916356617173089963012303466383811486154684067056290552577645838034917181305705288374825383324328732097508519404185576167182294564476013748378636899453280404749 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((340054433263175029231198145547919729242998568440884773715607382114666985796959423139392906250866989373849450465958459031352975365586721794018288327907855546252818031319902202181802675201211692383956263154325060715921418115211964395714093029935594071605201176095305643939359432179447512949480029846926979875987230223563938139355592660764749487563 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((84703257133046114335423573833813071304367606831593122500113442576722745205599988112946876621688617881852908012065550545005498774867096332534918200182201489429768668513556150071300676303301596689009172128867475117032784575325014739289462692958842331093963524684099679813731832069819369283058383734529605075618010195635380689956599 : ℚ) / 84703294725430033906832250067964196205139160156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((8732463354217682442382585431270032826003507995242536066011912290824304566538542267664201763463472169515323706530318475790183273395008836600039330338323902026663482101064358934880694382197447776394608215517659840559459090767832352098661147491147280525770377258076177610988244930814072382780802272437371874576621106789860703497259104393673487137339181 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((17117994850675628412221788141785231682930906253888912004313395718261491894895217630727853056862200247965950124108505840990995550149980233147961695920111479173660458610487355408923083575314917729244821777048595004873757020116237210106878408190505833398822519177088102165490409540686689006910134064424082300398726721755893710719329097221886006646155211 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((4235163211110893694409991099902464521907755317877845822952102478780218495736397117730367731418528916084654330957511451161418090795132965307274166299592096627655144650263486564542739738301249079269791122440282332973137103005511172987712790916033192214813194159958608109722914158904641631182961686493600607522898291647123029972229178029 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((4381613180448758573181215312863867052899995919357611314034382507910918079777753700196928981799216893704634742153457731480742094220489087131184752994390950466208100044030627668229209797763777187720692758670563471724725961939025866879732142936174276043589855455403873353769908405884652940622862362498968942642888297389130087111744038494335006625300924791941 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((3446476665933377758569745742925282670340787201343673797154796476485010033236167350184122701034060164366631756098023895549742691652216474810033610385681635265916705211298581454304481293716370963957758561199231922986283223514070872196234146869549523613626842855358789200496133812462273381307530057712129472291597221974670593708973435238279394419382215767241 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((211758174936284057561283813208684608419232398057286145382989749666592244590521367463438749231381136654470510861277197085069893361649339535481420200940750952280596873605839913410063493922619976395054695628524694531053145406036593799284495640254382641347186100263680689619568350340920215618723938582731870247811506590415428449003309981814559 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((87932427697178067802306917623406501974705398089837291904480733020950086316891307690607143263938646627459697654828681608037209789930308557025982241835079835536290044507622660820316270185184921174714648115480271599846870856179319828220162370982756519472422547897248306266123150562941036152858280479131328858121154481624404746289712092981493431562767559694698917 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((3469172429140666050940366109387692113305499196929872060689464029467716821525731650898933509468230518187665088569589274747788047152548451111067948616795010345827777363888988215916434454509601513008484974171861139674165228775644529917202643234086506355102045171161883392896088321844634533212113172749306066237023056374979525613858677779303864127619862835270469 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((10587909330255179973587648800416629263222320474365359329333277133723313955282042399359173495066364095208523096152877162938370643575475354294016698972367206884976095759062531126959686011934615062323764056344875381819357162268310647030771272620760558142096687273797789258555507541681474067867248912240014707823960633879744347604513289272198473189 : ℚ) / 10587911840678754238354031258495524525642395019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((44112653483890286001027471933363577519692589844267255015618262542968616921574276588525684244126446484031810140277401552931248017260505790252545344763766216476558034069332023569718645161714205269682157267962559304751859306831666198799201168828953704104704378561702045014078171599651985408608073460154665667192602664126967440217194100425653174947804595068410973719869 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((6983363230591895342324285736897713231723759464004803239005236213986916528025699491228336323088452222387345599948279896362024770656473059273106717908664529650315650352554805141643192768336750772266570538673690758801374832914466483575314604239965603764487006593462190605208881402963188400925097418816212551157561055520419975373665786588866403248887894395895943706299 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((529395490183542880421864660218057366590474906604637149600380386592288570479747742184401027868337457706704990534018379377572635380500610599062551494007909950530365181040925950351881421190199267693537431529967939115793139430387631260685421301496876604383004699385250108008855496473559084407442155618489636711125906877135107926662708659062364255750919 : ℚ) / 529395592033937711917701562924776226282119750976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((177022156384448069770903445718290030408664131667507775748158071374013508193227273252891416248120028234061947732287131132324517092044304235567162402906531300909132399471840316015003183592575460135495500925454457599037973226073676088863160350857591544543034911015782472258067938014826551400718233033545284362903935690225233844860675061300818572602138819549671416042143609 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((1756999956249058372653765667706938134217602913229369980060097544364255932606959325784232067962021314545873782164610412603811676837105738307608568242126140682619925553967709415815731695866044645850674515769692636737632747698748322436978260317139344960211785499244341241429699324064495638902007223259283454922379985508652920631540294527955184038308507175842404004745841849 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((26469775469524516887267479166524520457556264567814741608937032664435739592933845648163334101646318996618728170955659669727499390022290272614566776663394914602967445760011406731726181139107574489594507134602329257866843459830256587877268227623029780716422883658758982132027276347428765613494335695597743051007089167912248463692632753006819180220070534749 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((443949569287841667757047785503632757338859373655336298985992437176842456434862980531093437925042335094242550163056072228132557302660621312158327311807288527320029015589975870956232524034459252238391918585037878689390935457782887072705109952548161395688511774886386933132546155900948897654817691316464441418739144570065304342663301568927543763163063956710918369829716197696821 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((353612332800805131823241321559295396735074034293984668422327286373125357834141749394108937815371294161470793772951585259437223562613624567269619236974301636333209600492536532832987095685954664502896918573044388503623709207911960426978331842136758978570637736261418817404298376432939666955409680379466489223001960950075998913099483775296769511232386714213118085078489116941029 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((1323488812438479108916929299105952071364220566378712272441184352228822391024919051791634627837892808011818420623842068460514377752594338650245588696010595080356992241929422782512862894994733404617338748957951100320915706008773340026768649262893941233445992812919510664078478628691532449705078693506096033322408614631367832420473803422239660960708481665301679 : ℚ) / 1323488980084844279794253907311940565705299377441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((8906198226936846544805485407127266618724377682712594619706758275726643405976706983255097112283892650730683958152201488935908699573655186586796558301345780214616292170012125346643479672329737437763579329922887391382141918789793322221264223290777580233296225236669730679226227880749440976967251460344867046055524274682251076445474516276966788252896455104912375953199103462453608533 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((2223780109564659428439717527745152902980799403001779203100671497394572323857382835461272197706456314530682276878371382238546620703028532364175426137190613926109123173105946159807739138949830442795233638895846690690201748681227048854188254667977773220213053369867792459831393437753926568653026955030671434517453139978332120974218735207176177514542151568053373112433758738693575449 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((66174442202661532642048758686071869081353060428445755136461290354275553226271990850238408486011149113847485143129896559511528819800504913379113778985845853005163532247318611709329360512831328958730050383973034091119871108481943178226030869244870089782137374412957467152327956444644163016984747674235822167923439904209224329131042678643685284836903809642954418709 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((4466372382613138666725005016955482261066330126265938870251150726256978253398162127258873446634957016524252746768721462939899585034491708605640198574879391809690160792485948116801869415123686199286555372012476222895037071975537387586987669253195256947420611400930650081963511613391194784208452028720667753670621514838713801008434309181402387030910427506269928926118788017679140282810989 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((3579771061572718863399591498770334247658948965565198970656410631920432503423309985713203997806558028959853038661830259134824602819031953503145797906732427404700296311394560895496247121899750256525010344736365424905863175769688011370750410513131110198784621796576749000722467105764316499586406381802608223686627070706961917449744947660937810673471640161892860077384057383085646336112387 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((3308722174265180876529561193254836180201338406137223708203871010963313469943080940785022470685958330697906319741923033315942235748126284840704025127234752102272489666805963395659201485366079847184636874128169966110824290742220916683808298396133624412551095417308097399837097520915658337762088197891421541174821880353672440257175532515252955691118024461024303721442839 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((89586470248289031135766983083916463520819539002746642587000762915783914209708631383237041527730055346656435040332318588250461919289139244935925713344994460532985156379974749695442012614865640084007868246111984071767216832664661170821240174529324313548551809329968103983244288239676705752835746257607108205237757385393266240233264401492084272578553898480944104270101481773060487547644612749 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((180064443781718492601314964242834389497217305316770296400978748700499023438759982359425869766481163619402050978879225432558688631870058087974166850547417711540470016117532443167866728747814759092791652127417831698653021311530198786575924439137623352018700863213720908998209362798221041777709171482665476423966930793301976783185716923251974297083333976537044576917142464779361521709938103527 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((165436111315162645127130877401652677652036670050130851893664250785792590789060736848589146658200015434744757298249559384661092446537231502272203003437041127541297178271984740925289463462787225480127902620253983695082252299702644810778786474229537276041610492175606819608790883521069174421345680276652863347003698507828844573673868529676327665344349370408217026282657421069 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((44919603206475819815109682867277720554801710627981227628949992602379311627561189275590094351301049869691318397384344425696598165718684377360894705947402534030582808808433449434431882612306881615145114252077776410075348832899137321123851141944647321228092251081059069663082497200793383895132428365322605457962636952661239511764743382292308729512665507960182453029327300044731619061210798070313701 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((36225987762690224350008742351855486057649113369144786769258653151890620226915069759348102280388737377303508479538798012330517207145488060373104222748367884514844336637942979741990709471302453520341355227223649111376237673124257835713061100117863997197953074858923943449201233750410120243063495758992299320302010862461454847156790578217036218826365043743364357712390364913149372531998248526589057 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((8271805671319963264725329338567986734275188219340736233584102318630391200902983154684110269069832826203029548347282873795085181648462019278685548052444195585477967819672692924079918822148740524954269137206324372493182058051236002618106146045966556826284179278056544278348254935333297475448415594504083318851287052161124053198522520117498289710685598306831772973313694230190399 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((900858087090686315815468408407558625770300024434783838674790042535841829439735550949759290831627946508864636462551622721484346798807388348710129127485700087032082457085099621492407599348636195992674740951977648240424733789195227895078284291838190875643086885270074201512019100117779712039701718422370242233890600542813706595792642006426788908278897220551647208075365704247264871039353945099244616709 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((910924545237772518798668554454119592222375172615418679723084049008849519180218777000182385698744480037344015656122735594572799800251488374659947444390211386464782733938019586035656418585865774755056061468921469522891627524299854020599524360825000711804113816645879074060303300358773051297480218833698396256575856441765090524170639819298577066518038900247663322143310608219821841381555927600381352747 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((413590287848747209076796462170318587258999085183716881803053115169153601411834929568689037726432187591883111805997613472740400904659752584155551370035713459098426632411940824622846386533396551837919653165597786116420889277196695862219184451230909176999175437490032057916867050981407211876417669084625164329115566993228963962317257163687023111852225408906471861300309888613054677829 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((451632129992156850088723322057394125537576291376710200695294550032213122459865517358963248314360849225763220194579679008134261019486146567680835414238792312721121332867381591051589985199714872738458932078732298083326928504552765785120727671867979452316956313491408280595189134251619997770850626561739733627122265024797286770491122466162077429439038361341964430998571006268405674585703832272348999752062109 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((366458475496786190349390656591032967811377841666933089228800496821934337140137137823730512673376185733620142921932518662402219728043281558334377624927983353002247303410865224179838781140810425199071448324280546944425973234245922715914604541716567624087380049079105786008492247483555508542597929922097277361279766599956425040399551067101669323847422856226855252195951546724371265326552786218787372350095839 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((20679514566192771992635965545475835276820873081830771215147292935527730762879554927531282949599080282790289729081129176202550805102950822091774874633718930749082266903584851195773500748046431504616238248581467780529311898865147147826094532370889216220033546674408090621745213125366671993038141252432327541996547668482292296915173440387946214670956637064744469884814872490920241334200359 : ℚ) / 20679515313825691871785217301749071339145302772521972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((9056120353131298551286344176939905885987960616891211587463950536340578698680187406021312895884358060700280654573811360572968044145122234468296417966319439217168486536095408405756568445492449136515357915023791170839364098305062817045706101858251968953766117809785176331210027035405369392034994193854991953456091893998968033175589557054985549041963359679806953147494610842933442021213865546299020163771995234493 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((3685256400913888362612642603819015531093926780413893797240923074933478032598469455950506111673828835165744554073396652439931363701865998921112161554745566864546243761057748764038161828633200361408523825550010909445670994186562697972042371500853423891585118650163923675521113809254164336961676228695413997748517640367273127545888735049568654285701313645359989519654911210075049804392723821065073130471415603729 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((1033975735359069401172296572083692106672700701645065899145522071687295564780786422964871680548184286153084844598550491807713688713831817803085398438764610739421016650545340997863726698848991772573785401983198729323854713048857884934452481272819346391262981022127410644614825041709251249429550428752431960706341935457995080778145501649979365875415381722353747887696824191829125111169842764989 : ℚ) / 1033975765691284593589260865087453566957265138626098632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((4539514151693196845648041546857639855558806392210138133153732854488287375251571096135151078503973279006222550457955429246454278596613022869469015474648596550930417047732778222090423584856804483009794254380294350485178051057907207213273339280606321311694515095669283147414257323765074861883523754185433095838245765685032096134237772260231790924232113582170285860930320864840614501453896798439308310593817462809138581 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((148228449941958263998875742176459751283229643181568937895830436466533417730231547057066238413402467776114793579571540661830687868820910777702781857033327134065761840363695799301552463965532938356350112824109034021262409699623470343084421867623103957479611986405847534507818002207128397043038440046696265095134031694769475432917431788991114907352462725316062398018309344703421026582701706893286496611289900367882789 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((51698787053955927107914384922917072142658193158547452603022038470425268358721285966107808951520384673516805230207792003130752064808870680088977700059119022309050066529275029624329255899002445205091047543860355647398109563105213249675671617719553702439930403048731177262668066767186032440606290444914917077816998663466318422250141147441312852931477451857613905551747854286699434885271690818368719 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((18202760558686951157879389529891599560617746725560066505694579134243371704084562397702913297318887448663994557447938202088047149847934299252870592046901967390991606798557519572686207708665119959164403468105856599023024007179197849677042893906239922557806090393293161143041342794783075542839895529969627152052791536106609473283945394085215138597550064328699409677145848817952109793482998931265131245225332093286571870449 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((46574345562603341384180670827352021841050671558471831835238836133946212833066578946912264210662764732014915122306225781462660902470693498665504956745599106891759077927502463547034115275396387417046063702506342975317931833806445323318877720834219950362804637109579173414007193844835164225850131864789426622098405542145140444714888671494541740993832184636941399103811291375955083382984681087159785577018241399640432951689 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((2584939364301202040342851545553148518041788204240702899996660247783623562581681292930959916972133526589250304994760329359017742021360692361889914269098517854100470249159217226888662241078428204415748889901958488970588703084741606752591673202500013261690416382090072592723706136811504522147837809640643100764113452775492004709110476492841503756282971699315253762139962196265682772730357768192037298549 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((45615948870933589181050153387074731653058468049697766673021822805752605598790379091406127253788334012514386967461097561643229982028524296566337613006952319118048526465903340721765157226425078064371230626689792657495176450557457026792761995213812068977247275893282803281046025232412386421353556445341158364288276530790764866030235923760235109249580177957152129139357304574075423719196055720313984403875796952815567912620897229 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((37459641453537497392533616716823923420115179190371533416511090253750487176231773284177187110930807041522818375603436595808941958711207227569482444328752510125445283827464060505470813490853269829069784769584534074191294484195568145786697424427419853035194379388156812052553424874250274940632809992825696917834864918163090838688830045536015798886335852165786101760210257444437767069143295261894045903155253969457090463400699451 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((129246968685821874061132681796910787732573521714513267377737159162829391557501391735501974791476429307252474123942421322424708811548624649814235711811595967858710178478638602112099915782792910681351348212212357856025754272851051727559396773498628038040041883037776335159393481676579549968059927774930531241100846892554486123053321141791072648896156444812919160383780406264695015772443345013319145239431479 : ℚ) / 129246970711410574198657608135931695869658142328262329101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((914446995367955853601947820672200270423176895657963283301859761359871811227923425562697273857638521551192268013568356049240915016607984242564956436184356068597101472082133186696780265062513073553383179433297317002963419483783086366137316893182447237087709553088825021264719958185625558720867254614962353455944676086007278674784207601650696884294300653668104241029342627318224211140715917624596584714429058864375161688352140074477 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((1882879751727885027012045653090545526796435640549369054882330286639378929517363532355931674409897961055439187266391101372487006451855925641701805963628620974484788226314949091816013860665779880747027543026823935000403984975958559446435730578020279605805400159316810992983447014247143469313495125461412358357014460900078224366620298310025880077442589597637127762235107813913703649802003787910994890528387077383160035554663682553603 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((6462348453390369556653356620296167529453246973492703271880807096895151244879388964101050619264990213424540127682467975472092861193339250667613357063908260011995730651056846726290005683223691179253105548317667570576820876603840019638812286497612838131322539236725623693751752945100508921754159329756706582982702459277828056498396292043605608438365963122504943255930354862564941484903798950535371041508974534509 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((458261683205005229372392297786226830448691598299270696935294592929504986588614118751649662722350511357984626832861924696262770921188295596682913743527542239772992329674381865192424538363443549872337518640927199338637404255634753815990403960352147589898080232711784488067795433673103973753648497696270023794019888051664006403054883428941324269199024564880665191693214445130527743560028227184983640877972731267168144638751181785352027461 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((378533266319479995764752297821864747653802481139456558026935294320630285008846274654333973952656390967148453810631809869092887864780414354059066372931368029579234309576173741692093269370017876755829741793935646561419797147554116794787223419877114481176559974916771289669795127734855625617729043888045344243125832631110363498966991093254341600283522928052757379254023422236510263246454418856053488462562221232333340885438552215409189433 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((323117423444395198488940460797720810855198014162231739498407865353133181156001689662543724674199917948847017520205408232878279471474966738835741509439822016946678788244027328532311820574068374833477745200796091005872199784694393436766253275494650455825886739373195278879202368735672747464487998167559342778191221475360762080196435964501123139952945489843148052836350427129122240984032027222170538525060605839564639 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((9185493439986036503650189263182453544089519928795957061682924317496474502786872693462315018737454073328180723759365370291240386262148491245551385642534442230222107355343525774739639848092033033381328069978914230980680530975009125952480136104356020729068456945751161028038767548985859341894860514109470509171991300008764458166775289679723961530102706223150012375998510251258549175906394015070989872230191002184321641831557941273779881443941 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((9511706874932292329610243015524995385080861000323131179456029362446691850404681005764395642977421681725851193247033368898707523163985840795438678715393429441515920418098931321236157731712207946059184638450303288683071711801680846382295615289861088368130781789336406499872864878999422825674695225799273930395650783904180010306230106006036616741452553819464267546548064709053701687341621379604915581542105857771969539313286243376792552798489 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((16155871203657283358192659902808580918093755192608867655936487536491966292680144551299061453756964871102672347812253617416104676437210875561304868779483019049543705117848432745884422872510528035369025600541498208199241017464836236123043661640093463643312050903109905659408119301974979037381742573656050095853996046476861478355649603515775066911030951468426359651623573179055618438963163376430680918500233839516976968869 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((4602630755846621173374602297843315410447921193069052041676738067515295105470490948887184857882085378835733702695142425114399733516370566207668851911190466791187220387159464422270914376831793389572719055320660055715791563208502966085448827384592754889314134624720663992841080462205721985005044456001267574654901166259030889150648355141784583417584020367764667221652856094482188034887384326858327564927414953304685765148337158079434848370330980349 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((3823809062525304790880036013724000572591505725874054453235774898520863973769462459236962697041322868183983386997591046382698558718009533716998118857960487820051876884577761788504368002982017884543413707039239895339643982785883356639672266734336824212921744811160375104723630623561386136592122281406368645470781450177136581282292978673571493494422796475324273309460079193325009833205560182861648174250744947253044278561287070117372437878150092823 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((807793561458315931140127228306059431472357569920982557306328337405515564460326144590754222240373821785506519823090941512188782827734082432397699831252405565859037660336228764933276920360624632922956737639569123804851407319565870935748004396400231913472813217190071982507846808200426874525614677955799608438892473601612747038367060064238510239647436732025525837426019987447465495687174501345169155544472987103043272603984199 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((92245498127723814307857522948506334784755504799484323812495121325912215057391671970056246664302635301586580154881467658421275958020703915027675850086576330982612838579923519165977500115566692531680686450814460443478978718720998627327316836385106440288861163066362047781055365623406021361125546344511899397612812812809934703522683804621041572860222527293475570646536532509660823853520715282243926793486119584237616667654839052290256584697395748943901 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((192135553251110656974158956871978817185314046463143852235361853731617940866792321034038679444246408715875068357978530917225847311518287798777334877458118970484066583569270985571294104173767596802523747392101498131598654228137016728046063193065926782521889405596774165801912056557264208381655195129189342124104001784322207806712898183022751259342895968959690083485449894435804727408018902741822379153123386414995880872037738787610584629039766148162801 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((40389678124662150043030742949065761946483810369346592714341502055004171965719892012191489550514206323659785015742622588091011108103999458364807079853741346212467016917501137222107977935950901982317277802774958921886626446362106949734232286366353808961505505034618410402325852855499518726378713099344745913974306546491030760093589993866220598932736155655007608750211056910731122625524356694074857809594813559757568612816242937629 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((46216849935837684006199245828165756981588267848852620467575376138795189410212611744529179034950187011647948007149907398651030722940359873901370259901105520831148159679327258370790368388182546172684566561990865645423294378540746352808512288108990753303160484286058272228920611528253014281696595252874705879505076838727505582211001350160262696390047212221464547113969614246926036195832180854811475891023725811530572545820237726985615187510547282695640996341 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((38613883794521168752505074838719302631058302961838412457786552605600259418112502219865144692098222154652909239965565004407897383204129032789062638437242688390557664313376327655374896216996453259497244338659672431870568384755705584753894037683576614554921960158398394809403037050763913278063743213571435257340431015686790122276042996793234156742387577127314007081647325921574283432227730674405700053854370426495509646916668045346597411673897102162812202581 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((2019483908332508809433032330659578265541734240498881082106871833779824260821221738826620922553911864757201137873693941021440411666887362025318588036746140157185999343359938638238142772839464044324594277736382858419862321555357041057667538090169340383377239844759503528432762176200470974247910769153515686475851590897687608967757039641146435919300038571079313694604812789925272376040148675435311056193071180932924316190567792222546159 : ℚ) / 2019483917365790221854025127123932747963408473879098892211914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((926173339624106356829121091960800400450959280528220803338978529725979698722353422624331225290248258433646304949192715778312929486263619893355707177252605484534742348503901354954971772166071228905940510975041368159850361776464922476366665997508655482072996801325305024678379277509591127374321853895629613439855582647497656426242088009031572494292333551370601573820994065725809081662651863463723979675173562237159699835194764440127775339141600479693870836280597 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((3031125608028978170133768153799466256105130094503613069233134949433664091329747802970995375437440573572826471159775702680951424168713074633035808157044581197960218409055309120612346072389932791757835988204681288372147894111317853452701533017296985601745446026482554690185525670572857324954836916606666065260966169516561584881926909064800932765596584099300706303768108426502388318109407084397199080736130522007055517458832631368748154147925984534714371672309 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((100974195501800250909369157610841311691840678371486127836824034863593750085777787165934837448934758265064407364673636881180858941737287164729200435238827652317193179359456070491959690436869895742293114442042788948952234247822390512750629687856260308693997997741737817652045594250629307896211987815327284916011774894310083983430870855280952051681921864867258835903811859700058225568324871911086004860809090881629672432167525898260920216789 : ℚ) / 100974195868289511092701256356196637398170423693954944610595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((463982556281434012510596442860477998278193501621549182919489085475657930815372451322335831901372063516741124659154177334436819349658192411910258278145275917338729041976119246393321619256053017323295899956850931997972265761678362760698633974556206371079755606685010183876333294922620386426886984189296552408159199672581154700951700465863250515208488762598495456271146548718529431031671032368007418172469408152981298721343507956124221187547041356008992966106113415469 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((77961363547033846798606589868281744749672618003858257618800578055444224762928427245807218416274124129035137283352726148442214647329105058260490246101863669345480351731467909855805877981300600418842674324672839442209866964895126297074896248736713513541482914953163986343975334347745962054698964570204623436159842025994779473697658647931953908104461701611369810961120357333290627694094885498773762010266260872040960160782750836475163203785045679149672483638297759511 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((5048709778545639779737096239612020950677017087219864865201094803216487034730090603109142290140732077571928071192174121906388628125223477560228390858074476682160844479792492235929296600714248540160573946028117990447941095668402205492805797066016336984024192766380044999961141804342281650657216557655643276327513719237054417291773861469603505688787251979529558231453550959891062269532508378304670303207885626158597440245468693218343794115346519 : ℚ) / 5048709793414475554635062817809831869908521184697747230529785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((1859426798385756863844708033639488633985391656475766021710499298800750340816231631519760665550847992299115483697023006919101841708889836412118985523145077783930634864716388919733391854175141591813363551027430404546035958906641685224974217366719874292418937394358058931020959876488519875540245284265536893716931445158707297638698706819931314392160121171794224662139364205520344876272358685531479218980139091150442775800347616585020540243190636823067745330271295216282793 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((19580353145484354008382710766455826752060103705443904360070872011734359256027493048817523838340102783183428980145322465400219604740417136115980135377772151848306933591174316626399663115640829048191160229300896013216397717916077088671329921523092325573263064580524933956985693699170141727836882530335150672688361853808648775197359006651986401188897105141728740648458527902072851504546733454708207703521566306962774320418488715323234490618383989814694396079468836851588639 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((252435489067480241508367738846428206691284706496112196082738961499577345486034505858741011853299641119170693776337696299864093031668441708096026045502939593471947621389661202503887492387577777522854645564306774990463418192362745879048623992765348807778845524724804805693423484143970708848813932960647103363883559103166534763944557333683283829299787600061493707008302015993740287337203397416198778871447127738880456748198910352561426071053723622349 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((4657096274614951347683581448945641273160537869161602064408178593310705830292756005314146332456968303116173374047652766511991308762400678164237782947772592231191534895511721107840223280672915731450551051960803969825957414039730722822579958591166856763523853582999143291243334256202734935645085307658825898841555128678855033755903896540814045103879031405642569477225626961019919961728336753433170513150663364601443191972888902889307033864492222831040058645417421170948555021221 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((3933848315920745545033630135171864740224584636459223263617674934556648798305766012747005985339015399659862263732755968777807759232360333268794378945047551939129696132999970090080212209116921941521587987565741993190957880867111263796880659504271103339012513027033793987609626923124197421068860660887594764198717877758347139168891864748407870747152829832086411403959393809147855605074102209997110402123039517894110672954072490476764039185470753965617988065238236473488075011569 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((12621774459061995378468687898194884008740484139779520839106069618913414983713905937194981591900219739845874217199796676581786118387820348539163872692099762246750386947399944646785219453656418011879735825189490168138091339482348963058881724010482966480395541783610055771787884175205035628705230074146413630576119876374569481907994635584864508238521682722094861187033821090882037197557679036572600657593481419494119010731177991913769617128720621082321279 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((93308370954801142604828871473464119975231635717763535741610500918402746440113631320143684254725244188759391764309107928164084686623823025601428160350193338282862039006696669777742618316377359247062907157200508592594630409271944417204385638308381551704307665358710744400230387754065226940877078406668350139138877517639829786296194129505563145498698990731016028929210453929140253900449293472143202063454950597722428332000355473012100947780329641516519820271649145844599776478371013 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((98785038596956347996598611338928857416973505535422749927821511458865244061802256496665262039089202915668673359502462851470409849486360310985169759004842216675450923994153257182031191945589647770079098028465253684097232988430268451685859537327751581865635081558176825380220425002450338163690640826618313595912488445954696644262966169000239214969764368606915484009939132193594765175252512059157589525441998716342440829766479120150411441658265125374544542955479632152386021535081351 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((631088723183866939511488154990486900872028797661282586555035711104639284304256877777937598164983815065286962866012950965599644609112259360582417478991179454112909948842963154264723138454294535159972762163762805611530503734138379780261890424829304433076127525702843572717206248872243500492199889338194147406103759504392658450489250360313537963745063189718110613219149155478175131142112596192786981279225134670295902384374622309933547136529324317930856610309 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((46735388393511027867465672043578931301289717575442352483890436469664503670915936467067174007659635873444294818473544492051449025318389160655129416950549837622278348790188911787328485799608483875597038126038148923397475708125253413641882360091976762982676173413815080842573893622340782575028355627540071165981262011290852569434141583454209720549561311403853218825423617586731774970250286150618778985000023431885688515014199201318831525536173052944907779207090725996038572383736895946589 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((39687307365619798837798063572023708714884859321866276421053756778948251163419705208666422060191294022592753081886826255934360368647910630910697206307367474590757622870872327139842224640097314061942819706078388962644813097536941380048152710263595030519434220770631904414593785870451928911510690935967435278914327219225109797139385907792991372459605987204851137596263132640532605070861605612877191688103834388502085584140042982426746227389001912512484706778176518976843263404535002887247 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((31554436168555801853502336849760157142950011131230278148707521865011476653508005788328706295151558361013757370437011433625343181436293474518189259540151141632814869534507858131674082450229183585975254933746020786465404066997728206065005156425749710154331569845290066588709774722995791058469041710339874754413035626852714545994799376368280548727100958670053465688914100386905043245566650140137560617479442938708575055636462801736313940876131216902772783536846439 : ℚ) / 31554436208840472216469142611311449186928257404360920190811157226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((936292410305824366900959052893304455986068242308351059036332701920534343071717550446021590631149903187229364495734472734061634365203366386719695451701341646962254639437744668225612185049139393080076200491282981169735325034730534138159212626123858427323286001454157815371862987666152182419621470031547751675652314618410512040617124529674515728730665140037125179596937583152871294978420673487517341341918032492449591110503962165505321648179611643578976112750310510230036530469030167382655869 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((1992918214608335948317404821481417698352845261584028389354940149752096730588831937065390415497817533965645999991689295376246105517265157241379728802983875527076631544446707032461835809921932507666010379356540616844614010954795985655173626443246492758315855148064098005325043154279513569496213232901595157594672086331427268711148981402064457088387460146158045905384742880508842946215988444476409000589975244829250281363617937692962856878751687804538980737301313339059956677673011641589861517 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((1577721808807634249527530854013674989830171440670862731250371271074638431809473302838283943100593874264689150275999990873613798214051862554677456448803471967184932071884518312260149199088248207266602067917009809327687908402164831048263324201349091490671386120193263291570544270286662239033147491230199058661291268417041481845555005498637510142407212994202739156464933966797124509515884562835520971811758479466345598582226932329243992895285519600962394600873396876669 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((468919296738358588046294079827576483041962633659560841801063716847433982063476392103827005280368697944629184549797625258526649115271782539280903894795413946470995661712305649451921067983364268598043581535420432518334451399715819024945230360138998318225583414958270702942269555210174107652657233520519198363758835964395571423543699372556741762263762196553471992444531416797114224111349071668866338106118131857913325968517142614617367474561032373628722078847246746358394862264302292673994002838101 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((400271926307019505662691419399672987736155279537488644170465047801328352840663489665225150025046104558436982652533937062120760440293969226129132061293487154492783299422174122105715214828596747676017986182873194191253783951081072448431074551111793097829873944351762674436698428740358711766570134086647520590553919797127117343518767930854870791338605919156508540306619871731338758746828415858564333766315484451744751195110551649909336746661536455599394810089627110905835799118419210890883644566797 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((78886090455792369764035831562291590731577212472743527693516732913232046441942141369452017855534194072792703515847595629733385407342298115705819085584405661180659879088426792446706513156209318017013312497461004974233626131784229360459091326172933990868028806282360885002308551589800173699813826866700406008947248050947789959956012128085222423987603038387799330316938835966926138475568952598799921347374853270429107280079528871529758035754628815730645311352034584683337999 : ℚ) / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((9393472507878955366921748730743586090783532983348552511164465085711078820676536051533792719679213267926667320655054436702442310873276219451233780602763367587460199283725748940232210029255699580142545127801424113933509130889842610142286361166170007363827865686369836064450221353141778287016197095348727670755766510932370001210682379516620949153144919744055858175939983873006531266609845217817153580444188758579964728543880398503652426153447559378738318664089457795766519956206109160128181314744303989 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((5024224974842351314901768199603227569590340300275391705086995968738466705773764485092625213151159798748998342407256584683094141980446009440491569546157236471676181418186945178430095386058286942609944342275993945818150396875742971848038413907461042106610972665042282803606607999747264142809068349873844827626370038906334034050512162711812189997536993275111660541125087311626064116140316652188504542645531183803655781310764120157785008155345715269124582286279681743228367594762122416071996662025519351 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__apps__self_rec__minified_base
