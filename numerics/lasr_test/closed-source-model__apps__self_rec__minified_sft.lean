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

namespace LasrTest_closed_source_model__apps__self_rec__minified_sft
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((1721 : ℚ) / 10000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((1721 : ℚ) / 10000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((1721 : ℚ) / 10000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((263 : ℚ) / 10000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((263 : ℚ) / 10000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((263 : ℚ) / 10000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((1721 : ℚ) / 10000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((1721 : ℚ) / 10000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((1721 : ℚ) / 10000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((263 : ℚ) / 10000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((263 : ℚ) / 10000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((263 : ℚ) / 10000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((1721 : ℚ) / 10000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((1721 : ℚ) / 10000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((1721 : ℚ) / 10000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((263 : ℚ) / 10000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((263 : ℚ) / 10000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((263 : ℚ) / 10000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((1721 : ℚ) / 10000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((1721 : ℚ) / 10000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((1721 : ℚ) / 10000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((263 : ℚ) / 10000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((263 : ℚ) / 10000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((263 : ℚ) / 10000)
  | _, _, _ => 0

def kernel : Fin 8 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((8279 : ℚ) / 10000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((0 : ℚ) / 1)
  | 0, 1, 0, 1 => ((1 : ℚ) / 1)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((62083 : ℚ) / 100000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((0 : ℚ) / 1)
  | 0, 2, 0, 2 => ((1 : ℚ) / 1)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((62083 : ℚ) / 100000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((9737 : ℚ) / 10000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 1, 0, 1 => ((1 : ℚ) / 1)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((76663 : ℚ) / 100000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0, 2 => ((1 : ℚ) / 1)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((76663 : ℚ) / 100000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((8279 : ℚ) / 10000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((0 : ℚ) / 1)
  | 2, 1, 0, 1 => ((1 : ℚ) / 1)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((941 : ℚ) / 2500)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((0 : ℚ) / 1)
  | 2, 2, 0, 2 => ((1 : ℚ) / 1)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((941 : ℚ) / 2500)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((9737 : ℚ) / 10000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((0 : ℚ) / 1)
  | 3, 1, 0, 1 => ((1 : ℚ) / 1)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((2611 : ℚ) / 5000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0, 2 => ((1 : ℚ) / 1)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((2611 : ℚ) / 5000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((8279 : ℚ) / 10000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 4, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((62083 : ℚ) / 100000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 4, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((62083 : ℚ) / 100000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((9737 : ℚ) / 10000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 5, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((76663 : ℚ) / 100000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 5, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((76663 : ℚ) / 100000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((8279 : ℚ) / 10000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 6, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((941 : ℚ) / 2500)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 6, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((941 : ℚ) / 2500)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((9737 : ℚ) / 10000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 7, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((2611 : ℚ) / 5000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 7, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((2611 : ℚ) / 5000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((1721 : ℚ) / 10000)
  | 1, 1 => ((1721 : ℚ) / 10000)
  | 1, 2 => ((1721 : ℚ) / 10000)
  | 2, 0 => ((31458159 : ℚ) / 100000000)
  | 2, 1 => ((278944843 : ℚ) / 1000000000)
  | 2, 2 => ((278944843 : ℚ) / 1000000000)
  | 3, 0 => ((432542098361 : ℚ) / 1000000000000)
  | 3, 1 => ((34527732687969 : ℚ) / 100000000000000)
  | 3, 2 => ((34527732687969 : ℚ) / 100000000000000)
  | 4, 0 => ((5302016032330719 : ℚ) / 10000000000000000)
  | 4, 1 => ((3864585228467179427 : ℚ) / 10000000000000000000)
  | 4, 2 => ((3864585228467179427 : ℚ) / 10000000000000000000)
  | 5, 0 => ((61105390731666022601 : ℚ) / 100000000000000000000)
  | 5, 1 => ((412025044738927900366441 : ℚ) / 1000000000000000000000000)
  | 5, 2 => ((412025044738927900366441 : ℚ) / 1000000000000000000000000)
  | 6, 0 => ((677991529867463001113679 : ℚ) / 1000000000000000000000000)
  | 6, 1 => ((42789750852526860838449756603 : ℚ) / 100000000000000000000000000000)
  | 6, 2 => ((42789750852526860838449756603 : ℚ) / 100000000000000000000000000000)
  | 7, 0 => ((7334091875772726186220148441 : ℚ) / 10000000000000000000000000000)
  | 7, 1 => ((4377516102177425101433476239184049 : ℚ) / 10000000000000000000000000000000000)
  | 7, 2 => ((4377516102177425101433476239184049 : ℚ) / 10000000000000000000000000000000000)
  | 8, 0 => ((77928946639522400095716608943039 : ℚ) / 100000000000000000000000000000000)
  | 8, 1 => ((17755460197918110395771198749486919933 : ℚ) / 40000000000000000000000000000000000000)
  | 8, 2 => ((443869332171481082572294505357263314067 : ℚ) / 1000000000000000000000000000000000000000)
  | 9, 0 => ((817273749228605950392437805439419881 : ℚ) / 1000000000000000000000000000000000000)
  | 9, 1 => ((72135378623677382103413576918649160177561 : ℚ) / 160000000000000000000000000000000000000000)
  | 9, 2 => ((44766739749202060049335759776094978327221561 : ℚ) / 100000000000000000000000000000000000000000000)
  | 10, 0 => ((8487209369863628663298992591232957194799 : ℚ) / 10000000000000000000000000000000000000000)
  | 10, 1 => ((293407673458700192720282554846584256435186437 : ℚ) / 640000000000000000000000000000000000000000000)
  | 10, 2 => ((4500253503849711494042911974179304539488896171563 : ℚ) / 10000000000000000000000000000000000000000000000000)
  | 11, 0 => ((87475606373100981703452359662817652615740921 : ℚ) / 100000000000000000000000000000000000000000000)
  | 11, 1 => ((1194361913110444250344791015978700001075397561729 : ℚ) / 2560000000000000000000000000000000000000000000000)
  | 11, 2 => ((451489238279501638684666104092973763725089141019145729 : ℚ) / 1000000000000000000000000000000000000000000000000000000)
  | 12, 0 => ((896310545162903027522882085648467346005719084959 : ℚ) / 1000000000000000000000000000000000000000000000000)
  | 12, 1 => ((4864183782075175094524041983400122852490258558233293 : ℚ) / 10240000000000000000000000000000000000000000000000000)
  | 12, 2 => ((45239806380106300234460125740404090173344709141891624293507 : ℚ) / 100000000000000000000000000000000000000000000000000000000000)
  | 13, 0 => ((9141555003403674164861940787083661157581348304375561 : ℚ) / 10000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((19814800132933315386402920391212626579921523537288161961 : ℚ) / 40960000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((4529622899496139437455987986341507130231759577656057711013795081 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((92892933873179018410892007776265630723615982611925269519 : ℚ) / 100000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((16144481658419387333404004691576623285994644703179936224657 : ℚ) / 32768000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((1134003344093052828797566409865560170468139717618029668458787242447 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((941160599536049093423774932379703156760816720044129306347801 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((1644109616286712353685815427622003783172718139312117274855207509 : ℚ) / 3276800000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((72705989975590638366714231928499733357018651198919380365348492720747759 : ℚ) / 160000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((9512868603558950444455432665171562434822801625245346527253444479 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((33479744781787547599709070814821995784628330113147667036121035905237 : ℚ) / 65536000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((145726251146290874746969654298681237398943089055771734712453534303325696939 : ℚ) / 320000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((95967039168864550729646527034955365397897974655406223899131266841641 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((681573368858626953857907148166793153344680551049448338647848880305160021 : ℚ) / 1310720000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((1168756353988718166388618210033976486147813825672596007667029405507006156304501 : ℚ) / 2560000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((966611117279029615490743597322395470129197332172108127660907758181945839 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((13870625987050777588626415024894959198873049850665832002442758057186463131093 : ℚ) / 26214400000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((1172127017854031384148069173825109282520993019716210056576186327112915603631006823 : ℚ) / 2560000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((9723573439953086186647866242232112097199624713052883188904655329988329601081 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((282171949102601227563461366079991780491972936001254711958069368189472072838237269 : ℚ) / 524288000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((18814597817660875656463194865127078493814880796040635438389886169590504037019020762139 : ℚ) / 40960000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((97711464509371600539257684619439656052715692999364819920941641476973380767349599 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((5737902667349419173331338169277545688804778720509191939584582999237240782557376459477 : ℚ) / 10485760000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((37763244192119914890674077041188856580950262542487152517513145092819806142656974558235169 : ℚ) / 81920000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((981053214673087480864514370964340912460433222341741344125475849787862619372887330121 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((116628826449327596179086943680462544921824586277026355701421042100175752574413649443379541 : ℚ) / 209715200000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((303278597522786191243954798728955319520333054161004711118846734734286157961453836285098548321 : ℚ) / 655360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((9843139564278491254077314477213778414259926647767276588014814560393714625788134206071759 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((2369558401027291903569221880728868235433735754039228919459921451599316214389529534869311799253 : ℚ) / 4194304000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((152274108544630982045190202829804744893780353151782395557822342843616495819875402131638447777529 : ℚ) / 327680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((98701352452661629092506086556852871491657932716865282872174649745499563386899963092068092761 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((48121133749470490550112282635547864266778543539063428877004562513524188410255705430217611115390549 : ℚ) / 83886080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((4894582307407847220865733580937571525704626188605038147396904360649281041633072445818367949142898119 : ℚ) / 10485760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((989248496955585627256857890604184923079436024962927676898733925242990885280144794439231739968319 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((976813033107381061392533871273394522448500362420121805199321527463841497473948020062955739983330069717 : ℚ) / 1677721600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((9835667830383646951794246684438138378976424084991858748976298358370523647416573857054527486057454438999 : ℚ) / 20971520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((9910988306295293408059526476312046978174650850668078237044618167086721539234318753162399575197713001 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((19819651935418674990084603249836219131929433556980939384378605286778010416614884676627665643256948737733461 : ℚ) / 33554432000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((79079508826923305922745636308780669694981944533847974185268913508962153361119881737795801486239507969780941 : ℚ) / 167772160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((99263072187818734125324819697387436932307934392681019724492393805310967623320924957431506083061865935279 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((401969022856994544355909392421759257629901578666309791552742115673566589503036207539529301265553563747584006613 : ℚ) / 671088640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((79494897907064334855069941942543978533748747916307401182053863852154407259600438476936658915887946610947833053 : ℚ) / 167772160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((993898974642951299823564182274670590362577388837006162299072528314169500953473937722575438861669188078174841 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((8149012741138730311440831615237359589088173878753770423205453852750776487880550782686564149624166461778862924857429 : ℚ) / 13421772800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((1278889489305014545690776329926785074050057213382008074419297534436461279872171675282424503899173293291380120823283 : ℚ) / 2684354560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((9949489611068993811239287865051997817611778202181574017674021461913009298393810730405202058335759208099209508639 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((165134467318083454338662758978817680133647564499578428209648715713312012791072654962492368013462870159464508895482668757 : ℚ) / 268435456000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((12861709352776612246601721722840393260582344478011595541313997440858204307395283987684634366642057382719662644543582081 : ℚ) / 26843545600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((99581824490040199763250064234765489932007911735861251292323223683177803981402359037024667840961750483853355522022281 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((3344996567324319025271729775371719994579574885000192563659601334680235589772041127456664586934682484224603279922206472637781 : ℚ) / 5368709120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((517499316135660828409498448878900071468103181057179206894670123162620759782332304159493994686486805904364740025097171619601 : ℚ) / 1073741824000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((996537924953042813839947281799623491147093501261195299449143968873029039162030130467527225055322332255821930366822464399 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((67730455045749348513934494862550887017306816203669935682374278169161472192974013175947869255512136000023241115791199797129737173 : ℚ) / 107374182400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((325401838175151118859299396645284708101653297389370960931745664778699597946501799704456032707825710619613297050783476356213169 : ℚ) / 671088640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((9971337480686241455780923546019082883206787096941435884139462918299807415222447450140657896233013588745949761506923182759321 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((1370906976713807585814634875577628966024701408525099489201206364618644938033360483099932186568328436091143638629218475120116131469909 : ℚ) / 2147483648000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((209557467789927905138156680939124555883904620284771173296780708118147014217048451004380357966856036647525974540277689885127685461039 : ℚ) / 429496729600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((99762703002601393012410266037491987190068990375578147684790613500604105590626642439714506722913119501227718075515817030064418559 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((27737864432761145170991697846182550773080972753335987157561068296551035761391548177053400736423795236248187706024466956238836365572112597 : ℚ) / 42949672960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((2108984142866492025876706645432848815583161102592413343310575148378628401648831416509041841133023368968680566688781844917597679333225631 : ℚ) / 4294967296000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((998035418158536932749744592524396161946581171319411484682381489171501390184797972758396401158997716350664277947195449191903321249961 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((561027893106031488589234720430261292076791837234429454888868525354056169841688967074722520927854914959365940783285697775643741068822483740501 : ℚ) / 858993459200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((84911151623999667702782910222837839820558141127071717591552797230604610460780225083354601178303700367111817376799615622790124517824933311821 : ℚ) / 171798691840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((9983735226934527266235135481509475824755745517353407681685436348850860009339942416466763805195342093667149557124831123859767596628427119 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((11343513233424596559577731262938012995933772456111879250222733644860342344652644563375686722919743819571959316198319043879520783432164583968574933 : ℚ) / 17179869184000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((427387554920958526377977444627497695032001229116039308446584405341444489492810223131175458328522482407878079102408296221930754797578396265618967 : ℚ) / 858993459200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((99865343943790951237160686651416950353152817138168862196673727532136270017325383265928337543212237193470331183436476874435015932486748118201 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((229280756181027474487652098646550244814680073547682981869133263562705283913005868773103986229152087230833030833271156029819518645053759357468607099989 : ℚ) / 343597383680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((34423052650882132470895704706942024507469479402807805401473909206972169721472922378856467403458790008857641340127126406668055555867161223917981594219 : ℚ) / 68719476736000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((998885182510645285292453324787080931973752173086900010126261790238556179473436848058620706520254111724740871867670592043447496905057787670586079 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((4632864514037891188718345867162180076566022444464140787291776100946919088257846114261160426732755149532804274733092941006975958376591360020215532054977237 : ℚ) / 6871947673600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((346602894465275922412483750436561610149204100104224278141502286347127241279913335949035772476880012781818023602775638312534444054598907298551781956039101 : ℚ) / 687194767360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((9990770426005632316936221075912243035810694240986445183835321361385006609860583665077320829281183790969129678192444831527701826876973424124782148041 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((93583330490483328145381421220547770700257507207204796147026972114998593534050402342525203382408618770254253740615083213619927178844930637579346604320756449621 : ℚ) / 137438953472000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((13960963130870002849560611211574579215899304463972988660147861972595568325259606596607407523338208778075034739323568466805553178163896281765951188378614696841 : ℚ) / 27487790694400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((99923588356900629951914974287477460093476737621126779676972625550906469723035772163175139145618920605433424605755250760217843424714462978329071403631439 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((1889814050472878683058214613715246144012531873129964539932181829464796261633015340290536101087099511196891161196567573706630175435302167141509861168241858486183893 : ℚ) / 2748779069440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((35149109918599890255588903567499199863938656378138622623649889427353636114191947323623208528164841784566332303765392541139651618773004740163154974069223952868691 : ℚ) / 68719476736000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((999367388006780315371904072126025892113893910765308608945656366935954662837013157738926976986579043692383322311047721043843525713211038997586382150664683481 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((38151879831619294776332497944730021082658431882598180335779421907519457934836716927595025861279057033714954592761849246814573629216174457076085601462756165806176259669 : ℚ) / 54975581388800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((5664017108235479735939501223894140064634948826796546449487835767323345796087134579909398808583096670235194911733276811963410920190484462561508439814130083189819768999 : ℚ) / 10995116277760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((9994762605308134230963993813131368360810927687225989973461089061862768653627631932920576442471887902729241525413164082521980549379674191861017657825352914539199 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((770004999820585764591569457531603512885145842070470645265796094051809248183963679045333323624352164629752348300879697461386754498221487044183141185901277951965877200958677 : ℚ) / 1099511627776000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((57048190545408136047405364399689662457868061309533005590544477760675921212478989126257981406293055010177316788747729924894506241577790339602228949340573220517266402698971 : ℚ) / 109951162777600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((99956639609346043298150904778914598659153670322543970990284356343161861683383164772649452367224759946695390588895585439199476968314322634417365189136096779470028521 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((15536606266094149412909027987090020455445623068483312309894886670617451448973758012931267703391377088869259432230665449200720884491303860946605081638066988535798116122917133141 : ℚ) / 21990232555520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((2298488038648745307437968388510967170044159066386256892538688269691976001492070989436287797545320194412914943524221596047412910105954431026886508664100059117674492801398264261 : ℚ) / 4398046511104000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((999641019325775892465391340664633962299133236600341535828564186165037052876729221152764816148253787598691138685466551851132469820674277090341366400857745237232366125359 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((313406423185936874631021347918519230745162439118131481902198940895932987967200603206739766258851468888117723339807496621833558689145511620369655978000391604612721579958910083908053 : ℚ) / 439804651110400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((11576356639255372811861015052978940930779210507464739040522871338894649614871758060795747933576645076488271925449256297718060419459473938030035123490589804467031546288396781900597 : ℚ) / 21990232555520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((9997027998998098613720974909362504573874524065814227575124682897260341760766441221923739912891393107529563937176977582775525717645362340030936172432701272819046759151847161 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((6320518207538763948091314159059557554658059981796390320215690057359245523109606304487794870451173288335856258129888454026383781201889948775707600258437581818415626189996403036292900949 : ℚ) / 8796093022208000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((932904512243698666675566691127607328669091833601592569432444252783369288830331176548898293715879047209804993676898760582845038631654265769763633020426837785130107227369593431057137379 : ℚ) / 1759218604441600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((99975394803705258422995951274612175367107184740875990094457249706418369437385366876306642738827843537237259835888197407798577416385954813116120571570333837668888119018142645919 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((127436642805976106894663625437909219434849804445477492543918177652330308888658125554135765784066839711401310580548028812150880535364052413683968039394847986817955738193045579319023547272917 : ℚ) / 175921860444160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((9397768941759277897266276360468066404510391269788145434456161482761552450080066707991330028336469261267953435293421483849604967720352830424602241763254968656350823510901594399633173173241 : ℚ) / 17592186044416000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((999796293579875834483983480602514199864280382469712321992011570319437680572113452368942695234755716644787274181318386339164422430259319897788362212030793842060724737351202965563401 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((2568836257782947080066693648924158722139075023730313016404891304820534677489027685502680030032863410356805429658131142526226100206238541866525017020971673126670825740890431127040810200188319061 : ℚ) / 3518437208883200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((378687850801606932108177125950880626277764559806576288548793054024913425107394837373013665770017048659912044838628805913797549670041436718067439157136469505175152083192038235717110347619502081 : ℚ) / 703687441776640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((9998313514547792033692899235908215060676377286466748313771863790674624557456527272162476573848542578102193842947134920501942253300116909433789850753402942218420740100530609351899396879 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((51770512108142521461267866081698225441219658213253786694518054550793303137567939294429796832515027775454034536025525081238215967823311583010529178523445778083408092604889064388829387787241380371413 : ℚ) / 70368744177664000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((476863435459091023311511536538043889974222633173838286974357371336127113059994824240449692912406972566499515551635628040712611037804958568642023269078650258023064505363123414378999587796473671153 : ℚ) / 879609302220800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((99986037586941170246943512774084112487339727554658209289717260322995216711182589286233143554892084004108062825759330006835579915071667893202346174387422958626305307292292914824375106761241 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((1043123583423372993182692105090232341048715225703915661001459600068419732977644899560378279185880525139180997636259768067256743864134177597364888773918719804547345484701560741994265677047209518133215829 : ℚ) / 1407374883553280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((153726878640436592346180487974342386073943635963054029901929624409604636308898117085424988908130596228800973059750658984580475720135896678459538333415931844435030365086794145474076150018244024163331359 : ℚ) / 281474976710656000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((999884405182285948474445342256642367282685604425015314709569198214077399151880656700724195490951563470010652134461493126591766116878338487822223977753474674467181639072893041831001508876314239 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((21013554409071142179206178653192098240404534155503948056855604808341778880015038552684805584580008511397037400713840828734496981275049350246259994183186340330957888453434424883076352662131612342210481055957 : ℚ) / 28147497671065600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((1548660087798545309767054150849992457782614737034919087746206420433892819973457074890779902469082905363809540089513108481295463359792336594105672014093139458518749687727546440347652724651113801621950789911 : ℚ) / 2814749767106560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((9999042990504145367419932988542742158733354119034701790480523392014346787578419956825295614469587993968218189021206701595053231681635764340680192311821016829913796789884481493318861491987005584681 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((423230324347632650269832989129215552489028663921760740060356563173281186272043848833744165880184373962462585564703957814256100519611902903559943052144177305555245434471022266978073128854896254368036324767895381 : ℚ) / 562949953421312000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((62405140655021924584449623917009148725298595584564608355737920687487949405401561823344687643234118109546373789565477247997306549248894920461558752309232738837648930009923051333712894495541051433935282368458301 : ℚ) / 112589990684262400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((99992076918383819496869625212145362332153438751488296123388253162486777054361738822556622392193719002062878386906570282505445705092262492976491312149566198334856323623453622283186854292160419235573999 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((8522567774957508658109023404354057686824414053954447253842212442774295539023245599758387499528820658577702864736322825660449328182907854679487254848172369651311221695406780042102733121273534301799877254905005077973 : ℚ) / 11258999068426240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((314333199162364475739710505628087267160390593407300999018034192851958456891342306940851618315198876553587531317627575100152626277541848739558775859326072476624109916326359452132486777097531970361542380035497785427 : ℚ) / 562949953421312000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((999934404807299641614583627131351454747898319423571603605531347932228027233060835711946276784971799618078570165199495368862584992458841179352371573286258556014275503278572538882503966684796110851317137721 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((171586604281170273757451216496648328326645099503890153865807949207532189822218513082615172820525606320154043833646405993474277613087710389772812508708250564247200665527811559608358903820647346128061821682080691024436309 : ℚ) / 225179981368524800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((25332235947701106248071969953465743297351425454006179385141702300772692042606685710526261941273572103869996541196059027875774036821809782195431942972002824499791602245725762223553540966886357905172619864138011931822939 : ℚ) / 45035996273704960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((9999456937399633732927137849020458693857850186507749306250194029530915837462510658859203225502781529038072482397686622158813341152566746123858284255236934585242186891643302049408250340183427001738054583192159 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((3453967207264085498969177349207127999320212912142278839705594167414094792038591669294904329698429998107598311267637558715549990038839175588879687422518594019983210129186290287716086638182862991824710051869588519818309763797 : ℚ) / 4503599627370496000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((255186764595531649295178991253924196864869605387766953014431149672429172704848038113256949731973267489433333948758733879202699776520712273324339020664730057330468092610673706297894944426791524650717445619377830519890236981 : ℚ) / 450359962737049600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((99995503984731567674903774252040377526449141694097656506445356370486452218352125744695343503937528278906202081770447544852815651402100091159422735349106581431220065275914897667050904566378592147389353894247884361 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((69514840101560097429832921133105040624258188798248067213877999462817270056741597978829992500143434773242093531181850109889759557441403268714765117378729640137914327980210957867676395567324487653984748308500631446163627512310101 : ℚ) / 90071992547409920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((10282344847409893799306602807400402415140520114746640693270832448564420562588100761447751780366362577404034350608093523421760399419539951319991373495506519649293041628282551169568980164166601648890053279216205468609020292940921 : ℚ) / 18014398509481984000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((999962777489592648780528347032642285541472444085434498216861105391257337915737249040332748869098796621064447034977535223836460777957986654708860825955253387669070920419299437785514438905048364388236460890478234624719 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((1398826339691256557161250127547874199573970805190732351760843739816730631679440183902128686854577925458072959065872114796847056828393843066945636344280123882956893717034845395283729943349510264754032700188130896520788430622024011733 : ℚ) / 1801439850948198400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((25893681945619032268261993554623074959042564514695943444557640932568501266624688255649638499498389520579638314968450651917003433237415802238169569331491218432856388689033909269878202168411353221099053447881867064092405440096209521 : ℚ) / 45035996273704960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((9999691834836337539253994185083245481997850364583312210737393091534219500604388684804914827887268937225792557002579014118142058780714171514334658778083542796512238150151380045426274039694895408770209659712269304458048601 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((28143583573539617951337110203394362546075118851981186922369204630858239337203262842528685624201720722409046438377697628470965574988471186960236836657802567106921788719582734526034925275894732097139906609990789567265823958899965529634389 : ℚ) / 36028797018963968000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((4173124673433964270035672910724816943147428584993391204089441211719621420884149691159062041110337637897437786791724233670494403636394996869232895939433294386345361158311725072213066301044700174656384408329745796013223524095902100724119 : ℚ) / 7205759403792793600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((99997448700610038487483817858304189345460203168385241792694877404811803245503733921499889860078699531292336579424351657884098104645532625967176640023753650812324819645103275396084122774634039089208565772757877571608184367679 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((566143574283608073006662113381482571485443359386017594032458411112613280084303608400981698997490078310574654701359190697576807767807695320457654681885417328735879388517784505445190116373861677160958044092227434262469732817941363950379572437 : ℚ) / 720575940379279360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((42033282082903989259304817051713635961433311850905002623324175057945009696501971258640055490977352729090634954350634009799861518971419561100812962208199341813224203374630251252476901151929857842353950442883653474501023054003469890820762451 : ℚ) / 72057594037927936000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((999978877792350508637878528048900383591065022031061416801720890034436919069525413136097588151591553419569254541054207375622448208360364610382255402756656475075237181841810017004180452451195209619557716032662468415344158380014441 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((11386953288221293035251100895351186080280876383716452404523503102753433794861098620355716855830337884010604257572629918430945836254814942647729336979459396775427579742533090145750846333213263080576398782724840693319430108950800368599314403771221 : ℚ) / 14411518807585587200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((1693433575852888729346522639326286174042634624028988413060301985142052932058979413698212454598374582898257867502127146991759450742838542919916829068291657857109070035431243055511470997780123050889363756507407583639990060849205048831330769717941 : ℚ) / 2882303761517117440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((9999825129242869861012996333716846275750427317395157469701447248595103252976600895353751932307026470760613858345387782862778248717015458609354692479422358957147888628468345130777609965843445140440318331034412576010634287228139557039 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((228994134127678531458629503371714944320214520267446329735529665462813443851975602623827508693647270705881962510551672324461887564323614414727321708177829552223726803062581112788725685130930071197578839789484707318739644849759096974757831045837236693 : ℚ) / 288230376151711744000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((8527753426500298271544371816379865790822077962864050904840366284133910419837145750692253855585771062608815122101922114265844336801910625831583158067946812265960406440637785431072369934295102696839007567540934825783679510193649327988839055109721457 : ℚ) / 14411518807585587200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((99998552245001719579326596646841770316937787760714508691658281771118859831393278812633712247569872151427122133241465454320941121128170981826847499037137709806227369955089429337707832907217882317705395462633901716792041263961767392725881 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((4604463631266384031861827975238862799953374044526826780198596979530426578697506465962676186012736686347370812979325325604026513583237378099717398744661463476971685429685009133108899309118219623717008150207596066184537505278459043182179320414339908522069 : ℚ) / 5764607523034234880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((687070716564630684703852336875051026431579392792967793253243256932464058129755973127008850268162028513362779553840367234516582012900538424068592304821713125749907565213758343031673692518545541179766896543684064959348843351100493403550551554100069586899 : ℚ) / 1152921504606846976000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((999988014036369236397244893639203016453927944870955417458238914783093040544104955289794503697630971541665144141106092496323071541820127558544470444528463099485756395858185385486883148638856847708282969035146072313321309624339472244377568799 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((92570697705593017158639396908965072477575014050599749937520660199807212744213655626104102005984117663657569905646094991332134167367919626180793907978392768149952252771021664284046173597676154631552763816399618374704150046193381761571540517675671791001777877 : ℚ) / 115292150460684697600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((6919225232656700917284739869821349982529306226773000426810626368161666992251581885183685227970505236700520907519623797156570729675032873708829962192870076518200294777687656453161683955316263326387123172637641442861081854984707631946329217890720037633374321 : ℚ) / 11529215046068469760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((9999900768207100908132790474438961773222069455586639901136759975489227282664644924844208696112686813393445728344217339777058709294728836057189670810251146000642577201309916806445905587581095842176874700641974332681987122379906490711201892086921 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((1860842783521901621824799951460434922174709990728472012559251118906967917778028338532395859841825624698584233530877778972348765442896995387778695533472812946794235249456609005906734876358777130677832205288105904539772337256699201075629053134718567121211881446741 : ℚ) / 2305843009213693952000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((278709420272727195354210330644346379831311651068898205962986449637476494744264195859611590846101371887642982249712290018903442617262574992147875513456927496974351583422020301405918992938345155329002494068977583641969020713585048629548153327746584632752419717361 : ℚ) / 461168601842738790400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((99999178459986588418431372337880164520505513022801791741511235837075312673180595332785203795116934128084337184961775356014269054251060033717473284638069237739319896649644801240565652359583892477382345646614905500274171386183245836598040464587618959 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((37401521268363284406868281685879363113571531681202230484297840201895574128754240272026417306182663431398148550189295285027640031717526216360128840094430413629282023995032454293826710952737430000185415155546971212449031052504399976625791660289702317162706356188496853 : ℚ) / 46116860184273879040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((2740709935094570290831869004707392552508173640339274678138431376474245843135737611332364190960823679330796044308436550622523862886156241132032116045084066651770799456555256909436124253630502133283581015322186897316779479818295513231922751139696533741951526525681 : ℚ) / 4503599627370496000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((999993198470228965516193331585309882065265142315776033827971521495146513621262148760128702219773097646410227554298538172442133500144526019146961323518575219243829424362409309470643035884995045820248439608324802636769864906211092281195177006320897361561 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((751647133786957957613277553649557172984606980955041471142197011091027793618958607753671643170754324233750178735009988021923999108451228751884142305535087481603564111155515907892423034484156980069282418310616619074612685524261037456115931074406248225624275100011074251349 : ℚ) / 922337203685477580800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((113034421018712174536659599708261879010933482497439319612303454321649451360528488392128226924987075708658622130560646229050776064905312400262989430865443244459089315857975572764423315712136937696190486668964540836961079855228083697433420809837364436436879712630832203279 : ℚ) / 184467440737095516160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((9999943690135025605508564592194780513618330113232309784061776226458317986270429329585105525677501475414630273922037597529648423247696530912517692797410284240119663804296386673107453694091873984345836831517321041029817711558521632996014870435330709256363519 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((15103776451325905629107001536844373069682626411065732055241340320399418786607690526382734412373768323393914411771803226288383207285925980592082059197010776267507148080922409056964022948433860353649046455310083377473433557865467240264383421799824120018682076140311828147196117 : ℚ) / 18446744073709551616000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((1138082923877897724391190148619611072893427317065808758355882752405029905883162004801693035354522243332740189631018042700889570578585997672778515907429559101852180036152179706473150875042193477062820561065725855837537800931577842661545584419920250545171552002587883932040591 : ℚ) / 1844674407370955161600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((99999533810627876988005406258780587872246155007450292702247445378848414608332884419635088647084034714957724037800549269947959296067679579424733978669759743223950696635769785266656609133386624716399183128131900898685860833993000599574007112334102941933433573801 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((303462817482360103343140175518910510035122554354198454410994387722794202925305653551627165967060966790952450110472508957792495010734174013020253815399006657314637165077810890935392206676541887821728599373719227780408108435185243718060580828003627750557244335868606153140716664661 : ℚ) / 368934881474191032320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((45832321573757304031618799248988248690019206001586184825384958658298173172731894041772083151063659042185128124024036400375780285767945385231877279007367724449752985306797439054281333680122728905903552232735218693486650647792737877994684365737661615815920304261013295354247227181 : ℚ) / 73786976294838206464000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((999996140418188193583696758416444486994325917306680973281906600291486024542387950110158898909208723405134997308950747405899155012144319238057372609406940914151087817447538052222650067015307866027068837117804007540220241844628051963873204883014038256266896557498479 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((6096426542430700795154686413389133667097774964902753862781682631866926385107809249589930137851822619948249628194956304739499629643847754010174272241800612286451777992467478046177236957478665918616642721174761948017333127983393741140093888093042379631400500890616849732680884726816213 : ℚ) / 7378697629483820646400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((230703357968268172009183704464876105731735330388115975380319237375940410107688628513222825822211955646211196917044992786214108495664036703211749394009353608976381775483771536956434368319839155577831136056534488504427481484285286642281230377924100962262762609707259925055902856876687 : ℚ) / 368934881474191032320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((9999968046522180054679425462929743907826024269382011777800904743813212797186429838962005524069339021071112642720803237773439104345542818971876987833280063828256856040648167534351319904819733822838102902498299378425483382231675642208906263226473222723633636599529907641 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((122460661531085886927788009850171533520125742547367552173150410630130113057202772047547747375570792317869478060871849234116270641403770935160591053638145837409114909699017937364644305216780135665616830494417029449469541000987820541529184995745434249485067912884341824197942640423566214229 : ℚ) / 147573952589676412928000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((18579304466255876761197290380089692217393261104691934081905088714476126617800275325441840376353785882779889885621486108165391728810759998912452912122762212546985245864773462882999779081646928719212472544526417071122287549101531036070939380518296586893071064418387941056691943240045405259 : ℚ) / 29514790517935282585600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((99999735457157128672690963407595349812891654926213675508413690374029588747906452636766443733770057755447741569085530005526302344876748998268169582271725648434138511160526179016894577492002576319276653929783420553984576921496042641847534953251971810928962877407508105359839 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((2459635050717740440496514327874456600054624613027886285356267997958399149874292947825521645181604016683251992378665132886090475909471645602523623679957404070065482825365775028516055448771351114119690264639023387645895047537978975446341876278938822865007962440347026620629237053758745068563157 : ℚ) / 2951479051793528258560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((187019956439350737491527668455810429679908727683411517912241323277657869596683111164362453401530636138313655044474584457425423735997623783159359670688132018618831288883303379682408075323523925113011235857793245891117986776117737223198135061048854848504028716701764098501870473755722628889261 : ℚ) / 295147905179352825856000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((999997809849803868281208486051481901100930011134123019534156942606590965243917521379789387671882308157351852450459102915752257113234604956662175971627616643386232733897996236080870207056289329347291417884676938766438312333065737031855741877973074622680883662056759604274107081 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((49396813034511725752414363305229823059840346935396869884457559433110215414863782874310684475338241380364822775262517478573700227040111814369151460008340353579939604001308907405836952837752503467438078292237600054253342919134205337022885232899842322376241804568822601396915686740989500399712112981 : ℚ) / 59029581035870565171200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((7529721402938940844104349462627674428366558706240543718307062876616405881541643778977595596288028150922455783459498679226899357239513070171361579066290595707115056660064352709526756912670454289148584400514800382729700830966184021994717326072435566713698465715756902947830493132473631214283095401 : ℚ) / 11805916207174113034240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((9999981867746526225500125056020218659214599562179404478723285327839966601254393159503276340535513629234715986437350913039512936640469294436206154869105038190594620803941510838513524444219019357666225648667240376047342787805451236886733687007739084801175035838167912763785332523599 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((991933805758084312843764141882008726916957529287878278537233430873730050113352547015800740745190626758620193663463887788717598035275379224785451257997236366682611684789476480638488135139881851046989275710270167647909872215401016175515384670947688124702973465251849364316662769618334475892206360098773 : ℚ) / 1180591620717411303424000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((18946191144802953708654259547487134874190725132169873615431725483935057133678348423730499570594263171298322101175133822922555128797524094987344512149249195783872921477433623391345750152523038130096548247792260787533027279595106639217429788182417185855626565102788902518650526249874774483113816100751 : ℚ) / 29514790517935282585600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((99999849883073490620915535338791390279637669775283289679350079229187083491785120967527624823293517336434213651714828209054127602446445288637350756161320611179932865635831768232053468873689261262118682145316083073295950940241330790185268194737071883068928121704192149771378767962876121 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((19916968219988166549678642010338851307706173822716622259426204541874223427398926294620986972020612806737268454560450665373396259871476624015196997419481633832926140446939864912062638396621945664366282860389482160736675113983590519590880221914788077920194245850607283218975547586708161231065000902458842709 : ℚ) / 23611832414348226068480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((3050819734445647785037981809676491016422310288639269695184433123585464345864131892432406134202559975699986582886187470061969498216923931678274330617958134613851866106921826660849046649113919807860427289348043844105451233560839592575154676140109782794209917017920868743860447462708701427513325834553864839 : ℚ) / 4722366482869645213696000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((999998757181965428850559717069853920125120268069570355255339305938439864228489016490161205912047030028338854822547062742759122420654120544628626910259573339958664194599051209193170668805273393989080569481071851763817177834257977611943835384228218119927655919589006807957244819964651405759 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((399872718330599553813451993638463247516225342925001813344499184915404611141398973558231124720646110271636162183757715865891259440304242275320974002434875965933041042613713329088499224650966866285668552976136406193128163402475894793610695324878493106180009146400317252432684624027411684972425877865124210934997 : ℚ) / 472236648286964521369600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((30701706430688514846796100514686100607585279715142788313859748851198439879111566997871108028517423993521715253777249503194832256073893880856132057969263521010210833680579991970214888804907870463544434969646882853073203221874840716855223695311488753245988673600790309427840917003423347420013440772320763408331 : ℚ) / 47223664828696452136960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((9999989710709491785453783897621320604715870699347972971158954113864343635947660567522044623745837361604617379075867132447302774520595463988980402190039007681517780867085544960910259967038858428835598034733793860752642415289821796649283013146025417814881063358277387363078029864487348988278761 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((8027485153978629961068790470410147296399450559062468772297857468654207687743166309546790230571293908813023600189620238174513753069323072373337432936125971587203402011689813756500746409261647385120269696484883770619927193721876650164460571644285156765206613296419216033027593830938862056149452133072223114105039701 : ℚ) / 9444732965739290427392000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((1235775276511508889515519772632247010342962109904918168761479794849421472789536194111944484828841124978791387951706753457010554003959675421986333552858146823142400761805256491787662630134271535958746007658087723068907007763243010147088799857315929392458317104094182752240441542818367688294637822914609612211930021 : ℚ) / 1888946593147858085478400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((99999914814963882491771876888406913286442693519901868228224981108682900962010681838515007439991787516724627281369103989531219670256009846364768749731332944595285707798601226731376042267114708932329916129561079373171126556184434654459414065835944434089400323543178489978923009248090762273959862319 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((161137856888499821149304411802646719584027225572834363040520772677072784296296478787139354290745760060633347415857283089805483502565602354986068433289978886839133194073740746641023732851664378390602521095050051491304219664117421731428912022826211950795924160900680691788407346420633679012047067221376477893999440728533 : ℚ) / 188894659314785808547840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((6217235014564531971982541089011649980792016829722501810823575988006054695666437291343704081127567706785277572962478811556009085418076014536647337391606315293245450321731550733362733640787106191179255736197973352316499426030507528923596093163002036290702072346821841033342584476016414181477721572206905943410341939117 : ℚ) / 9444732965739290427392000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((999999294753085983149379368759120835098459059651267567061474618598785737064486434941065746595692008850963189262454811929328967650049505518053920479025705448304370374864619556109062253929442675250759375636636176130483756758650934504269489051055783969826145278613974718535503593564943420866113700139001 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((3234276143999261846798549726694792263107373539217962113281042595993794418868881987051755066719121101113932488792890133381000459236970105613535501397313125298787991704377480455758491429570108538437289298888734534343392094953822738103543006665580026577924355695920390054127060171568114058357139472988067730239987606526408789 : ℚ) / 3777893186295716170956800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((500432633162730919840504535092792337220720858163006043992282167032591365955101305143198344121665552234591212901396744593751606882365019974264796091221506987680496633312570166422841523245950042423402903624638386694252815267351705819583117636284155114929662053004779523970495877604038482334964614546063259271968141090894019 : ℚ) / 755578637259143234191360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((9999994161260798854493711793956761393780142554852844187701948367379347117156883194877083316065734141277124243903863387962914523174759856183968407645853815406511882333504185305026926400281855908401036870895710902184275022204871086760847099853690835486190656761645096694755434251124166581350555323450789279 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((64911122846834048365555250567576102226935359769684498419856214793168881466003361737601857982269487898341368903308512653530930347763910367487278822898921299727884218104256585157233795819746768749524528809779870305239016440664249194343391353423622464235072491380101530254937825209772931039261397456883091518889087007949970087637 : ℚ) / 75557863725914323419136000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((5034709020222011899180280473554002841152865005438782113495586388400393419498388133077417620080253445953462650621832561969624129453893717480949739031275101876760964937445008793609653010713125294776320439648153884878721465446125222869564714229934160065932576415429999675727353878557623571686962276071329277225707507303425645801 : ℚ) / 7555786372591432341913600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((99999951661078153716353439942168027579105800211626697029984430533533614782941835970387372773708212955633311615280084988944969337363836849347074446900023737750511873839081150140317923667933485065652184254145590559183612908834127727293053139688706426990172447329659755535880240165056975127001247522849084440841 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((1302640836093248854469141025941119790608887621699170464873471719051551000988007387845849973722277068249643678355640636319953184803994978905745103998638232914527680562276548492984295437449361390054641844579445385613254067867941860393254054617729504866534863088559428912363738453003468700506459549297797683794019167588428909154452821 : ℚ) / 1511157274518286468382720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((202597175518383432105232671946219107772793357123920908754470184661476427403430142196863402391071894973559465643831788002593244369573421474230245420155656208390141386702374291013740513482672099602599007512229916906034358166099857662931351338720681714314090034976941514309400290915513268579237008342635264384998757282735030063299041 : ℚ) / 302231454903657293676544000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((999999599802066034617690129281209100327416919952057424711241100387124796787975459998837059193530295059688186862903823623475401144035205275744429345885296524836487803513752842011692090046821322858534433440071344239481131272237743454259186943482800509051637691442253116081552508326506697076443328241667570085722639 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((26139350740663357129069782252254029495284653779876970524009235620660696533243222466303577110091120010289749341103180144463388599455078018857172599372642415247458958251554347864130739206406026085388547494421611785330260358663825131830998033171275840551646747443961780692591311822012684779184620549371691243160377404207092745302623169493 : ℚ) / 30223145490365729367654400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((254749054495204948293870036576238385521918473242063884158799794954768410236136496757298455228005753732617659996122733802834050332301690176373512511602218760826669784077184625901362779866651879130714802201694805600661437019756555421321912656382256267422740435710864509842237186823725954204149559436389303795944015768262822703095706383 : ℚ) / 377789318629571617095680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((9999996686761304700599856580319130141610684680283083419184365070105006192607648833330372013063237312799158499037980755778752846071467464477888130554584369929121282525290359779014798813497633731945806574450350658958664285802856278057811808705094105414438508447450413548039173216435148945095874314512765812739697728281 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((524481784614868868040904841921782378709588330678835423293077510616910991625680424966678417496084864044222613922116556364941658176517495398327591503220300124462403407003749658244534125070516391120760854099907960385924851283178318501560221949791671407212218101613222475885283451327880816532689768415650623266346601273098455977162576383824469 : ℚ) / 604462909807314587353088000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((81997729828092481239079906588467144935256999038862927293494270303541066843854920088570240830385445950507119131696583816446539265884829109233549206383600591358184337073305585245173892053145733009488039859960078061205679514280011692767407386757159718725376622972205330601648523744309817846084629450584802610679328105692026820102188275244799 : ℚ) / 120892581961462917470617600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((99999972569696841616266212628462078442394858468063647627427358415399346268598724691142149896150541712664233213535442677092294812625679138412435832861403998643195098026878888610463519376946909666779332629874453105518781622161847126040623964269474098726136411436441973764216315058866598116448743449851188163671957492438399 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((10522827776138951374487715229145657327501098258355280339694468141302881128855080177832343119145608776071891276067173939642880870076685729919051243211318113606438119278504419369399386150438817782507961542786555168294234736725585215805873724421119416241447341203397821105117050638942663364814329021745377237026338183195803993144009455724058917077 : ℚ) / 12089258196146291747061760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((824728763403112680557387536207318485494952078811236885588205358638027703220915042603441237657637001328176202574906634111697814575502665111200125650895051246040209862181000554330513504120856020726923205773805244770372497971838914719239586045735840909017557631672269432665882431996260945143890359284101180430630704427822758558902925605263409671 : ℚ) / 1208925819614629174706176000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((999999772904520151741067974351037547424587033257098938707471100321091187757728841717965858990230334839147186774859929923647108753727997586916556260259563704767012216564530318806027476921743465131266094842730597260589993049877932356490325800186976063353683350282303100793946872372356565806079147021317986807040136079897505321 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((211106622770892202031260056052638502394474368649574523669479626244843635716174110173217431030589846285901964351596547359919205915522130886208389809126019508586775550199088248483045486134768791347367776259416247829604761968867444137960777095203039113493890368124675064256694130707204796773980285156368241430277929792556844199945766007969146992320341 : ℚ) / 241785163922925834941235200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((33178020367919456661515350157259754635019864082479637076684644753579684268858213873536877757938726870438628830772668295145562509138804307988990174932098560736729384201745658520786363006900352207821742778211235516623912228705153862464502104538425799954257861752484812829247330064325782280565774681963109548140990761643069184183180380783264646930461 : ℚ) / 48357032784585166988247040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((9999998119876522336264301759652239855128156048335522113559153239558313943446237080583039346580116942133299559309065359837874413372114092022082169278688927911766094140937746509395101481435114147821751999202966614720424552459939401979383407299747974828505144456987187371473086156370740008308529258189491612775485286605471446552559 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((4234864027208986102457124409800577935990160128623803765416616378139254049936639215597226256409576402924779508513233599805855261370513981661376678120695213806858373117866715659558596027679400395922325226133451644670881751016572663013418391681145968343554220368605940775830422648217289807207813446441373106061526138414762360394238230524119300297033565653 : ℚ) / 4835703278458516698824704000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((166828344648921652871093179370575322556401352663319594402858894119295034542507642464399199416192230749817602172966305497824783958117954808879917232550652482810386840064428261688423423709832301918005089435199649040734129060651609064954504554071730384631033280744190772398528643039629611024280265203556516134763593059890432010205771584075419327623916747 : ℚ) / 241785163922925834941235200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((99999984434457728421932154268160893760606003924169787578156229670303281137791396790146982750336788163921587051519752114097762268307732567850818279458265634181511493392823603351282045164801310029816284801401360603270394869815838308987315229034613483605194090959396924248425680288593356528786313728550801062168242687806698106008635961 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((84946628456141927755552821641136151041437023844238397044679378843159920904969923374610839827868056704913826622698589661014182498523102383844109893286810574032305217662608188551409633911185628750785119852383975068186243347584253421681977124748304648497554664711251596612886509137263272267608869870419586657095954904646271300373933821961561704056898723441749 : ℚ) / 96714065569170333976494080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((13420826234054868132425380997904318737755665258320232738049544924691131092204789765555603061546494198383467653436778761483479561972713240205546980282035818249334950019430247420414454483725652765118071700122616992358794855945822585178649613275514473704510147504094198194094658975526618781640364492101251441800486549800241719592241919029970252050711423909179 : ℚ) / 19342813113834066795298816000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((999999871132875533605176305186104039444057106488201671359555425440440864539774974025626870190038269209106819199532027752615373819319717929236924535634981185388733653799186612145264051919390045736849021870801864434475599127205325360105982781177565030767401879052847135852716207109264398701821891358672081993690881212351653619645497121119 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((1703816049277306808819407787341397875135768829242297000670803968349264004043233609826103568852796204816176280712266967813746490527036862053261029286689593183309182431232445588318926799631592882204597337292502006558217283558922418550311180048374088235686219503449524633512527392921279239133762877447213148938503303288144208934073393304511999643704941898441839317 : ℚ) / 1934281311383406679529881600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((134948725977912186188630985520085191507691988531636772564704362897029037937971655599249592833050568790924030801121647492759062184306503153642349364983238389028953164598268937689292045339197658295576299597324661863003227725774214182361728388677530126664064138019359377075106738147040840218319037388523917590100746667461687298072547245712388503924952915653467941 : ℚ) / 193428131138340667952988160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((9999998933109076542717254630635755342557348784615821637185759367221409917524797009958164858303326830782195356152925657763902679850147944736152498230522009233833325919803465961950641085840630188655373052068368635653023485174132888656317431445369060889723320156678521437724637478657599956852383438558446166825766805557059340317045070665744201 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((34171963965875080362300250784500477563561615388983706171909152209623901908937716711572010180285810874683581193016337013307717956939159114404949619467374625664008752295418801728130366851151514555365793777471468991012387476884091138824520659407842811479433170454787985228456993746050034479686171415221953643805729315364857118151893242157162837765691397341454418770261 : ℚ) / 38685626227668133590597632000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((5427358328644836798140686549171072974992564003611323032415146624049616328365938139438173147485372864540236917779053090619913424473029788078591490057188683932478757599106487273120040340305794484660705234222484671718168464553966530262784728928513904384993348505004617344613470706832055888199659013336600543366142021137390260807029767258828753669167915883717011912281 : ℚ) / 7737125245533626718119526400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((99999991167210044697156151087033418481032290587834387334260901801226052707187794445443646861893242832045795353590071520627350286479374834470606532850491714446906105290052894698989357549674577331877833498074023934571381433756646185185652014936210455106019367577141478982922273685806270042780882487825375815150523383206894278484816140041696240079 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((685312447443301969477502927991372969646692954526115508230068522578684171168042015652607464585399880073892430383769131938800468286629371324559498528844733024620231359005369005963444737963715356405282075206385377263546734092833942427051361603643105608668998984338376222464018231381051638149014769940727910603447071872105907692541243231793628164747749182625263539191341013 : ℚ) / 773712524553362671811952640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((13641385734459595045207033360078625481625622511001676150264888283176314956186091118494637242308093731827409659215388843986943126091279825751853143898229058593463649252377539223436351314191820086271909111972186777731794692358851757464884266349474471341610960452282854183527094284278495929025534250457592974282720877143883924839035641357900707018150752320242299382494381 : ℚ) / 19342813113834066795298816000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((999999926873331960047755774849549671604466333776680892740346006012350490362807750213827952369614157406507139732372202119273833021762744254582151485469220903905935645696347915212932891153755825730616583530554844154316466890071273767152013031656886357822734344171154304499613503844790109684182926116706286373631183089569877731575792823405203171614041 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((13742934952505447688076026186358025038602801992680027443889637538871415958003127451551741579201205305682628819499772841267616362145037853052982459001862832130429916220390792577640099662738595779274388704384394641547278364886893973754601512298538690992672270154236350095917501112378964974756545409014523424257848333988879429711716193099960952845097127599258472717422167852629 : ℚ) / 15474250491067253436239052800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((2194213250012923415149670729880402996941778050249410206406598383582095813542184243744906182685420315948851617127719962026794687863771960918738788963868641741467363767659958473022973437158562745698721131905932210647891971328490110581043329864738037935323132199363762819939538645665382028126088932266776083790702813996288523682261027476194753913277923055693460341002100919159 : ℚ) / 3094850098213450687247810560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((9999999394584315297235370059979421731213376777337141110997324583776249709713685364020281617668035609168472609844309461345468063587173759683685632148199679863437241210720064390047871405861944481223774695049463554753586029382900075518251515889087362156414417635392986486952300198331017318075350445320211344887292564798549017739715988784971677057792645439 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((275577194529006245933660817124367905099057359506098839741922169587968545636171424051415095800389235331936393185143500523038998233072274304165524796197960155366882288304966939619099990644346417354754863066744535561690015311514415453033686875198378910388689789881877787584559038958774963598353714927122072936179208809857683628731435889325406957130516554352668987965185965997190357 : ℚ) / 309485009821345068724781056000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((22057165051280528621908305709087704386654377839763570585158034629090837016368968996111391069483828464114958556732438301059993059935005998198448362977260981786732001217956361239049531519378877412094613815420793550393694181377045507775682770460836592157847671273670455943238508483841980556877122503696507522627158011919193864491577333574285507238845592318247437007036093216748611 : ℚ) / 30948500982134506872478105600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((99999994987763546345811628726569632512715546339574191257946850229083571346719601128723911512673666808305784736901038030479130098438211556421233348554945149589396919983551413085206327369131038360051630700314508769804938737261029725215604300045754271292954963603418535125478093341982492376345826336806029724321895143967187317867108671150780514361465311589481 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((5525615626150711746392925610904201836326038092821852772656409324668271692030363643136680467028588609914687280742306819352883993215605452518332174261729408988494553790064355987194569937185583836787386963666798293998382551681927543393655615031376205561909583082847545055133281499830375392646508575697945433681523592607316911672732490481925013192127679117295315950295047908910921290581 : ℚ) / 6189700196426901374495621120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((886852062204565824532642182446287916948473740822545263519219756497289475218974743773950641143113867471933647301576518795932165010999183716678960935903743349481743717636662925721955448837551380872190676784572279820541272355394569022175290129592434764385154536349867615666170777545668700391540246808743331715008653658093011413319793334918772095987414725117023633566714206477809892501 : ℚ) / 1237940039285380274899124224000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((999999958503694400196974474227269987572772008145334729424541973046582887179491577744705263413425287505963591836803693854336718084969953475611390892686390893450617100543822148932423184289035866582867450567903818105215087805784065095059988000078799612034374143672702052303833134778273054383767096242417120087660969896904343804621792688457311878398571314649313199 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((110787907490928253632377298820954264283369689194681856597391056663609277211316050837391401424406459613452360581996310262550790601015845959742899278056579561084676326365070928394190607260628768552908319449029520091603917353392936491244861840209341962229039159645534787740012050262119290147805482653066860358732261384015338391189550167293225770564138187836367911974594865000505182922799573 : ℚ) / 123794003928538027489912422400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((4456905933811732687105602492228899401462729843928440691538600226236720230650535134798291946387814487265184881675746896656155205794328566412544755098349588611411249668622346236800411692567461813208801880702548089671791642717500655100244118308918014980530436747572125873099504260679460663689493986383041905658502735020039733049676237293595981898715028689538104771819646677576878302937577 : ℚ) / 6189700196426901374495621120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((9999999656452085939230751672127568227114979455435226224905782994852659722959010772148414875799747955261872576816897781420053689025466244824586705200550630206877658975402303571011531542728927939439559623251675710093075711944086274922001640652652381988032583535466300291023434522829322617243207789790971337205745169776471062358463821667738085041261771913981663974521 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((2221155677708320694145063481895277080088542815321993437663611051658796008426625887253963037617954904383892296302200728793132858560496376826378121596976315950576669551682238962902803928765793980742607427596300882783426484679354761182177590131476856099815235847177373518003820234295739801420163748535172655031409717347879967673964818548105653119695273102478361586622643082557753151202658689109 : ℚ) / 2475880078570760549798248448000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((358349407176558183759340215043351183046109940176512637872717399426464232877702154679601677398247123080271129558783705635834914441812015107417416754483402875387985434128175491247662072398367146236668929848507067512491282430820615049326447761058012676439764665055379728281036163953384849475702813953452052299061881956343185773580369093465646960902158817128833664518242494516414576434722146739 : ℚ) / 495176015714152109959649689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((99999997155766819490891393093544137352284914911548237915994977414385169846377650182616726756746113321613043063467096732376624491441835040902753332355358667482740138657355671264404469642252794410620114120900623203860573819185090270079251582963309070478921759090125500109383014414503961948156517291679451700726364260579403925265721979587203606056606209675854196045059359 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((44528824145225113810007013625381722039381171355651465192022806378620973492271079083162143205205209639242146372320971219934717227689835456228916438350413350367453784671354704628601549248086187679124049407548854712281692895384368585571939648393569633751247659734561978234620318767567170567982670448351458440037719579532464488842525380626425085933361668506374575748682620275809097167020208267626197 : ℚ) / 49517601571415210995964968960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((3601314530401341323270359190310670458802706116014362734031624992527491034804603324021038891983480081295486566500930767683828413301704757577679745614553239769185779150094971415003197207004790729723398703786751945251583082318004095459589609690616878662178727770212666990189205175236794340249756601203388887322366982327427665346255304317508732469101744050486955665639729315478136495511926957539681 : ℚ) / 4951760157141521099596496896000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((999999976452593498565089843421451913139566810552707861706522418013694821158160565861883880819101072189634383522444093847346074164646952303633894838570014408089605607944247602398004604168210884925523924806936259504761690649033362345986123855353235794494993243507149015405581976337678300968787806657814180630313569713336885097274912269002458654542642809906396889057046433161 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((892646824951886804086418976698595390952455865738761710065044994869417991668216332127784657118574356237676346277861382916919635276398292832767183192266447475534416375832935957226967265816287913568110120935495168780545821580790224871533300026968664026726338042825403189656846583434182629947540985659380822319215840837554105474794591949780820156578908592001959303386470016935554045176548589299797929301 : ℚ) / 990352031428304219919299379200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((144759382559874224078730551615375644800570635786801659902956643886727364633154811765806551285024947184401306958744098781430140478926031697184715700105134709839505633436942470809849163185968806460632823328153628636623889844713123011754596002398129416798894322517198810199184653171733309464725527716349913766940245422866536204186749876708810332947184332943603143210248854770170761594064856213042279121 : ℚ) / 198070406285660843983859875840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((9999999805051021574620378813686200388882473624565868387068299098735379424368411324770536649301337776657983061182314652962178148009112118121785015368521149284573844828170425900253080117908617916298412573476625292439922036883347206862419119398469439142624049062995686698542813182099638653720594251320043601438366043656716071720338998675071355200958539823215059844503287420139919 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((17893484150047557235919914577865219224347294124910879212560196844848393413984137521810030006785467695767634146610580749778412225533374230795895269724238875866538900143098121164931348387168543752943722343355153642291335722608149962375383102242425705293102921765343226824368211245827770131160665377783710515353336912164874991058005863922432375289286553138614158940840824324573430754805564545681077306725333 : ℚ) / 19807040628566084398385987584000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((90912568559566977603784707139159856902132179335650866597962643909241160301524966999997732295564226942944585422752052169262925968990855909202572912234911826021127324689270374226897942001873467854926468278735466120533255806247253214048469581537680116944519730126682723827892178087294813254759230066701302168063113168636190697293920233349183076367707955432394693186056276002482667236544179432634883272399 : ℚ) / 123794003928538027489912422400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((99999998386017407616282116198508053019557999137780824376538448238430206254346077357775272919565775452951441763528383011873872887367439225930258142235986594926986861332422956028195250296165447729034557695812980796110114543357231525613967889499928486661784502192541290177235950334602908414152799806678640976308232475433952357772686570030915749708735751196397480452642716551338389401 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((358663808779289796539810403124219191888376134211940082278454555297793867629789727204702068700176357105552831778362208415484464107496926386237720340700691296925796170386842649404433356464476000943666827470603458536907527998731783907196985905883366549984056697807677482622329241765218002451580880149103527514408192160034770897333963143863412327391355451675105607179717868528953275280485504531804907286701423189 : ℚ) / 396140812571321687967719751680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((58461884152105763454425304568217078713325104845606714088917644528922036637532410732548811274839206128430944210315844337752069178005219276571495802942975766300883645641136672992170780127549128905533845154147569079370782943867754981185613653627416216430796947771518084503839147384273110283909039893759088067542841248757358058065860175350161904770180713739095377305654977715215531963135829991312463460936103919 : ℚ) / 79228162514264337593543950336000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((999999986637838117655199640007448170948920674861687445013361812965963677579731174445021484501085054974984986360251482955303793634515029351476607159571733019400524224971129652957428477201953741748677103163635668010995638304454519800558040157169907941072913893652049341377336432820177478760771029599492468642855856664117691570000072113285951491838623284154974740667429050328530525850879 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((7188829129506127006903945192173242678552176832306577484029400476821324669500234108507681479877125408989792276746610246026990837726237568470531398810645127545064261524959588828899076776437636903078522548187457094832009920370650409254548604721616805854930724901166903816410592818302442636372501498112212432354830766733141512545876669366456074985172227952460583981600809122120229949272976108510444923556662858522837 : ℚ) / 7922816251426433759354395033600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((587372548623836215183861926713920839763603698770399261130281898094327489279672405777479370259920244832540463698319937326679742686077232210855238044458168880323823641011884840226116348692300598846602352012020113739020054389772359685408796618240633011222917464011609458032671514293750979556919879685823666293261212903097871775849295237586792064048735890534608364963584660820199657673147763627997202093614906689151 : ℚ) / 792281625142643375935439503360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((9999999889374661776067397819621663407286114267179910357265622449545213286682594393230332870184483170137900702076522027386960107500149928000874830674094377667616940058535982396834550362754975027937297737091739695463032889522578969428820014461209667844142654125545316497262968327318249346660423354054198147894203637322230368508030597025894392400931962169519035877985645107669904223519427241 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((144081187201785096814358472878789635817561095436997293469123770869883381732454629518452009250666612088238990158993545583763285293127874949611812411148254564266527337701852723610495203723290237469266806535616395057009495242066645547322973960302351512405914918539839231850580623476772209583652007004698745097491413387319949088239498367310491800096691179890122019410490608672590803872506721587516112421808501290864494421 : ℚ) / 158456325028528675187087900672000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((23604055547344673090324899120334658435860187557917984989647582187930977702653287565310004495910877399036762722033160595506285760544922903882253780302710020628524505725007175064455600750721738319776931499810386794028472353838147312845590097728379789935560927232131595487901822418805328608063469311637026640592492663053194383001324658013690499372558279752294838126096478321463199676846854918315017334662098912271440141 : ℚ) / 31691265005705735037417580134400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((99999999084132824844061986548647751348921740017982477847802088259784820800445198981553925832257336165571679912491525864736642729993741253919242723150827352710200646744619398263393242453248438256292887965382512938738449292357431287901200899724354840081657033505389675280840114781867786341001644948214706466416111913390745220877985312777379674687315714801448098033843155846399137066517338128239 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((2887589425506335212486753336580029899117430574348319886885296096080556298363607871005005300297413768910814197864219973527949823958894433417493607390123389017546453947519512114684907911890456788642313944745473559570060575712591530720879210463344189680576690363824088950190736093904403583267635083175369410543802881798318229824912541407225969909990934232463122731276886792311401782875297374681233028399764447726032491982293 : ℚ) / 3169126500570573503741758013440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((118561041608123396377401225630173456309794836060773627845046292533207129747564592804156988705054965665864708523553978636610739824900482173337930179338470220710943553413379824924258510652979583675695087091560646537694854788752911675627172225678853340354412924520025988468538845955218613546091540762450290649773939029261091941351205447921224812404894819219893633077667562111420450598115927866740862957591828200994477049607 : ℚ) / 158456325028528675187087900672000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((999999992417535656883989186636254733417723085608876934101953488702758531406885802368284951965258486114767937995517342634154665161618183841197410504965699653087751154398703998222632654270443820323848819465401824619815621691427173632534042248817933721036038580391121121650075310279083403117152618526269554835458990530961979683648840404483926326736286802841188803622187487252338455773697042363690681 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((57868626384232992557079907186908654304252639180327309458343855669565330146647487428963448458405273762229513969961035225728661207995793150362527695635447679374855233129784098530185205521500834168663446962386871028243329680837933254936879375259317150358843648172831689977512989666283257396528671793304617934648980170981647583056695594558685522075572505042499402693482994318332138818208748105041097648480909789894572119186166869 : ℚ) / 63382530011411470074835160268800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((9527741921897412694842012542803931048936074194671916555992406133026132717188389653571073935078691353083438844157948944194905193271292011432945419662755998378951673652048294990085259081241328498611265180166735355207329951935048197718465646628138938426852573807096235319491164287925891682612025015233911430578426022741574355760921175726948507306328707678980906402000458419570524447835051471179021545454924270427168028900742699 : ℚ) / 12676506002282294014967032053760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((9999999937224777703342546476161552937965329425755892137430072932970137881517607557807031117320375006544163758664888079668166472873036944021273361570611027427913491807266870401285175744705004388461144376354061706027453531983325570503749335777963673276457363407058091766140973493800531494406906528778985644482764982605834229800928749708722426059049718440722202105188090206962110075350437813728995147999 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((1159660797490491673189443289538778126380753191305155016497111714382006971967334172521170226657014965407790577169204447773490592510185691484854302027772474144866010688301381695139335151722070085386345142852932309334312245551792982904412943879200039944283269563230013169019549977071884163978500133689548845196742807551937493204118085933875270387039215673272334808127462350481077938038687711342001583065140497413267373149820244376277 : ℚ) / 1267650600228229401496703205376000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((95701960765126083005359223973664203950332991077308326217076907067945365834153176410896724620281903936202099711170097997896348545240952437697162921416409192819940756412568968779412585582197993940650347325721811113539876736078733706237955338679312216284845840405162399500184015360665049483934194841100219328227169504792605253485673480480328706963360128905684251153369033337855144416380404577879774036279303674438667665956748805021 : ℚ) / 126765060022822940149670320537600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__apps__self_rec__minified_sft
