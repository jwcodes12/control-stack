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

namespace LasrTest_closed_source_model__apps__self_rec__none_base
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
  | 0, 1, 0, 0 => ((0 : ℚ) / 1)
  | 0, 1, 0, 1 => ((1 : ℚ) / 1)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((7863 : ℚ) / 12500)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((0 : ℚ) / 1)
  | 0, 2, 0, 2 => ((1 : ℚ) / 1)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((7863 : ℚ) / 12500)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((96641 : ℚ) / 100000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 1, 0, 1 => ((1 : ℚ) / 1)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((78403 : ℚ) / 100000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0, 2 => ((1 : ℚ) / 1)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((78403 : ℚ) / 100000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((40571 : ℚ) / 50000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((0 : ℚ) / 1)
  | 2, 1, 0, 1 => ((1 : ℚ) / 1)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((39081 : ℚ) / 100000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((0 : ℚ) / 1)
  | 2, 2, 0, 2 => ((1 : ℚ) / 1)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((39081 : ℚ) / 100000)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((96641 : ℚ) / 100000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((0 : ℚ) / 1)
  | 3, 1, 0, 1 => ((1 : ℚ) / 1)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((2729 : ℚ) / 5000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0, 2 => ((1 : ℚ) / 1)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((2729 : ℚ) / 5000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((40571 : ℚ) / 50000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((831 : ℚ) / 50000)
  | 4, 1, 0, 1 => ((49169 : ℚ) / 50000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((7863 : ℚ) / 12500)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((831 : ℚ) / 50000)
  | 4, 2, 0, 2 => ((49169 : ℚ) / 50000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((7863 : ℚ) / 12500)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((96641 : ℚ) / 100000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((831 : ℚ) / 50000)
  | 5, 1, 0, 1 => ((49169 : ℚ) / 50000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((78403 : ℚ) / 100000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((831 : ℚ) / 50000)
  | 5, 2, 0, 2 => ((49169 : ℚ) / 50000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((78403 : ℚ) / 100000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((40571 : ℚ) / 50000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((831 : ℚ) / 50000)
  | 6, 1, 0, 1 => ((49169 : ℚ) / 50000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((39081 : ℚ) / 100000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((831 : ℚ) / 50000)
  | 6, 2, 0, 2 => ((49169 : ℚ) / 50000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((39081 : ℚ) / 100000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((96641 : ℚ) / 100000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((831 : ℚ) / 50000)
  | 7, 1, 0, 1 => ((49169 : ℚ) / 50000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((2729 : ℚ) / 5000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((831 : ℚ) / 50000)
  | 7, 2, 0, 2 => ((49169 : ℚ) / 50000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((2729 : ℚ) / 5000)
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
  | 2, 1 => ((192002727 : ℚ) / 625000000)
  | 2, 2 => ((192002727 : ℚ) / 625000000)
  | 3, 0 => ((58219888910589 : ℚ) / 125000000000000)
  | 3, 1 => ((2982998692401 : ℚ) / 7812500000000)
  | 3, 2 => ((2982998692401 : ℚ) / 7812500000000)
  | 4, 0 => ((3540664112991506319 : ℚ) / 6250000000000000000)
  | 4, 1 => ((41871334343349063 : ℚ) / 97656250000000000)
  | 4, 2 => ((41871334343349063 : ℚ) / 97656250000000000)
  | 5, 0 => ((202579533728178402868149 : ℚ) / 312500000000000000000000)
  | 5, 1 => ((559434497254253682369 : ℚ) / 1220703125000000000000)
  | 5, 2 => ((559434497254253682369 : ℚ) / 1220703125000000000000)
  | 6, 0 => ((11165416762885925982763673079 : ℚ) / 15625000000000000000000000000)
  | 6, 1 => ((7276335893316446704467447 : ℚ) / 15258789062500000000000000)
  | 6, 2 => ((7276335893316446704467447 : ℚ) / 15258789062500000000000000)
  | 7, 0 => ((600320248487044903046704980488109 : ℚ) / 781250000000000000000000000000000)
  | 7, 1 => ((93182609646725345437227535761 : ℚ) / 190734863281250000000000000000)
  | 7, 2 => ((93182609646725345437227535761 : ℚ) / 190734863281250000000000000000)
  | 8, 0 => ((31721999051367898761507867763383070239 : ℚ) / 39062500000000000000000000000000000000)
  | 8, 1 => ((1182304616121927953672920113688743 : ℚ) / 2384185791015625000000000000000000)
  | 8, 2 => ((1182304616121927953672920113688743 : ℚ) / 2384185791015625000000000000000000)
  | 9, 0 => ((1655313536013047020653135703028214542666469 : ℚ) / 1953125000000000000000000000000000000000000)
  | 9, 1 => ((978807722430589977749905205913625537394337 : ℚ) / 1953125000000000000000000000000000000000000)
  | 9, 2 => ((14916583152438301530980170853934586209 : ℚ) / 29802322387695312500000000000000000000)
  | 10, 0 => ((85573741094585330674918368607557692210521313799 : ℚ) / 97656250000000000000000000000000000000000000000)
  | 10, 1 => ((12375640613154130172536961209695875083274497923 : ℚ) / 24414062500000000000000000000000000000000000000)
  | 10, 2 => ((187540617776017140328722083424487651361367 : ℚ) / 372529029846191406250000000000000000000000)
  | 11, 0 => ((4392613031198421450812113132777223130673060222139229 : ℚ) / 4882812500000000000000000000000000000000000000000000)
  | 11, 1 => ((2505103272082302115604736547191026370105038365270917 : ℚ) / 4882812500000000000000000000000000000000000000000000)
  | 11, 2 => ((2352775933177757466787554241966746402654428721 : ℚ) / 4656612873077392578125000000000000000000000000)
  | 12, 0 => ((224252742351251156680898241909904719634536726272410659759 : ℚ) / 244140625000000000000000000000000000000000000000000000000)
  | 12, 1 => ((15852960526742575118474269662771681001660493053325427159 : ℚ) / 30517578125000000000000000000000000000000000000000000000)
  | 12, 2 => ((29476677857638390616135695254584526964071773033223 : ℚ) / 58207660913467407226562500000000000000000000000000)
  | 13, 0 => ((11400159963057610677700722572526744380292789521597972877082389 : ℚ) / 12207031250000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((6422147758009135119203917359417697087381458283044036682106697 : ℚ) / 12207031250000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((368985126682881711099489424911798135518496351360232449 : ℚ) / 727595761418342590332031250000000000000000000000000000)
  | 14, 0 => ((577615987517460322804996015489982546252858763680751357596109604119 : ℚ) / 610351562500000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((81311029010713009787326678275744618167370557602860038770839912513 : ℚ) / 152587890625000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((4616455159710886965435466012143968739581936810745507746487 : ℚ) / 9094947017729282379150390625000000000000000000000000000000)
  | 15, 0 => ((29189463112383382756521493344444081884024732901291763329031762748711949 : ℚ) / 30517578125000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((16471926827338001441183213465432524018621897419718805363456077714429677 : ℚ) / 30517578125000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((3875770732025645375638188003322186382858931358110880029609594409898751 : ℚ) / 7629394531250000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((1471995952073131221814833506477440846116767438538308130022147646477992482879 : ℚ) / 1525878906250000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((52135288376235798995762923990692800344827789204445462265137329999060776127 : ℚ) / 95367431640625000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((775959255685393709096639514131168756494637980543601767960528590741937813263 : ℚ) / 1525878906250000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((74107859978590256800249610191296252567803371748937699143128552165258633022883909 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((42238268542910980058490801999056742145600434819719397001881002753804320575487857 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((38846331437045554466020332107695688061469685150610662195128496217857852419713039 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((3726005597542947808642926935071080262928350595226151391935868489896708000371423072039 : ℚ) / 3814697265625000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((534599264407149620474235417390147035110218095393537564793356712812783640604544742303 : ℚ) / 953674316406250000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((972567635793625945984179782932252719508698455252781234190418071912132068011550411879 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((187136553615493060544452188682768797347266111998920188122230120503599340283069005455694269 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((108239155578098748385372997233668625975830713474252325899996931564271199647848094310049237 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((48708682061781476807324315010698358337876376820868059936595225034542468062744675563386137 : ℚ) / 95367431640625000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((9390756142613075209348969747048612877175933429908190952306998218951528834624392620342972187599 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((684690189584251511584105583722204192650149811235826911063315294777767708407534161583061608949 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((4879861114876866926186903450223233790416002466707626960867798689576746591261547671923916856253 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((470914318755900386818497051607509273039904795184805215126047224741082476349546232999934724623079029 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((277127973807855966083600093428093860888254929229488693801944313351373204099093247794525459891201817 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((244489711537736773942694989664611395713702621230643087343657713847481652871232324587031261481396709 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((23601562390942900218613243880768258716501977445442732382878861954970457147977440219040351712682939285559 : ℚ) / 23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((3504358785761155804452676010912946812977691875020825679829386296733377152548697205107992023388070203293 : ℚ) / 5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((3062901993208326936450960406114505928561296007369798766537430464140454130657992164134247688237095873687 : ℚ) / 5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((1182343865997807686019357917486649024387201726939057095505778308375106416950592727126686109335259529754414189 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((708836166895234629078202112787233150382613670468758822016296713580914134744636824333841971465111617849153597 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((76755975127513873805928722986656400401507412667253970845908569251953712782045392047880782977182626676126293 : ℚ) / 149011611938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((59209116899140219691991370070350837568413161263644485421764931749086442442102497532256782141840814381666338061919 : ℚ) / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((1119852913834874052007131441033339753450890506198898717690143590134990016367030955372279751619552306476592231311 : ℚ) / 1862645149230957031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((30781159183047777266073660999973459158701695747649222521275370101380236476215912253839424423928248322740276243243 : ℚ) / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((2964185277302176056248781875124203830988090365627320418046425045992186056318540427381189908276623680278585001510115749 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((1811188309594287034984481494901846580817010066587485400988900104150605205341404616879693325396086272179886756412032577 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((1543257944555973131186549476987653584097969758557005736849404970863634501814292276774290322655195176714642183219037179 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((148360570664784494934319329455664073627017814223866016680561510540948980490899503679282255768690899332582472096266906052679 : ℚ) / 149011611938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((22879388989969901881473677090264276978935667764469093237154952108550153488558057675627852482544510048781089015569533991483 : ℚ) / 37252902984619140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((38692773680572747706691777678134686792586005211911807721685084499471598872672822096671053014018719668031863700637619062869 : ℚ) / 74505805969238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((7424167201408867251792769515345747131121739740876468162747061044156841087496283763772160398791558476822203475417644645463239709 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((4623114343213756337731136278182473784293203196864756041372233976160738590303582038969267069400706195699445497538151466238686757 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((1940510533601411408917337267980223643243652370089039306827685450158929400068433481528112496472275403058532876240527657196050607 : ℚ) / 3725290298461914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((371457411976753928663109452007092306856740103027099189830811013622487199760811728580000319539372318963153617201169260911089098233839 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((29185424010730994257017753891150796170734334213913941855184272512692711336293279635221819728344888503823160844565679017983742669139 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((194667732872506226646767686505808868344041938626410559625201258231918373112471888380894987612762605434596245192195212621789573286233 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((18582974883728622409322263577379741981484802719912441230625833633677928181495892640219192964031874352654105403468638084423795804445082069 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((11788826014821740567705491483209841682348642857326996283369847913732990252554868677523753499321136979814228620425770628899056187023484137 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((9765642456431598307815574405672486740551239934176080691664785709669575632530808002815180303485961365387079153149719043512327450175226449 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((929558685128740878245176055597873511930819931149567653167720696351947224251469860306332877743737174361529710324126115723157819582141424621399 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((148771809612787161798914527942686817816503572928039579729915529954980939011673356197296896290307867936885342156999288575123466993312888682873 : ℚ) / 232830643653869628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((61245423544825265451093405171882234873024454817242805679993274021881934896972549320180229937504637400617864858099043880384093011135278073591 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((46494565970407493095113162751661326252545295426669109256667596371694850835106383702488231182941160901021621877560120641004235898267059738314778829 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((30032307694746511503785054999857705469293168071980403102743242668094299304412840457374126996197635826249292743349340881966927142449565218453112717 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((6146381834339253085384521250512927958548993306921223915714738386156414874217187114047837172411576870957511313748210185915138539600463985696259221 : ℚ) / 11641532182693481445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((2325403063787869748553242375997651667392015180755392431652261052396031793231101093193650027323105838915348221194491654526182854628592880643168891871359 : ℚ) / 2328306436538696289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((94705970085274990680727900470914630145971307589422904371942079458275438971415522331587260649316603790600027667374762629881647543660162429291292524317 : ℚ) / 145519152283668518066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((1233802641344841290880731482170762372420564430299854349825491521492885414523506563262550323255059528044052657412466288797960303869836443547332015217223 : ℚ) / 2328306436538696289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((116297529091061030878123908936600725797761447898427026344563883156759405883179002451959575258525726990634592682081720915781764595136641760574005112112905989 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((76437975435973896029539106626524471729958976181037087671727350612684223360743522088792947474565470420618858537847017824889669601383985107587650343195380497 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((61924052650538317707405644411515496011967566979122505463098934508760913183270234993977121061721335498397843080178969797833816566716493612438624881618956519 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((5815987122259605449234880734466828046340979702687082885825301303552885856086455308478451927813647269737036059704737499274181971389288692868247961403532708879719 : ℚ) / 5820766091346740722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((963755515221518052634032325511474238407073165762251355655873672294584411178329997155359710354186123560156500491552482378253702752251928264503544493184872133463 : ℚ) / 1455191522836685180664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((1554131851180806425477987563838223629710014605001458145485158469610202964960496025637324002417570125520128908927135318901087121103816683027200042119758917137859 : ℚ) / 2910383045673370361328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((290844417012502870954834127528053680668099887517717639760818299186444132067283578320279273163327483380501289978280905083052836761234831558357688042102725531959079549 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((194380665010305016648165127542636641419458876082389513503095435755462131799317074881873119945633050918468816856291212886122270460726399147123013172667963592800015477 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((78016870657007234137804932251361687833444263714813557308459818835617668875521013539833791713478162839056198426855276720760210311527805192540003761934099454237204677 : ℚ) / 145519152283668518066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((14544049016379674891204864450440665878385480536481322362736159216293224882101762056032050391509359328230317835708834600124536640240058351154129761556149677557111816382479 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((1224899328553634656167137289514964203823570560577779168509367435910531579023566738556371438825694577412423728497366759815220352954005308086235834181237308351430244511729 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((7833553359292340859478086648722336707184812331211801284320393971769759353406217918707011972194836642580356027707672200074485168367884944715258113887562549876395046388213 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((727276621331810835695887008743828255351977330845583729578568715564232426691750588375276316433926217305632224912543128561652576031179407364674198556094548568169583502453555509 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((493902705417840809107247029463606392847347461470206570374930447959019087549104588013188452080308891016091092573370251259540046223203384436146119678711218096701749458591465657 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((393311115859269670913877171131724055582589134600074133260999725911880511584979000522827828986161140429671318473409028624713946149918762134861822027374428640792776301376019389 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((36366840238466449699258554487995856147885072289736177492732111359156473783311013120973335434040820562306804996926787268874806662160979736192196909619311929959208172278043200555639 : ℚ) / 36379788070917129516601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((6222267248754137386864377823990546002527180123740316734511186449582721665570692056740079404823325137237790827410591306003764455857649324215228204370666613114219310755005669879253 : ℚ) / 9094947017729282379150390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((4937286850971664040383137227214999250349117724908196679572915681403799433968784597336470281774823450555220188986879801811309449164209406968864588179245576019374792940611751324677 : ℚ) / 9094947017729282379150390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((1818464097035499944960654946944979879775845267866886457057634489952337297862711113331009191894470131033349385530316686285519781090533108877053620820165104310375034757492490689742829869 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((1253991477654134344399022231690689182051928173089521297573182490697590396011712882854940698768720216578656703724251615920031342456514812650129937954698875014648299153214549028833699037 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((3873940019674069333907543317135475654195560251544364464754679485602291501139068983837311144843663709834284775779282724227334415137073733119921212094021088793664928770849201758635979 : ℚ) / 7105427357601001858711242675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((90928157966861148977600538493129778702385818362627450449285288891856276511588052578952373924350547686154017920350478279289823038624018760250942450294918446976225535146227839773556350615199 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((987010166084572375531528568295480854256327871253688364471729752285315851187872244879260122753492328247573200074897201085551375239540778697985476221814784176205685546060662827529694368303 : ℚ) / 1421085471520200371742248535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((49804372665733290300393986798754918535217376825932715428369160570429939748879495419424424150966240342880402444709490473318200345197307075558249934267791031350474722576195696968176151471203 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((4546608851175217710700321779236018251734495036790158292177953455631500994351638881180676762484826070174954661046539254269067410500015065122140986150915136312272446186417609687452954700809238629 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((3181500682068051319281008650657102725969163261566390015656826807236601051352745057835083245173789019533909296058698958181320279370887314649048397518621389111668113987018946091127508040647003617 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((2501324348274482048000340752284207443210871742659041846873547731233011945742231707749338081447380807404605440876704269825116557113746128372397250585394014702098814814430656516047592456971407059 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((227338595416114459517327271506946996491120198137613512071951749648425626841840341048381236930771878493068085553319144084950333911396111207070381949128777995325205414229148842629653825166531620417159 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((40052359747982655308829970435676053775092288445882613055157599151661553605067333414738587617893730691444543375309960798778732958628167723273889954271126389876776974852161898501230462051736249536243 : ℚ) / 56843418860808014869689941406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((62815721973553279232225636318879124070257863692582049335968145736904789916936960990694079151712842797254861773745725538639916574441495372207879816185606341619646414166976847219635516349302386844849 : ℚ) / 113686837721616029739379882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((11367260540381414825902710562386471594641237558641117798271154434986276106600304476673875163518345882342265298983710994670519997119251627782052466058103652048338908860690797694327685340831354371944557789 : ℚ) / 11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((8066256278585027831378342228029296506354171807034765633767967874710029412735792190088331266226338808498286591977270058795199810851523683555691068045954068369520234005248216237853244683200666390356787397 : ℚ) / 11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((3155153255618788359692577723027061252784712283297623686697889687527933117517495343086732710431508147907405129643068733856956312225953900712170447786028690271071597870380377676251303731308834705503616347 : ℚ) / 5684341886080801486968994140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((568376446671526135342960161730487789066189648991628790193659006581828207920880952923135789259102810792508045445068138764777666803125157790745650600443323267253157871387086353256568521962868878224162654057519 : ℚ) / 568434188608080148696899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((50756993558850523645170857685914454727009392748915395042137567720886378954923877401821143786245824787909834488048231919684047702170583262429582465505724965314138752383410449635374061793315552653817350880719 : ℚ) / 71054273576010018587112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((316974519818544567843324110518527494873123353286567608344158257396005921352418900358426524560647735798780481796773204568884180874493470869268196771928677174691710105835826847620856752661187941040201114658193 : ℚ) / 568434188608080148696899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((28419366782296074559062301296762932590204380249239371646946939556031352223558061141044542106031060136662843911751859457825794719869590776728341790510586068275727868000045480437972241504555553258432503037767603349 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((20437685757545009395345247106867857948492602254883411995265827172615598175459469095640276391481682107742483401307599745385089772857600273567310757620576328191334480718641935944529866396275403305288641769154378377 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((15922752658137256137481499051981437690441760600742032280914047908112667794269418848690780750013450764680262089142086341249525838541999506699679831309643187571825088619686682939845872434399911667048226355283711529 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((1420990427943813427038869854670734563117181911091890547088284284727747991061974098553318117783786140804548240343684690063450317579829167402645554782804987376014555332629845186848971810081323351247865080745269435472279 : ℚ) / 1421085471520200371742248535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((257129266202204651229577806843798926112973150064370100558459590755349600096735846192936191095718659632289247412389791772573178613461744446623088667340103625894213735190735785675135983382187742468873659292984127200433 : ℚ) / 355271367880050092935562133789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((49993096394529415614459982952042656234783017465730818786770545248402207803764992136859629273670789905006113147969616168832059097282264973265687054077909051152879170988660372639949126293894632306486818935819506287543 : ℚ) / 88817841970012523233890533447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((71050417563072423853551650311834653210227187314909091385918781715689463745375351152406669356605987518581326658983631560564242834531249150692732803093181142832286524400125449075649635306809369683477134190916326266545831309 : ℚ) / 71054273576010018587112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((51751998605206110943097745588042378014145485430177414942065962712007896529198119761739725675819889384848699611804776664105329690890040088895641042762293165235838476063788552733714540241852736142695171697206265102149824557 : ℚ) / 71054273576010018587112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((10046116646704499410561310764563138365232065430793566069270963677192448139693671081695334421829018481511414674089768146584222366444873455517146053730386466657661755447309268887230672365168618717502235611893707028312366891 : ℚ) / 17763568394002504646778106689453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((3552557236499609773420327076700857777892127216553176746618110892987237233613623371604290982466861519616363003881624916043651896039767309292754862554293452145848696581437489594448181354032562937428350811259666272960030922037439 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((162727307275893278323967154639224392587201135360942673139258739262028388051034329210789407124357982299472924604152778851513990085429240573445964711934351635698410758209807724846617192255725985600446774730786644745944019341307 : ℚ) / 222044604925031308084726333618164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((2018835948448180404265270582514883017250136599059232832056792867189180492338156091185517304784250366948548261818689009405470047116041555051162494970012954336673265187964006054986696501032882878618049378885185129800249574861183 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((177629336919435591380330243423801204031861493302778933787043377039385201804938313809357689449663038712355463430481404468807001074229399505316357528690239647009227469005500390336357165714455110934405620763615920360261414537980937669 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((130970398606705521352290548224034799359349839709950734605787057364467175134433831949248035548790884029725745334011038038833736781776571910114513513520220027943682803985863130220719570321549715576816838991965559241042929488096693937 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((101427767026788859325914556559757410599011392734902512901460032684052745075301349288687356316062270025146961490899935251067286758824514402975146261990446091128133845468159817227201502447517950963314410227226206875690543027511524799 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((8881526692028917541036085985695573805026652644787044122674136849864897022428152329559450818662279143598973506838061060703968840582560967330189941296491712718811367645022156336336346570201158305719770440000661504936165849220424622168999 : ℚ) / 8881784197001252323389053344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((1646823377018288688951957099478186462562587292408294240952244217468303909221220205472038224957792240506888140609679694111248655428964223809334602013154321925156901953981118768548018339462247540595749556812629853035554258870322125847823 : ℚ) / 2220446049250313080847263336181640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((2547969139091176856219823138530442520005205443090695358654648695856030822572103278762646870122755489747576521959311044484999128955149439968595063642771773348950206728968101157228844318389608972279770514832404372800067492262161257751839 : ℚ) / 4440892098500626161694526672363281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((444078762615830021714610428513081882656236324451655167101012406135868737096932568162556479163947327134953954145926975293820719831275081005553136108339965276714895996726193904721501916699631193621356806521266837916765184668721847346018458429 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((331271183179524976664916101951084822542936566669511711799465791437033869075630499717282493562107100662263478926731792260468938661671075845776080026756524032221491095214203926838445558931914159846262769071321338686222623238281647284268874517 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((128018115052578470644510636597736074166914966511308985118153051615977500612173414094975111486945615379121038097910652397895817436918681353786964792797307806834143485704149185193111852771084938970494172207217081421951609705280682255559253617 : ℚ) / 222044604925031308084726333618164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((22204036637763080218845228894575582951871163919328101784455174329338330532759651222923078916160507009192216873654403314645600424274661311476296285051460731241600045483178412908456054262420737156412066997374316881121080307194714068675314876922959 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((2082162782185977290710262635365907585512622554024068350166109351083303153638403375592768420017560532663997466405467601265520282904436840072072341867702755160656071779233332501692887222487585105922530199835871455521464003807847271308094703760109 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((12864331751262646901848432262469521548959264263691467211054290862496170600401758140536724265553368925802345595460451854872728583139557950996542466296336326579232061197297626036722981637275371395312700267611581385320128395108903780540413316912173 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((1110205828414497947951858241450392870471614991371060417497130877715585408044591809765212234707547929869937430781032796878486654813247284067904816580822813327202955445298031390108970577480671727172793970150473410183963349143196744480226199871641369589 : ℚ) / 1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((837474449144399658917323613357842790009566044087436986257421695334999614762696514762415722130076851969087463627530301047465428273598283465866602031222378015616156784301511067332827555832008209161817526840657766100490526561103147254650854576169374297 : ℚ) / 1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((646368546053805462545627391913276458669265979320597757692232722384076011616542151652990919869270339133925785739858505865450370545137621005348133454061048757882302782198270169070886598378290201920303140226702718571112085756424258645047795969851838869 : ℚ) / 1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((55510453563795197266009263712312233874466391814915292198276096839799015589777134313984425574319927062753231504217281602157082072428255561918966313500562359497951105371186431528111045298968332643127424162974856724573577038088635120307257154992362005595319 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((10525090558348358656013469735959262154335566219891135096057820774327061883088020182067027502113930266047494876020268906602212513233590623198405964462959215631184117225590915438717088160647612460389499441605836276314473060905219285506748960187251485734413 : ℚ) / 13877787807814456755295395851135253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((8119309077039639226116562288921064388701772079962782820887327038931504523760390464598369501035561792215577160329395138767193260057307965193024380022668375626822992946415325410000000713639637440008213866652833143263129443032475272171742485048610453847667 : ℚ) / 13877787807814456755295395851135253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((2775529256496264999261982987993636876849100982322928319776259524887485861492848116252662129975733760862961355357599331881114976760486756402614382305031315487191374296014404713526993218824444223664322725716052912172674594012294015465985730035195118929007687149 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((2116161897565235595958158871934455309815783393461503493969035395085422204873324255943135758658019208394305037616166968486289283454917549780124352473235934014221564808023774809424982309726972512686004081656701561418545946245246563981300689189586526034951121277 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((203982329131474753576036222267270980889165143464209800892516516120344467176810391762567464925337106906266590819104436519715282001127444574226845548901650234692386870798380592906931967675222749621173770822713801383361069349038006941834257316635366694940617963 : ℚ) / 346944695195361418882384896278381347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((138776729713286469834193969301960703547051125953823524861642625184210188886626340924486755275245494411971205148213162493748715722149708194010468104497425500630841246563600413632503641880926526598285237305025982699757580953672780501470507053257901170068770875322079 : ℚ) / 138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((3323625911047920788501669419911498292906058018419344335271799156441769535697407410158562635858311912900522040026608709946736385121337671865922088701625583209847379752678404810048683954744019519566349589876512470106374319329898269726525241513188345076328658440301 : ℚ) / 4336808689942017736029811203479766845703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((81995387665400568048882230123853107237171803511900363004161425062285722705182453677278183278756015637969443518135403064715152000258519062028561487256820984282537880757752359847759663648367333167030014492512838199286655031912598001252849656729701163323326338763163 : ℚ) / 138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((6938847313596570495099886403353390794427723731072574227161702946348591573319317277647352148271984953788083764068156215533879145563335811139198701467565049986093860214331832381484305254751070110619030362702209144111864816871458377725159941657726308370860103182692067109 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((5344743059841828008427049867134040050692334420312771081031355988666810388587372887711012213394283836109332653432351495132179785006100071124439440734684666218063775157796575499097690250268928207845026007708900324188628754800718657370594618560039963522183270416629763457 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((4120013076346666840003326766174019992349458301702436153115160792055626235184381522709027491245898763291170250431587212103882922653857735131140939949684258484904366581361149922063309505651126371554007150876359961025794247163731185912169123994061380971714364435890445739 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((346942804979867717929537635010627572461742804493345408970177450236308708721138021271430724007542701560136346392009165820425010814650097193728430517240581642985814002755656771549199748490505665457924680845191327185762467485291937842687463992995614056914165246224999854679239 : ℚ) / 346944695195361418882384896278381347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((67140463406740397856944405129575070750665207383219987616500529438793519898470222543396927288899390358564418711138982119815700354732016614043559245600814227453605439642952393356036947395542767578364124501111113959696911726904179394036093677874043882169603492215021486796203 : ℚ) / 86736173798840354720596224069595336914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((103509202216808910465563226102799388142977922569843497990428198905582602895348480979884011933200123080035202739236497862195330412653800068883739025818274131535736898797537667378840522840666855951829097106922919546539013917016447942195203892843698625342578941332258329986829 : ℚ) / 173472347597680709441192448139190673828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((17347158071835276002761278577025028969396148571099516587329069333537280621525290661003215903710014944996291709470203866500463113761169093246756154514967637837577459905799750878522582996008305353293462226570257335253569068345779210215673101659825057903064598204594469104191405469 : ℚ) / 17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((13493227251922344562511843597958138127673538597836144319317075589050526856498795184621693003121844483157488918283730064193645866954248330351619383947612662343986514883507255692849307656961379564237877960162883442028718421280883986848716042767734809850884607754494540816368468837 : ℚ) / 17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((5201031413980279859919519865573896883189687049507546572109987991915865831832646971167042675897667638498184947383432351669415895049339307199484959626647274019508539817662716445107943074124140720010726050571139702584793042575896475022683967899858478641635144970427175538177684487 : ℚ) / 8673617379884035472059622406959533691406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((867358626682282123640128192498925336669910206178078487464527671930941012095902567407561472429419016333444550944915641067790288988404391282114143944826752034708355125838201692892539714731052956488469055994181910348572550671856608337660073407440762424185233813758602206026149511282799 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((84732997388433109269054932545688936584143552347448634790071468281774354400459597121494711960810124226457811379207807867424907309976120958943353481715263137729312477436110981017719984331852121692824886066691087475838221493969390909131717931790758436084448994973595010153200537773899 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((522671899034340229196213086570709084483204155649274950737504488963523401988509336649045269548019093000138384646885750281811940002800909153905147667825705754938283582457510739259782680686154656542296454945960092213109243228912922153851979066876270699647201995145852551491719334686153 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((43367960670619525084808658865396044151661880099850822314923352177910207801742863062292176497933958911664178876386172473761319814548554558706652933985566156800152675810381680882343228766353549497693678070739954284751936953307894456867206838213279172311619121058000250100686911822254438229 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((34050669007507916841946242354678441538018729984307598615027214686947117833181278480449871522797431187298725443469374537994655870343091180597722832357813216692943164734020672212075891779844200778957972369636237808295579890704160694417375032907341685925188110370086942866989468178314725417 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((26262559570257778039769278445158935025366051465125038576896753338984718060427270975360603703522016489581295764751698962309052061794439154323417619625765195604184934815848611340470057082495691212542074235809274123565740876814327980146655619549784316114042691817910883731794825142304337409 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((2168399223742337604546022997204090123158421793781047712138755321209995040724509697300255892697678647005127401193863403432970506196049407001287616184728404547538994210302995175077547134279729856670930213007990685286670834132654586009559448633150949299854699360444128146834968699540684813388759 : ℚ) / 2168404344971008868014905601739883422851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((427569029936860397136782696463582101168218489240349087411493606150586554855734650202501132893552503475970990994055646496088722813697324774273665633085830881969062335101372402202196686506999826933291997479857269701678556813557934369366140468894079586861632422096500775415168996145962543049193 : ℚ) / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((164949987181905470916634122408344682647539618638211579529565510041174082154065266125594920841739836761608496537574917064855917481828235943750603576633573960716750603731803943700975912844785146509599415392459239125037192507657356249111468601248668247501899554214050311466386000684767687860581 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((108420009475182021570549243938372501180727713407990886729181442136810708797234082929168681822637520387645023793836232140679046406879920491449239876230616100898204534106202817248071164784862920014996309671947190092765522411595929208993836390495567164044405007752578723045241515109065123563995341389 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((85894506286791838016651618720348072221705188100466947764530222155198267141648535621683625459804103129301331495138988818517544138755652104523117471102298178721152208007159307566008677184037153472825679903358048635320555303027556261003398944674360435693777673416780456995573636475321638196669141197 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((16576161703371751189020632750153036128264540582203180399417364313140114317951585634577031767169554197851588226028102436562050941986207543123968270660086721611880111670247376681896594763817798593642552960769418048200002317530075742286066862039242518259523814905063471673351471971135979762107693761 : ℚ) / 27105054312137610850186320021748542785644531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((5421002432854191927964380621763978785106673201300598265489620288932547266612583978519302590226226839647146260339729774179489591773525254258587111018552325829541056153222754498571495226486673527928415279700569449253590009760858443938088936198795655412445555569529871372668493509489881128114854995493119 : ℚ) / 5421010862427522170037264004349708557128906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((269590250468071508960366866410848869471887945222118736344133516972789581006138648181043834676732482887921886441072928132912088457662117015980717579611033820586671305209141908427889236649883992852364236781600000519822783301162383185621875046949715285996765936604504450554122239431920171635856570763097 : ℚ) / 338813178901720135627329000271856784820556640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((3331511513896666554243659461925707781578793794856880741828134158262114883592155989367691392596936451117108372414763574521466010245385301650308294218829225846255410327711522440876047882508564230739160886111976602463735037259361075942748310681454455043271635066877607914591395793306132237033724834473143 : ℚ) / 5421010862427522170037264004349708557128906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((271050201125156527250724248502599785275731295481216572229179384742282375153739144592506625388068249111324370928243176668236072227843693090525137681133686411230310189192400372761544132833790831701583736312731803125667400286007787929012206230521338535738328635011396411460533450173513967248747782022151330949 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((216592581425935561877294855569566315379435779488302495515497088796664401314408356364769449368002145721606478293080152296217627488760417591228980332006735733555165280156580884916167086562620762414634867630463020021276396212268924868574023492916728004002542006068789392379417700356435417924078352146866244177 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((167391561597008676588743529939223772480945934218991259913379127669260136980400337307435176908460603457454910965382015848101161385888425404688488139384122511313052652077308597709891613625560452230178836501487931173450951773777779789865020138520677514465236024496398594727111949056556026564781565351076105879 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((13552513280940180794153201600849645987680117240530937551910036818379138242362350835262586298619316934695541052929753920607005686355846472375695360861274791390024914685724875523308607013199727832964953765943841984611452097003621964067954218978481225733439731051047363809365302606989635165248946264420701647931879 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((2718720838316707679022515651001416645613902637051309093380981106941007150495225425813930515418195554499294870858457022016007175504049770375341030839365320672726577356809452560051965663395595112077299472849529089955892183749680809657981326125196457887999884748022694012956823051479940792673179475892418528989383 : ℚ) / 3388131789017201356273290002718567848205566406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((4205232063664136035555981324280001638597970886184180316227158204579939896340788764604201812918454597247127750359208971896721426312953947870719777990637758576667914098899652578081497799644359864636112393471287428752545266508637565526829094356768496840033651247753293244602331766079000551229326948690553449437819 : ℚ) / 6776263578034402712546580005437135696411132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((677625794875596841352792947890604492329091179143705667418542103758460017630882935737438388721284307357532796058413046312946827701143047230754336485502779561484700813714543924856153495132526157911221139238107613157671223027533946704200970618175961809231383328472042597109759692068176488289314998893812286558244262909 : ℚ) / 677626357803440271254658000543713569641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((545969278133238089719373598706660676008522092471584476355435080784802586210202069391483807264541681249435312635942518770044648974796201056884775426238733160274283032331693263260649851241961038092108827701653315985377167823762232772433605252970256450164753749205531727017878696939277222162112120946350909676947282357 : ℚ) / 677626357803440271254658000543713569641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((211285569371584272894787466745487755033233936685569237681772332360727018647303307424526751456012535103621852432778701509780499736069363381219237557276693114414256239895814327766495532243277009260565481998465648931840591018355169965040224704448026734137470406651995392993386290517898039700817601029099022150588476957 : ℚ) / 338813178901720135627329000271856784820556640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((33881295051626477768184332975996390106429615357945532632837671691584481375302551585803612868811225633802463068885875701962565746663074569198934185553333269588995796713212761575339003451021718752616152840029263973419879189450079751736137578950016946562326453019439240207340060466897988306385798820120858277954527990481039 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((3425983809009350576072006426813111388973562191825469565943149496916404829502586158688459827552204648095949330065149868361298019907675535251840547069023135071640001099114226507852294511271388939896890464496182415027379343882805741612372367908374845457702757080080882110492535994239497049782163954861485736004465238586089 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((21231100790991575080484409365343009876221240724629394395001494171821344508879190565177434728518194814138246469335060182166701886343644699260608631286679834741457059318742226465671237676121444159320030804585188890243188466024557119456017942951228336091697475214933719821335478234105596799715716422505957246186112838636133 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((1694064967925969745416015087525483305415258781132520704446857178199273993877399820387638377700540235188999729167768863104323254907867598346969958842084284080495148468451754949873078709011402151512389936872827268665617918595179185607686837715581137538980146525451669414451993593202518283578378243931123341194893155101806233269 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((1375772939429347670824437052702843991253971645641384842320757846086768376517377691060225852381296931239527707690030993727984190862201002109386297178889208173728193219407459030185822462465422430569745681000566663677761639281422420348402625989602526293071588185423129148538759608654086871808520354792195570457808623288405023737 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((1066687935154558917762064622810004017117818426640558414682218524789783947463614113682170169100078177316905311797008690421820474285976893176299101748649626596358964876950147910914791139208147481542041122438619773239469351564094341576771997738823822029895481087911453774165798508582442265432173886750114569010682667069020343149 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((84703257133046114335423573833813071304367606831593122500113442576722745205599988112946876621688617881852908012065550545005498774867096332534918200182201489429768668513556150071300676303301596689009172128867475117032784575325014739289462692958842331093963524684099679813731832069819369283058383734529605075618010195635380689956599 : ℚ) / 84703294725430033906832250067964196205139160156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((17263286911787019121301863495519953208191652972915594004366170212330977748473765735620593106901284436889599158587387463962736826332999761735686720446643879191233250195582190354637808266037707669147655356664545436658247633045213222337649119856103635149732355312930043596977969468466022523401692411371056875093237102589296897992773 : ℚ) / 21175823681357508476708062516991049051284790039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((13397811599070073835474515657435287718599516164254401873869638103871747858431095804227418181952650412588741200209384013784611440693421723334587636708752605527185518150022355271463445997508542389936019652523991631981922117324454178074456234754397051184368349848401222736098464025820412484876859563112174440684173755767331456754657 : ℚ) / 21175823681357508476708062516991049051284790039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((4235163211110893694409991099902464521907755317877845822952102478780218495736397117730367731418528916084654330957511451161418090795132965307274166299592096627655144650263486564542739738301249079269791122440282332973137103005511172987712790916033192214813194159958608109722914158904641631182961686493600607522898291647123029972229178029 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((3465662623340185093713902294700780979428231021378201251200315163461663980924679939940774624365540259369518570672359489365234797537783618191464438454915541021531128479001088030897996440539275820385850886966445010122451755458895442964829021794667836523847844402538316088404450275630043341686772773582208083783676066861425558062980556317 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((168275697484592868326562077231303185737956718475179386088481130843929253240045062231089659365066208875907768243470330389082148557534393879160173793505954481193524893207744496631822548730143713960956462974085095452695533092446664917376381256309842682623408745240271146735078517578464781546464278563127963334300654857393906529850431099 : ℚ) / 264697796016968855958850781462388113141059875488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((211758174936284057561283813208684608419232398057286145382989749666592244590521367463438749231381136654470510861277197085069893361649339535481420200940750952280596873605839913410063493922619976395054695628524694531053145406036593799284495640254382641347186100263680689619568350340920215618723938582731870247811506590415428449003309981814559 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((1358770204339427449475574722907512874962594029369541149993292917438382170687832296654545961642484738610985987112616685535268501512390923570519217238942994287384730323346667615049676591464093678104883583468757885323527400755906326717894277358384737787278003326369781774140141853660182486428984153638591963878211695405220253924262604847599 : ℚ) / 1654361225106055349742817384139925707131624221801757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((135263129953914841696855945213071490426698362230062808993099921460279162009104819667537943093982810743048214840439813534074992715560435989027932312402343228761763175352155330631917561418287118554680935334633756736429144074746503190263441556975347449941883712214011612890537308272097123518671341977573836184571897190493060481409790389607123 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((10587909330255179973587648800416629263222320474365359329333277133723313955282042399359173495066364095208523096152877162938370643575475354294016698972367206884976095759062531126959686011934615062323764056344875381819357162268310647030771272620760558142096687273797789258555507541681474067867248912240014707823960633879744347604513289272198473189 : ℚ) / 10587911840678754238354031258495524525642395019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((8727570682049211509531287143258272979872962709034688793727852572536498212925126609220661010275192234993601954569273326596396051093962514246959062416945039064246911076351387363484088949139044023902885129260949648479787566106612656281399812476657046024581546280266421059819030553868346321608179989795009002982688590953182378186986456867092088097 : ℚ) / 10587911840678754238354031258495524525642395019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((6795282505799215070338527902307738442274352974205937608424216619322551951557398223963723868836028638101511032966780003263948756800261074902863391967782702631347672563923863792718358577056612048567767166475012023719577547574815059522392136408977526555149666903670037941966567519120869757006029400149557701373013234576215758779853948419022041219 : ℚ) / 10587911840678754238354031258495524525642395019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((529395490183542880421864660218057366590474906604637149600380386592288570479747742184401027868337457706704990534018379377572635380500610599062551494007909950530365181040925950351881421190199267693537431529967939115793139430387631260685421301496876604383004699385250108008855496473559084407442155618489636711125906877135107926662708659062364255750919 : ℚ) / 529395592033937711917701562924776226282119750976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((109481118879779933817548798425003060766277862938681056725370184109292788632038731870659538597155268891379674299279910279454995860262565720606764504206201943667842876572225582160413167154033830182018001712863556177098640159935250961095679576803150579949683099044736404991025385017572506309387571441075562472464381653832772976483821910270811952715363 : ℚ) / 132348898008484427979425390731194056570529937744140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((170684928382212250278947789022308408157231046699969786328099076221624193460533246743167354103168688427046439602095336057443350770785559820619056550266194516571561447700010230861612125396015551699945920675412857676077305952070338389513171099630559004218290618472726745734631886368959320437742928573736627550144150974980023599860012267735724134952809 : ℚ) / 264697796016968855958850781462388113141059875488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((26469775469524516887267479166524520457556264567814741608937032664435739592933845648163334101646318996618728170955659669727499390022290272614566776663394914602967445760011406731726181139107574489594507134602329257866843459830256587877268227623029780716422883658758982132027276347428765613494335695597743051007089167912248463692632753006819180220070534749 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((21972236189142122397130797011677107650905149618716488983836822431137460299063520003149072667292698091835260669618944907384853625814196383073876995920779546641707399058164048061723833524195813176331902110480556132092276250962077539602083461548880347920426150092911720027770267541285617850047694432063942212941350354764113732609988868920103036308775747077 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((8574364863203188383970349941420237207676447143394902340243868724730684582967407581483831787047173298166919407480828789492886317168511575047666834126029225815683059682824841958785213277406692887297154892536154029441382996303158855371314129254381791942285504730297853266121199410774566332089584198777123824842273561597462849068433055207167909456907599027 : ℚ) / 13234889800848442797942539073119405657052993774414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((1323488812438479108916929299105952071364220566378712272441184352228822391024919051791634627837892808011818420623842068460514377752594338650245588696010595080356992241929422782512862894994733404617338748957951100320915706008773340026768649262893941233445992812919510664078478628691532449705078693506096033322408614631367832420473803422239660960708481665301679 : ℚ) / 1323488980084844279794253907311940565705299377441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((137793658074887986209730429181816697823448069682315637140412424532592985630797780096057560577072845445454761871819756917093677490095843146987770375479511337857647131464679694767620453384722791558489541287384125009016559737334166721152606452256454446834347598779850634524643868922773231036726110061649212392937518336491473324003640064210151616378634165300679 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((861444820190852243014891964856086962986388638520321308680469962092841290028370711870573929661165159909453622309303084719188268020768688461371852917895629811521899571706963632482312808932226085900559428476029657092975402655009521954913620199164516225142346094895239933826903599983557652398415165012389938666293759645180280163490470533035083503345972118938113 : ℚ) / 1323488980084844279794253907311940565705299377441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((66174442202661532642048758686071869081353060428445755136461290354275553226271990850238408486011149113847485143129896559511528819800504913379113778985845853005163532247318611709329360512831328958730050383973034091119871108481943178226030869244870089782137374412957467152327956444644163016984747674235822167923439904209224329131042678643685284836903809642954418709 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((55301230194209715291079852027083007893552612396338930398854132211446667490787276128383281943846046825118342599342457781743319675996585988972287536942001548280757875008938037628501229645528102964351986544859177704913362757493159793661064800745445734736177916702787920153386930868953359440463209239273406796877680271454260683684893557181072716864117254453218381257 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((43272432602845869269121510913209657290208025734653712782219489364435591557878503174042840210226210024109308412249981116542606718267332808198367333576198013576797918171236885456337979276490261535925445009216431872664449662277960725363370319267321007436578757976592499324654855548190142650709830428184044858271246489894864510016639144785671108721703263046986992089 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((3308722174265180876529561193254836180201338406137223708203871010963313469943080940785022470685958330697906319741923033315942235748126284840704025127234752102272489666805963395659201485366079847184636874128169966110824290742220916683808298396133624412551095417308097399837097520915658337762088197891421541174821880353672440257175532515252955691118024461024303721442839 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((693524287222377306193161940696942534581173198032906822824914539747256044646387901088256426837210385314462761855252562677872841399582589018699112363559628007815968712902999034621557414756783532254731874573315624975651436578582417168906681710048827093963022036124136725306366633925266757448812465100781026754305759956883102243402606944747266721797812087505897427493153 : ℚ) / 827180612553027674871408692069962853565812110900878906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((67925548779397400609385091472690988089430644945267064217199933013363930687317885907099966174748393299596997750686653247997254011913739056348171698993965106755590207271686685320998957027536985094477959577404397356869416559250683334185121877421074125631715774991596667529419347875033167677743018100038046958892008467725596366285946145499504192889109661850247746526519 : ℚ) / 103397576569128459358926086508745356695726513862609863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((165436111315162645127130877401652677652036670050130851893664250785792590789060736848589146658200015434744757298249559384661092446537231502272203003437041127541297178271984740925289463462787225480127902620253983695082252299702644810778786474229537276041610492175606819608790883521069174421345680276652863347003698507828844573673868529676327665344349370408217026282657421069 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((139149130840562644381242383200106638797034132111820015187430308829441843330395687096226274677775221114917238302349191057918866953010998220544291668096185477062201901492025993715022222539044370342742079405981933099549316926136061060876135227972750159419101282268533743525619592133766676866682935678608980518646116627853842814677163990985288635955625568449421078842162358637 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((27294969146155321865949362073685104793190677978076035813731532033202698636819013403133926985471351831379396814329811307991528191297346216767204996516792213547019989211154893242156095956358615276186776543461599793474065086211176779535747513228384924780569934836513689984761749998131943247815534814184914880606917401320968639835577054595605951927131045552836052353946111831 : ℚ) / 41359030627651383743570434603498142678290605545043945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((8271805671319963264725329338567986734275188219340736233584102318630391200902983154684110269069832826203029548347282873795085181648462019278685548052444195585477967819672692924079918822148740524954269137206324372493182058051236002618106146045966556826284179278056544278348254935333297475448415594504083318851287052161124053198522520117498289710685598306831772973313694230190399 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((436206313925157801230122031167926043633763357163608566542149740452363727353620938197220455031530878739102411462690797435966633564729388180270654857779845306166138953100340337792677700259990551859766974336884795563897107225139805258748491536517306129054273079178716556406630934364448888675129470293213968285166936370934460449724028813807292826950206743868675835901948083045687 : ℚ) / 516987882845642296794630432543726783478632569313049316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((5483898279517751640788269155643380287145905145801004852322217380799440128902575096051732258051794801534870472884382146579672376989549004050179116271124555523012393178232973384071475795242732889814129131448224587387030707261288471033560746286151188848620645669471318032312791823695758178683581644663556381869241009739949371587298676066154171057699550362531052349282542410501103 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((413590287848747209076796462170318587258999085183716881803053115169153601411834929568689037726432187591883111805997613472740400904659752584155551370035713459098426632411940824622846386533396551837919653165597786116420889277196695862219184451230909176999175437490032057916867050981407211876417669084625164329115566993228963962317257163687023111852225408906471861300309888613054677829 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((350039122503044232331928671088282087207038849544311665543083758439618208851953385565048616488722499506141541062021293174188410277856740536992232949666416548273658370217998152922761130046541210486523115431743071762841944132686962474454119493108509009674155001462278018086629582439511368718376688156585494943779389051105517861847664578155093574882615178421439958148229844629662367217 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((275437593655557228551074108640238110014831527710736947084575529345582299816904458892037866566247933160383151944060122607884523464075776925388135594923964093701781343700959193452701836078946767836798376954960974979050488782995751682969468277613301906789734141782995451664770226082606446311517547323480976662448290793891515237715419290605116202163159140641767226876025629494104187759 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((20679514566192771992635965545475835276820873081830771215147292935527730762879554927531282949599080282790289729081129176202550805102950822091774874633718930749082266903584851195773500748046431504616238248581467780529311898865147147826094532370889216220033546674408090621745213125366671993038141252432327541996547668482292296915173440387946214670956637064744469884814872490920241334200359 : ℚ) / 20679515313825691871785217301749071339145302772521972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((4388691785888622697567854672200819172973780358257982252966555614355788588453732710329864003621165431526582074597327245219379304525927582465201091272661928286644575234195768501580206837616909328247291573610996713942480327512358928041984685908906291255688710513863241127857601614583470970395791615745118928112045954106295119200468365086582928047338126255651264854732717687008329342742143 : ℚ) / 5169878828456422967946304325437267834786325693130493164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((6916936776625061563847797786703115022894150334990273972633898402828129415626674301333582630748986511326241409280015931567412351573020413515324892323994591337419148497041809523977355538617204686840920052711127335689927569272690490158098579520370806220991830411771628197967538214631455153047988656103179343907100341173160299033212430182104920652443912499741634691744241588741429117539799 : ℚ) / 10339757656912845935892608650874535669572651386260986328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((1033975735359069401172296572083692106672700701645065899145522071687295564780786422964871680548184286153084844598550491807713688713831817803085398438764610739421016650545340997863726698848991772573785401983198729323854713048857884934452481272819346391262981022127410644614825041709251249429550428752431960706341935457995080778145501649979365875415381722353747887696824191829125111169842764989 : ℚ) / 1033975765691284593589260865087453566957265138626098632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((880335022285936951192735872878058730778829371271748288464237692438462620686679244681614828907313168125920786868370351626190963815981885342084154747962677839156595842557565977160476539116769843622700411516087589436971119081777641811428864642220262677682680706310999935369191927256998440999777407199058274492763881182318483762607825300731167261029838284857270821043693142850004902361874214997 : ℚ) / 1033975765691284593589260865087453566957265138626098632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((347392870118024542956190143839603224026164900776561547464866565999715615870958052486839158345315294722597143260869861220792706318615932354192173844373654186281965396490282099734068898242388640550828196667094896507110450957894459248989327604417714427146901946390439893620365220358651747173014359897305612819090437050867781231275200402397817669974690699536688838346938391472635171647951818697 : ℚ) / 516987882845642296794630432543726783478632569313049316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((51698787053955927107914384922917072142658193158547452603022038470425268358721285966107808951520384673516805230207792003130752064808870680088977700059119022309050066529275029624329255899002445205091047543860355647398109563105213249675671617719553702439930403048731177262668066767186032440606290444914917077816998663466318422250141147441312852931477451857613905551747854286699434885271690818368719 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((5518053318357577578196226073117852234288659454890955169711003992634863901359520662404265986134902788172076584424037159725049196898650945122412471363148787274743690727414517487528528479821996075511671525360318603636819527584440721575834482191380121556264908109749179258480339685119968016724251467607970907235209677777376430031287884260347952012505787604927889186821676130525236751451641576861669 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((34893478465185911111666989875260568649562211220092332282313829889696396671308903417781211076183592695143398047875036174931677844891134502565821924103573390654935044305226698450669223319366049874537807245818646719538350526254382553972409884480914239621926351271087519205131273531179661217970701148963656779507202183970742530727867759995904194023886929625755299037648536542344351583379003419688093 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((2584939364301202040342851545553148518041788204240702899996660247783623562581681292930959916972133526589250304994760329359017742021360692361889914269098517854100470249159217226888662241078428204415748889901958488970588703084741606752591673202500013261690416382090072592723706136811504522147837809640643100764113452775492004709110476492841503756282971699315253762139962196265682772730357768192037298549 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((2213499000924427230965318772183997499012461732415019931029274156479832383333667560235878423416849721196755133782666540006769206664334318100945130904386429679633800840295782832372139346247012832260097678352479998920738063861335358923778128353268702701127496299719554767987035739304841252272661590646254868394450123062427084114557019143100118600809234328467272222928182416206610157046666892611755629977 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((1752361461115167239189402736110774381583875371536834955957327456389518703147825565512547927680695902963273703749218652723067795016434423839832696295870813182914997249399543248378044698723765936191151036770252438629958733244783097713305569247650367296076545874761714775507476886481250309801584228550051830782889298121521438000206531745801406500939634918766322905696131396166261196926812732345620220229 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((129246968685821874061132681796910787732573521714513267377737159162829391557501391735501974791476429307252474123942421322424708811548624649814235711811595967858710178478638602112099915782792910681351348212212357856025754272851051727559396773498628038040041883037776335159393481676579549968059927774930531241100846892554486123053321141791072648896156444812919160383780406264695015772443345013319145239431479 : ℚ) / 129246970711410574198657608135931695869658142328262329101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((27745904247046865353714667085967409861859114229709534774668901416466267409159619355915883472996731725529730044102644234822544716524601205514525415048849307313667961073388663900112549459488886946816557518605404142817082268565354634533662618358286588533050650393606909677926990016392524947724837742574270010205424095028227788685481220053160255276165098044634570951373527451889899298991622937048748891358333 : ℚ) / 32311742677852643549664402033982923967414535582065582275390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((22000319587834964253158980757878891872444230960682879878037790131812746456406428243310621006497884742778927063954681957621536405975281501030654811988304284113630797063502984378300331897070028745047711624416863258524893571495377453682795289749821800381356158385306425952281089432689729890818169178851134065849917987900491122982837960579306388700493345761944408541856601051491647458050058856115542384237647 : ℚ) / 32311742677852643549664402033982923967414535582065582275390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((6462348453390369556653356620296167529453246973492703271880807096895151244879388964101050619264990213424540127682467975472092861193339250667613357063908260011995730651056846726290005683223691179253105548317667570576820876603840019638812286497612838131322539236725623693751752945100508921754159329756706582982702459277828056498396292043605608438365963122504943255930354862564941484903798950535371041508974534509 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((5564357694670107267651987122372959166596771746787112986533680434249230833348160952976314438986822121604611992150927809646893737689589373779770430406662922614513548070385537539573690807509937237928296236893584934571049874053098912087144487847011732985937544521617424702333424671737253842642187987839504399988516793081484506535763014304003727737927752828666084698711261402733859392635376852473067946650759060157 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((552395280121776651236255406616293076035707658015352572060494980034092199366029656990053011717277389490806135237118527266715429102415279862979418535279263559980385368233682109298821273823935754209027746079456920200545743691017011860713417618782362129010933021062109499795033107509771758616598950259505314631127662485023852659170397288794045999074525257122067976027569309206656660091162691278516306909649820033 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((323117423444395198488940460797720810855198014162231739498407865353133181156001689662543724674199917948847017520205408232878279471474966738835741509439822016946678788244027328532311820574068374833477745200796091005872199784694393436766253275494650455825886739373195278879202368735672747464487998167559342778191221475360762080196435964501123139952945489843148052836350427129122240984032027222170538525060605839564639 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((8717628595437559417023734192856942014980384945398374839181483874035009422793453066439386803598508242641654996505409386254544604878471401146322468512041156440718284288869210466026431188662968481926741511952270606221040293930456608272895635407163630239771629896535192139954370761938361159464107736784637969171687748208855838025221842781306110929951618568358885199894129275056643714076371918348224100136410314594891 : ℚ) / 10097419586828951109270125635619663739817042369395494461059570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((221909769470731948456502338002024043112239596017235055816949309827231345627538819388274649563812544894041007473268467947233616164313303934273669467357105768538065303811945706752295682762233534634347896148705107555353611817687048845379761316584146458282022625198286975891014938807397398738592088500371562677173785748859816116121213179228342679578180621540101198891025501140728647715459025104192065819191356788611083 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((16155871203657283358192659902808580918093755192608867655936487536491966292680144551299061453756964871102672347812253617416104676437210875561304868779483019049543705117848432745884422872510528035369025600541498208199241017464836236123043661640093463643312050903109905659408119301974979037381742573656050095853996046476861478355649603515775066911030951468426359651623573179055618438963163376430680918500233839516976968869 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((13984897151972511897164789091837561415726927065938180734490037115386129779439238806469836547080581788853812976300873865849512367913421627694805443730938143969160364319411913410940066166588874732698010515099659741618914364813612912055392932386650567657089912532666768871289943760219257008333092352396085471647163781579824239684231487493349718715374213970464072876502029359352624255135206801926066302461754443718796473537 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((11142900634716294753675258596877971977848067093039464043187094634073477003731379714444832418284390551083429186120209146896810523316049152643585061123153731965319713538939168500016201283905186322307647616021516213349811642960053206805670324911873192462604777640583236146970980153522387598530303952411346458150171392086058193058330630052718873314028836421475035323508417551270793149166123687400735659534647245024925681499 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((807793561458315931140127228306059431472357569920982557306328337405515564460326144590754222240373821785506519823090941512188782827734082432397699831252405565859037660336228764933276920360624632922956737639569123804851407319565870935748004396400231913472813217190071982507846808200426874525614677955799608438892473601612747038367060064238510239647436732025525837426019987447465495687174501345169155544472987103043272603984199 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((175262234258893909985588403808948746998203296867543094389055964017311359778616283249361228312869290946009862738192412466506864151013587562429333302190561997412454193043524104528585517188016157632355034822746288711668492422258453046267466093835534857354761555904794172558855847971540463855698511488417826046268516672780162482386880707270530350029825361846002576033806867720451100230880343002429162467253924640962027917117723 : ℚ) / 201948391736579022185402512712393274796340847387909889221191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((279753365420827327065001364842605008857640343644726017864913738452822332321591108313857199672624581236379324117825294863145110699331437079473408597052377722320588628872765638010893897956384730592208386185104873969741103254931484227673017866202599810958428014562241611521229033216642239203030657390477320513862285139986114618831327557584553949114979914908480828190979284488027829553683246219103666370502394166680445351566789 : ℚ) / 403896783473158044370805025424786549592681694775819778442382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((40389678124662150043030742949065761946483810369346592714341502055004171965719892012191489550514206323659785015742622588091011108103999458364807079853741346212467016917501137222107977935950901982317277802774958921886626446362106949734232286366353808961505505034618410402325852855499518726378713099344745913974306546491030760093589993866220598932736155655007608750211056910731122625524356694074857809594813559757568612816242937629 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((35141151634674079179103030634251139152172160755325242137183529627452712429885667150506285698343631312001191681869719486659332892294595369929674045101401720428320701166767552885923638299289944888460035877776931020537943935122662750075306753124606246325200991552616248499649553453265247002014146242877333830088626430698651429174805176896521029131612952790737614614926022125356284415924664350963593525667089934968476762160956158117 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((14046479057714940522855100035076518498032331936061390195274554618183592737872373467444483012159266796363803379420227712645316356194412012289385579256709074268480521161883350717084151198183963672473268208210825880056993340347519696953351144111270289037938560753924625711680128753557782510301985319326129799234992972758137899739044540414358554565784017187523150122690447453143230079908774663417145439791808241534789707889437103967 : ℚ) / 20194839173657902218540251271239327479634084738790988922119140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((2019483908332508809433032330659578265541734240498881082106871833779824260821221738826620922553911864757201137873693941021440411666887362025318588036746140157185999343359938638238142772839464044324594277736382858419862321555357041057667538090169340383377239844759503528432762176200470974247910769153515686475851590897687608967757039641146435919300038571079313694604812789925272376040148675435311056193071180932924316190567792222546159 : ℚ) / 2019483917365790221854025127123932747963408473879098892211914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((220177388405860505730384432580770988643835127324439231148599344557491360546070199798171836164791914179343484394241794601282046151508422911746662225868660031305332580840904656609943887650320312470999645241064989026614743990371639454210238096794275567601352328541794527690450209683314878737956783400198888868267540213894504835341721128465983974885672627639636136984090371271807588918551320235663142112912304385077946679492793902453059 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((1410504954585985980934359445706417372694958523516080265238908665163351346686128451443626293865041535841096687013060089699529025468942897216925158224425521775089771992686868779264823803953724563825986538873468825071111642513181324704311224721460645474109044211399663945738409280287028636756750387859724016609974387519000344122182425117268200514098439045955754494510136746033370031947702478926765994478076190592006954483787220497302073 : ℚ) / 2019483917365790221854025127123932747963408473879098892211914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((100974195501800250909369157610841311691840678371486127836824034863593750085777787165934837448934758265064407364673636881180858941737287164729200435238827652317193179359456070491959690436869895742293114442042788948952234247822390512750629687856260308693997997741737817652045594250629307896211987815327284916011774894310083983430870855280952051681921864867258835903811859700058225568324871911086004860809090881629672432167525898260920216789 : ℚ) / 100974195868289511092701256356196637398170423693954944610595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((88285407212046356470697027191289539463695016157177390629994659874249375614260240495975410085735529785886352419016838054992312399883324567024412826528425203104636746793263637495210544739258390171926390299662329718943868367313166823711427300003152604925713627447567108488221596247773865560932790513201604869572206150251809669043542789266144416738167431479873063435182515148935960060779362466625311764094722905834440589026211302454651521897 : ℚ) / 100974195868289511092701256356196637398170423693954944610595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((70816857390160505338657115293735801330542631569215022570207788600035024930120524517289907609873763921235158487998071000945465696097681308776284915214353332047506850105850985164815028581700012516067137771432188706970423168778603213477868271196986821289881385110455926568097958896407588354542596516719292385892073267263698588288939422653002012542746101079146793779239146453929747951967112363276845751259169214770388134538601938495353563569 : ℚ) / 100974195868289511092701256356196637398170423693954944610595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((5048709778545639779737096239612020950677017087219864865201094803216487034730090603109142290140732077571928071192174121906388628125223477560228390858074476682160844479792492235929296600714248540160573946028117990447941095668402205492805797066016336984024192766380044999961141804342281650657216557655643276327513719237054417291773861469603505688787251979529558231453550959891062269532508378304670303207885626158597440245468693218343794115346519 : ℚ) / 5048709793414475554635062817809831869908521184697747230529785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((1106203685917775827453346974985781123976584963289740023029652051082153488974710776520376697106398762040128646152670675643544575542611717817478329957314901147631867933781421946645206444259408667431323565686358661891832592603090376517790735546115890687029281421023202820931554388682266537656814134654536670899300397284725727351858252271541381495386657877034642687170139185692195151418934610419903106042026446269901966778240249387961896345076313 : ℚ) / 1262177448353618888658765704452457967477130296174436807632446289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((444419904301251551152947616434207152864472651256668482046009040003827921490568291230347879131391165436910383319572518183648276801966241873302305006877457540902977181179973646540913762876491454704421990927821085316183886424864047879249687639098408103836930731113116965072565085932420599260705009630880177621067731723618506215319255816288202745627962522440042902380755782760254694982597324749965607852453100731974204289576162538277231847727571 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((252435489067480241508367738846428206691284706496112196082738961499577345486034505858741011853299641119170693776337696299864093031668441708096026045502939593471947621389661202503887492387577777522854645564306774990463418192362745879048623992765348807778845524724804805693423484143970708848813932960647103363883559103166534763944557333683283829299787600061493707008302015993740287337203397416198778871447127738880456748198910352561426071053723622349 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((221759193957535905297175996627421077749231425439452616472361956580106520323450921974105304523205031279466613837883354498173981889390762923322917815487925388234520919507102503826449868106356999612596430554079642236300306033305845124777532321629748492795895056950021255404502099787881889611887723706727493848418968837056709373423537702638913260214048531018654448032212195332867646346451897901316044305887346301917033690921163772691237618474081892877 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((44622619812174146749892294041120247112411053683772039146578077830345699692877489278298382773318161797990240179832991624603389786427666630843126561960844102510999052295848610091202544168927985275358879626945433935855003907701448843235939884292481561276037427097071977655500027117417340382892021782979414880417877232380803743631459186099800169622228891227524727007357147828388140366027790382521057426115456996631167835821058318930502761304592293101 : ℚ) / 63108872417680944432938285222622898373856514808721840381622314453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((12621774459061995378468687898194884008740484139779520839106069618913414983713905937194981591900219739845874217199796676581786118387820348539163872692099762246750386947399944646785219453656418011879735825189490168138091339482348963058881724010482966480395541783610055771787884175205035628705230074146413630576119876374569481907994635584864508238521682722094861187033821090882037197557679036572600657593481419494119010731177991913769617128720621082321279 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((694590731194572438015643760572190550725776096783169683392145070005837891992665816057087343684472511546882798895188955184118973551798181077268271482096171638517396722788720716870215254443471527942077881523592553695857802991841783797854743328762569281346599042888869243782199916237125268086266991576648867995518719772748295848168740777833970934600792232331707614113733775475785467624119336947666860482396718341873018069165999752652125470487361057565077 : ℚ) / 788860905221011805411728565282786229673206435109023004770278930664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((8960480264357874823483770076028752636690167708849734695480922821279139351185160797459094238383906170774765233708114528348478868585531486276984104404881440703076136493448723418977131417364463098694550643299560347466584302864767309990961842042382424543039325804069195940614264578268902687413149974589549948409102585659321082571775826716257235079859363740341155055213742740617678908742783228428705123156876005046324620275097953029081979543293955890913063 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((631088723183866939511488154990486900872028797661282586555035711104639284304256877777937598164983815065286962866012950965599644609112259360582417478991179454112909948842963154264723138454294535159972762163762805611530503734138379780261890424829304433076127525702843572717206248872243500492199889338194147406103759504392658450489250360313537963745063189718110613219149155478175131142112596192786981279225134670295902384374622309933547136529324317930856610309 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((556926001169175433436166488660584543629434300763863504420631239007189740833664423989183871328818345327790806896533762837406597233474114955847303426258121515135239642958067096846144338897685308286016498176868822692468870948003730669209448708363539649057703548659024945906787534653006781511992633532931640774555314537367442576403284587056118676480393170686344536500155921428425303432935610133469140955403610966024483705002777580690780267968255729550085319057 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((449813132480175382331729490308825583955868775059261629352483455050271623370357655940561237928727029024351785470304715592494403361826706264356390367109566256035277862072579112439192956683473683535230228093133769318524608936137272222321879478681128553521484991334528700669390905135192493801892177020596704762195581932381619650568897201193732469188057189269916637347060721092156697841504199262667180777474383059196278902553922385198194512419820469821689658439 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((31554436168555801853502336849760157142950011131230278148707521865011476653508005788328706295151558361013757370437011433625343181436293474518189259540151141632814869534507858131674082450229183585975254933746020786465404066997728206065005156425749710154331569845290066588709774722995791058469041710339874754413035626852714545994799376368280548727100958670053465688914100386905043245566650140137560617479442938708575055636462801736313940876131216902772783536846439 : ℚ) / 31554436208840472216469142611311449186928257404360920190811157226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((6976982320113245078339229184437344010085077766278732619571313016668116903076820882139411978360442692935349912609331336801214571010715261448175012772681811726013106543023425866505513981828951920458270641054137508607295941061366106717939253621140008247101121939468665143554708671041631197268045976555188795434645621158992520802882416727595712312934149830033156108690319862229151819618276645522187543269819058624868433543174220501134938166546758618612171723970103 : ℚ) / 7888609052210118054117285652827862296732064351090230047702789306640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((11289833708944664079527130830535795446641085852411802812902901780490890062064945360638233652395913667532873550160216058942621100599337154920224233553815381111037980671772398068500912216396847018464707397548136147639989064269362319042728771981961255648232423593931545706630910927944464181590851165195792784968025017206912100689906617988669133198831395332026441725774629083043637051660844732783497733890789170675194091659265558963682032191925886595959389857961779 : ℚ) / 15777218104420236108234571305655724593464128702180460095405578613281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((1577721808807634249527530854013674989830171440670862731250371271074638431809473302838283943100593874264689150275999990873613798214051862554677456448803471967184932071884518312260149199088248207266602067917009809327687908402164831048263324201349091490671386120193263291570544270286662239033147491230199058661291268417041481845555005498637510142407212994202739156464933966797124509515884562835520971811758479466345598582226932329243992895285519600962394600873396876669 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((1398426711246662460367706681000549761113284214010688377828383509536043097128601976625752145187289372073755311787186006498058337151876994637905884086757833601722222899038851335828259630406331399467996273449906491916401287283860352544097439930181130271145109793108375231108983705380593359723477984146260747451821594792980618809149380474078655450850857748626415440820264966645298754212310063801176070133260350256171449906771233579524091983711815339320371669102663368437 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((566705578251128401446469294711149392060656949524791186121350299878658983754584974743337013162689734874582411142584372083913355512388617334799372210835745644937260254724881974420253517005816289142692843835476282782615948155104266334377146029099387672674622100353417092317923185227372550394500053354546659222105203093412906648396409076486136684117437434097923218667256048995197440517317650451089675774590652008363149629343183823158168108077604630860860669331361022837 : ℚ) / 788860905221011805411728565282786229673206435109023004770278930664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((78886090455792369764035831562291590731577212472743527693516732913232046441942141369452017855534194072792703515847595629733385407342298115705819085584405661180659879088426792446706513156209318017013312497461004974233626131784229360459091326172933990868028806282360885002308551589800173699813826866700406008947248050947789959956012128085222423987603038387799330316938835966926138475568952598799921347374853270429107280079528871529758035754628815730645311352034584683337999 : ℚ) / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((8758791223550786321897143492225174390090992998236127972389105913330090947443737862921277647928803080626053951142938093239875430717064630891766422621343950695976332034322164506103485218986405355085056885962185931573605443292791081105229230792299636166335228160403287941711592762308326403110029320962473763650768629803828189705090262262417647598903277330049337131089246033923888114159096699844543014994731182272778401610983170579652729605388564400930388063929330995898849 : ℚ) / 9860761315262647567646607066034827870915080438862787559628486633300781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((56890785751105441246008461755216465767946022284211797702776732485892018958172245488886275233043220616289975811034613553387758032550481634013600454145261314954871466158236729060612174108185623634672033780329938991059416579409531295754124758791556104210798574342627389841411495648060634942624556451604952055715845207073005308220409210937453071922397625183430124708622265533371969170342412773078033850602434888261293883122876905906312455850600002736570545357731693522916053 : ℚ) / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__apps__self_rec__none_base
