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

namespace LasrTest_closed_source_model__apps__self_rec__none_sft
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
  | 4, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 4, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((7863 : ℚ) / 12500)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 4, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((7863 : ℚ) / 12500)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((96641 : ℚ) / 100000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 5, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((78403 : ℚ) / 100000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 5, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((78403 : ℚ) / 100000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((40571 : ℚ) / 50000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 6, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((39081 : ℚ) / 100000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 6, 2, 0, 2 => ((3917 : ℚ) / 4000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((39081 : ℚ) / 100000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((96641 : ℚ) / 100000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((83 : ℚ) / 4000)
  | 7, 1, 0, 1 => ((3917 : ℚ) / 4000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((2729 : ℚ) / 5000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((83 : ℚ) / 4000)
  | 7, 2, 0, 2 => ((3917 : ℚ) / 4000)
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
  | 9, 1 => ((78508658300495247558896544374224117756941 : ℚ) / 156250000000000000000000000000000000000000)
  | 9, 2 => ((14916583152438301530980170853934586209 : ℚ) / 29802322387695312500000000000000000000)
  | 10, 0 => ((85573741094585330674918368607557692210521313799 : ℚ) / 97656250000000000000000000000000000000000000000)
  | 10, 1 => ((7962742411054162922633364634548580345431081279 : ℚ) / 15625000000000000000000000000000000000000000000)
  | 10, 2 => ((187540617776017140328722083424487651361367 : ℚ) / 372529029846191406250000000000000000000000)
  | 11, 0 => ((4392613031198421450812113132777223130673060222139229 : ℚ) / 4882812500000000000000000000000000000000000000000000)
  | 11, 1 => ((808162032645881233982945130215878884140231710427343 : ℚ) / 1562500000000000000000000000000000000000000000000000)
  | 11, 2 => ((2352775933177757466787554241966746402654428721 : ℚ) / 4656612873077392578125000000000000000000000000)
  | 12, 0 => ((224252742351251156680898241909904719634536726272410659759 : ℚ) / 244140625000000000000000000000000000000000000000000000000)
  | 12, 1 => ((82055962099563671681119144996554015888199102231098011331 : ℚ) / 156250000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((29476677857638390616135695254584526964071773033223 : ℚ) / 58207660913467407226562500000000000000000000000000)
  | 13, 0 => ((11400159963057610677700722572526744380292789521597972877082389 : ℚ) / 12207031250000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((8333137730442234085445825139043905473526561858470034115748127 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((368985126682881711099489424911798135518496351360232449 : ℚ) / 727595761418342590332031250000000000000000000000000000)
  | 14, 0 => ((577615987517460322804996015489982546252858763680751357596109604119 : ℚ) / 610351562500000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((846301337115436786777255545893505476569146218960042306746166161659 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((793238704034800629992547145256725977640642209441141506356261566021 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((29189463112383382756521493344444081884024732901291763329031762748711949 : ℚ) / 30517578125000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((85942354562721896579902888165904311078728829244334294099668855597537703 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((1588679507342447660491659689139878304486817335277317395928704172760977 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((1471995952073131221814833506477440846116767438538308130022147646477992482879 : ℚ) / 1525878906250000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((8726013926660502780992274668937553588320399366094759443317706131831195312451 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((318276096941724291723423489835815223753277667941342358402909227249832974799 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((74107859978590256800249610191296252567803371748937699143128552165258633022883909 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((885771883757879627029790079301342598234564182458891289633596966151934185247977167 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((7972861487232793249459651009923505683467577195135453870100063921845470817031377 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((3726005597542947808642926935071080262928350595226151391935868489896708000371423072039 : ℚ) / 3814697265625000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((89888499334640534029875600950273299481241069653129786000156373863242985959348638675339 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((3196488910900989124856817877169048611867718814478645257957783586377481456406772475761 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((187136553615493060544452188682768797347266111998920188122230120503599340283069005455694269 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((9119011965091044515027747869121074105407338119572195353168726245251370406436783432021310263 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((160238461022377262188041782750325884587044686844515554561764468363332019726629565849474531 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((9390756142613075209348969747048612877175933429908190952306998218951528834624392620342972187599 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((924789466611316506537680370924732953020291268141131679216816682369924277308999219404067542125971 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((32139580584335143494275286224788373647121510982422863575234575407314439807194653496477355648179 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((470914318755900386818497051607509273039904795184805215126047224741082476349546232999934724623079029 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((93752565102205050855474300869769097247139770169019347548980679191575348210333334070496073631359367007 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((403003244306219774589941859293644290561882267276184105622480197674746279142022922356635332230548021 : ℚ) / 781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((23601562390942900218613243880768258716501977445442732382878861954970457147977440219040351712682939285559 : ℚ) / 23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((9500911535871041490434142523953942272999822700619995327485877055636568628136096806334371627272183876822619 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((323494204492975590634764819542831772297691169108191234191216383231296988981318424102039293380814147112981 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((1182343865997807686019357917486649024387201726939057095505778308375106416950592727126686109335259529754414189 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((962471866001868041556849435840817890600834615030902141815024754437640568412961657345840182764858180149986654023 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((16233372816225965578307689391609989255455196509535543110178096061771296421065451357558975324689908308907470901 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((59209116899140219691991370070350837568413161263644485421764931749086442442102497532256782141840814381666338061919 : ℚ) / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((97465730113717269436659513584648900701269675250533231138395566597839298088702143161637841682996653385679832559249891 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((3259191230936010405960779470521604280600769509440100995899027168316232571243944465937630052510001771251977068244759 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((2964185277302176056248781875124203830988090365627320418046425045992186056318540427381189908276623680278585001510115749 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((9866398902249234044916833621377976137915165518644125673945251144163387979962664599200126026186604690531999069256297233647 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((81811489222211838091738017319588489484008934314429037051974766871246934070106384927339590937932661420215320127571441507 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((148360570664784494934319329455664073627017814223866016680561510540948980490899503679282255768690899332582472096266906052679 : ℚ) / 149011611938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((998414412994079961912186080422149523801770074786716850393325743253347656232067980541182048977906854699128408402311419595475499 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((32864471437227063406261878574657183350333258309009316244195972028432985277597572137772528230561711667612496816718006308684601 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((7424167201408867251792769515345747131121739740876468162747061044156841087496283763772160398791558476822203475417644645463239709 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((100997753567662269401375985048307517160389454078517041620133280087481531188495184832372898861628428436927310856708260484969637392983 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((1650560880884484410448452952049171545028465618058517395897768298787163969388001946988146468521460941995490704337251307802182009671 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((371457411976753928663109452007092306856740103027099189830811013622487199760811728580000319539372318963153617201169260911089098233839 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((10213274365329784663207501321979425676897306329515746565080708937246297799340134859331184130811379029373888147147896992288744116413692211 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((331645162067342240146643717417839771018137315985277546441048983564727030493285281658715436465443285050081821245557454253309826497682939 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((18582974883728622409322263577379741981484802719912441230625833633677928181495892640219192964031874352654105403468638084423795804445082069 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((1032463502384256911527248005464901731698801610470384197871839119301721402452423318385928906459793591555953941496215473460991079068191424713087 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((2082753391735428812087894289866640744258348318325506918758838784835458573650012024984637337420992384247955941355280572382208157590496140943 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((929558685128740878245176055597873511930819931149567653167720696351947224251469860306332877743737174361529710324126115723157819582141424621399 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((104338608275277341640571026242734315771049397515786967300590068302913467893813032815046427924996433442197422504789790326237670591919985123375945979 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((3348952484868963186436074357816639561834980678821446128734711254982239369598389976171961879507373735738841546059639485105706000875449241880678621 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((46494565970407493095113162751661326252545295426669109256667596371694850835106383702488231182941160901021621877560120641004235898267059738314778829 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((10540962907391961805741659902407723682674607569854968338004297076332917228490388712813291791354797372673163304122440065182438502744050833992573791831143 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((168303138283820619693959988333670688650843791483700215221147787656638804051554410070144110284267138523964222232893874588026993397428862888202828738841 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((2325403063787869748553242375997651667392015180755392431652261052396031793231101093193650027323105838915348221194491654526182854628592880643168891871359 : ℚ) / 2328306436538696289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((1064595841814996568793773762094279063445405999581064926469929326937843662739678262269995877537005316645698082948961238807668031068288668125679125161928620931 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((33837069554199801196938621487049245437929748990380649523116150869888341903461633475401227217856167261850265478554427863475229052614199015875907633223994719 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((116297529091061030878123908936600725797761447898427026344563883156759405883179002451959575258525726990634592682081720915781764595136641760574005112112905989 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((107488692337256701122091800745006940141768850124089200669787232647236490737629152072332064003766114453908537007019277763590093177193009536579979395624594239661327 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((850464122741415061855024432843280630443809841962063373362038302017414226225968438461768708286034155099570046968051532837962062888978349521019905592974939598837 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((5815987122259605449234880734466828046340979702687082885825301303552885856086455308478451927813647269737036059704737499274181971389288692868247961403532708879719 : ℚ) / 5820766091346740722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((10849720892253146878362182034123755606672040125626967918271507580104905947962939688556092566853966723803291971803247299001220760973269616932668363363208115986249786059 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((342048358341804585921746689806548598976607129656839627001502743209941781143935056967478364347952166052175995968968385467007717767319839298919635310605125162756343041 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((290844417012502870954834127528053680668099887517717639760818299186444132067283578320279273163327483380501289978280905083052836761234831558357688042102725531959079549 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((1094854174345407520550884764458609789280841977175055027431888326635722641653332117629572318229571952801843954040420143801237310678532327511685490338231029589373644642352503 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((17197806162339112633645552854069271635069016251036529405669345628991128056100382223845237255911047549367503819460449336336916042762788320776058380975076577594886812266411 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((14544049016379674891204864450440665878385480536481322362736159216293224882101762056032050391509359328230317835708834600124536640240058351154129761556149677557111816382479 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((110453622601564954133387297818344606181675171400181004133667882515426328407717775455026078313297108060481526538690327273096736901681247029578515510299808654110506692423526564051 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((3459063233364784033505204961919531462238576716871033851377188072548677409044486424303344218983233134626178671226683874457087703761410275807460929612041923177876594687691852099 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((727276621331810835695887008743828255351977330845583729578568715564232426691750588375276316433926217305632224912543128561652576031179407364674198556094548568169583502453555509 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((11140214482931501181891794377649690612659209061324652367315125894797007988753578378514328981618782158984586286725285328444377596031494600447045488098707956042612958802884217509054367 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((43487052225397045959258542701861590094098958028226376654900697031638702567315238557834018392992095584661064135323039446234667819209455595237578539951761180685592198782922165201351 : ℚ) / 78125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((36366840238466449699258554487995856147885072289736177492732111359156473783311013120973335434040820562306804996926787268874806662160979736192196909619311929959208172278043200555639 : ℚ) / 36379788070917129516601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((1123313157267634352088391204513105790379894398231211307319243930892306966071025945060394074648257495068689163419580616210544572429227824944778778167685380361658658363419095750026183587739 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((34992394515459360402580161285983294000567838071402489617936361503853911254301304891623859314544366600219198305410267784441122110039301565146223803710402469300629804107180614271989885861 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((1818464097035499944960654946944979879775845267866886457057634489952337297862711113331009191894470131033349385530316686285519781090533108877053620820165104310375034757492490689742829869 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((113241474507206801463275257636660041227778912641599881184323177624143758327209761153026642633008413460566711526798467927810531161777449577293443862987640532311271035803110135650493027397021063 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((1759932612489785759322999381952250922803568389097639667171957723264477868880675217476139565786281235708583097310562831968436041068612257618680302283129524188140921105679723299918391405360381 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((90928157966861148977600538493129778702385818362627450449285288891856276511588052578952373924350547686154017920350478279289823038624018760250942450294918446976225535146227839773556350615199 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((11413296509885508210097785843730510640573383610732820801072772882485155099854892090490709995064627594211533643553807811871801329910070884946494822612895942670421026603818741880412772090773936609571 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((354081844540222705484861275339191126652984518754025518953926743844151922561438651518403145297782878330753036664998003479026472729715238969533893042778891476429234894519031949548007878013783367079 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((4546608851175217710700321779236018251734495036790158292177953455631500994351638881180676762484826070174954661046539254269067410500015065122140986150915136312272446186417609687452954700809238629 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((1150061338305053201864263265145848720655617135865471013914909172773606900586307410981929875294275505932357190300919598654149321188134644357861071298275001949635228927505721512055569370423985044891388207 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((8905192059230451404010789153154980865165274959669693267513079135046211222529208998362589233218938112714637101958723884767256713109975164885541386622748327767744443063473289808890732884508493239951367 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((227338595416114459517327271506946996491120198137613512071951749648425626841840341048381236930771878493068085553319144084950333911396111207070381949128777995325205414229148842629653825166531620417159 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((115861327583223615537258866874957444192773460771668864786425689512743938050404026993705207107487163871255916650618841802564507180825902352969891766532794891452840097894886648867054765447207229532260859783019 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((3583618820679887230705759962297911448699654423979452947039810558537810308613354679770126382301282925742708999632208472351628848183792447567369030057887345148445222348945462503643112328607167560814935675081 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((11367260540381414825902710562386471594641237558641117798271154434986276106600304476673875163518345882342265298983710994670519997119251627782052466058103652048338908860690797694327685340831354371944557789 : ℚ) / 11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((11669889231954193873672593882112022718173290763860495511300531321460599365223583681071668616431434476635254417142591565163859777620373539614110847552380569690064944368370755763537861694289764233009250509953180823 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((180271181602242758578227015129322223240956928356118222808073390587186410664573145628483579088387282552334509935492689262323054527203212661665556642520420124826042063322880003762608660155487541721990113672148751 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((568376446671526135342960161730487789066189648991628790193659006581828207920880952923135789259102810792508045445068138764777666803125157790745650600443323267253157871387086353256568521962868878224162654057519 : ℚ) / 568434188608080148696899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((1175191719183771279204247308466507057049766041938146463752024730389947651793071311569658390550820458503996347574914904322531109808948035635715408503930735553859926949660884677931797409608834684755412817284779445605491 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((36274711723051442359060586205293055307349797551946175064399117646181688275970208016867457459624458349435439887489078291934570590695240203575170468784471868731455728484360821465280548612078285477591531555016446891659 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((28419366782296074559062301296762932590204380249239371646946939556031352223558061141044542106031060136662843911751859457825794719869590776728341790510586068275727868000045480437972241504555553258432503037767603349 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((118322507257430548162055190353461986970779625520880664424953282651549519398245614800020034003180366284450343543494122836189678495998683047777921793827436278029427410661663705424856601921835170158108132419994639723807078847 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((28513609829469261790507503365281582239901246146524963669317981625974277183775058897750214204292524858783571467430358818722366462562297530412991773918325459347642001161350678673874507092463276439280078057497048873835651 : ℚ) / 48828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((1420990427943813427038869854670734563117181911091890547088284284727747991061974098553318117783786140804548240343684690063450317579829167402645554782804987376014555332629845186848971810081323351247865080745269435472279 : ℚ) / 1421085471520200371742248535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((11910923549582228909975304658504393888501382726716040942157096487882004403557029558210689650076636232875699892452954348474663278103874174189300085002116599136211210939553755057552346049015998148439707457690775039474677673443899 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((367221759148866250484387830981122809346392888617235599763970431352690590042364484276361947744548193991546176715469101772797373503508752858174171599889535848723526374441752034320075719659284011323635185394750564501281571438701 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((71050417563072423853551650311834653210227187314909091385918781715689463745375351152406669356605987518581326658983631560564242834531249150692732803093181142832286524400125449075649635306809369683477134190916326266545831309 : ℚ) / 71054273576010018587112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((1198796895186354071619353029398840816788551789099413161273285706170756236769252869067705196779770469365250679846051030039888503469977747428491087271753527216866670396555711204832440718010761517706943198161701658838870202303243055783 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((18474398709634026289105814317741157898995569192080113752542921749353216197696887788047115486920621351975421222967953501012289926206858090047208830487179237857278425362595764815285129784851857327593735624384641678532198065015319521 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((3552557236499609773420327076700857777892127216553176746618110892987237233613623371604290982466861519616363003881624916043651896039767309292754862554293452145848696581437489594448181354032562937428350811259666272960030922037439 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((120634197512284660249133495409321629972266800331758542599688999805587569240942710085869176955753342632733939505048399186878258969670251432923086263823690970487373244006283295922965234102059126967813165002780729719619628601716902573359811 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((3717711129582291436665780035569709562311732024764141570821213938223000159970783461421647099446124640741702052945495928666567727835621309972310609694469596493347913250178504569074685247958129463578909407483153310424157217824419501817839 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((177629336919435591380330243423801204031861493302778933787043377039385201804938313809357689449663038712355463430481404468807001074229399505316357528690239647009227469005500390336357165714455110934405620763615920360261414537980937669 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((12137308264549776168712458674099244697386634796634090683663791919874372072694972873083587752510461343699614258071616095057021417434113413997299352055718996732932243144074225393844941453207721194737508347873623680255887421651892017036516862287 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((93517375189466378934043647525534376044268625738141130589610390471087764728034303849210483475147320720787022628401676486796135060696461911992783153557075396790386596069062893372061166834192683814823299105754647122503506182349695657275187097 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((8881526692028917541036085985695573805026652644787044122674136849864897022428152329559450818662279143598973506838061060703968840582560967330189941296491712718811367645022156336336346570201158305719770440000661504936165849220424622168999 : ℚ) / 8881784197001252323389053344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((1220966628354628817955830348369955969881825332755399619791247472499762376683861659052908395694245264427132586355832530815563062279308773376403155023803042825656453369076857915156903712078550602622708087720033214951080357533689121239282477265082379 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((37638152447671612050468030805702052406423111389750510378694484676874650326004719566201684160673573817859344746964880815767778880921835544289349007468931109651627805861210096041525489189569515109429499452597606043345862027623482826368721685464721 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((444078762615830021714610428513081882656236324451655167101012406135868737096932568162556479163947327134953954145926975293820719831275081005553136108339965276714895996726193904721501916699631193621356806521266837916765184668721847346018458429 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((122805250582562877977834498435784368230257528409049908118251304125092395703236933954252878040995504327903174585901684153897865113920986631910527751047672574349740273372721313506247438017898804836356915029850590698589180341340259149063122613779691349943 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((1893528154295838400966207917781539913699587342730008448638165476100215205219386340610845659138291036530664169507035026970875740541726686932387981711685365733582569259296188930912203268495557233554284252588191664317791604365162876417508758331067320691 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((22204036637763080218845228894575582951871163919328101784455174329338330532759651222923078916160507009192216873654403314645600424274661311476296285051460731241600045483178412908456054262420737156412066997374316881121080307194714068675314876922959 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((12349915286025406646158828389871530292236831197216636471695151444418517760948767726682248325889798631055752295433486853514417779756617484700826309772964394764634135678662438340731759456089676323301620181053953502257900686002738018037365857005611428651840531 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((381040324817192669701392084067684694661175555931623297039599566736609816785585480326837111219636926363746541088582649817019536589552613526156760021570535702593174632123094471140173547490340484993024194816874936484622387683248390855741329496083249139377619 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((1110205828414497947951858241450392870471614991371060417497130877715585408044591809765212234707547929869937430781032796878486654813247284067904816580822813327202955445298031390108970577480671727172793970150473410183963349143196744480226199871641369589 : ℚ) / 1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((1241786710491928195288098938341042355700416594443375468486323082453451365566823367459162131059117948965050999800381906332110521145278640051143914923323574239187942994788780971410008162911245903487199662084230312250537890802607497852406058186081821952389568194527 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((4792302097057962616517500323585920092368909162996649023719185642821156660360900735290018840903974912568438434577554424021666849531467366347383663602931344180237657388997876058585278834105879390971991094058744536993006633852540741255696382129427240068957013081 : ℚ) / 7812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((55510453563795197266009263712312233874466391814915292198276096839799015589777134313984425574319927062753231504217281602157082072428255561918966313500562359497951105371186431528111045298968332643127424162974856724573577038088635120307257154992362005595319 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((124844100906778499145513483051232593511206715602521129413728165110785179150993596543037471768271221049293538250117420574191169732951863414761701051302260370898456366326308792234685876212931227748375956051645870598037447694224140891116646560558166201459888733309450459 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((3857357759806037953988721965379516315884938015630375009065974848429730591068775975525311216842080736270213902631487834004138983178009661920785307005172271692650780067108404924922738116160179324876895395038611586197116041896696839021462248589638091092069258207801141 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((2775529256496264999261982987993636876849100982322928319776259524887485861492848116252662129975733760862961355357599331881114976760486756402614382305031315487191374296014404713526993218824444223664322725716052912172674594012294015465985730035195118929007687149 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((12549573256495679022348759331462033821711387259024836926783966833428783352261160285925878110588805696517592690322057657034149232100019548766028650737979478775456169346890548816956370641213034102976675410801449638908470869697289721376376672000634258744224609824056024847303 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((194046909502134441036711608776520720247231356287806863252062512368338268999971177958194105533013633723176030044974096026256588507770800403509061187869791158143699758238337091014269028875329426145842592955721323418994848280677320827569686178833318932456026437431805560261 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((138776729713286469834193969301960703547051125953823524861642625184210188886626340924486755275245494411971205148213162493748715722149708194010468104497425500630841246563600413632503641880926526598285237305025982699757580953672780501470507053257901170068770875322079 : ℚ) / 138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((1261338505504868636257055187244217463921833596353469547356545627974503959711197036852566991265208034413280327991231007010011377378363889128818290170633363847197398512733347500195715063681042365811916500980549256440364550898780880142392945894031384866647870002610952802388375651 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((39045701806282171635894915603392931867622306271466035632839512294513639001882031506844163451819591037494985677604907492276187245511212881574830011655550895060806459706770234826951968068453949941210335889474541511639544117955528330953762301900558156397283420386415769039442999 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((6938847313596570495099886403353390794427723731072574227161702946348591573319317277647352148271984953788083764068156215533879145563335811139198701467565049986093860214331832381484305254751070110619030362702209144111864816871458377725159941657726308370860103182692067109 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((126758733822978611069005001033483550398810146774863870779853784406058679229633451271954093283369818424640491184706605726549873358161956968451689263981417323894896093988359735899617584841373726127825359259839137338171290327260375883602420108991883081536421345800642963133224969651567 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((982060361334271438563586297750880725660606632532662377944100632140532981978831822341619441573611429800749684925683184940744145084772431056476786743883097649536714160835585771986378955847219891088852802889545016452963153868848481215116446980704190602283938037889118316446422714027 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((346942804979867717929537635010627572461742804493345408970177450236308708721138021271430724007542701560136346392009165820425010814650097193728430517240581642985814002755656771549199748490505665457924680845191327185762467485291937842687463992995614056914165246224999854679239 : ℚ) / 346944695195361418882384896278381347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((12737065582690083665559099011632762932433601134979501091749675090320086924344366568661808347369908376940211561761179898274895016407679924885939211760435194758233507318692118804185078371841259866627175081424561764240536831435880832913896370546147066035541012898883045459742087905680340139 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((395194018441941347204084167914799114924360860145357554715432081715149639417168001266784525006903291982198812353720751816593121118432803673203447576489466987206807312600332804966732896547190050608113147710401431343693884467590561290300113151388157754682141501142621010492121449565455961 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((17347158071835276002761278577025028969396148571099516587329069333537280621525290661003215903710014944996291709470203866500463113761169093246756154514967637837577459905799750878522582996008305353293462226570257335253569068345779210215673101659825057903064598204594469104191405469 : ℚ) / 17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((1279698845544870236507725301202408999037467386305706360435298700702329227977836591858625097120756329821055261035539997216886841385134323214233051769793141411552753861327080301679843469784211591778265641198968647857800556613721946059056504349108904180862601196913696395361726397771211474011863 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((19878275349645191684600673680511111326180013061968718568061954817226297827323379474624402352066353631321428129682141276598348835942184866731990279251923587943579993596919517893557340199623205137364767760649649395381594096748991911742245989552507777304099305284999227612799793122434371606231 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((867358626682282123640128192498925336669910206178078487464527671930941012095902567407561472429419016333444550944915641067790288988404391282114143944826752034708355125838201692892539714731052956488469055994181910348572550671856608337660073407440762424185233813758602206026149511282799 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((128556682617053977206890107865125161467756265205489354441384929503359649968213643261550064613707313053856129264988157994113702561875956734758653804200405553424384260846445328480805027859744549074475533675828714764200770015633291713806554346441462712085867449566058488713789875616374740942092853171 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((3999375231408235021059183140327901100152465351249947159471063643112063755403444307229455083713218134069449285864197188790788227354243054976241639488382065435909020316446835244492632086088294288270485814142748231857682650047228987437620566914834687232019444839410935528781862774043782231423325979 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((43367960670619525084808658865396044151661880099850822314923352177910207801742863062292176497933958911664178876386172473761319814548554558706652933985566156800152675810381680882343228766353549497693678070739954284751936953307894456867206838213279172311619121058000250100686911822254438229 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((12913130732272612324451429237327374370881681996308306254820639544021968545499749338985159214208924166168104536930268349007103379853805600400665326031210464985286504179578019697097457698300180752345556786528644995834165137401201581859084202532176877169540080821062220249561406817190711249806043653329407 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((25144314012054180909087024248088443977140871220825418250614928525032980887202751011009565277222162047638805002952845426615585904768747222970839425790527963671600919258644456473802988396409688484504299540313900245630764838573278862942183626618114259518664445888331169763700529489024779906895181456673 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((2168399223742337604546022997204090123158421793781047712138755321209995040724509697300255892697678647005127401193863403432970506196049407001287616184728404547538994210302995175077547134279729856670930213007990685286670834132654586009559448633150949299854699360444128146834968699540684813388759 : ℚ) / 2168404344971008868014905601739883422851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((1296940107589454951423828431051015731931521871560513177009703792348976307854195112972358013558692829582942758667226264271431201753254677488613726613872224404812279554028495272441650474860964685497229711279478010294156876775431979888792997339950327948032836265546066723931048377338573717817949833626511383419 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((40467901044865117471287018218603146096167496634482854734213583095175497843345749479185555091131024202032432355191730487388889576119539013783966434389189682074443100141349110038013611208453614919966017733045696439508518055480913053752117294995432102618915280525985441066479586369230854191857271929541597181 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((108420009475182021570549243938372501180727713407990886729181442136810708797234082929168681822637520387645023793836232140679046406879920491449239876230616100898204534106202817248071164784862920014996309671947190092765522411595929208993836390495567164044405007752578723045241515109065123563995341389 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((130245039878461482305200472128179029907818001909411285270947957489254221782949892079520516130071028034541842734750983383107336603120108231190015475794820447578818654545727683848214239294933643705459273907634510317069056537871890687142574974987167492488442221833088421156811439308155524741711529583948833206587623 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((2035232619374170694671979509416973693608759211635628071769835269680012829930765356062975598712188524919705093675764993956042900743512998078174926198256397121369629892162988354042569933500640154966971176272348249346643325677664632559722952445821782934322002127773723927260645255263016507658256594945680674386601 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((5421002432854191927964380621763978785106673201300598265489620288932547266612583978519302590226226839647146260339729774179489591773525254258587111018552325829541056153222754498571495226486673527928415279700569449253590009760858443938088936198795655412445555569529871372668493509489881128114854995493119 : ℚ) / 5421010862427522170037264004349708557128906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((13078463658774905758964101281938591147394295539178223156154211265971691993628681421526059246663055785433779738852882340497822762682924192966013772849042461388828223080455736663049794240583717549103383120012175152593680607923668289513598449914780538075495350141629048013150358498618394076173856905201981000812848921091 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((409410646814343633582838826105953157375624385757318894533610918038438613149925236027533973846578017932391215543382905687088911048675989656799330580419485473369283962707416666898639103337579866777834424607273068990856827026613985213854573959438131089563504821136630170110012722705838691578431611075579313234762578559 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((271050201125156527250724248502599785275731295481216572229179384742282375153739144592506625388068249111324370928243176668236072227843693090525137681133686411230310189192400372761544132833790831701583736312731803125667400286007787929012206230521338535738328635011396411460533450173513967248747782022151330949 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((1313130378370106492133774849982483674915356337465868744764659894875126975914512731093728120608230488117707214150457718608083676156605525783170746678219311748340942139912358903885992009386758202974370745846974779264737172934579116164551706617486480289216664633348302129509420801590174801025356651730739620132562662985244047 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((10294262518243229374148378113206591500310436126259311317291162170997437907044402323995731826599796509055103375102640068417375225936069748789563397558512159818739968640950400812270591779075239252698754207157056454648732569259709742524084456580226442901443080917889930098278618906588645145285086409426967167895397991460157 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((13552513280940180794153201600849645987680117240530937551910036818379138242362350835262586298619316934695541052929753920607005686355846472375695360861274791390024914685724875523308607013199727832964953765943841984611452097003621964067954218978481225733439731051047363809365302606989635165248946264420701647931879 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((131830475711084169228951920535311839840861196368928778905530432238134569712257267749117708494920563932130662752087705611887085421688055206196427340606769938698113040278430687633284152506773326514518369463909799101603942753229944616088043147827633452919558941460547529280366137006645362376485095481557378041895488745609072852299 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((4141252449800591784701023019491568035689572406665439348798414993654331967190196946989907590489623423110653690802192105443556821120156779240875154797961415876112743914272997787188928136642872146128974794848717919964881732732598372788341673291726075548500237960105394696245016952242756811893272948666194428135630094282718752801 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((677625794875596841352792947890604492329091179143705667418542103758460017630882935737438388721284307357532796058413046312946827701143047230754336485502779561484700813714543924856153495132526157911221139238107613157671223027533946704200970618175961809231383328472042597109759692068176488289314998893812286558244262909 : ℚ) / 677626357803440271254658000543713569641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((13233717752071533233392149091439169472261519782893827691009179709459449609339517899845327111682602349353849032417432773895913695860687441862350016412475781366775987580628180223839245088887591041670045520290907338960613903515849186872567077766530923717212109401085303244021736639172425908877566589699544112231312052385006097633198583 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((208237037815371468281425344294071341300846428610667118440121907064682813586608694628581735301887390257238803840113970745673464899095730594638501501430366777290141915074146527692019186219407720505192440725532607818997085463178890529216832969180984762339604597192273110280031837209961762940948508211553175876329451274260393457389371 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((33881295051626477768184332975996390106429615357945532632837671691584481375302551585803612868811225633802463068885875701962565746663074569198934185553333269588995796713212761575339003451021718752616152840029263973419879189450079751736137578950016946562326453019439240207340060466897988306385798820120858277954527990481039 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((1328333658937622818239889692476468696167599498717904954729937291707387171791754886682587516026275917160706524426739417410421853659994220862094349964369740747629369684925219339974303211169486186669210265463084193101732907852595511886378497398301046458386493248453050110223793404227027918167155818517721785833207609281481886579725509187411 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((41881622429562439321288702054583323259968479185379342844851637414503263358512492828694895009144301376876589201776968090773508937244335894634525570417372823185716701036463736407060614963448672117400553294279706550484310141955401192657539804468717932372740165440396768817598039458622322622421603360177751656694321932411853564733263792739 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((1694064967925969745416015087525483305415258781132520704446857178199273993877399820387638377700540235188999729167768863104323254907867598346969958842084284080495148468451754949873078709011402151512389936872827268665617918595179185607686837715581137538980146525451669414451993593202518283578378243931123341194893155101806233269 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((133319258865989541056841355860201542045154472408875899633734518750139621891048587510631638262591688343739118678422376053525171283783665499698927682336548184231655217601125785063326885966114914351005512224669064843197023201252514351883273324693461858278135390254078398632142642467477947552552387911932252035663621445045545648662775285283731487 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((526438696263340570556388374146327354001790510327732282415585173628368149955131439480575294700079576681872329888928621491757609566678889101704968441270490274064318204105563074109909735852847321323749204171972031497952487750343511159694875079582273797955832455046557093201482858317054282501063680247797154900743463350224219614077759270815211 : ℚ) / 781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((84703257133046114335423573833813071304367606831593122500113442576722745205599988112946876621688617881852908012065550545005498774867096332534918200182201489429768668513556150071300676303301596689009172128867475117032784575325014739289462692958842331093963524684099679813731832069819369283058383734529605075618010195635380689956599 : ℚ) / 84703294725430033906832250067964196205139160156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((13379506997118037002402361970687017902566235127282665442005427282985891364340807561402960867394811276598705035156057198375543475158448969083955432782548169051664668656332045641959968813881337032149527719686684248123751376769777242828110088218067641190483459842998720491974823635286936911922995370268766796540476641620230255308656536439367784458779 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((423477573138578134881592484842629577114750507000682169713969390076725197291807002452465111843837450505109130085295739289085500551090285958750683274525235579993214264157191552417959418602308129416158584062970421857481331829323065333711276823294310627555684382674561333900509510530380994558195135302814668068202509768504433934507526961435186010821 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((4235163211110893694409991099902464521907755317877845822952102478780218495736397117730367731418528916084654330957511451161418090795132965307274166299592096627655144650263486564542739738301249079269791122440282332973137103005511172987712790916033192214813194159958608109722914158904641631182961686493600607522898291647123029972229178029 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((1342610083303549253797162630475872464859638548232441320010304224354931134578997127631136174664664363967276792853029288576299912990561269385200992041307649511069159763532530959845086293114744420298049328129064014121582889801867314990496496326250004624982494778416301531205778249852640768388536028132312848587288245116056017379900083233550889049024948743 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((21289770215178030464739670060890761912437470456803131350463451493875571964020243871377045914650775838335252040760269008674433874951833758472314480289417596101061837158034271279405676739091587273372870072550186676494065391829176341979204960121597491211100260170187656211520652090208187327900433620130217007345795165167637902113634035111504058109862541 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((211758174936284057561283813208684608419232398057286145382989749666592244590521367463438749231381136654470510861277197085069893361649339535481420200940750952280596873605839913410063493922619976395054695628524694531053145406036593799284495640254382641347186100263680689619568350340920215618723938582731870247811506590415428449003309981814559 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((134717278739928793283584810093052337463816761956739853752302257572697119251075182188619526348669436788408118226772579344303932476822359947526281266009880683010973389144302833447109313562786110020878155946834357627100849082759393514600319135548310296457486786093166397992124608789202550199736967473577809988956349885744704127546796479416447572776925994420131 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((4281038133556811854584428879754953135134228588468185904549122225696990053323421523802578744881521590147243085989700116300720767187533226955774473304110971105811701067774212099738743951679611154374814697943666373763454086843299173720838500634893619037567533020939805496116399306605042671945548414837484967321418907442714532571486932684972793571885649400519 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((10587909330255179973587648800416629263222320474365359329333277133723313955282042399359173495066364095208523096152877162938370643575475354294016698972367206884976095759062531126959686011934615062323764056344875381819357162268310647030771272620760558142096687273797789258555507541681474067867248912240014707823960633879744347604513289272198473189 : ℚ) / 10587911840678754238354031258495524525642395019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((13516408175868459303370333615811580538622251646732264296731570738157534071634549799675227303043798861615242159011222254838000137484388530908232724048660529092509981275827267763821805485547288115811192353686762356711965826874093520354438324567448491418926511096288253747849432409007137011507349390188972453292617142749249758810084643854990225039220731413505847727 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((107600548340991222675679434321931782441879031442039128141103470332477902967383823210005736069865641242151663252090876993581326880603861781322224160845971735556630404590191713760756643623484292355971654059930195333458902981999775312081234165730616849714943018580315816060136186157200653829211499205816918413508330887961157761162310497741881489766846768770673487 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((529395490183542880421864660218057366590474906604637149600380386592288570479747742184401027868337457706704990534018379377572635380500610599062551494007909950530365181040925950351881421190199267693537431529967939115793139430387631260685421301496876604383004699385250108008855496473559084407442155618489636711125906877135107926662708659062364255750919 : ℚ) / 529395592033937711917701562924776226282119750976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((1356016137934601439565031188746170705151033481630817453823227516775001052102621476212331470410261637802116813694984792005322884320231221834465776091123761632061163078613399373069242939405643737471629996023238049673169675568304053673403823558393771168103517572816009241100151535684558627565117975084451344596966544153310604152413820409761175214143406365854844084154859 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((43268996663763344044243372114013040367189663502525504429498949700498669920269911184732290684719006980064871595041927965537359750543736907809298519899405952732210457923871757504485587162619222229446425860630658787722945461679861751931637803655780844821114080798901630211826847007723088476857254238304171656194500431662573225028514047405459168219929200034793790219241 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((26469775469524516887267479166524520457556264567814741608937032664435739592933845648163334101646318996618728170955659669727499390022290272614566776663394914602967445760011406731726181139107574489594507134602329257866843459830256587877268227623029780716422883658758982132027276347428765613494335695597743051007089167912248463692632753006819180220070534749 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((136030067183481534438131585741069653134026078135242885030572761171925076089307239974067718164280256322393810308248945966929937100843217160149734483700236915257972522098665559982038191411692278867025481424280957113626010019650484056364763676579714576580571744922945347797917567774664337129559584411829919368258573438113598780476935130102782033001047319699896200845683022103 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((2174832918873798692508214901465329573242291788730083934963006266656828669633474317645266538672580237230214123240582266880843876485287314054743108488356300068381392813860027000795749143435077883514343271036093009955321258703584849256399074639169511118030094160388085452752228285346550902592075706608972735517197338967641131602783792593094883295355234820886566983102014111 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((1323488812438479108916929299105952071364220566378712272441184352228822391024919051791634627837892808011818420623842068460514377752594338650245588696010595080356992241929422782512862894994733404617338748957951100320915706008773340026768649262893941233445992812919510664078478628691532449705078693506096033322408614631367832420473803422239660960708481665301679 : ℚ) / 1323488980084844279794253907311940565705299377441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((13644963028328945493583393045660217942480664561235220873871247887027170119005038500186637646677188785793325357964308204355911111055460005746651665091594772922302242968295961174099069622064926329392141995829893947097789547358469380814908048237769525886081358776277273400315653646864344887517585094116570864519072685374697341372577582970785088035190112842508689178438288976747251 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((437231522737662441286098810068493578129627011308012098120042316502009676263128446028673072206660100736296122292252699483868457989013507481913865759591701032358907501928675529584356639628930462632247244590634135440180627348728082903544034153237465062322381396140610999788751067810419134254411472645549193558608560432175944323184791395156163802134409667205725528310721154473899 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((66174442202661532642048758686071869081353060428445755136461290354275553226271990850238408486011149113847485143129896559511528819800504913379113778985845853005163532247318611709329360512831328958730050383973034091119871108481943178226030869244870089782137374412957467152327956444644163016984747674235822167923439904209224329131042678643685284836903809642954418709 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((1368604875442232687696421291232219754969868131648222975724017021783110434183398451252240155532559817713397269275167447009857944383897011346277102907929678419430719596046230378557373583836166308742988006242858763464461931913296124007128889581847995414911624480830444960050324074760947794946424982095266922642474989079724048889926731418077689261942964561711915320586085268693461768767 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((1373388399857403032465895237460844741486550632528737751279264294315079770873258477277290672515981157306957618130621349309979980337242215645105856022206865304571784477897941125374948334821700138706323725380991528455900139548592202404287091014359801152389498468609385807704363986500782323360225094425846255030682072287716538349431082398663828207216651438345277923801179594903955669 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((3308722174265180876529561193254836180201338406137223708203871010963313469943080940785022470685958330697906319741923033315942235748126284840704025127234752102272489666805963395659201485366079847184636874128169966110824290742220916683808298396133624412551095417308097399837097520915658337762088197891421541174821880353672440257175532515252955691118024461024303721442839 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((137262819594440235801324416638893999348211957971020092085412872586522376511715263752683421853328705571648655360558994886789031818864591483870882775051414448944813311854650199117555194227024271109082454391915245435159894158604508701959744768605841879871243957775082468661855560767875744857566918469314106823598682972232675005429972398342010267230905368528137228098637008655623367272932539 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((4417244094454863455613932283279577321584754117018855124393796005473732136045664835850053984305281019407294365523953958299571475768645658887244709972545596427218893566412825431895200109455681358275804030372032330936959017638272103746665726237891256510565397233143298298706571886304010155462154629406738979343470765814405640629641158512153420278875365005820851873632021455892592811186061 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((165436111315162645127130877401652677652036670050130851893664250785792590789060736848589146658200015434744757298249559384661092446537231502272203003437041127541297178271984740925289463462787225480127902620253983695082252299702644810778786474229537276041610492175606819608790883521069174421345680276652863347003698507828844573673868529676327665344349370408217026282657421069 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((13765680331745767542575463432017671154377129142048409185383419179849952389487192254298716967690677107820830145635469535609705557034444879212764402084230736678348243825272769860350087725916875471032563410906590620838384002282531649060617269278695676848438413419325149648300087139449998020559055142813890661297665396443198497902865235675848510526821023842802964312995737113264096138628700282663 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((221975720987915521731252122710590405581044319710333027849675871130348288336372047971044630213460463193953069569429793971044513202805193619847360747195397464698914828687455948472547275919645305755605976694355115689059991508695984990827450028819893084913214886275444665399887531755026940648404773158803992709284032714535492192054149078182505266494517631891421154828801286393349445259524212081 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((8271805671319963264725329338567986734275188219340736233584102318630391200902983154684110269069832826203029548347282873795085181648462019278685548052444195585477967819672692924079918822148740524954269137206324372493182058051236002618106146045966556826284179278056544278348254935333297475448415594504083318851287052161124053198522520117498289710685598306831772973313694230190399 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((1380426119292141439655040390455739390146946590200126619446984326999518924287388782116181523949434000408732606387886768796080041908036967633099287352721193585927561888641424739801495878727522896406212505541039510895274464028498675911466708097286173169837337043814927818825855901734236397029336679328803385364496538164099629104140479674358930373131321941230390794644184920651797053409361371626856771 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((44616496423018153637099491697726597638860831734058741466745843152806258319005902552235884335624557916484837577260569120684673472003256095421765047711209744605585373435935887406757441270113633796331133298694696429231985209167558787325587321494507801858673523790849825139376880326796376161696476400005314897000984035046561621139742911523139082816677423184887479211199378120538408833583999059524879 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((413590287848747209076796462170318587258999085183716881803053115169153601411834929568689037726432187591883111805997613472740400904659752584155551370035713459098426632411940824622846386533396551837919653165597786116420889277196695862219184451230909176999175437490032057916867050981407211876417669084625164329115566993228963962317257163687023111852225408906471861300309888613054677829 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((138420415053652302950868083094296712180673956984608362490074793976798995072927493896706613701116746575817547094674486155459660694698507566505322594909242127949613061057301532097099473838348551795870166541036213327401138399900163147497207330887960453487148136971686629139934880455558032327654166836276638988943741508227679609080125332255370728179197445782084965516381833811160100299220378646069117190607 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((1120911445031325108601084019226925860791910878636078191886296597469878229151126569085835510013459464001425631520858958238280323306071480364430895786849018327033483832617815006927561648577565497476860466558646106809212483030524646087377468807356107217526775947963902033934006761461369189146890598963702785568518643574888703991438246105968796476448259096625557209428041612716955710115422525437250722017 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((20679514566192771992635965545475835276820873081830771215147292935527730762879554927531282949599080282790289729081129176202550805102950822091774874633718930749082266903584851195773500748046431504616238248581467780529311898865147147826094532370889216220033546674408090621745213125366671993038141252432327541996547668482292296915173440387946214670956637064744469884814872490920241334200359 : ℚ) / 20679515313825691871785217301749071339145302772521972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((13879037879683138964799381570487364982136644279121686979365474851596363746721821642413270816511207913322300756730601652536369303595425608070360619091990045042264807848077460483275732553218489313846693856926196695676912141997294470340736342906107187116333938197185076374314932049808896977225695465892525345221226555239569791199728068810893164430500666607611253001677563841535614871259820982225351201855623819 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((450549907468223186183966661228013486783187429591474321848538585129025618949549259104348418209464762015151276275578436292837554476648174986767523655086227575318833501304154165377585154076415335160743468573927685743342824090248217413668022740305087914744671434186110416910565043542229628072032343461493342143271083233466802761000011402285173350263656476148143811070823591907557839977046294641394844540879281 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((1033975735359069401172296572083692106672700701645065899145522071687295564780786422964871680548184286153084844598550491807713688713831817803085398438764610739421016650545340997863726698848991772573785401983198729323854713048857884934452481272819346391262981022127410644614825041709251249429550428752431960706341935457995080778145501649979365875415381722353747887696824191829125111169842764989 : ℚ) / 1033975765691284593589260865087453566957265138626098632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((1391526658195813297875328686185476257705848670266587512796599613499959416134268691688125989108153193579494787838059790650023851938284591838692629267774769799822613615626177013520103454913394309224413754916883199398839174408552375613169798165155847054442624309459755362610162967215734915565517986839326436918386879848453772452856710650921647592608595564087354035972626127126885854485292997839719064091849154874423 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((22636029916419728020571641985551835993380485258956111493152737680721165963306261197056810165466133538569719846047329155568318087162096430524524842654477004525802374833299862932355956007425053154332539875113371476079014878411666065635861121652791315291013833531520611957517610624503487389031749978567907566516591314861060476520251773140039866486150057877619358349124819018197528757033411772141647150709810184451 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((51698787053955927107914384922917072142658193158547452603022038470425268358721285966107808951520384673516805230207792003130752064808870680088977700059119022309050066529275029624329255899002445205091047543860355647398109563105213249675671617719553702439930403048731177262668066767186032440606290444914917077816998663466318422250141147441312852931477451857613905551747854286699434885271690818368719 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((139507435408713765840870974105165508072024647878428054410106689172621099760573128400943441995025630961862886489139871147844183403715910089006496702466700761950141209373160564621066382221130316198774362556178792452172612151650636223602878573228608376755782220359812549094414504510860758823907419516611449353461733986974546503957730405224103352926230719448441190057252055020093790055150332948031967530621760556705196691 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((4548763171761056236552608363823721608693153477598681199496081442689736985452675556853690728002518968595977699238928377742007077081574207040839678663104627229763672041198750847424082570812008387941654276199055109140178715412834646130676493923407114405263797114833471546976467567087914003133806226210188791166500520042960357440078416753503304601499002267151001717661823773265517532987273014394638276786139804479305459 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((2584939364301202040342851545553148518041788204240702899996660247783623562581681292930959916972133526589250304994760329359017742021360692361889914269098517854100470249159217226888662241078428204415748889901958488970588703084741606752591673202500013261690416382090072592723706136811504522147837809640643100764113452775492004709110476492841503756282971699315253762139962196265682772730357768192037298549 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((13985484354680778362635865529171489056249683884935082768944339924327495218338596537901435108843921581454526672080342937169408638598068835138880147063421662500431988055458031256500095498000437207013297005071235574844795073375205710940172215508257574195379348281417437464886433955897462010665449657282241825352853376903923733096296114781003032185087541935473350829755669286155366780250679939127916154871236595184488743729247 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((57127093841703084316150808109770834462656887508470048122086578809590005697572602945271996278154224671199466972071333836957138780715196845232720594923657098089558663126545000449693974433889967204210595886119413917010290939423604441113191823628452021675773407094991517851563373797685677717407786315188935958914610918265722545268521323027551460174333368340622807747098251695461698624044523446160200819915543309980314799741 : ℚ) / 78125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((129246968685821874061132681796910787732573521714513267377737159162829391557501391735501974791476429307252474123942421322424708811548624649814235711811595967858710178478638602112099915782792910681351348212212357856025754272851051727559396773498628038040041883037776335159393481676579549968059927774930531241100846892554486123053321141791072648896156444812919160383780406264695015772443345013319145239431479 : ℚ) / 129246970711410574198657608135931695869658142328262329101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((1401950429805900443980930676233262845023598711163193721163279039663722462734297769209732910597815298301647911585398235168484847127628210938714828448570896060293297596903739593218497091323086611590932092006301911587908854330713533138610679199892585110153664854183189801619555283758081507776796194195285613510235272164726054825720727014542390991069065510063647244884826815685451966372406815308741181729298783987999798003297700699 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((45914160517028700857371319912115705309714129436585047568665006053151992566600480659971900998340065098678388139703351391657283437815924921871840366269456968630896111701938369946579767497843436595960684468606861415297979913034593793176108768517714692439017373025574002394500321051446449270702492120873438501717993023652392711810352181986607065571935026738688195707946490928975590144837286102669518363176149266438891179846626901 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((6462348453390369556653356620296167529453246973492703271880807096895151244879388964101050619264990213424540127682467975472092861193339250667613357063908260011995730651056846726290005683223691179253105548317667570576820876603840019638812286497612838131322539236725623693751752945100508921754159329756706582982702459277828056498396292043605608438365963122504943255930354862564941484903798950535371041508974534509 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((140528183287930481526877947080852049771999155021036521622304914164025675389087801691817094705611406506039811407962019228346245868478284046527187848251245424085150541982866029829709525066040912004997948722833336859710605584882693763049851068074911829260864249106314232578887219766667766220750010522736873342509197659417814226955484282899084831019468945572785228560521003305850679084510137928431608473089173272331585319899286375821383 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((2306253027151962634154251874260645629295357409052067931009036439023498918245649391736078118421034772273558967621019369273511861479858794741106649314083979013092422719477662631627979495403067358710748695112424981377425558946680910223637568765344147910616765218213269469007933513757407154989507812527370085601041997215416409427281778881622757674195234965360662143013050374960913589071050503637269051898778107993516201010377324219221 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((323117423444395198488940460797720810855198014162231739498407865353133181156001689662543724674199917948847017520205408232878279471474966738835741509439822016946678788244027328532311820574068374833477745200796091005872199784694393436766253275494650455825886739373195278879202368735672747464487998167559342778191221475360762080196435964501123139952945489843148052836350427129122240984032027222170538525060605839564639 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((14085441094347579178711299561466650403006715586770558344792654165730725876526858185024620421227760287877493478500160983324092947108982327366441672541107724312081738154186071275224407155379044735941077682498931011099576142493476795299544189586350017022038095132623256699684456254770070791584413908673529444075097036071979254308261990749674601737760086000879973812547075332401443263756927392803422532371131228326657157709933243159877175011 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((463343494580610111865841099181658166628571678429593535582771094458366394195704720911931718353325406889777828155437491068170036477914042525907493859568200659913218484594278106880205674755172137899914961681763599562124775983252719849632555481342869050122945200662892906809251417910021615901017355956872591752392338560370982367170441589446441131465752690448426854679629159210480532783579582585418967317642093832133669549434039717527607639 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((16155871203657283358192659902808580918093755192608867655936487536491966292680144551299061453756964871102672347812253617416104676437210875561304868779483019049543705117848432745884422872510528035369025600541498208199241017464836236123043661640093463643312050903109905659408119301974979037381742573656050095853996046476861478355649603515775066911030951468426359651623573179055618438963163376430680918500233839516976968869 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((1411738693829437151987915145912420566777142073835736689162044579576243800846173001120182087207319922347480532920927482769018171029647280721710069672132596553397130445249231145235697640138425770779768904722403213352905579034639000011706264216969388011570302363334536701580115688123803611233106012010060883693179873041950077516012874783564447671836367531304839267563492538667050582473350848612712460099312244419068391361174407424566674877320687 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((11635500829409273569073881875241401987638109750979975828640162430147794849841528506164489253677823643393831445209182418616612634177444536880226498754781997684976176092673031883021941623574173079233070517583527940260583376996745291321282540811541875786529642667730379551342438741996195653202157734124162872802813201879575681603187809469691434935754479837558809392736023167068906490930963899569959111191726482615700533679563199630290195893747 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((807793561458315931140127228306059431472357569920982557306328337405515564460326144590754222240373821785506519823090941512188782827734082432397699831252405565859037660336228764933276920360624632922956737639569123804851407319565870935748004396400231913472813217190071982507846808200426874525614677955799608438892473601612747038367060064238510239647436732025525837426019987447465495687174501345169155544472987103043272603984199 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((141486699066101614407787683489656012346032007772364300735680600803862117088884198434873101369731834577054571825158069935817355206406353082592549232797872288568792010733159408797979371890699508079372527600618906334913544335835109217984350051758683492091132418134240335341652987992865780485258633630105313761936106617587096987106921067018351248140665992363761430497850156441561020382792667708048775751015153693518587478095093554321198810782518075179 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((4674799986467455740621236487642788065600350381587222677278801323993719478153159074957605553903811074672204661320873734441955677002765749395886655345035114007137130002455712773634257438085492934110314540829427360908361671829500167611517991165889411950543996129106756216491982857354185537091632983453269650623395860638711650917797733576313984221097448257470087298342470155250255870842946679896408118042042179527352575525262381111423703746398316921 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((40389678124662150043030742949065761946483810369346592714341502055004171965719892012191489550514206323659785015742622588091011108103999458364807079853741346212467016917501137222107977935950901982317277802774958921886626446362106949734232286366353808961505505034618410402325852855499518726378713099344745913974306546491030760093589993866220598932736155655007608750211056910731122625524356694074857809594813559757568612816242937629 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((14179303753845318341476178119826643381304896359228020740483828255695269588992349647486094816915501041061176948498300366461839721676704314487066237967970862178859564291184301707248707973916607122564969470730495923076921233007227234750137621217957828595021349040783725202019599409713243422578193073245061944411524080465594947078687323261779033458940387890605101120880764397781808173683605389372024066126751280605641161136756699334246886611595922720627543 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((234761592348656018698090480391030735174317483881017508816794054759402767808262745442658995639859220878585585460667340124950675076313781657723691155492393469550056596190663952144183473745724977371670235600786521771374570446889058989225300169607845697550292405823960525166667309654908239249987313247980085789768368251152783733027608754511535029223321448989475248710753976468765435422033672524311906673300619093389021859496605717672412845330502092364391 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((2019483908332508809433032330659578265541734240498881082106871833779824260821221738826620922553911864757201137873693941021440411666887362025318588036746140157185999343359938638238142772839464044324594277736382858419862321555357041057667538090169340383377239844759503528432762176200470974247910769153515686475851590897687608967757039641146435919300038571079313694604812789925272376040148675435311056193071180932924316190567792222546159 : ℚ) / 2019483917365790221854025127123932747963408473879098892211914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((1420930194916572755507718135554694896401048046928795837894119428489022832311983362767155353318366242376162142222149266077782160385688296725775555656376089331847979977208435571996862878922268053589192949450087328717851749221155955825178078952347836325522982974806082089998159676337222857894603520349152031414073791793873291379991570805148186829955593527070139827803522455611991487102439569426601331806358720036335755128697657329670832085779007722633732359731 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((47154940073053442684363543368528980884538385615913204823229273369851739451134623715686110165870414995479064599197057493887922410595220595767611410554526842572223928200109832069139976094935315209414508108484671450539094084362822063524036460778787079638611539651007718045659419346919977861184005324696239943312291420666917074720988222401811795250479557979508950853034269736423600605821034011204364919454446605730508147556761035850884547346741296375378063419 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((100974195501800250909369157610841311691840678371486127836824034863593750085777787165934837448934758265064407364673636881180858941737287164729200435238827652317193179359456070491959690436869895742293114442042788948952234247822390512750629687856260308693997997741737817652045594250629307896211987815327284916011774894310083983430870855280952051681921864867258835903811859700058225568324871911086004860809090881629672432167525898260920216789 : ℚ) / 100974195868289511092701256356196637398170423693954944610595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((142386776822702873927387483472848071296047402524640174534020407462952818061962487073819394253435006366051730317195420653501609936449736199767175828614071983769572776246114470621748646322540188308553109611824976515383693059996485610522944886409616727832005498243397990113433244478135911110553286808811220623688850746834142206236473038031765532027944253169926236194179959075978315556639283378217424417008889648408864744260821522916283183072762031179037650244620927 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((295974044551989619598340036850890008094981774958336914803746156706707530052140790404264764519892799159344303667550640260839420085596819091798919906126953529589275656694003466115391986127943061895613670082982418754851405212286580931505065685925474699289340162952114725193190368292695520578855988350616182191014016380481208607912004503470294972299345311118139726124442076734692273922157952488099709079844028601823492376573608124628784272628081193033593540385203 : ℚ) / 390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((5048709778545639779737096239612020950677017087219864865201094803216487034730090603109142290140732077571928071192174121906388628125223477560228390858074476682160844479792492235929296600714248540160573946028117990447941095668402205492805797066016336984024192766380044999961141804342281650657216557655643276327513719237054417291773861469603505688787251979529558231453550959891062269532508378304670303207885626158597440245468693218343794115346519 : ℚ) / 5048709793414475554635062817809831869908521184697747230529785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((14267443869186416006859138082296576789955766884784691875590658061755840009073918600277294481217798583861819926519462309529505835809075138320235836679888726290357187434967884266832381682909371108803243909114143363003478749412340832940552898080449196970520730810203095460343342188579880975860767655786264035447990484708009999742616111453513759362716449382721717714078220167149919249620528666896438578463145402019760437268778526060051627646353635681749242398625837899259 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((475550235480341674522652330866220854600789379414267412600833172147494441984837076832529042772803143251242948602645563074923837014838424257611223302694678764813351639336592131771201301510032025007657406383798326755878028210590323309155541342280031947256594623667575384612105628332680622265127485352876765568646935476925191449994155918193894701756933606473005200495892782431222054972438140478746670412911361854154983629389177396070430702548716861832894484045839597341 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((252435489067480241508367738846428206691284706496112196082738961499577345486034505858741011853299641119170693776337696299864093031668441708096026045502939593471947621389661202503887492387577777522854645564306774990463418192362745879048623992765348807778845524724804805693423484143970708848813932960647103363883559103166534763944557333683283829299787600061493707008302015993740287337203397416198778871447127738880456748198910352561426071053723622349 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((1429561315794594890415786116593921510203912022738787898444675906005936000530069671643217457590668073680567460357674057070910095493919772647985981933969542944914411710387258701768400326792476638983254014132826692298970939009815189674734490950760961226044996714681374257824983439009091312777323570200972097783312512904394333065381312487096841519332009946670146231093861038483368134579977644926254027098159766115344455526415740353273841382495447674953747943488339029104876903 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((23876227325277465503100018980452646530174314315289632902305306500834563976059152996324210977733912542669248397907591067901432862025102965953579308180403591163223552919569059448920987565025681925452760382294962523349322324361640849591561138241724705891827624589947088230674470528064940028154526359305358591625967183404332101359657427769889390348326594356317468414414396496725431515447254392866836051098393088967883444100621907086590605820865225228285689734637393557627961 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((12621774459061995378468687898194884008740484139779520839106069618913414983713905937194981591900219739845874217199796676581786118387820348539163872692099762246750386947399944646785219453656418011879735825189490168138091339482348963058881724010482966480395541783610055771787884175205035628705230074146413630576119876374569481907994635584864508238521682722094861187033821090882037197557679036572600657593481419494119010731177991913769617128720621082321279 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((143231979341437869127056424990970805508947806505119374690326105457193213973074168084623175573640271001921904445494506892776016379135865889261527896721421070536225909482508787866877904578903057057072378917231075361895720533009954114562356127731823072942707748531957798653202959690587512447714894731532620747788303108347063294960264196340657877055356003170914084946629070499979380381148834279538767906722857747144821835569155858043462809320016543578056711656118423850610587678851 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((4794812710866542994686648964998946308281564156536793999487402378386942042755180897076483768969212221597259397939888657385381163953611757011791344007651515393745229011259742765317952641734055366135533204045493025658779365164042021135510211673554943430676175003259691293377068678359273083474581843796635164285960611440803171695715556165161874945824320330258398326143850020077795317470482917371848924856767547061933562335799306952230498984763576517980913413838265667677140944799 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((631088723183866939511488154990486900872028797661282586555035711104639284304256877777937598164983815065286962866012950965599644609112259360582417478991179454112909948842963154264723138454294535159972762163762805611530503734138379780261890424829304433076127525702843572717206248872243500492199889338194147406103759504392658450489250360313537963745063189718110613219149155478175131142112596192786981279225134670295902384374622309933547136529324317930856610309 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((14350210326381628464753935409517549068774678028444460061998201116047503693347028371852006534271274150874060531608936487687053386065736127220927134256727816530381054212513910671145271751652854688339646788315873708869306427732304971423825478336197560897550303045206532973898615984988622412487562639018112105374395784131880442999734261763324517337223037059052543087174313028956143212742707434557615792426861669459776236203842615615505744158389115536407455930506428675106221875017405967 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((120355072249236391473058945792943098523928709492197615124775236164122084074141561324309599162230562323267786153059910211640964959906427043547093544344288148446752075353664634921677844630464081366139774114071270948168328534482160277800878259183652287625802295080589441798041323995662645058102190829125676496192280508333364210446161941442437801966360279150934881284551681516904098758733098232210005925714239809763216076021346767378694756564133650910064913279392498671721176449196677 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((31554436168555801853502336849760157142950011131230278148707521865011476653508005788328706295151558361013757370437011433625343181436293474518189259540151141632814869534507858131674082450229183585975254933746020786465404066997728206065005156425749710154331569845290066588709774722995791058469041710339874754413035626852714545994799376368280548727100958670053465688914100386905043245566650140137560617479442938708575055636462801736313940876131216902772783536846439 : ℚ) / 31554436208840472216469142611311449186928257404360920190811157226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((1437666221159909031149000004120324656721330593025159172134416859108211878455275521894623057285944723065269420540807256413753721985198301136645771700808746885249509628649757321375620162805769850005048140896123740852411844348431984062353210641987892203423209075930600018579294266764660783798854580376189280420260935663840001424167145755871273047551501217003216359579639312585063861669471416898449061067656386439157800101905377509699728679819013437293253297609610128138900358883791505364939 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((48334149257115569702571765706085768264531173784454696029520310698118563138389052925595786534190227016546538860277108558377791405838803571516733493462966076518614415415669092084526269297139967610249140203911934348233686720458443493442781528824140998617523434135819026589126371735855113729495095846807030788304591125197124838000739576189358821969212833419322554075394361631574695370453399294624941431873697252049413164582480465878321712911317447650994245373770075309747001230776783076161 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((1577721808807634249527530854013674989830171440670862731250371271074638431809473302838283943100593874264689150275999990873613798214051862554677456448803471967184932071884518312260149199088248207266602067917009809327687908402164831048263324201349091490671386120193263291570544270286662239033147491230199058661291268417041481845555005498637510142407212994202739156464933966797124509515884562835520971811758479466345598582226932329243992895285519600962394600873396876669 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((144025652202944881343092258478929955056834431311344023426605435636636049551016910759731707770611258443943010128185311109155447637652110974872244422633087302224640463046637713058793206149859874284104998886965895200518032535015239572698087171161819810214655341011365261804659105750229772202675598929586876510428592832049693508462604750012732784048696675842120504754094920580789478958809726735076035631097368542055511669010628792748331842976087837836948094944154584978679163315896682380323833463 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((2426223931179657306354853578555217901906042816031907159988966512209620940619267938028110555057655696304868589898761428930743391170768149367558863199264039517280512964378662850025705697217655112892033025081227220770766977590906466886279848846694501171252554320526158990141140688187539428508056095484901100109804371797513584939714148048040139152140970656799214032839051462858256172335107626764359330892423641740694440775098772977219865608632869588259475750964016132671251912655585588839177931 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((78886090455792369764035831562291590731577212472743527693516732913232046441942141369452017855534194072792703515847595629733385407342298115705819085584405661180659879088426792446706513156209318017013312497461004974233626131784229360459091326172933990868028806282360885002308551589800173699813826866700406008947248050947789959956012128085222423987603038387799330316938835966926138475568952598799921347374853270429107280079528871529758035754628815730645311352034584683337999 : ℚ) / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((14427930741637513684520681844157149552932490993185632179405431784491803606891505799530492324967598006827180201963699392870502060555999643997448722048181783401176172866429804119977816605942930879146770664548825738450533628424327070690965941939383209753219179378957327214236971822936756655652784453534694014384946735139505186619682714550654369366876256094894899827237103851648692239975693684420661054993324973980665831545773424586286014595327771380846230614980906460543678250242948557396527754620371 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((487130086054380308601074730813790612358015743318690571228247342574095053333018029255863183953002602572155783172311806678145995314720067264550799644654408385544033622506432049361414296910516123425485382869776520489597709261585296424211849631831549098637629156978991554948929109558798668166124861011873591206870759421603160171645412089459718074022850927229022070226118107408994998105412036020811085912662251823905613694330976877386622222417762799401085017706667390136895057648815862211719875963779 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__apps__self_rec__none_sft
