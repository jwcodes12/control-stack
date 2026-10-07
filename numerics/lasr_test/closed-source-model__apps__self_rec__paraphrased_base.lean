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

namespace LasrTest_closed_source_model__apps__self_rec__paraphrased_base
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((5511 : ℚ) / 25000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((5511 : ℚ) / 25000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((5511 : ℚ) / 25000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((154 : ℚ) / 3125)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((154 : ℚ) / 3125)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((154 : ℚ) / 3125)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((5511 : ℚ) / 25000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((5511 : ℚ) / 25000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((5511 : ℚ) / 25000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((154 : ℚ) / 3125)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((154 : ℚ) / 3125)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((154 : ℚ) / 3125)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((5511 : ℚ) / 25000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((5511 : ℚ) / 25000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((5511 : ℚ) / 25000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((154 : ℚ) / 3125)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((154 : ℚ) / 3125)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((154 : ℚ) / 3125)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((5511 : ℚ) / 25000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((5511 : ℚ) / 25000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((5511 : ℚ) / 25000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((154 : ℚ) / 3125)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((154 : ℚ) / 3125)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((154 : ℚ) / 3125)
  | _, _, _ => 0

def kernel : Fin 8 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((19489 : ℚ) / 25000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((0 : ℚ) / 1)
  | 0, 1, 0, 1 => ((1 : ℚ) / 1)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((54363 : ℚ) / 100000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((0 : ℚ) / 1)
  | 0, 2, 0, 2 => ((1 : ℚ) / 1)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((54363 : ℚ) / 100000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((2971 : ℚ) / 3125)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 1, 0, 1 => ((1 : ℚ) / 1)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((71479 : ℚ) / 100000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0, 2 => ((1 : ℚ) / 1)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((71479 : ℚ) / 100000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((19489 : ℚ) / 25000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((0 : ℚ) / 1)
  | 2, 1, 0, 1 => ((1 : ℚ) / 1)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((29341 : ℚ) / 100000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((0 : ℚ) / 1)
  | 2, 2, 0, 2 => ((1 : ℚ) / 1)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((29341 : ℚ) / 100000)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((2971 : ℚ) / 3125)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((0 : ℚ) / 1)
  | 3, 1, 0, 1 => ((1 : ℚ) / 1)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((46457 : ℚ) / 100000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0, 2 => ((1 : ℚ) / 1)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((46457 : ℚ) / 100000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((19489 : ℚ) / 25000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((831 : ℚ) / 50000)
  | 4, 1, 0, 1 => ((49169 : ℚ) / 50000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((54363 : ℚ) / 100000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((831 : ℚ) / 50000)
  | 4, 2, 0, 2 => ((49169 : ℚ) / 50000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((54363 : ℚ) / 100000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((2971 : ℚ) / 3125)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((831 : ℚ) / 50000)
  | 5, 1, 0, 1 => ((49169 : ℚ) / 50000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((71479 : ℚ) / 100000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((831 : ℚ) / 50000)
  | 5, 2, 0, 2 => ((49169 : ℚ) / 50000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((71479 : ℚ) / 100000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((19489 : ℚ) / 25000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((831 : ℚ) / 50000)
  | 6, 1, 0, 1 => ((49169 : ℚ) / 50000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((29341 : ℚ) / 100000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((831 : ℚ) / 50000)
  | 6, 2, 0, 2 => ((49169 : ℚ) / 50000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((29341 : ℚ) / 100000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((2971 : ℚ) / 3125)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((831 : ℚ) / 50000)
  | 7, 1, 0, 1 => ((49169 : ℚ) / 50000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((46457 : ℚ) / 100000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((831 : ℚ) / 50000)
  | 7, 2, 0, 2 => ((49169 : ℚ) / 50000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((46457 : ℚ) / 100000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((5511 : ℚ) / 25000)
  | 1, 1 => ((5511 : ℚ) / 25000)
  | 1, 2 => ((5511 : ℚ) / 25000)
  | 2, 0 => ((245178879 : ℚ) / 625000000)
  | 2, 1 => ((850694493 : ℚ) / 2500000000)
  | 2, 2 => ((850694493 : ℚ) / 2500000000)
  | 3, 0 => ((8222666172831 : ℚ) / 15625000000000)
  | 3, 1 => ((101356304722959 : ℚ) / 250000000000000)
  | 3, 2 => ((101356304722959 : ℚ) / 250000000000000)
  | 4, 0 => ((246360916042303359 : ℚ) / 390625000000000000)
  | 4, 1 => ((11021032793654220117 : ℚ) / 25000000000000000000)
  | 4, 2 => ((11021032793654220117 : ℚ) / 25000000000000000000)
  | 5, 0 => ((6954062267748450163551 : ℚ) / 9765625000000000000000)
  | 5, 1 => ((1150236405761424368220471 : ℚ) / 2500000000000000000000000)
  | 5, 2 => ((1150236405761424368220471 : ℚ) / 2500000000000000000000000)
  | 6, 0 => ((189346078911149545237445439 : ℚ) / 244140625000000000000000000)
  | 6, 1 => ((117640301726408312929569464973 : ℚ) / 250000000000000000000000000000)
  | 6, 2 => ((117640301726408312929569464973 : ℚ) / 250000000000000000000000000000)
  | 7, 0 => ((5035624716274393487132574160671 : ℚ) / 6103515625000000000000000000000)
  | 7, 1 => ((11906279722752735115790184824327199 : ℚ) / 25000000000000000000000000000000000)
  | 7, 2 => ((11906279722752735115790184824327199 : ℚ) / 25000000000000000000000000000000000)
  | 8, 0 => ((131775764704846654670726737817317119 : ℚ) / 152587890625000000000000000000000000)
  | 8, 1 => ((602560006242290822874345762373656141327 : ℚ) / 1250000000000000000000000000000000000000)
  | 8, 2 => ((1198361084568006939099701817604899519237 : ℚ) / 2500000000000000000000000000000000000000)
  | 9, 0 => ((3409089743567131452877793393321693332191 : ℚ) / 3814697265625000000000000000000000000000)
  | 9, 1 => ((30524343317495205723605721935632051600989951 : ℚ) / 62500000000000000000000000000000000000000000)
  | 9, 2 => ((120256503640370561230277089910455152564281031 : ℚ) / 250000000000000000000000000000000000000000000)
  | 10, 0 => ((87462546643239199885135315442446481351070399 : ℚ) / 95367431640625000000000000000000000000000000)
  | 10, 1 => ((1547266547981921595936571998193680105342961913583 : ℚ) / 3125000000000000000000000000000000000000000000000)
  | 10, 2 => ((12048504307401464820161553438802073458852009688253 : ℚ) / 25000000000000000000000000000000000000000000000000)
  | 11, 0 => ((2230127487301573141561402162657839475051011006111 : ℚ) / 2384185791015625000000000000000000000000000000000)
  | 11, 1 => ((78459172235028208157231119326828486815665862316375519 : ℚ) / 156250000000000000000000000000000000000000000000000000)
  | 11, 2 => ((1206092839663265832018442529593597119443571802682497839 : ℚ) / 2500000000000000000000000000000000000000000000000000000)
  | 12, 0 => ((56602202494307468330890166748038633529269153498097279 : ℚ) / 59604644775390625000000000000000000000000000000000000)
  | 12, 1 => ((3979212710315580357626757757502475471711974464847251495887 : ℚ) / 7812500000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((12069114397488010550034669140031417665324415054290853029283 : ℚ) / 25000000000000000000000000000000000000000000000000000000000)
  | 13, 0 => ((1431601521768735984675718459752524928851926532524417870431 : ℚ) / 1490116119384765625000000000000000000000000000000000000000)
  | 13, 1 => ((201819068742219215318564260441454318800757165013022974846884031 : ℚ) / 390625000000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((3020039041246795910108278605874776789803563231506743818873392687 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((36112511991680338964720077062116958338395196192368379876829759 : ℚ) / 37252902984619140625000000000000000000000000000000000000000000)
  | 14, 1 => ((10235104248673210268076923131313874459817014331976195959772466357423 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((151175685957060254790989581179086476600626267795968240303750015103279 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((909097494554094210067804581863597401056983978593067355419535173151 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000)
  | 15, 1 => ((518983460209988274063391551206411472448852146945241563092757817818689439 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((7569243248913054671542517486948452242793919983817917908976219205301421359 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((22849919780070644159620818495939649749199560758800289689771320989539839 : ℚ) / 23283064365386962890625000000000000000000000000000000000000000000000000)
  | 16, 1 => ((26310054998872492730358643593028006804326926208022799101982492985230108879247 : ℚ) / 48828125000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((75814505078551597847404179276121779052722837966025427497866606010236576316323 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((573635054311444336517084506667367833962150239628258845763953274765141922271 : ℚ) / 582076609134674072265625000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((1333460410616818420349273592507173830921493154592402271042991824341495104460112511 : ℚ) / 2441406250000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((18988435492301526236137928979351059149686976910619392360072974981318230632144896047 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((14387397766416927486637319325440331716088346020115136645093685371897850923139519 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((67564300765777311446317555723761846147785145257651725639055887932536376399898044836463 : ℚ) / 122070312500000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((951372074340534961221629771671687610586891140701705483548215726152880600860834049681199 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((360591599893229220093471200708506624814845775586023898076230834212917216641066085791 : ℚ) / 363797880709171295166015625000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((3422362693794621324150593062384951153840276954950426780774085701188695065066447732103876959 : ℚ) / 6103515625000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((47676348466231538641296552464228345631327801788507894264679106125161989924339393792920485679 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((9032459810907387278061572339983085611016529320396019749607662727975543635117736945980799 : ℚ) / 9094947017729282379150390625000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((173301471236478185528029886405904483257872718120007455734325341363222148727361821459026930755407 : ℚ) / 305175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((477940422422566361715963294694222767377643401706433105515435842510218954434993428490032101679523 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((226155862269480145853639786068305355473101139925198028900103738905515369904809575340219791711 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((8772918736854708300329508027155698542280205754511108425398661473752330218203321450803917285187427391 : ℚ) / 15258789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((119803479512036041150841681553754102255353417752641665956885914440690180542549962205251164108726223407 : ℚ) / 244140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((5660607925137550442329030859044578072815268116002184385234121767529589044074833813805543520655679 : ℚ) / 5684341886080801486968994140625000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((443967780728604575494157795599371797637246632791326795549577170196412870279994757725361001456707375046703 : ℚ) / 762939453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((6007262011652520308906915779045597621611629813191617771058224130089306469677870453679883372285811713289519 : ℚ) / 12207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((141645995987197017565236609120904157061096760312766571483827799127384160879974436197256237674058528031 : ℚ) / 142108547152020037174224853515625000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((22460807330472496698099581416160421530856495167266730377923639556481065044254946985521982356382439283689186079 : ℚ) / 38146972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((301274061463510297504414463990182236878407057514412135258789000307292615330834022635702585407289457389353322799 : ℚ) / 610351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((3543699019149265100196049442881910491963714761735507711648319977193589911389821787048326816029726652796159 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((1135972388683945430855160651051437873139598638841237109856754118128417411460068919840810612675447670104489202308367 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((3022396644473060026818497362888507873949732914134021745128853813530448568806038366818872139860295248618608989362083 : ℚ) / 6103515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((88642155268069588159399636785440787952880836991463309792314108035525873783076236807784841317603342736344342751 : ℚ) / 88817841970012523233890533447265625000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((57435611295264439338467646363844941538717078819883696183461282153447285153410348405037134274455508947708653392446940671 : ℚ) / 95367431640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((758144991940421180741843700195705136232436191777311664543858468542028566300893578648789039130087037618351215423613342767 : ℚ) / 1525878906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((2217022091116147219180510251139336375788694632126628444542409651504363754158372779146918772438771546588614895874239 : ℚ) / 2220446049250313080847263336181640625000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((2903145145835425492377503038692596318494915073642491522080238680195081407384026723624180773293827433953147204491259297564143 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((38040894996500405021339978720976308186111437393487810858412278247255237679848380360975682002300409999625445166669618973672239 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((55444421711181068543158232530151548112120869685515861755687021698168545204792527092794299956059218671465515705693043871 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((146701150205249117271150576438633908018672635066131990300735276808453170522468076934193099231856688426350379775945682813911704799 : ℚ) / 238418579101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((1909032983941956231840916694134140857853621656019552739374852162631166583873043033286120415932823588833424558630894278936903164719 : ℚ) / 3814697265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((1386478289164669729551342499922549058266498629301018629756584365875606777496201560511468111843638112688191435588251732001919 : ℚ) / 1387778780781445675529539585113525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((7411036528155867691101705039698697101047403754736787997365827065465418534046883023156527986326913524240058355590433571347394993042127 : ℚ) / 11920928955078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((19163156256114207645324650199641929656164198912132935917072136444971404623544077690912457235677553913733481354564682919948472346615203 : ℚ) / 38146972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((34669124238416795477069406634551197024290166786447552075326072706549700486623472212808002031720663178180162888179438004985399391 : ℚ) / 34694469519536141888238489627838134765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((374290263798949648573200403570028665248305164345143008355312428911340410151991738849107294552558032958305947645404966572869165475956924351 : ℚ) / 596046447753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((4809703291462757795385726898538804072975213761876301963745575420976423174503881136598262245211350884140103539508884877219367147881102702127 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((866867783804668604998687982239784239499750435501076342396029830977947112783804849955415151596204004679553194527729067279160448731199 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((18898430737635765778927819458878585278178514103576615093677925550676626863151931467284553868236034075558390532388789058607006578523613198244783 : ℚ) / 29802322387695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((241464864485403172568750078440121558597259750922828912694498431928794933160562213765137686923167723228498386814005664963551931718334262027053359 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((21674416776623278391471487994346554060944620612480476836956225375929211281043572720781085889458419847199812208150911792203557985322337311 : ℚ) / 21684043449710088680149056017398834228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((953968566997540556719286371953664782561153800451965863532068279496943576988274104755097442399516188649990182600249926063228323870855539234819561119 : ℚ) / 1490116119384765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((12123859456970393733829496894347586584527326216645729482561335097628714499344151569407070356557300092490661541776485879916123690126827290692049243439 : ℚ) / 23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((541913472010963371287689277233704967527099320491632013075439876351484398656258188755302582899655144402077140124653119918255141575947031854079 : ℚ) / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((48143417226222970299907434827638663591760349715966942747586178796440368717104177078568847431486789208254739837360194369135016966268736666317807126380687 : ℚ) / 74505805969238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((121760402341315317748160432879934482344711440735412642209916133051899525003577736202600003591141971098392721363092191449306513902806573261140706027058083 : ℚ) / 238418579101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((13548870742305472610933312516804800497969378891436416302827247750214079445411815840652092038131379109252081383889364654086874454173631703804145631 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((2429056578603041549765262107486562249927936555217569729765124740056166525378272970021223609370132880483061318281535174236153538941893520701268878289348610431 : ℚ) / 3725290298461914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((30574300989040524904904070874835776483151629757421017494868737563421709866967185695164849278313346233997313604386940951186779096018991126100498436774452029487 : ℚ) / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((338741919053886542412167732459936866550768731074579317325800231403922194311630878918468621731142447460213814090619827743499096237389908275438994202559 : ℚ) / 338813178901720135627329000271856784820556640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((122529163940376823848939698900638433728713654582546409588694955703441355506686039956411958116662812437942766103766498117622831670029573441842933694976878262624623 : ℚ) / 186264514923095703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((1535604541599239609494907185825941625575124327980806816332158055799668842570339070854962663275574207758316695901972791305546638825929190930479478643498210962136879 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((8468940689368574492512947058409912333354019446396851315362520709831039644939374199242034968918235158552107022812089822893053886570491922380030558013672351 : ℚ) / 8470329472543003390683225006796419620513916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((6179389718831981005413901013833697775627228271306140449437601016185764816622705655862462087754075088948157343486987058941024225858809419098488121991861994590759123039 : ℚ) / 9313225746154785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((77133287469644262609150593656458612402760264833817827414127167576646873583157899362128112585715856975443560638919779534674335854316825597343489131830576108177165190959 : ℚ) / 149011611938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((211731170818288639970640078233805849993388676152937610285100166113897131640223463769028019509247485005022013767584818558362727195372317075264415545128460448639 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((311572434757224594057957390115040203861191701503230333024068531901502414119616026811022052502878937963970865133723979481414777766041235149481762876682915271487520757268047 : ℚ) / 465661287307739257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((774945555459305753535461753474869271771211817741855039908188209137471211242421249627364892729168230801647826618809923975216455545584545566423103038596278748608353714837923 : ℚ) / 1490116119384765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((5293428431157239596539185810010018923737456688597335461846317137393741198536315085394587072215724235262874026316460528883931190310611087479828194559008565683525471 : ℚ) / 5293955920339377119177015629247762262821197509765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((15706620114246906589998844334128956658380128558514211730129754854189082790075350633896854555417486303416020683353094674673914396297964081550088394326817091339586841460482990911 : ℚ) / 23283064365386962890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((194659157174425081180520196241998810669131974195933302794116545475563986026027466807118871263080642060600066557919319790871980398781516867324797285732078190401318795012965132847 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((132338617771813749800736725384069676635126912880391830190922874690666622218274244699255107450412249621038151898881499247418934967963499483894371683760517936606227904319 : ℚ) / 132348898008484427979425390731194056570529937744140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((791625103029896328762646138029495544063087056535037935151169030338862594291119958666821414967926348856959630569173058386372564209891388337669185651840117661685177835745313162319663 : ℚ) / 1164153218269348144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((9780031320148333686585622163289418129520372228553849524247721645029303673690586377467520359303242987367864083592197781591848770040866133277782933033129912590293590476051064464106799 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((3308522098679635852461171369329744373702178892033915362965895904846401800411946754943782789101084332864412542357301538832947623590640641441617409744808734066518775627272991 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((39890750871320905004159985124504688901767715305648221960063142274841787348733484027336401679116207987089748608630708750146255153630821607807176352004929754456003374983364031034938198559 : ℚ) / 58207660913467407226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((491399807350258920622956599198017572764249987609454091643506168991831349385387172564134566079994703180292644374192497707394821787874062806472958526732830876581911674621024472441869439279 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((82714156604286365193481102024857649243086526599547951118217345289551524688228430307099382776791032563194536038001449690315316236157995461055681698516577418222384418199923321599 : ℚ) / 82718061255302767487140869206996285356581211090087890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((2009755966850657687442293786917233412649572463623514860174356282305109262147278805597202211586651805561266848319859974737330991408698190302369629353045737187441550410632025180054290597768207 : ℚ) / 2910383045673370361328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((4938404910237992724209092837636548075776662236694629398240110872569130404503772458286679455262557732413630865747004964663368120202131039645774622915436821477180607200643992088426963349589923 : ℚ) / 9313225746154785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((2067875433638910522877386527562207254698632371216064384577312842348069664648883878255059870936880433624098312844610253014555198126483173540514180622389577303736049926298305614642911 : ℚ) / 2067951531382569187178521730174907133914530277252197265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((101236105280015646714459934159423211692061651359813679966531737740527585595178291794387627790221998540908949503363358563277598040228713767934358573754575411688499015267037362482850429486791617791 : ℚ) / 145519152283668518066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((1240803870492705665895417166859608697143902243056529417991218298596286597044740159006709111284279628131971684204833293761773288372862956579975768762523661497701689231502085641773328652467860700207 : ℚ) / 2328306436538696289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((51697305215638065970898219290653770401824622640566737921886624984521529694342097903312861824688862770900052019028609221000666256287030569131080866149750472072511877013627678123775692479 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((5098600026136710724181535125759119839916716542547422865020787133201530830528749804830974635087952372725274037389072220752850077511008095251016123950732748523841817504296354646744047613424123533425903 : ℚ) / 7275957614183425903320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((62355120764058932925127225961903791052526181105326577642045218508678870468166319445899058191835536728220841133264167436429969759548179690339283805881166746854304640730716577691924775823648624118627119 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((1292440803583803737470356227130399161736234479590426633631132809323340092213033146037664364101361246542071113798848565108081984668777938761795635000392486950221183971118589818954264470723231 : ℚ) / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((256739212013360508122426818866958183555051732528596843836551798703004512748409018377587596993176128754372272133669382137485774795599491232923926104568314217661105032144073959207366151051373585204645235679 : ℚ) / 363797880709171295166015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((3133729918795527378784298264352940759653192461917513030495037734576278935971980018240443430982490920137645781282590952928955077737810810828749755835420030400452305685625727739917358159541066345789207620399 : ℚ) / 5820766091346740722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((32311179376950587783647793294915545022454333996448361619624256695902575057139802983128040791971429333858423936825759685391409799209813248528635130522649178172860654413130196981599660269925048959 : ℚ) / 32311742677852643549664402033982923967414535582065582275390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((12925919593653593203199318359654997536476403706443142147669159736546834571916491774114962582904872612609741343116783070831768389403441881982832792856141370096858783721669648723002905787348146860508483230665167 : ℚ) / 18189894035458564758300781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((31499194188037385400688189668724964043987157599144484366412260617387241400861826365042553549519873172033207830034596533892760615794542118614350653231621556119572294152783802921123544738170750868998102508197283 : ℚ) / 58207660913467407226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((807782588775035923917712363133888950927034020849545543524534873121445285288597620338182386994731186287566824104797230508593185576800050400574570058755909833410881293857494408974395779000569279161951 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((650670078925229618132273698650032235958669154130606469241937410209290117040509785959756396389818464765129312544107761758911400682017113868764433812603016548687735084232988421871130545174805566418920807637561403071 : ℚ) / 909494701772928237915039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((7915782422075269189061926126017661632639013023642543777056031359338693074663077377342519119884016406235763099872936132584644926095517370413588781157543257121024085044354453678564664491504169208046159304162685099567 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((20194625220077823086287309235348359114227503672155878695741603501638847164989479022770836540140316089558389834978393225381972593706256182256797795875093926743344665535988708536501999336942094681587263039 : ℚ) / 20194839173657902218540251271239327479634084738790988922119140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((32748576936420318476858462678841636906704648651773083313015697597485612861973363089026673947353445328557693985123005310533215657151875726622330935116739873222350686424074844107360028311099344639464945079516985406919343 : ℚ) / 45474735088646411895751953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((397862415280408763759672556787413233424534096432800778589108805713466921184279469680675243651976228985723395197238853503400892354658593131864838692707614117414985363225825946978544540111412710601527577884724080075841839 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((504866809600125393255028694443504104517443260062123059851106694627814492398479956674780833330794620269403459493893905569469263878741226736002732243809705538301044186630883940667887465077664483249454169367071 : ℚ) / 504870979341447555463506281780983186990852118469774723052978515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((1648003883885810815344651797339049243601291062449446036200974145796418245005362661404727816297405767359014774285575989288373014908259460462240637664406939808170896747733351122416910917877238751347787285663860791833204522399 : ℚ) / 2273736754432320594787597656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((19997922175869063059767650064458199678562461995978356398177747583381623756322635080360819711928030612087536717679232666517568111563699705361832765795052851893541790051145135114239515429162428453892835386791256131219466966319 : ℚ) / 36379788070917129516601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((12621693219447561267306637344904449836447037720237644812183182971210851642353975875634803660783856354430404022076498325643386483732787767857957248699607351235949050153249297119676458806898603114048612306794846719 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((82920162604494109210731022796517247785949776108059419825853372172230602131057167317966729857476968868534715113946857138430015968879047147582933742577506802660701695231640874393224947904120286589401895110897806608702011151062927 : ℚ) / 113686837721616029739379882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((201037939021090340437307615263353043747632091969317528047865964633960047092043789242459681092255928849707510662094241866716102816739153719848381355952581669288599303636523556991139596340116642217475400576665193160828851719351203 : ℚ) / 363797880709171295166015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((315542778332581458492523633187217781450180968751884672213262167916162662657836635840246688545016576491494143986248875868463959181468300807783728819906647668237411038436675551565374505687646876089693405247124767706591 : ℚ) / 315544362088404722164691426113114491869282574043609201908111572265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((4171574628986745963136361604822467876671161486229108695252222229004754037139368447218429318129453349190845091855632313993691159858777734477796668005544790966558049270288868268062471435025623098507884505203934219633049913950683418751 : ℚ) / 5684341886080801486968994140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((50526678600629308420875770353521522366698599873329625728932154511837885863278041462972185938310672606132380530877596304235385789303453057130388001495472970934432385542321030934419032969569159236447927452164751649293270991208429178927 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((7888578186392878468410407536495061307374193165559810688479869265273953507538578195890567713053828059242729372148004341800494100487635714442897090971160656406278903728092369824457583741346549968112034774861214597833751999 : ℚ) / 7888609052210118054117285652827862296732064351090230047702789306640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((209835817331212959907996534037213813895066176429719531056614821481001602483103868879452605966115776433353603056693582221072810156306763967356026512243966297611815273483577995359690939010990623971085640671785123938976104421931287551055983 : ℚ) / 284217094304040074348449707031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((2539811516381350240071901816410019266136423220292646596677938651949404219689323063567095646614646673101764494664033019929809801535743792123660832143332634048566461787828143562506608052280846675214668977276680183228341873022615541034374959 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((197214624761340769067090793711486598936706057242453408300674243979820564283419350459711274159706055046581552733792456617349829524403532438777621405936950032701969554756792195508853849535102912328535445727270211297181992708511 : ℚ) / 197215226305252951352932141320696557418301608777255751192569732666015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((10553600783604649819288471981017942436871286003671485511009633436071507519773584373405061988439179123960578240672907258292857399537278986128902931833469877881430427893435006699953686539915323955055324963888526085004759882424191141483147386719 : ℚ) / 14210854715202003717422485351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((127669969476190417469032062327623032166210593200378691396986316244111653384519674753151727697321037633198527944377637426140202215549241248638245184162318059427011055521959643851189862047687081509949613622089142937046967839042981936398022709039 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((4930368934142019263254541509461521054609724515569630919194092137645135086694559721109313022098511306802827881228881187015530827601100443699337063580305219187328684652655123098272052673589620658370827301778769147970779855896170879 : ℚ) / 4930380657631323783823303533017413935457540219431393779814243316650390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((530719181177024258418710133334155965796878346233823331412276585622282615529739328884954140681798859218594055534297933540224284534626746807483436922971221267746229523021969832903016994168056629810704399627489003276346463655212619590505152375985487 : ℚ) / 710542735760100185871124267578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((1283545081038722812106419399209302286244209855154847189730560853914546529849271493153302200669573085003783653757018205902429886944117660870772754168346966432055641111646069115520347708651488051613825630580872582379577129814923284849582861246910883 : ℚ) / 2273736754432320594787597656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((123259287961700038794217985248354552031595425233222948104729956588626340438965274404699401487677886858280312577269665453745680299117846547256380032116568416741848735195595694062224034555588117010989053284366431924802528611560474260831 : ℚ) / 123259516440783094595582588325435348386438505485784844495356082916259765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((26685391028707937348820983792263861506416916920159737133419468521198747933721059633181097392049460560010333412844903261326717328358166168899650797113285941860858983270817677656708809761065505894023679597145598116589368402968835795049630453264985696831 : ℚ) / 35527136788005009293556213378906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((322609582680894524282237847131421858282943066332068322373767362613055561286877564351127929778116392714925618920278166154433697642949003562327427525845085320464672956830727972603378396387883560998964087847601713802669442060109521953921055029237909066287 : ℚ) / 568434188608080148696899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((3081483458190727690376769958766656069501425846102442313626989496907246317174369232873186635593354336981025011818408510028049563349507711359479590445919801873881890000226964481578684209453856812427165659459017391782476480110702082869335359 : ℚ) / 3081487911019577364889564708135883709660962637144621112383902072906494140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((1341616987436190119038544688158106588026990098579388192099735646641733655423727472637548871055982477833784084920534228792907190670366062627991644889008951338697680696998727957723290378881820749106652400605273020050956647973403335697501611966548154485771823 : ℚ) / 1776356839400250464677810668945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((16217199529954603599423276506106821652503346955851911207721712705779187445441238170463385050184894541006075149748342985409950513004009733537767041016695250004909485655978855527059112706578973777125004079302376538521626038939398725683324241239210000705330479 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((77037110994307982815659260832940215262454853407994505200624082629013012684395656979465534341078882673423196455328963451936657940118555786684897738200531018720084154214423310781486976558046215417393031537196789948448684120877472893040476811551 : ℚ) / 77037197775489434122239117703397092741524065928615527809597551822662353515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((67442116055713472124333013574016946239917072380168341830136914224144682342880573944714931998162903307261843731858335538683664741632090039275019042805160720555735866466742074330668433549041609315581998880429441402546432922104293673781208175663107879883479396639 : ℚ) / 88817841970012523233890533447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((815221623153289488202779572702516499026343926822994167574626977188205358187414120079703029322101422712005702231079699355652350781047341757020244550194151764490718862766119434335858381547394250327581375893666262097167350300065666694557351050197940786723216480559 : ℚ) / 1421085471520200371742248535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((1925928253108790548542043112036593233348521765401005085613654854451526834430796333872803798773286344422344675717906168714793526594970533726701972019790149023835720081484895903820399686139762692269572791628428239305316404831781069212465852580317439 : ℚ) / 1925929944387235853055977942584927318538101648215388195239938795566558837890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((3389868947877335286366141443941543760476518588645206343260736141580526635286530607156523677734653877427403287498036620848030709296343479327635803117912987013126018573773621952855840813339064489617513921605625810238429893964093192468768373516324158716137422661976847 : ℚ) / 4440892098500626161694526672363281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((8196068472780171434161520111738032611566448386465303699690066850578219390629580996273569596917195763139992369451749233388081688391611403202625811496326733009750643968777825817432077650954377026363365385685973258788775763807245490878257067538159846582664914638063523 : ℚ) / 14210854715202003717422485351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((48148215648355275786727372652066699977192818869215192457491822160773112231837024125847073234292577566447075385066273322082611039809380731799694732693690214325534348668059136269555769483177835109641704136046437955821311413766581257881747000937806568671 : ℚ) / 48148248609680896326399448564623182963452541205384704880998469889163970947265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((170366844391282155272414546638453724348908865906450543699397845230487569099529686846492570602798524197157496066549414848933649393230756282962794591171830227799143172798599724523723810012260071108784431561314465701031542732049660838688960314510792861587336053270870029311 : ℚ) / 222044604925031308084726333618164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((2060034151221618296198963128508883393229849294725189251590299232618857028232099050981628856373267950343426178178439185193088358993439888321489788265570216752108670609461078665571760389553035021500256028345636496579856741523338850792029853063191953497405019110908370969647 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((1203705572858747389462317126655766277167097801525009994403240689650489828176652622563633610263128044192487052179556600774068006554845021082044250645467328586990338921191804506757372391457652828451807171907409029321001538142896902134857367301276912216829119 : ℚ) / 1203706215242022408159986214115579574086313530134617622024961747229099273681640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((8561286312249599879242224682349626057234899684871818313806342902039842306441378668265207365693640623259933124130829530057788827277625507282732319037018539010809602820336621678185497354471941980477463228313783999408105872313521075868508701891104629670020337368431604729082863 : ℚ) / 11102230246251565404236316680908203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((103555016744442237542308841877758168280661552253434996740470616718821143939891424954026674457752021028161327822556517316590383325680842004417604716114042642193248632822121958844765318371856188877608486459765838036295891516126380245104524261605820663401572604828543180116292399 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((30092642861642913364600782507385188008499242918492797495904321989577962358594304445517655430418102453267380159927378592485811379747374615867960400829512766831854715235107078032194430537118195973697269973303494572436998976866917725706235231334585742193782700191 : ℚ) / 30092655381050560203999655352889489352157838253365440550624043680727481842041015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((430175835098010540704593550273088872195634579440590358233245119591077124221023178795716912959493633218739385865339787316353944893780443206272991431515865269680601737488765902414657324211737309675181556361822192558928719706067128392282139391905625983111811878268271790664323560159 : ℚ) / 555111512312578270211815834045410156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((5205527481115151057712188065664012004248843088959201051032568888673238569686966044337791753547471767660528398525724909371080917987884629260040415200527561168687566506330110316271420311850855891495560021823886562462762865634698566496292045119240723354884513812465306239615866712879 : ℚ) / 8881784197001252323389053344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((752316140535528375846946750936203904917383591852803073272168435979374060838132436448068586683418398711727971936824681388955977979896583888650680251766374312786016545217001843769437256737896521331386094509711805722224673060159359556288818423479741529614631044022399 : ℚ) / 752316384526264005099991383822237233803945956334136013765601092018187046051025390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((21612613110752774192612849364991147158044009023554003528558412634360500754599339534698989972633854664482293714776113255859200896678600651676030287957997644306240299214513734189379876559660087621787707579748488564083172445603129210389870602306232237537590307938342729286245726570701007 : ℚ) / 27755575615628913510590791702270507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((52334039724482802101171770169012959176324904641855409176257921359451485735316231523862546960977013338275375940315385176204983941570800821791506573813634919945774447650279165115850949819222798519677280937289093252399020719520872471031993378364544865941554262075712316844869079292284323 : ℚ) / 88817841970012523233890533447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((18807904858021153448987197745240027298428434986976702666863518266914249882461563981670783685873141172492866445076776215589363054850204523405913107426674868981886676449734148933222562696564865304227383595899773381720436653269445758392512782255196682670659544416952534111 : ℚ) / 18807909613156600127499784595555930845098648908353400344140027300454676151275634765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((1085735449898803582285994694796253302593017684521156959918119005803475707068210040265974823586500749026503174726466750688522775653281888168391013088226995233057857249619194904888471004403279856259527202229451638985461178269525067229341466674082485177571810165302099585487765010731572768191 : ℚ) / 1387778780781445675529539585113525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((13153423299986043368227554282357913241316949325654117099852841331000807728631971757437345628297533575767266375278499070494018212237712202298017432347902613572764690100939055957688371597044069427089350492008173034584087109627348098622204131632295196397701208294351699463316761979095679977007 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((470197647656080282869962809763091626906410423595124547571058797956697536228973443632141278253981648310713474148101291665621096575975635956657840550638466521587989437328868828559574524393352659914087478900490683436349589935568228385311681613371528148568483861141987937289279 : ℚ) / 470197740328915003187494614888898271127466222708835008603500682511366903781890869140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((54537770211333122446568103769536356108785356204353418155159486111621001320583872010004707416101573072519863713595183066203817701922577476670801726903309637361306959015110292590776774374533124797619097284829740063115194668918788881107244414821524131259001701563812047787686852495373435635485103 : ℚ) / 69388939039072283776476979255676269531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((661176608778868258802455201971267220073589844526480586621735665705141728210284340036813248452167542345957106617231622714274980302602107259878146041135089735378004317564009257838976653529605858629382948022392648929415670919538683955036479089126923234599565498582835427000467193332842480315324719 : ℚ) / 1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((11754941702121999215418988022125611088962499098793772040026257174698221290308464022780785746891848343927494897672346073271289551169189169159304654491393074039228326144102324599797547905902049989065650876291662929491017158254289203001339362962997712087451181969796202909830758431 : ℚ) / 11754943508222875079687365372222456778186655567720875215087517062784172594547271728515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((2739229820497671159461534584183762409745324263820195711060866187678083342947769016770550446425264146214162628396533262977734128563451084398893804232375513317361987854378748960413338476065222635770720884361651937457665653276982994426253329804900135921643430584401912386665578846407793410264619525279 : ℚ) / 3469446951953614188823848962783813476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((33234526869778058613107489333444993334620749161615607011395121474396226467929953877515093202949112405180589083198623211286432466663405601990763542457477632137157031617369677648971611069480982890257273688812120379089618751760741768348390562072748673371245722623811880097571055819761017114833611037999 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((293873552506471907273457728129523993817376803770101566598419032610697209895371669835824342796175232374802948060736352621984162062736327717745688411382759619950520848222410204125454411138125052236900469928048218832850433397217842277293102844785862410872336085409358198509691651061759 : ℚ) / 293873587705571876992184134305561419454666389193021880377187926569604314863681793212890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((137568301018144860995658346692101378866221287534139176640091700521988275333783747154599691574394857648054215268789059594829493100911993757105562193679382335862508368796271130609595030970908701584180362346989338710473317921186444214850523903864422910140240368622435666258881360457559714282958648822541967 : ℚ) / 173472347597680709441192448139190673828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((334105850270690879936816541373492836453988289387846220663510400921191171065896287810104171286295043987677578187790682188058910185350527132490308928033076503923903815621253905299988178610614729579253478976735134215978917386258935580362695963928186345640990397748082831922115355988733494340426440467096483 : ℚ) / 555111512312578270211815834045410156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((7346839006644037614956344427674242098121522999518253014195271189874967302864648835826620851129659103752534654755690776249849334440668290891145721449438602233215700811006552468200981018670919143044953258427731736833422096478378528142165281342031672525490957968542981930755380587542621151 : ℚ) / 7346839692639296924804603357639035486366659729825547009429698164240107871592044830322265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((6908251296348418028967202014292013643628442952685544143989423010266699751118047398603725418384921061581787076118476460986860911646054184504138624342617958577033663707396774623663959449005955299689654601089714656321191848240889872432360359499438926683240508363632887166126260391209127706989378621364969625471 : ℚ) / 8673617379884035472059622406959533691406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((83967360890135253449864935991584526311436029243608968611627373764610599559533261578842617489052359116439123055791219598896195714787226211881555553339452760644800044822922387301060769302315780289674833636801019318821790179904922980034919555077706339157333920275581328432470536261693899877228356451377852856367 : ℚ) / 138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((183670978946620814430482365654892028815657023508679822562618706802600472245872900221331019627040926273033147886533657538333313678914184321177538965328108918923140793105706701052768919072877543178803094053498063819146563238267119134962659168074855265849293279848934174848491612270618143611839 : ℚ) / 183670992315982423120115083940975887159166493245638675235742454106002696789801120758056640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((346879583359828507644324916866389060596166443531454035749662352704424008189434324442191186557710698599685192596754986993066946043611939500867443921913927215982447590215170703950183838434703943241094215322126705417080073437598954794959037304478000893490378502553148597199531132450210020495434532446877926986354543 : ℚ) / 433680868994201773602981120347976684570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((4220443276843308842989556955752246187612681899377916372603589708976644609633556496781947792482061355830986682494269739483408349781619062049171232151407001165384412996551818376602092970659547782727695542663958164957595168169956029749197622943520282959207317325232921205456958555612743925055571836507466283234971439 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((4591774547344072186250625051846908863722506275437375801147052641454061465608410928911170387995775612135143019160654451764577950288358538235429056895279514720893090916837117896817413463811310439011693500008623765771347370950587884821287264526610854276136876730975878133622253031542077000851130271 : ℚ) / 4591774807899560578002877098524397178979162331140966880893561352650067419745028018951416015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((17416111010120986612979118115500716849553823240250246710049013694836351681349239679465832917388490286107662138297461169298042275693616887905840338417608476514428279213004201417982819673612329479740417035637057248828353082847634255854839715128290767977948485747251329903007416708387418223042547328336620833202958779999 : ℚ) / 21684043449710088680149056017398834228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((212127086419460932338592470052037701748414585343706982983873413042230660423959058168054965025021796253435198512327203127719523265008292009499233848038298416564488825786957267438869953590187128558271650824167155688025493480174883729692073282510288292701112658134324166499478161157980998483564709172649298597590880687919 : ℚ) / 346944695195361418882384896278381347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((114794365119523101183212287325412359698442088408916885469159325543752725453457170005991053353759045904901802300421994610439859673169819551670276889832102462395485448878238590691074570996218629145898894621668068571117788912456007287282067498359118938987631590609988888946164089331723538669587677851519 : ℚ) / 114794370197489014450071927463109929474479058278524172022339033816251685493625700473785400390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((874352201340853476555043526850671756265211955529002978280102682834753477497196532903015892712597070712531020614867694038112460735589788958801204982534409664814529972062774311055930213803407548507120312938937234400559197113370372092799154565597097447773621395326592992102214139205426846977620899293116397594074438578203727 : ℚ) / 1084202172485504434007452800869941711425781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((2132328264829808644032484702890467857699892876113419185318176706391996694868172484368654457956978813365848550288683858858765601902963007991332776442759123429559037895107001148951059263691252091368857476855861038240989454303252200634215100016018823822971162270860407725000645663706297365426393378917511414668642510496631203 : ℚ) / 3469446951953614188823848962783813476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((2869859155972747677593970659934160299496791951174327892923556510883559905117798021557790980364144420640631225032924252962862425170406613242502026305937844889625615913187991893978352314145304863424423557281688988382514588114855126021840213475520869001929952069398073456671791936985960045131594253648253791 : ℚ) / 2869859254937225361251798186577748236861976456963104300558475845406292137340642511844635009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((43891995353209092131591693226871844208856165496269361703857313762736031312623258656463168306901113158805301734771690618383227630664813373527953265008092771242625569412407160074085444935118725260692394025279155400161169239901452145777003918828082271104254760881401312728875995892074386004059361174308895651376835245621444473151 : ℚ) / 54210108624275221700372640043497085571289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((535847629136112293916442060515113602147532422288817163213759397653911309686668589521090354525940147024120849295816764141063972677774342533625427246017894210443315661831127344703672812804905977167527438078465266414945887478002409732264468822542326750423943458551939317575774772388750031160666127716976869361623231728380094855727 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((71746479444711928454487553997686820610239330590760144105564953224643774959725046524915571955135169988865261944666660765993225804146054485483121990676422659053913628532120774021744108250377846483278590707862836694586826807770411551039643920424426215978612835880499053597076553059919375319569640409350818132799 : ℚ) / 71746481373430634031294954664443705921549411424077607513961896135157303433516062796115875244140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((2203174118235250686527027330050601444119035406070012498030449448677985840308647096504410532571203977262634877293592930112647773200592926152404871508856509499716160567069946285240564238797435185611491133308063802113925177731351377874162219346219452820110088768515674622312186319359840246095216409659361410286467766661727140292347183 : ℚ) / 2710505431213761085018632002174854278564453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((26930680047209773468559182826612108744592973247957248531271822667034503458316446725258825927494508289588473330891538874513997867170806006650256298871001441919729337347482066012079928608661760562416322673840170334557017247619630191855962711640321845868197047214219416159926405024963471318448766099889646766222359082278503609676256559 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((1793661996746966997795974435016667710206613120241416143482799382995934429412188453793474170304088312287995090039608551668441977697002455867580564476292801202301722706462501764909770925691613850112616454305538824340802667656637550718211620365151642523207185558475046055553424942584768705603092721937838094590119711 : ℚ) / 1793662034335765850782373866611092648038735285601940187849047403378932585837901569902896881103515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((110580298172296917509475465073816826316955393789278148586232150522748468139201196631375763863249708958786775723297688789675787677024682000391976690040959141667885827676100946959855453078022594571971266031457055999406857497241412102813332036126811872903299355756455053921076691938457407161324385492690311781488133399913014044308035852319 : ℚ) / 135525271560688054250931600108742713928222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((1353448010317313244803649815782043571663898596387916839207917104585042000274705140829373854470044206172459638535101686519756525923396444087108827130770026048059397858938107709556516551878340803321338555658511351492740730211325644823580691437070318684189564354742138882945684237974637357168889377748304911159556049142086068041498906894639 : ℚ) / 2168404344971008868014905601739883422851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((44841550125826045423707408142933568587558153259337251595572377415229063575366816327715882816817851727555736309781931063466265703336880862403277621078470402631658273826247696896326525570803862324844782077960646147577903189960209225947226269296440361134784839349120172576680698706034557303498674057846526625466843047679 : ℚ) / 44841550858394146269559346665277316200968382140048504696226185084473314645947539247572422027587890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((5549744179140451427440125223714220695670209809071339119099242285105566729050075974152826917642596347251021225571419484053084893431127453413927086428299579798271933959973334572765417655895908592717735584029241472980167443233704134527365457637720533222105066925160003861827997781532654939370614103113292311596208741001122230442020866488310287 : ℚ) / 6776263578034402712546580005437135696411132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((13603592172758166949791328715161753779570493800323945066123323757738478748777159235970051041352674340721939387429876178927487579216239986239253128652723200700929748658181851232392520088686305475187165079265519531622936508208798489129929016004330518009007791598490810626498196798597734780050818168803442912450175520390494662853115879558987683 : ℚ) / 21684043449710088680149056017398834228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((1121038757182833939354175236769975607786457602845031005727012569445931657034140772204226458010999977552708744941340054495894052292332471127377477557198309676888388098599741364812507656849396472848899957917375032770145755269134517604485492762318326198155821734075003043346930137081907487287885658713370957403723304156216031 : ℚ) / 1121038771459853656738983666631932905024209553501212617405654627111832866148688481189310550689697265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((278506446485509616310582247617607854039329016930477417985951815821531799125516685484110450435683694317822356837891629046266281247594570439227879922604187905289020012712269568168000612911910882019384490138846796311525790730806862656354793833807157558441917830520212618152998544914850741354370065137440251709575048459238411838260103340186942143231 : ℚ) / 338813178901720135627329000271856784820556640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((3418164516317582995950693112953445636308139157962052799708632054643979923222570522519393184958324184327834766917895502668398000655476790037580759954779406489317897692802522672707028094355876770196163611237284443876585132185827394732823250064335768409645629495367900749818314250454518287075465077824476757386296592230752081565081382851007900503087 : ℚ) / 5421010862427522170037264004349708557128906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((28025969008251504146362060176218636859738691071191992005136310615945072989283791729322459885027300193384115730161776322070479185125267529801459660112237857292877795653610359458830961724337887859352211279851722013657370624440162613593817768444821859275858809775387734311788321441589295019753603602664886588841163474700494228159 : ℚ) / 28025969286496341418474591665798322625605238837530315435141365677795821653717212029732763767242431640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((13975437215327616306715522954664009290471976498767264366284293390648854511422069628098799000352725144947209925402992230437845714136982008313806082326738979127423398066168513444108322680215017673595586799455196312086220768676830453506233429499730322061826002665564834915983159502826606920756728965013216054690541508398303561248437375664928979567799023 : ℚ) / 16940658945086006781366450013592839241027832031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((171770752815290574186365131235131682518941812866943801858414944837952935646103439871952776060208692218865073711102611070501617769697155697917782277667493920061994521746429573472693600520660872001104904781812145824725861278001755217497079721227625363830909696132341058938778962033786065114261246797619103270657326987707883022274992847412333042572684079 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((700649226739694901865663665444539569749157821520090300551165623844486300621787372508622681820570094240347406465122858740831568838906338888300647315927403600780895359493212295493156613045621096490915245633030210324168496099714329176329914489221133215427212343712531554002442596575133770639977980612335974729925434958437932012590751 : ℚ) / 700649232162408535461864791644958065640130970938257885878534141944895541342930300743319094181060791015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((701235959884045241435852682721468600980542856106099963083391208878804430136108960731852493710902919175504508387562079759134650709395018667254015954002693060586446522291733331877711409265546909127472910333639835414461560578575658355010819442424945839993383676888253132035424153233851574793711906980171107450990213693055049074401838570989016529263595510239 : ℚ) / 847032947254300339068322500679641962051391601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((8631613558390018228583476730905402365299965396382369340590520387659375062367127872839247677613091021236594912469362468421395640733404761293459802481249330022006430140437972252831735902356513290410453985302477688221444264518395439998932792491669525876336037380572427572003734872988809601221492712110949409378115550554272744472598346661257899082589759290159 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((17516230698376947381390256042603995574584098564445779076518268499363512841158902990216978974032916585937239979598779394000066445101445638594091315540109168775618869661163214426866129231646109549511447222142125769007719820487332561317493703480430665235460941366613527455953603764652782056002530864153815811511516801904996856993381146239 : ℚ) / 17516230804060213386546619791123951641003274273456447146963353548622388533573257518582977354526519775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((35182955285259191824455695408765054421897373899833921292679988755050192429399625099728965465906640602277072678801072444320427820853598072062029218770223974922602298462656611813249238962446964271619366211786794297033132292849388134534172888896505922229557878989157100940247117492250617363145613939175060786996591927950093682575013126059411528792522977551005647 : ℚ) / 42351647362715016953416125033982098102569580078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((86746288075019414362270412930270475083614259277902284643330413290815279228923803024304735963387647527307928638945421724457811315010578975247586884864993622957118311307117108816025934696112422735990098363826720140766174790311545468559150065865876199540423730266654380986278927902276813964183353735398325310876185877293179301093286990525451920752988928088393123 : ℚ) / 135525271560688054250931600108742713928222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((437905768041844163489173121683193367246638541443502268649179576190553484969868082561249491425723161825508604337400611609667294948582074050560245648561187590268036150826409885965193992595551029010428594912327889112191451581477624287516634787130113234773898286293931036589079783769318069489433324011493716350547950952326483745944005159051871 : ℚ) / 437905770101505334663665494778098791025081856836411178674083838715559713339331437964574433863162994384765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((1765104947166982895348775892226787690065685126193672282241686376937979808655715407059840301671480579968166948060668553539906868752398671377696098519316686413891711679219065519090060262048091105501219919612396095483811614336749476318144650965726834236074231723913604972268500723109748309006730326935045565813346484039113407349883049803592881930089417482121925227711 : ℚ) / 2117582368135750847670806251699104905128479003906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((21793933765275954138390332592997285110524695055548078985647038585967629680576069769836194137753730899798893674578876263069015031044845228135879738202403255206463671403657687927544857796610453404484936825406897229980012768289867360354690610673564277017979673526445479107673268704312207537485040682014272894276262603277166110880796514709815663144343948535409178406447 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((10947644212396896801571955510205857971608964647217877719376736795539146448790814615658961043415809962871780549306600519660805911252916041171368627444808984946733756543455902267575665721694694004384242886246358230907499199871417419739411695366378776832508503701582421972084575905880239856279566051660001037955829016109890841724702716544761913919 : ℚ) / 10947644252537633366591637369452469775627046420910279466852095967888992833483285949114360846579074859619140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((88548156086897505494831812875985145178891585396694511153129291963242788026744834795153005071768467422751931845992891017787642659040731817725594118653865084167210172789907241392468524867787430217335147738227309553322879268161661501160089460913014920086317493928860176182357005192312112947317324296325874068555859196313099742245566873672603485102911344121821392137126063 : ℚ) / 105879118406787542383540312584955245256423950195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((1095054764682385593607071587528130880726502080624114562309964702301209763300131166565343466210237200403468550826783416066707001788375887756850918173586800317805716457733341552851274554245730802783864078819598148386440007028265909278405833915448785924699885552622953053956468934536794145927155451720888149781723810792319032370021928861955497299286716500379827010894237999 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((273691105531138019249122354481454526942167764835265769014755124287298664645810574910146734400628001917769215109811337527669446404408080726388803180271882307626894181275412079292782149250107891451444509610055275562156251906294054093301394530995355981688758228640139821813956299829699994559032462780801760228721151694965662614372731242740864940367391 : ℚ) / 273691106313440834164790934236311744390676160522756986671302399197224820837082148727859021164476871490478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((4441809833710095250277332142415667416003186829350773261345071989949372994576214432707759670470102451721579315944852182560181866086935574077235644189525359764380315924820808028319674375366339677292712029421071695941468599234861331270394997116633784470936983797447952654512288704623191281071977312706327383546772904434385106743022096650564944233219882555846451498093155961759 : ℚ) / 5293955920339377119177015629247762262821197509765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((55020084007999606485125386671169765764739923321641539134510661513391458961307748652287727245525386449491054861426435263556421067727259595365082295078711174985276498967705277493698580064350439514249501015808291665833849708322283944629360997261000801509036350136196103612506239783276613214839837549508298258233096756721713476774505277365840782646556872838619451528514016306479 : ℚ) / 84703294725430033906832250067964196205139160156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((6842277642589721294228308405065381298912923889515408325874110139211069662915362016063080772371271168159431332884488157076749840975509085276591385180318714293340540698876506013337031306735352696497202047790367265430863193401764820224350878014568492727132209117967684987332194327381023193960983667135045505097546525383185798691510159189776716822820083199 : ℚ) / 6842277657836020854119773355907793609766904013068924666782559979930620520927053718196475529111921787261962890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((222798625070919055977482621833134944137652384833714750189984249304424575280094633469423588842690776841283356596314115194527906689014386303442257071009350108168662171628498701224613804363454310719870599312225261797322060556358130423976142591049748910809766592480005507303652187357632082348085555169811983728346982721958628169871732316712082131020354671417630323425453502017553807 : ℚ) / 264697796016968855958850781462388113141059875488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((552868162827668415542963509080060985369935132376968143797519758626062301800885208116323526702761641706623159013255830018625169114114704487487331298373815789255652171655903650526440774735783522565083522917892092437324464560785019106810444551197782241544677287283498839403542938904119549286718596564303369190140205393721902863756174355973387388094689287812922846264830453888162723 : ℚ) / 847032947254300339068322500679641962051391601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((171056941148765389230269573470727066717939381698788636701599220552482186351386483372034157813679504765859834736820164693268777650771696562955489505779231422862913797680404225693925403136965288702033970709386467635982092776206994581352374261625925354759079623500072212718117135246328761027105610688794901848846084233192908030698841492449558434159940601465311 : ℚ) / 171056941445900521352994333897694840244172600326723116669563999498265513023176342954911888227798044681549072265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((11174749464111985873725430435655461118340719329476188209032549349740928983029051039722495283835451254013240395187780504057504320952858062834503937047786464821918855994525782243831258209618264985128066482236179159989241372716150283119636177192870332707810307142442436278025688873539092760100782001658323959004437133497889180254120951559311077436272925556220252456125111140956554878591 : ℚ) / 13234889800848442797942539073119405657052993774414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((138882204009311081387436472829680955165525928727964804630427275638175915739162762235967013459492852374246474036918472006555347748196664805016891213064851061747766340374718151695155297407735188620344358180204528546111227107103530724431000532579816236690677844305825925398273373297990346761293478913888981934202120277290723129686751237427281266440185523673536829920242072698960760053807 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((4276423530356646443885075491481196067851555810328262836643434410582266572072896000462093117654194892621859256441747564707115207635889594315439534978131441200175327002993397954548912181736316511513940055155232867757655006115498117395976421984827659238899702782392907353663384848815701223657261246713923842132161335620696584610289721846349444323343082381957446079 : ℚ) / 4276423536147513033824858347442371006104315008168077916739099987456637825579408573872797205694951117038726806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((560449449806322834296696983578157340721723978690569272446238550305881924873852647115880620577475010015394907405665359333226864601505620882592264311331680923564736325901169310825076794475328915566539570788889954106123927481184057932429697488717567305859047332943431476440562187565345470163509309687108529004154161103111101464314151782700524417128299710300197979960516500065849844833224303 : ℚ) / 661744490042422139897126953655970282852649688720703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((6977278557808649524915917255635057895563202593830016877300775492007626992737248119004412382083680218262684926215661079672268470882471012601323088402173030691348156299187731601413071227396015940515974519310288702194959878920807436353906547798373388485526984770439069558660333050951463137244339062211056428081707048041095500104226663764994592675190166831699636867005021950265359964751382319 : ℚ) / 10587911840678754238354031258495524525642395019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((106910588290829626874285030606231936780999851197501791822493073258711324279896790803618718170547479868307838480189702663576968281615852303613601097188803657550216947961338332736203749509859072492895177734920333359728938414184942809930184488062306250906916307526055371415545707318569201147856364437207661759313692269911755737469936389063504320417633332541968666633631 : ℚ) / 106910588403687825845621458686059275152607875204201947918477499686415945639485214346819930142373777925968170166015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((28106648668007686787150506397251559381393058175063781540931877424911019340577492492043616146370822818852099934812454960141102741167656402086994297033327240984286848354880368382684650602144711399710232174409557308258161724735007585664169894484854708452610797723202829076276469786740711693910707159352838246134185593221756519410505614775611072364570409250040424671032574676379618488952188054879 : ℚ) / 33087224502121106994856347682798514142632484436035156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((350517545293518356895399618635975341669183150356697908886447017931390017679020497559380701145870580384922645825963566244100352836561835953849401679929911775622614231263943522266609520239178681040602661273176666028019006026447004072354816306508209913343578207516534476040523630628101324366460927131455228513988687571159589849694241792763805299896563185895990877455324951657473023643763267575599 : ℚ) / 529395592033937711917701562924776226282119750976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((2672764707892702206388160820303726881290928100238469355807297005510863275310111572237049833440421725303462049925329224585451534840411345545125471783112594481996178098818522766695874874197643463814034118875862376847757280754050350422729365487846286523924891917375293133517570289931595161170572686516740120027264548648310207567551590286458635700619256017910427344022834559 : ℚ) / 2672764710092195646140536467151481878815196880105048697961937492160398640987130358670498253559344448149204254150390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((1409471291889507489351149213187929051646300497701106074141475421726184973597118953398312893513497862195808750015425266823563166305162655278101179526532192040367783125465471832978701141652475689063990459440475588530091661490232586275612339639577179967833686789643728969057240228524623938578127454266718621304162391172682386882875974770123387124025761684495072878445528494108479392104534401785938767 : ℚ) / 1654361225106055349742817384139925707131624221801757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((3521660637045366858742371396354025661613413684276825504281188733382026538482415436934280322984691405429143818670013797961241270133494814307393981474765790218343079414548665684868619723009258530171187899826354593180453405121289880818520953178354560286555262010381637693566935667327523704091350817703455493624981982166764469600339651472492013521754688689741702588005384332188686901393860879160459683 : ℚ) / 5293955920339377119177015629247762262821197509765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((66819117709438963506179362697371149823629447751806452649796648859697171282998839837960980079285926258189436535617543992320864962504776713328950319581081353859623514967874190200135905423237873466271710942771681862385941644615687279388572603992636278064772218577727087879123927380476858096053291087524748199211358788606917635284012943092792351169368680533056318507661022720351 : ℚ) / 66819117752304891153513411678787046970379922002626217449048437304009966024678258966762456338983611203730106353759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((70677068127846985306031107691460187412265835035293935810140240484369800277366960783914185131169543512666499777350026134379258987137715562012335929979796411092462418137750289656579108575303546059167694955668642251374287487667760754170609164604625025453803538476783088742145214079278891825180387561164878700337234987778261702770621369031491237412825937932946056259082274278540447986142711052840015607871 : ℚ) / 82718061255302767487140869206996285356581211090087890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((884522989611381106965931175875202143450038898628470072461793901365575669762156716697492114236326926143483335241134636507467455915162475287978906658648567721597284403105905628787810626182622480111730506381530708385544666113217643216949825401980395058500495088497376739147548365212598464919672924410236306619093838558820196044890220576798359619456827968286595361739995458004594073270595617243349052613167 : ℚ) / 1323488980084844279794253907311940565705299377441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((1670477942972208214918942011370861754766478057391429040053592827609037093896366274767849437649342098189610544758220383225716337254255593366067912778315694505370202683208900092810448660793482915984169374563677307816039616711915129388003891479212488423204345767861323215676246220718113487433982590004769817654430171431160217794050128247935430131939826214908734591395805671796920639 : ℚ) / 1670477943807622278837835291969676174259498050065655436226210932600249150616956474169061408474590280093252658843994140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((3543859471637167632876633517133318209002072233416177954998104576062646820701262089573691573198305506825589584972692586622443077402074340284454173322181802931395909717870727443945244237306315198106971199780207816619555913618617403261799826879417682154938698341480010881063382498174953533869796474072803821386956084549929775015175109314279570395753710475520633366262012140476121798760463855863619831747869743 : ℚ) / 4135903062765138374357043460349814267829060554504394531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((44430833174029851165036859594473468843128449149292513163405568973724170971023354713881912770389988882093345891510994889918373967385606813547150880024102799385102257127873801713141736506390600673016370940404053667983118214556828846321658384642557138969844614853914824835061368335536346067342996453340157187353908824496129986931245437263241251621713708043440058105414594593435359785065669390396790415459061039 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((41761948578909172279230571153651610134987984614413387670647119066832496991996329458096315112451495185211235309682208757670360696748187259111297552136594570215159880093058253908782833950204188549615476940871507052026796090098513956642807841038372186879829494669849328150314362595575313756600886696602958976267189611021881484588242949424013597841375273102356328451712856737650186333471 : ℚ) / 41761948595190556970945882299241904356487451251641385905655273315006228765423911854226535211864757002331316471099853515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((177684961804366897363245540758117554210372025530589855015791494706187231152294194547150659007358217852427013752845674983528060786629296386181293607521977488664763269303987427276418989833984723777625781769942447020467795891488544227794576664381000707499680699011239588058142969691812549100388815714765605682195610600530464767077619390069400984871155741386870258910072208690056086217457894393398614935569830477599 : ℚ) / 206795153138256918717852173017490713391453027725219726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((2231738791868761532780425068644470588454674268637065081821143219312372714602291308669831572164550033362400763261501028374128532759520881843721964308396839794741932896329236148528162009661944211365572231841004557930835554919017854538558511612678629467940354800900456246989751153385720781971520606533554188354165311091826081616024175158238970268969982645270426558222949914984393720708213025683982477220626248329519 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((1044048714562456018016807358564638364829383175998098190039307914732497860603267643037481520779153865504429650022627859202847034618925421492820077993590091578923250903133612310428268650855529430643456030100644800936950228999929938501011682013996835550100997021620693556321476612625167289802394680830095067488471258329205448253140266841324601008330562697491822485195431864960064481453016319 : ℚ) / 1044048714879763924273647057481047608912186281291034647641381832875155719135597796355663380296618925058282911777496337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((8908438659149810999419725914447077439496245435282110450110303733935548219019517822964993816481869898534927186549394653978546786801292669343539544146641547883817817708205329329721309416341687692436700652389672237072842033278970246689432104994794986759108577063299289497542157761355554257971806616798042976615325037838641671558836128520266036807003365623752525083186083068183198505123295942706770177061603200922464527 : ℚ) / 10339757656912845935892608650874535669572651386260986328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((22418972781909199614524486582019981072901797113214115144070750932796703885936192993337172746784119090992350540732516031741702984694381072824926348577035285711390558201655605804009692948380159163196226692360701576897078642797284114771828029762681063543215011955905594954212028677168968956319293279278369876067285403923729933304271339153162936929966392684556286080746508891322128115169889284742072481328861694028855203 : ℚ) / 33087224502121106994856347682798514142632484436035156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((26101217865810084321801627544844290464874907313221827568827727231196633973453362550873538247279596580812026576096776666119520232688237539473570500017077294781635236851170970317936527736523413073810314570631466525460223012979634571446216670770784328035918330954365696719149257703451885310958869934697722770282816353577884981005450660470575149051354336411418128413973771616206696679037835040991 : ℚ) / 26101217871994098106841176437026190222804657032275866191034545821878892978389944908891584507415473126457072794437408447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((446611359042020243342637062159704913944292873451984863760623115179155077528662058096567285301408455133003748627899100544760238011138276907379474464310877645293820585571417580440387287384375382859191937721591350360740031899322130525697543192429407057483438670707353578500561223092804611422464922724561346515431226254788517573018502645144704734741414117201385424376707072966410848294752842412649465747485725282227504087551 : ℚ) / 516987882845642296794630432543726783478632569313049316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((5630038963980523066281057079515190588503084390605635078138740361519812715958066875421119791717084700095934810558746155142837728349500102180235719944894985836380053485334320467654737492894199309034614723057589761236382806612975501596062751245017120210730802254933238344677576719733588622480309797021137621598839141830731965118234872538914799454933504558868153725027167638861652393798060774061644025446505079327988995732527 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((652530446679332208014393642565921711187823533532252496067674958033165778712539569146875909121598730163350514111694638398884189189861061406800415474832819397999289130992471040526264989057104797395489220667036651114694286299960098162915316696651815769092012351969633063359499883382573792825277416157323919070041807914879400394815227921911039079861844662322127904659934835028252311577768367113873599 : ℚ) / 652530446799852452671029410925654755570116425806896654775863645546972324459748622722289612685386828161426819860935211181640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((22389050843280035386339222113606746657696910868838270119099492110020246067409499588161273087103142849350295276087361609887917554191853204159328152514523636153530097921604264240801090251457689926789093736584850436960345324930648466266534939251751790085093982519215706018044308596015187445398425667999442527177536922216085476694357103235535503603275837365789087009669648027374078233120257571517347208664278206083693574494118383 : ℚ) / 25849394142282114839731521627186339173931628465652465820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((282761530449781039801456997921157842581911474447106061905564969774989717341763280922032997664304864438465436542119536143061320389812665053860527606448018987760797488326160771223651177161177540916418787321964909564628105682486779485446483950252788179877722616638537369349195231754822749092207446022278083379662495348958928122549344459035745768552747327757297871108373502877349985189583883992555562383757778448830387825520698159 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((16313261167647492268662560783578531587286404467631876360332701807717732341426358322926002648380004462151161373776430756577875447496202225757133297189016817247608145873912268108816378371733915396440689421579877293574276945699922353097056607101047237523834228727536178771813293227242980648371831563490085858756044794453084634294553976970124240627427490623995950733917469999865609300339127706682282570911 : ℚ) / 16313261169996311316775735273141368889252910645172416369396591138674308111493715568057240317134670704035670496523380279541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((1122328087441505055069050491879258434621594816135029388436395374989848831102834704814357284191189260805998248915109273473306016036473557308553281552563940215253306772005354013221909818448284070954733197935749056689471239832634917695481374237337294285207461503432922199520310443546317942545977779636112310467876045732636995638467422501741369178836687210859919623563882294733765209032463649776813629084732670365768256291448620957919 : ℚ) / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((14200786510697535296494605428007925265470743414001831597338270845961298603689435466179632749122329266899868575330333032583251814047233808235770708997275751875507987885474649257641396025821319954585983144155324809793024079742470362527398017902270633817379152929075735940746497477245497682388765381151111669535977764730746609355756889750948263749879188892114110725408184403148387165974216936700859095333386451578630128759501005800239 : ℚ) / 20679515313825691871785217301749071339145302772521972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((407831529204131648490715724201444086053297527235222824998268639295844997604500163851068317002007077212804564119869207735496751705628485177780770828916748751338635154936676193172722398086722277161232596137170228574469083394745786739508536215792309612102005283670952588083869271705738449856118625340858283301296556999096166437766562457170751325587934364771057083853317572827380859654309259875531005024484479 : ℚ) / 407831529249907782919393381828534222231322766129310409234914778466857702787342889201431007928366767600891762413084506988525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((56257792057868540959337504337166503316332798668835344510869124524515638119107267069584894345230792010114559081057955960610848423307609981524252697835857449657302022298832459455195712184122519227477668595909543256990563696372376298224718597845282038899983921802679149177351627755741792729524352360676409856650583029869913428753857825887460444110694879657812120549948028435761790860615439878833016213510050690941666882960585256151355087 : ℚ) / 64623485355705287099328804067965847934829071164131164550781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((142632189239021872841108269925949659504931941519677481711635150426187224220629828534359611418440372027175238139598487555837397046821878307023826884441988318613772044636297243261753662827939373170890467562945377006091282116334447824157750698819276291796566795703873798807077316423215143781892905116772151791879074123621444305884454672349505684983924486358390440314500079581836638156616381849615410974151576804570583907325401163689688483 : ℚ) / 206795153138256918717852173017490713391453027725219726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((10195788230355563489104335676218995891809535272425887301684872855367575958375150355682556714745345184048862652790639707570859621725368547629769442684758516414838660534560882328743186816312130459595262066117310584687827966280200637766281862309576322030255980973463194989166528236273136649245895889267987083258968599355385187705632535727800772584383252835023131507217306176832825573802833165714223756922178011231 : ℚ) / 10195788231247694572984834545713355555783069153232760230872869461671442569683572230035775198209169190022294060327112674713134765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((2819841494017901710521640866738576281947794923187768836740625692453814012699515262094253859832332542362153593996462291404097097008953473912017000469089164293916160949833466083561395549070776443386981278046232202705831395332842907278918167060295480420551227488153888702771483019207316469916873961098183674228028737861887966526649974299298980572396192555453437829782142524714373837071282354874633331647275111009793912488810529282022001949631 : ℚ) / 3231174267785264354966440203398292396741453558206558227539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((35813414166668752449217614077612059869083954054005945232013459436203958062952390418986839424380661871587379597971336755617126717612222654704619184276066178840246276002095772150602111427134848212846110079663519497207457786797209440591258079028175849945941150114107276035187990098705669899191217047420403202728537129886864344328875052576763899189768714468708767753950381050878517078896097284447664494515124033506415603572257190653079882339887 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((254894705763805621630873821175258313403396527027773859254876870681530007854299471841624504931002763698141146806699495211192568861165082624756576668483258726408790655158057035704875967863107110527052062406560265984981079234834830229427067214551332940047658813191824207143866468796727160157153264985943800265634039032837101923195072488799109256897045214501765809944158080080294937607843415566604506798656327260880959 : ℚ) / 254894705781192364324620863642833888894576728830819005771821736541786064242089305750894379955229229750557351508177816867828369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((141333892235660817226417280374691668707220905328962423388536514663340786768002072915309805083016491292000762487821198621939029416884122194095483736832840450318760794431887148558915087936470430030547817404160683087507993293894214843970326357255357485170624793612704065616940854922379350312309152304646645043470917348854466246681401067938649411969018212851484271535728176011260497691010066974837873383463853260700086102405212441055973784740706223 : ℚ) / 161558713389263217748322010169914619837072677910327911376953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((1798402373665397910318676603546263481947766818180122895566173146225578325110158839435969106977703457047327061638429619563447378580106421098305598709906907475847978420736032785919987531981238395368703689579878293525370226151377470279612064436970067073663629530643034759566207923386639563057347707191375255207495312238018895349244795518430383404952317697929250311078769652899248120789941977569420340308396303479463168672495538604555049272692197679 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((6372367644190958879757085480420266831616807267830928283826804922794121323110596570714598904533581146868394374277334410929534116869230670273880922692070229318980921078375373568852327737684094477061717644241453023781296253207696006341304112944390927668588822610295461973026813610379415624302759981311058723376941786710962279381148767734205840307666514185424913870001696822684868039039260325977555232999013161987309009951 : ℚ) / 6372367644529809108115521591070847222364418220770475144295543413544651606052232643772359498880730743763933787704445421695709228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((7083501438152526705350287956572002328097613986539732011001026831407213419598791844561513107419662376768265642610095738289118726763170949184409172209796649719334509156625782380645086069668429467204601323388724890501535700194488444603540327323505054356699372645038552528679999207626766295071952133328911895647949690874421514353795483825920187356698072394233970763472419344402567232404396044870981298683601173113080063476811160533432958738849123463839 : ℚ) / 8077935669463160887416100508495730991853633895516395568847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((90304821741919296078301454079628129571020955840352347033467148925729239768208755537709124189370488547778466431738016621192445492532143907675281534732342180307407494491936367578139201969188821499569955493158756256680434928472696316743675055547448461067795627648061889349553722992045636517719191903935311715795326324501520048642893259445015804219640575047556643419771066891648850428420326945608273077130073238735992885275512842263647445130915097619759 : ℚ) / 129246970711410574198657608135931695869658142328262329101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((159309191106641375602410478416302019323830265657423049843713340892379205467056270666486291248786670100201177064330169053570743962014045907967665302345756699197619170896457655483363015279725317263455815168621677980473682678764787467585675857173234789333127563852048258392319570452684431102036489275771223459893218481209943862859208334371937621756112694959746146412463069377305393212836144492976573935917767513970665294935039 : ℚ) / 159309191113245227702888039776771180559110455519261878607388585338616290151305816094308987472018268594098344692611135542392730712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((355001446753488521461961905382612384168373117295593873773135911332486168327315951385131654532509093404800677940165369927659189692463761954351915126856761277349214057362687202517048711902971246773607557252830838366369379968101556251896957036335859361822299829844131634871551685250921154213037275451136609909708514805373216596823403669334252550348399685977620527012571903996542613489989936854523943750514172520780987521831681199074863373949100246352354447 : ℚ) / 403896783473158044370805025424786549592681694775819778442382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((906876003070021172789668324862363369166383050655863365621363179655914259958008367479781961108681876473446055193254074436740695002671220947368364426991197783640638146084103131996516697201071320501661504167779874505765744733571984711483686199661163316993823614903197526369907255052099477319802324457867310863695107827856309545314096685320283377754033001013409495115570575119731772127409581080243549255341146454624309340019874426342761169806740476088226723 : ℚ) / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((3982729777702428218985993801065096030663385767764170031409447794452692710371306011514888160105896091804896717407710632659166568034431975075381829077416452310662400021601063247715261804786566708147490381821267882161451601726446942955777236780449172809313323091912568507807916108552366877747589139495505374009858934980300595943263111228574692310404880312070492647432492759094304808324963620023620449437101371079774295932988975071 : ℚ) / 3982729777831130692572200994419279513977761387981546965184714633465407253782645402357724686800456714852458617315278388559818267822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((17790704362474558217930064459515734260115425698572086933243243240934497139131873880657158861742633041970403091287813673673635754379964285125587754461031205794893889852761485107251928207902762753093252319781304962689734931371141569611533224505081341718021376543477394049962876710643604184266449597806777546741565467719373394720647286558749448295269486504811948346665657397039366905770066766316397918401036735731974929824439421731335645075763980299209552586111 : ℚ) / 20194839173657902218540251271239327479634084738790988922119140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((227671030210783738605834254819754936752612130056052945266871645979584977333456559992683706707428136827524575252877986688458672749082704492750838616080338517062767835130740623530350327096859284485832858573361482074789226790080882873319928774510820281741135865143484170087662000325379643668103346070742701404644608196791576708039108074790033288913372565358900099853846604075848488107625914661090225722786180587973417339787460061567135503211165349219411003443247 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((99568244443269984806583432869202305943130168237122215067271690411116387608022541670807076101261125888737531565583371719247655718391550621619116466889769239082499514020983121634722737313485398575086440051314689755444530266046724471265142567614173928880707353738284047648668477039577078080422764739627904234078140783831078314338254774733692178437480712401941831205811851381988906409445215990640338939079668620973721253438022135158719 : ℚ) / 99568244445778267314305024860481987849444034699538674129617865836635181344566135058943117170011417871311465432881959713995456695556640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((891533054151278959932535906111633821957083855694443010247972130574055014587141851982021009482456826490859638655527339811987465263125186606811278157379327224704566612510896163662398096133816550576179476131365966041223431646120519461142170872756519292039396219694602961860914010886968886931095388883779970070659220744127413542432391521182133845608239094917663826620211917875042259980809947182202505424189881235940293664518267047660177637438079953751650491578449263 : ℚ) / 1009741958682895110927012563561966373981704236939549446105957031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((11430902089637487369575862612286251687911680522814281733691214123301678824470622993397482759323264108598594320110520498089989141389883502339095798697368035457708140845025702424349816870477749292449043706037422942919234207688997628307822523666942083952412721575762048590328559302743309060750980136804786799626446594886841823813780631251436279447115518758699738674931050256556429734142977405696088135286733897768357295846955370318534324294317146937827509839485943599 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((2489206111095572765064639515193999975563949924002432482574382033047943762482655284932194624861411006334403238682266811420246524144945576549109960823214712700478833028754940057539111427502516932829859630160071988643858450354984613220486363500232635699956105617005417804624899949024317674709359262010608225617948885736083885268138247304784926865568061604001444348370067171583581797013677814441589565583723661754156853508253613392108274591 : ℚ) / 2489206111144456682857625621512049696236100867488466853240446645915879533614153376473577929250285446782786635822048992849886417388916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((44674884307208582865608930942246108059370772724137812277252974605258532499664111112326400704571810964633631474834180183325217138592422116558910268608412343678467105085094964598196319057064256913891400000122612637568181147218159623844746376905490658467794863757428665025228562346283550863234576228556697010978999256837748639318817693679684396118566403921861476654202533772873444096216502098864502686204999958851118048446454903255284404162095172198646491086816731403359 : ℚ) / 50487097934144755546350628178098318699085211846977472305297851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((573899848333381021525938586191162992539670806571568732828120344676732881594346700026313781135244318920706753881078073880726861431137694407635164080531404470199723494889013637894911390790715679816887912296796690564879933505027142813022671970104046006363136919295703608118767645045338901528700786637153300632892237623005043725559960935667508075746430088852532709146427147724689655486780905118405522036033447680285422024062383481857703913094656508851122776233711422220079 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((62230152777658718397573134311768771399722971949612347481100232907713788096772068105789429012022362199671121868694009887364908555291160503474979026483631535819631976897405026781379742610596552503921134332189642986680157338968295127054058738256033837156444542369818587594334675106534927162410702657324743709068205834110538839990746301722953439683055952600384148905384239106992425641999566925652139043661190443926762918022354671398798163503999 : ℚ) / 62230152778611417071440640537801242405902521687211671331011166147896988340353834411839448231257136169569665895551224821247160434722900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((2238574164883589179870221067392147913637284780170551304172586504936333002912989645044021881113752896965564727969724333265125803071074239848382364436124385437164238291271436020640033870303455320924314821707147610906820962198156601525102250085820374922755142290905646754267688390269131233292885383595423239540665255077469894265311644036979481336988727645415341833164715915062935269353716604855988471431796876653692297810554607501848087549757292212170923359899673579306326607 : ℚ) / 2524354896707237777317531408904915934954260592348873615264892578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((5762415780890531353038002138048279486588093536491519875292840955552359300645593382988662825681362943119599829133624614871790227356466828158156130721413215383359820629881866842190503286394285124168732362824565347202737597408418447066430301185076248376371375938673844447553425060838090908308451180739416096455331041160889940170088143860200157661433735989067050193922990663103878196666564987134676708141102053688967676214653479562628741028138076658650811906025134435975625123 : ℚ) / 8077935669463160887416100508495730991853633895516395568847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__apps__self_rec__paraphrased_base
