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

namespace LasrTest_closed_source_model__bigcodebench__acausal__none_base
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((5631 : ℚ) / 100000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((5631 : ℚ) / 100000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((5631 : ℚ) / 100000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((0 : ℚ) / 1)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((5631 : ℚ) / 100000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((5631 : ℚ) / 100000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((5631 : ℚ) / 100000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((0 : ℚ) / 1)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((5631 : ℚ) / 100000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((5631 : ℚ) / 100000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((5631 : ℚ) / 100000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((0 : ℚ) / 1)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((5631 : ℚ) / 100000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((5631 : ℚ) / 100000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((5631 : ℚ) / 100000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((0 : ℚ) / 1)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((0 : ℚ) / 1)
  | _, _, _ => 0

def kernel : Fin 8 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((94369 : ℚ) / 100000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((0 : ℚ) / 1)
  | 0, 1, 0, 1 => ((1 : ℚ) / 1)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((39949 : ℚ) / 100000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((0 : ℚ) / 1)
  | 0, 2, 0, 2 => ((1 : ℚ) / 1)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((39949 : ℚ) / 100000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((1 : ℚ) / 1)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 1, 0, 1 => ((1 : ℚ) / 1)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((2279 : ℚ) / 5000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0, 2 => ((1 : ℚ) / 1)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((2279 : ℚ) / 5000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((94369 : ℚ) / 100000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((0 : ℚ) / 1)
  | 2, 1, 0, 1 => ((1 : ℚ) / 1)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((6191 : ℚ) / 50000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((0 : ℚ) / 1)
  | 2, 2, 0, 2 => ((1 : ℚ) / 1)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((6191 : ℚ) / 50000)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((1 : ℚ) / 1)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((0 : ℚ) / 1)
  | 3, 1, 0, 1 => ((1 : ℚ) / 1)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((18013 : ℚ) / 100000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0, 2 => ((1 : ℚ) / 1)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((18013 : ℚ) / 100000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((94369 : ℚ) / 100000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((757 : ℚ) / 25000)
  | 4, 1, 0, 1 => ((24243 : ℚ) / 25000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((39949 : ℚ) / 100000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 4, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((39949 : ℚ) / 100000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((1 : ℚ) / 1)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((757 : ℚ) / 25000)
  | 5, 1, 0, 1 => ((24243 : ℚ) / 25000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((2279 : ℚ) / 5000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 5, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((2279 : ℚ) / 5000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((94369 : ℚ) / 100000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((757 : ℚ) / 25000)
  | 6, 1, 0, 1 => ((24243 : ℚ) / 25000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((6191 : ℚ) / 50000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 6, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((6191 : ℚ) / 50000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((1 : ℚ) / 1)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((757 : ℚ) / 25000)
  | 7, 1, 0, 1 => ((24243 : ℚ) / 25000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((18013 : ℚ) / 100000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 7, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((18013 : ℚ) / 100000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((5631 : ℚ) / 100000)
  | 1, 1 => ((5631 : ℚ) / 100000)
  | 1, 2 => ((5631 : ℚ) / 100000)
  | 2, 0 => ((1094491839 : ℚ) / 10000000000)
  | 2, 1 => ((788052819 : ℚ) / 10000000000)
  | 2, 2 => ((788052819 : ℚ) / 10000000000)
  | 3, 0 => ((159596100354591 : ℚ) / 1000000000000000)
  | 3, 1 => ((87791922066231 : ℚ) / 1000000000000000)
  | 3, 2 => ((87791922066231 : ℚ) / 1000000000000000)
  | 4, 0 => ((20691924394362398079 : ℚ) / 100000000000000000000)
  | 4, 1 => ((9138199494623862219 : ℚ) / 100000000000000000000)
  | 4, 2 => ((9138199494623862219 : ℚ) / 100000000000000000000)
  | 5, 0 => ((2515776213171585144317151 : ℚ) / 10000000000000000000000000)
  | 5, 1 => ((11860057855734931356051 : ℚ) / 125000000000000000000000)
  | 5, 2 => ((928161931610728671786831 : ℚ) / 10000000000000000000000000)
  | 6, 0 => ((293721285460789318484065222719 : ℚ) / 1000000000000000000000000000000)
  | 6, 1 => ((24906313201097445223427634747 : ℚ) / 250000000000000000000000000000)
  | 6, 2 => ((93389141005916999709212111619 : ℚ) / 1000000000000000000000000000000)
  | 7, 0 => ((33349183987649227196022751002769311 : ℚ) / 100000000000000000000000000000000000)
  | 7, 1 => ((2637562016830638972298661970284367 : ℚ) / 25000000000000000000000000000000000)
  | 7, 2 => ((9361802794045378221383314647067431 : ℚ) / 100000000000000000000000000000000000)
  | 8, 0 => ((3710229143730469921261470989380337109759 : ℚ) / 10000000000000000000000000000000000000000)
  | 8, 1 => ((281014996174751187409135071091512005151 : ℚ) / 2500000000000000000000000000000000000000)
  | 8, 2 => ((234944722923005279029116045434876793009 : ℚ) / 2500000000000000000000000000000000000000)
  | 9, 0 => ((406440614064700715999523755796833032710847071 : ℚ) / 1000000000000000000000000000000000000000000000)
  | 9, 1 => ((6011845934172387575166715930569403471118067 : ℚ) / 50000000000000000000000000000000000000000000)
  | 9, 2 => ((2954246634963351814185787769146996340408247 : ℚ) / 31250000000000000000000000000000000000000000)
  | 10, 0 => ((43986394308671741868159057310791336463889927243199 : ℚ) / 100000000000000000000000000000000000000000000000000)
  | 10, 1 => ((3222579164489802281706973369234083572768417198367 : ℚ) / 25000000000000000000000000000000000000000000000000)
  | 10, 2 => ((595713246232174791222454442896650250382318939763 : ℚ) / 6250000000000000000000000000000000000000000000000)
  | 11, 0 => ((4714052044515043608356302079362067630760828544013446431 : ℚ) / 10000000000000000000000000000000000000000000000000000000)
  | 11, 1 => ((345797647230569615455885027945636593921663627483146367 : ℚ) / 2500000000000000000000000000000000000000000000000000000)
  | 11, 2 => ((12041399468229046836335206215416833868931984809172291 : ℚ) / 125000000000000000000000000000000000000000000000000000)
  | 12, 0 => ((501170377388840150276975870927318960247268628870004926247039 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000)
  | 12, 1 => ((37101226844940684761513803604021356982257512492113848448991 : ℚ) / 250000000000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((6100161765119076847965593051761852971289061520580018814079 : ℚ) / 62500000000000000000000000000000000000000000000000000000000)
  | 13, 0 => ((52925947343807456141487935963540162959574493237833494885006823391 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((159086645811637603058127491895245579287626314137594313638582551 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((24785220616349888738615417549747782942696472429208630708590199 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((5557668724887765828616075028943321638332085352361109078803208916585279 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((425738697580415285392924846126043761227390364744809850181965843696287 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((504780200897618215255203356399768582207979088841475646499563153707 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((580781639898933573480670384406352319687760562616965502657580022249236193951 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((45491888206508069787385076975444810093959887061771060364499620944771399167 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((6440977399248853567258391593117209996483153031503768105632202911337489759 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((60438782575622462395797383506043062056614276533600417520293169119638170386961919 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((4851091084564993258547173165458442830435112914055106151178045319099043918843231 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((659031819732286436953231252838173809020091950276744093435292193773411006079167 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((6266647472878916153829003284081777723220632662199337800972546076651134501247209334111 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((103234432612436546060291019102982143225962155367537453950979867941447716376199193843 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((67579909574094980260948951136475431830935737078176143585048934921153188328073308191 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((647687255368110438520689210915513281962607883699089308939978200707490911748197897650720959 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((54798099133435323251241259008321827701018029576789108638008316150115248579608078592639007 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((6944101318657210752702943196911082987619767054011026258933824117332446585033838790593407 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((66752598601833213972758920144886072905529343376799358995356802822565209850765687403400886179871 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((5804180521481149768279529101218027830268814532080604049712505931644546505455140405806985552767 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((714865554116837580812299440760161163045134699151186593620303087631599253418664730696051591903 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((6862475977456398569395286535152753814021898605125178709032826125562656288406907154571538227908246399 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((613374710670657798306980998552993351946313195741157450668206224940116827584025500796289473861083871 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((14743141433715840852223580979803279074065258929374776724436079600813272901428859510450680606692467 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((703914995516582876595263795035830224675432549467057989592718768643222311280671421269761491029473304427231 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((12935013351617904346891358659758301192430492092298256117787028684388787962960429915845687459556713532531 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((7612684211529150548927510089772033859274640533672710432765909667529991937467904126339908130673750039967 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((72058754211904409481418449073736262472395894260656795419875277478092246293245681353806122146960366265493362239 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((6804534225271510339216358852612533396241150835818295359391906835775667021360462314898149470349979414834394527 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((787176238896278554983582300952558837414929854400658975491999695850129940599942826170909498282117049596309759 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((7363212576223207218351977620639417353257528145483921126978210060330087190447301703677329940886502804108343101132191 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((714397769831440538591922516604360939191900570806288931723797574729753812839353732385134584904027201078299381287167 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((81485086646780457360654726539399223362755129023655151758469867980660980535027525711823335016468388950482986606687 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((751169007605607841988657776082121176209559673561172152831806705183289998075321414474325949191518383120900230110743732479 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((74850532456295419772628357338982127931732930958358778580242603432363562741826417526535009732564408365674863329736226911 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((8442570934073994998891495487048122718901359103782248097637254801891080240762079998742479323989321204522508808858037183 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((76518068078733606440627645671093693277719936834294254890584766961441893828370006562527665499254398296736233815320775290310751 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((1565408154421864916515346200873988128037328490755954959235392683173381986948681934228043541464843044811748864201002880300019 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((875354841688439075800385766875640027141624423747449757909323523447281050102743019705642707373443712977772595753191905481503 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((7784033566522011706195590294335440740925152719115514539769593873384310078689449149299173265499138312864701648918006243371335261119 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((816927975288586763497185886728779809571413084211493072487045164953257503820014017597642634297579378218053883294696083437032450847 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((90809979572698072767525593955772609776598891957148987444688882021540988811163957227948729423862014659493033606379321360287880831 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((790881463639115722701971660486141207280365736950211991603516804237403957815844626770213681891888183446729029906743331180709537256538911 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((85111653029541998491439171660675164334639410210527350731819326297999209390002312320498075695087715167399700319084199329288011616202367 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((9424439816417137692379861613332867831101907455616751866359063457262488697387941871630059663854014874871425244531900486111669945234911 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((80265692842159711635662363628416659589840834230254555435632277299079574095123441583678294946455595983684371823269461420192378321362320492159 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((8852144485555557279797231901267000929769889749806568732809845930577294129033898612808391153496205270082257614981637679063514182149575888351 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((978336299220965969163479393315245958718936203315436866488558331585243455471335249602327189024432930827753421954294192831491882722784981311 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((8137693167821769827345821593250051748833689685474892141905182376436840327782704058810137015802068137384310484590115804762134549808640822524552671 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((183834256906961680448938716239275005094231052066109056324562002699068920774136732312019955242260180722013150982042870261846545532135989931547507 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((101572300983621068822527428277825150812728488048508116347865531899931240019644983074332824277273937557681173848292916190306511087281134155171999 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((824255966554172596836797837933414133485686461928580096539450155681968184892525999325853820044225368056819996120284638379597875330891625780819511009599 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((95294111531950520141773212901865168143855970996678130400949355687633245054679443001325269219724436804875219421988023739363851920916597180861210615967 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((10545481833376552246357362815922916418893571475110151836673683539616108072315120830485198166407763056876278566883692932747492167994960863186246401023 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((83415211307750713790891775167938358362910745725738175130331371741551655640122786030381499143753503758154046213875141039244271897100911833310156434464848031 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((9864822350157814494993487964835263584294665871169806794321224687592420955406017128214185348548596689461372514852078109306947040100609222538553685685818367 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((1751606570841404109089741614643822373212554213006187181791102563934706557591894776841302184627559996500315242064464648072141194270305934225293795898063 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((8434910075901127109732665930823174940349524163392185848874241219878488191102747194901071692696874396153239187157183184732442694657515948797646152564013243837439 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((1019756867899470877548213588728134517576945773373462303032578648813566848207205241982184776471275920515370828494139200182421182198741667785824416429215068644191 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((113628165761339865114366585298905759017790941529248033363705415732180190352493117653467360463666130181815115027165064286777656341093728090021178874956017776319 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((852304028952713464218361951225852195945844245775157186372413269678713052106175150035619234568111339890585028852836219960015884652135122572085069771313365807695280991 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((4210923596856185726386919849431112154732647013090370845490920693447888798600555454081461336613764099284181681816466167637288240001284663270671337898592066485977239 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((2358141287841709770834870839254537418655794226483590250948180722306569504590963394654510150934277569564222210316862797711099145126597688571880568219830152553771731 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((86062078908238616904822598975232445879213375629555808520778267846310472014207642733711351546958099034134618587813301241406739018737339382005095949249071017906395971839679 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((10853736225775655148893109788053815309049360247886780030807555882272502594891701175906650478920808590191814518069255948712809904916780696954156922284440964698379948217887 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((244612022778686942871773586654287762067552746675113767465130115828212917101898004700135489515481861591572383844522143664147842289621293506671893475359540525093776148147 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((8684692324491570038691203842693710685175487044785552094297324358388472933508761037137606534134888847752249821513353424850312554459223980140438899634685582888808681466538667551 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((1117657503019453464095413349791405539679699087309650580197699457775386148946593231979439203362955931576920543717186556898323503536774223657216362701348355989286442089267575167 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((126818863687386322068520225334754702505023990460545953776464307763347599450359284349069027859019587514064989621033433330174319910567783357239231060632148629273641923991494879 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((875875729969944972981250215431162783649325536929367765586744202376761802262288270313638791019775325673532063406393649349699145451762507781873078519625643771633986461315787518120319 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((114955795472442559839549664664891316982497623587494098998314386358694819646315170996623346574852673454625592080228623338155913388693702569453897370898609763239913034150625070430431 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((13143945579278952695948771196953927004854718612033467718820955341963310728652811598506357246490605080617639025124764320465695042544917175026715500976541422361813441314878795807807 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((88286516761533737155267601580023400730203201594487506670655463634092634517689881781227779069745177708485547291597962295481758657137376096867580546818552377085327668367909552297496383711 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((2362106265228189651461523298993046203529859797196401833322741607034912547011005396502396745771716674355363337440514010981075497247077988791192251258027319659205554899774093096199367283 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((1361616227886477618630083336662338936470522474301842464571229671894398146451181030774802348263850429682805264749131713551183406100906841141767255870467422400042387198038449765390496671 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((8894610300269177241605448293505228303508545931270191517003085447685687826799876453812684283032782675172072612360808103862318082715397044885296708622719969273165286736211256540762436234423359 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((1212123736947021073434171761145846096596251644875674435454550681557955821873647317056541514910671646253265027091147280821963956898671227350626233418908770359415998393658974309712429983304607 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((140979221064496205464578307009509011227780024710386648413527860725570721048100582342055704998588051479636042365465146058048728013497328386774117007282600289887003396663829493018561848346367 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((895685479426101987113064550009794889773797970988036703268064170612650674527277541069849203105520668273313320355877099953383095147769303728780565096017460780339334944009520068495210345006297965471 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((124275283016530294704953828380018445504887683776855436333270024375936157643618834105143145786173467365576875174639865850491263616993501821623096715525820296033074318289209977962790924570472832767 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((14588614693935220988900755610513513331903647051386499617595718576219416518634760689885627751910458964296987925771884635123327968297157047426683733128322254473000404165284717149448289055205488223 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((90155943007961818421872788519874333953063540724170035650703947716545231504464654273220599447864879944284304728663766045500809305999841423581293147546071756379842699331234399343824505047899332703532799 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((12729256652604534942373372510024563429058733535247169156483785380937057639634154679433816979927692623257618922944576035918549818493955221569121822475655063557636159345756476674858635768617659098943071 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((12070108266750397462618672969171123024548483507889049649774219441805863439850155768297459645747154731852393661161228602288009970398207952656232473460581692998822659613287372357873057729289876306923 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((9071026185718348842653713179832021020816653274599202094321280842062656951844824959109554749295560855462165552939270937947865873397899035301943053040775245577809375693189259031677374716865212127899686708831 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((260525904994678811795437675990329367129030521741637040886025704876330618735896598171776818791916384636072208175075979650307545128727541140730384056360319828578126913494088299283533355615130286599856361971 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((155943864641436575794508887385896362257861904127059222381196426497219126319346718237749056549729399397954807288434876561824455068781801800850347146666511874798359441127200536878826256542430803592267049247 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((912333670120054861932388259067567991713446752870652102439004951784610873888644286566209572136272782369109101065326059143202154606686334062409063972404919149932292974790577185560362174655853203297765535025672639 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((133185357118308758761024772457803936858939945300521731629399632863779095112833357083613641304665317822230830179342367593274650797277045167218104904718731532986792312676487921877593755464219036341626418503844127 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((16108278992414246930590847431208538695452765091801283112502987163245244509355058585031176770867762834266006880316769432929655115242142627449724367159868800074114722092562014675001713500435868020729776629640319 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((91727016115559457265697547619947323810006256621650568255066458294961943557997472678966631112927926199390456758433754875284844128078382659135480958011879815259960555738011978424145818060098210942006835774837701269791 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((13605887038757518485056912146892312334812203567605277001112467946567336842815380028042802670703163696110783653657639897026433468150811178840717730247495358013293969926780853689783215821090729267016605565169206871167 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((1662873345790954083735351409849711994577663075074648976829095193272098625561593592419938800292220343155871957643839937718163426488799778060638776745098877051258054611456025043925604634450680804216819098136891018207 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((9219286783809230422706611871346809000626480431128542475662366602837263651624663499241402011495895467510278013836635013825755455522628893159956202526623086286267217684440452391908216704513408068386243085235659031128906879 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((1388827429121872591683071928256741435855583740620408401520963550643813979594897118897344400335913630072193488228623008535037933278475797307507638822775112877416932992433468011672736388874304544164233449547140468572038111 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((171551810576379840901172579411143751975637981816816055270913157317533421907970096525374706963659486034467078702457279842454753928862056140478686780323082291430659607016686766802719626988517101001644951997363685419042623 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((926324874501293265760400255687127018580120331805169424885781873943149733540167869759911866422856159373477425887749409619722716582214966018611906876234894029748751065662961051771986502188225806005541373710603907108603813264351 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((28331274710429963278135951242704452986252382436361310033273457790275947562711246736527804502415321880853205479396072617825159069142197017725143519446960384453515821985875936497720622629447142032892486417001739880986452441459 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((17687064539057963483772592820347785183524243264389935671682360099233218171813013319263925794734274297698992026523754958343546113481417486616282497050330696412818541686894284435229589114708328858263839006395536637164434087583 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((93047352081812544196543211728938489616387375592122033457046349662141097204452101701373122922458512903915691203601024036403613041147044128210387040003410714693359889315547971494670594225000681086936933895695980109931833253943539519 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((14437929786096550997217620313092836227979481239270658037371505622768160283546082170081124573923195079796207620137006072560836722717022375290302300344363026786651486004778668086476214870270228221214445784046390756376304417406924447 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((1822383897260506245956140446428401779369678185356048400430321861279038094081913596493419152208614040515496037535575700678958580793223232224243814525071413347700397010678052969896956272283953498638059057216539564228643224832020991 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((9343885568608567983283586347648196326608860247252964175308006971266593202086940385456880237069487404229619863192625037291372559080005407335086014578081865734897679394818946521980569306419089273493151514802933946994157172341397880868511 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((1470511772743286839258970288280044951339231498057790630526973729945314849599800921185046266234781167546262023581051728063926993747463406181706457658276153344578041337067266816103237148228170086650418495529588461370541389738019536890367 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((187649724133220900787752589948066254373616900288474613620819401288386379393955709481911253330433579412274410920343560443168524895777229213344130023485907906430698073825089604338310138292714101433389198354925392424956853242387781345631 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((938083137224021952014488760041212639145751532673014976259641309871457133887742477235180331092010456849744996869624832144149537027821030284804732109719007587536559106809669164332784344877463035650275215300438073643891618196685376619680514559 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((149671789001898697339966541660262203640510864036830566904169857817505882649371708800947164868780801344297943187138565327044697464902585517605098725073963114491739367839964940208302403702941360222698698045201073273898716625137668727150131551 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((19309946460613365328508984660671874847282176298803707739347018095306007323737722357216978081498534406599594527618411901439330930460139269755958765084790509584243230907126510091684761251729796599792984143989723619490415804652508722074537151 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((94156967576693727589655289796329195543545426386819750294646090771259538267852369834206732664821934802453585609589625784611247659778442806946737764462073027028237546350521669368920525841741309211280821792687040571700408117603002306222630478418271 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((3044820331594141019225240693846028875852190683522601214171941584770374700525578880222495996458412756758903421874701390965459920419318808547759763154985927976451625044406399947855883688190773820300559296964334019852986460709548168382060141256947 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((1985825672453036576522527932551491535846513924123473886046415621105866095363068795986361802324742945094409423524876532858947634969511882503601893102683295373073481288980725396348539587705868445563708172831188691297565929893992291023464666190879 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((9448598873245010378908180042789789854248838342697793015555456939992991366798960288884255154846581165372742420391363395667978830405631869248756696094521369487627749011552379416675661103159285608959359871754083331710795813650077724635923415617853815999 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((1547588410432292366366919257194006761772157062587590975676454687505607347765596419829173905470096213887579277436627063142463611492963198717325479251024266320122710741618231982429676603118376765583868762823191082578696224284656997667536211362005953567 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((204094132064199686656310114701590456509208689987234555273333814508233915241036823346031624041630065156027520069850071909202135857050627960492553481495026256308551028348117126937345100658815553813041525874796034037651117107465860262453513244519462783 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((947964827069258384447186042458029678755608625562048029084952915970198602293451083501718274707717017995060329469912572285791494246549073869135920653743887117177943046471186493172265462644038623631885831737561089930216090138344184796167456808441246762009631 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((157225332683486728208166386501009094622235985298666101406072644860368450192192228962360033113465031995293503703820861657571641308312690631037795192873877830297073712037948343018594075012686810918181157091408326741926402692264867215365715513819156668010367 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((4192588120245363467155092464107698573454501596364183132510560571786840798202475864664412658601162702444639637846605571995598894446017327202779856800112211146217140470475723128813498857929454619181050300117575332442235433985732949720993399669715970368659 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((95089492765698844481896499640721802754488030385664910456717921727191671899830685298973651865892547271175848231746179534037857520552589551956487696173156883360965307352439398174173519444255280873517434055241902495624562210265402375029526731555792015684086867839 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((15964064335074503604828830665916582390525463695932719543566985874789089693973407297148777865032672865269862310575640413878381362094335884791932967378249803507271534889922614894530509597351802666447200740093382005895260702109035251499142929610061284209142599391 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((2151837852823566383938400086728522614954182284884228072393467390995866546211941965065693666716252777127745157110097569912567812431488668075235452329107932213889727528527586011901588771040279282521187184433203679031580559360366982483752706407819586990631850559 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((9536600342806234254912090774595275804138280939464811934890013555473350885515121940978844552932413793433593621781655216447618576357027323428581787400164641925890935089542353566298580856434926600752966734359123096609594311220535756729161408130188536728091593631098591 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((64801999708979151553610280702531569290367308180957440671780528839901268057286443247617373663617160455009168203702914404875242223522809988434975395944268788256455440760454897438810477235748010231678825909926142402594520575923531040250889596237383896328073196283927 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((44150563393131655722425991604867429577392948109522886666123905629373302323520461112058414218527639532528197828877228268573492119642346277075845107912717900780063841961609698044256092414102655440629018921821463468302628470758009342159863728698779476360374552029267 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((956269437750281520401799094307781582360725433976354837483635689216464649715176542448232581615678957272534796493913021120945317432236311484631834695166137093904401653465022363698030776840907588386456717754736087503950805555570738826774232923837762022493275599373142934079 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((164318694353982476442385856223515907214370143894269986055309276328065970771614471674519784299276919332707956847925688390589896984788617938798347265449615457308024362898354369510596265670945140641428973471343803210743359125805361868724206834112842502171313186129865859487 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((4526644002257249007345508170366286370742989225541577278730056678350614172513255342650760302915853213070534101512898110682561469641991438986825233678161137637995034725979537425553499449917668922115581578955941404442062748446216246915275922621136541429219998107316743219 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((95873190571056316798797378730731040145799298478914629658493216355668552528971495134297260494490007518851836210334077890162488660762708478493221608348133191414664479635840695439819466379699608208441533997796689841660333569473655052343857586789645764300667925037244125546101151 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((16658208393271351816515203164097775212238970747235249699730563360822077057499387189854844587352550392186664832402942011600839095705124746555019629889420875906159370570652241849500950372711459222689198150803486503192695780953164600425791879440935748971583991914110821327271167 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((2319177862560414488368429184644999151479723954824051538808924403245424727558889140495259117186333216824239087793423524057223306188100952886822431681138568096340446979952492773873391116399986425042522617290385008388311267069867068413964908415507685251515292364213904572795999 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((9610557121000013559985709833440357527518933998156694686242346334268085633606511024328498175604527519546528931333016596416743892427516036406926829958204981140610472278754650587960323222785872327022419121838075823667644018617659353634637496607752081131289731417839690883660019518719 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((1687955789574599160167801896928052855271607540249435008533751555006879550684261996391267015519080452322896102139000989711809572704914727241152732307156458004272987494061620603077749495592008227156407164316047787397738967782681834507114190326346183292848048483148348368786538177631 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((237505579441914927091165323688616873552956692202855009844075053695657639013367633834826384464418985348765418099632893077658893643121305036483094704809660828499288468061936876348122702771682058240799226244041454316348190896480694960761329551605399616181430013021532645977917888447 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((963248664951650279642291451271933099514434282472049120846003981218544973157812838854856044333623657492086388720965443187251704384492260839685278016325845865258269658473797621335227742211079985628778670108737377403691898392929895543147105917376956144278680664170113789000112381961993311 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((34191928113445008004940253578564298425946031885934565905004082393433612922718876631894123629569779390990520643528459507564214602181724113917821273513587443262760454157832148723348297753239425431073417362657441887609989941183158197305059569851702082338089456838233256803379762987380723 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((24309173582349345874131509804707091473617923264264078316059696034115520390272272519498973285031581749648912473276824656738578080898379640519391278071319868570467652857906789569760011101338702779684182790724436083025005166225016100456833091355322872333031603924467363460942062878949151 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((96531813262822285239563401965081054668077648802604803485116549703612870571929639789893910047719730933870700417208787908137756091060150163180260001122653748458557649400513807727784106804717407163802214319491437568209000759442401312511249238316945974379434815597069468154151605373371346765759 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((17307477504453345842964545978715539091136619772045574809180704403062660106389938842753310808593756344237173235482979717330334632232891395329836578134156673060382543934431160429353423049489455363631242595730401468321174489965514014471493542217750627443665015305362553031959796955206646290207 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((2486725628536970123404979628576921943921882985470478534415381295679396468197973758812573695334004160421853460994355459849383945930135496271625364537380958767764937551924331881076641103515027911208147458299788433387704612906550515070299669006797061957528409289896162046535266124404693107327 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((9672710685799276235772358680042734047971819639853012700086963678980242983002428177332498397293263288498444127671576106103051904557255310749157956045943711588285626816277087521463258375054376996640851163116087471874315192667819969460374079370731874656212884113079848640239132847479680622937911071 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((1751415291201806323010307447935569615129435072678375316634104495499427218859795886780423745637077576530307283207082561595417491317820478061452369475675289787594544191005847441605192708806262542745047133233023509425175146215833722804900687449345641947072316019598599080007898195607941013555632767 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((254244518121358249609951845848248937837983258034481744569878148237740868014631095043537152666034524997015513958805253298533523321337398130716741139566462935134411110043570699616784582338522804315945325971214997873991620811677910656352020114385961917120299322245970078621811392910863331245400543 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((969114034708191899093601716276952769373052647593288955494506675421686550062956144666690541254167963272309673884238965556838905181163626420087287154099662118874926317025252472312966229595506502796000483412102058633307250416869502698006041496136596279432153660867232236330726727683809980706027729859199 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((177160485607571614865435209362000406392646245335136141818608212642558500205404964863111952748669687060690280071804593275350835259821529668812271745521963590954950358790140793361086433948277054681529834934351633972186940879691367484718332641421589620006249782326116795407186927390035374198080819362271 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((5196084157340823913539010626736724439735578969627458769824448178800654771558334406970933108755593536688806206600204904398624772888864054684876653095825047623012636823147312879306793079819514824996770165987611914094314607807083296066215582986278029996184681820734469993536054665485490060958119092083 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((97085322341377361325564100363339755892965605300731085441061100452869138042891108416050919687614576526044591614781746940633330643041230261637217201445231014496107921611356050559702310120698353162355769619116659171166571914589558100108132129948914454293732908822379838910294350564793464069247130839082750431 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((3582645186922307180868967924294711331024618511373388336748683429933679920063237610843675404334680408369279252450680783204769649607510848048813938416481859513214353082917129827070437821727224193838776703839381581587265123910200300254099345263301958402955238842600938537425618171144630892426151241340311411 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((2653483852133203595171659145966602519489426026932267718493768360943702257193265578965302375341980035303877119346531427056157789674579523513800183731401859028846804511675342703235034123180135688441852067726057699584714894987268772116597065376282908966294835912822185535189131969141551489224100803244602527 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((9724944784033440210932158587188009423863271206624691801987494988636807687969591010114309240000499972186302066095338677040626779453157858560442550083185005606983208454542059135268547303780182889578351623186420009323818225007902008349104320971149108137245280872659163018125567568448994410750782490153400075423039 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((1810574934343572522239579811748581931171571494637154500634849900880465983540329957064615002749237377232144494195626866978724043605479921093007299602109434281550664932442996098227067131004030575968572590225233864640974462918444013062984464566735915793157232917202032597311278049838734386802163768921449032813727 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((270873948141561951710575174296128861907856801749224140052371472279731673781984704080466613347069253329165293987797672308919786304087754114044992173707884912002848653525022669013569336148261661553263048535563326530436771290705535506152416645490504160834728407157437528082516470089376958940872485540708674938879 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((974043314324451719265456873714345261320553040497965540661757914582666904706002334033477248669607181875249139675351015613646908550215053954490403008800085794125398398646679578536157540510432079106619464328479269859879402075770704625896625665726370185803699910671972554857491685866963153548140592813286211717596767391 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((182936855734678228866292177555384810163434127281369037929667198294578610775665856991126378141279425423900546555172499923180582428556639407161358867428727110395017368628950556402673444136684451460235233398073498269022706014458334655064001468940675101153937868067518491431190309698277639725917767344896879467107975167 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((27637793724481629980613257719337884518825569400666089266139147784876652619526650501588921986573172328400550270690805417443463618489345992214577506867597857437874092983487846305941735483139280990151233793391148935842732254031559306991291386623524257739885308417192970649382424621234984393223524640927138544012965727 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((97550493529484184295361899715549047965559269878752510106709432641251693130200734260405214479702160146385386062023199992444245112975244426631304841537455296305819721481888505146878650940428964873212572229214260217406959294488405624841238667448931828064109356870203378029346632903579445837184479603197006513577889341921279 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((18477103563246827161106035895302535173988192842385878260396638294360955891000313251006849418359041078886047399282428381370198149034507232434800527169960190295378550858462129796431920482988961710885641987574642081427598555005412051572670096075070008139753063774622086375092507918262670386737640163728997857954615320809311 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((2818575332841584041731812005969059638853272750273388370028803508104054766177917406182363611134922192075550874591694365382175254910566235588253158658608245854034554692846899003176605770482452485932343515095068132796191620590893328451442957455644485373125689093959148247825323544811995079852191381360073416646626049680063 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((9768842523883892987769007114256648107461862739187995626260062448922281029003913091420179685235013150854242497287067360086970967066360841296769606591048118857083901296524336342205791410597340986120197228698720522456477341661576350410642851808488247682581935898484222581251412400477888724209262155674098307679831839307769177951 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((373121482067398170195672694184789614040382280722011807363592369838039629272328866482352589831649493346510305130433441478502229691739299074925474897153846646525390872601715849803156666367662064287404878399320677380954831052382508104621956445570106044634532976700679383426737215791555462648294218603349702842470683824270982899 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((287310054573691935855774543015575670425588627121197126861553388976697642395292243843328349108673468906667057292162584284537538818006550972417229300510218681011040400674605322391940778580847026480971646330392951029152985938079204769633837733117585031764537392096795443274062303281633628366187096237191890737528265087427717663 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((978185900136399097362773432365285625253068524834431959254535833242346738426070274524230936715942956032964010226483259704047363191085406232334851004390619928424150681451705096277618329626660471519176892275069556983695310255261298611901955282315227445557574708804057600770114536820697881014903860368808983197438050843634869554057919 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((188306695585778783792815000887929374880968382724439957607390263713506061387937336412838552727496478299185648115988268426852428110405951706330020350823437511009113531771136869546608325352846815616884118642819555070429312731695996176867858441018147220297214184558243962342295125635855343383878346283865429339113968461392010036118047 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((29273295421745156477996790132795832601653027281729542476889752355685303775152044229610941222279076959133859384654280699236305153642964507895836482214804235492101214187015321814496229162743498765240609952692294011085937387920684438096926617802361307079212427303222519191442570035597613636049688713726650653858342460332906307489151 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((97941425209971846419027566038879639169506823620100509562891292047247019358529825736577149266946820817874780681062998735011245616979538700739207554433338412025458675657915958230622564148538322036793204147106039022994342733478753488706575618036805698809822767695130111727074938725232438333495462399144134935359031420062979004946891758111 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((19000963610747394338660475754404808559273838882854056562259532278590566265899594584440622954184757311345584424845062193484697512657937601384112215670374081603392839468769625271555859601643643380940503660483725548926328664081256944312439748891124399422948537959546705120040019627533432654549733218138186814153020354126737593474861098367 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((2981238172195905853315465688429640015832390427286278240977747495066639366154712596698350976621561484953612147872498027165470271438642859701366880758907338519973937885694000397242110836661667601684893706145091538031340510119338480437024136821381318115850378638158684810525686311598314284456606322084386897215660459188676342047179312351 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((9805734355639833174717212379523032668787189438205264986940488339206653969845101124935048999172504533762025178091234127624276237628742087650058277704319712604430509763161871062265620756133412912290137882158249796560953129415656487975750834498515316990984164764621733513572334892561459973093633291144832869714896436079923265717833228321176959 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((1916703102145345011547787522347574982461219369628539658694540072199250385591222564124964991108283029354935221821640061069001600129519035877879709896693552619147482646438570482213896098351030895718414976503787105470890660662531064794816785072323977174841201458158376583477916511936172987195452794665448361888113476565365673021189027491734751 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((303480357487517159922073318884483491694668860549125494401724596026495211278040783027454042481263921603610284613099590770757899179030134155208722108215235610732681084129377212851929757771199468709959473743287996866512382746002002631783621485753570350693414960534900839222167147866354541311820176311297773615110862456518262599259542128764991 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((981667345407375416864888615043209069920778280093992651552586944082592728480312348058995639002910080346588554031291673389775324268786762069448349608678946958767502775839822610274944365135554043119908021801391875051660585869826087113783630500790391949122184644672588369942307671476132416200873080052046733082125061776426278662526203923441148443871 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((38657894825691550034614596277677595385900253423268026675608177910817029089344955207980387442025201570932926278060628847318960055928935541500169068864867441405104716616230918639076201472337832318841954295663807657543970132946922875336123332749755361912175200105470549264558955501828718422789865761138899406277663330321828391271828425553526646387 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((30880041474603540205704969033283247418338571807978601964755804360536126169946726292780871905762095258966982482420475042451169210486956079458455140669644846976664194453547964939713251817040485267801030225047490470980903009766842215258997649016244474768796625056816295254744775462431815531396783902820912112953832455893470775252436413121841913759 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((98269965718748610714122673713012596719353925514189992534366077326130193193958595973979359457065621372227215255378963926119707575921137949731771304221423545551930469453228219909036224793477099495182600109375549856750157827949618014840647426729088497846711442733107491883085632649531139984460191691431598154227059954779571491103935338051217737499662399 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((19486789065658188140349953832782468164737626032836887851160689458509267419719391429622030353865542164504906170582164299667130893189175265538344375383589590487466072499856468927320619930285335788755480332299207430250876422164103373280606967406144711482222761299155599912460382071924104653537955234545206143070956514104596406739591066783927879139211167 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((3140819513790497017708638504006552767186760444570370470693476813842351682055244597525752476913627289398527351247737786003677044491032125961823451826670323366739401616941887283182776877774848632716018299992392757935764053616314326381242746834861083252117329457408795812409466012717359714940868570530260223670119996618169768478743134443971352417612543 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((9836738394912587644481042595623285739808710596848595405475592351189580201520678743468458172603825623275710076434857446743990684232101867178237526208071518570190126471831693884595839497535640402260886789721661264431655644065777502442497057012997352453296312139280620901514908067503604149193523829728708486216253420872593382043987273916555366670105640931231 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((1964063273324098518656606587073332038587487993270500513051269498706441236472855482865609902584048030155145763122015512159393635609313005277731281646993067392733371347832175267291275578048291746425049667066516034167847857885855293151001388945342584954724066170850679206066603994194319349431118960114731449908626679471519058373117303979075826123174829722367 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((63864609842799065044697401612387952668068183347547097877483295102402408549797751684698229233828896185216841655265265391839317688905714598956494092540250383503693014096096008120556389735761724160765125039682562109449365051771891822283058224079320102343272860489461307330940649482734870699994827826802223092008718078646867653764509934171244678229821274643 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((984593165589505983422031508706373851980008210314005099819326174589409494037304932342374929290450420242905484203081062391783656880299221103743097110729501135950272045020285120195424777542940849120957625459243451863150911474843357127996004773259547153665119680271772913855060359422247619955243650287668491135741619074325764870109035052231413397291199229039338239 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((197905554705733310398040603206561981750941079605241362473552729238411531795796895693249546310041401577024507469329275332305920580270001861246083651211721870765774412081158292290408625854133427018841407614593490442499305797464953056787876960966600144036647453009167493993137507932111764293973965339350370484605050201312699318765229567813773423385779558022314591 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((32452190626285897256195033332196935083850267788797454765256361473871607825464889482372050122570402963191683187655282320591872556799074725445288305915839552961899756924942067174672466739863986428632341124709839702252679967421711925867471661958723481632885397228254173631472302531803929155118849272910177595972177443972660177792710085794430095061754489323236799 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((98546072443516090149553691445111794037501394799122347264849991769827984542806429160217579702210515707902747638760556776850231916136957196339132331242432292698491222616519286507722040831949784990695650156963345308873688364969492768811854974447730205344223679107566938107588191058318085647556388033996987839988800850425048105027319528844026250888973180045213310276191 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((159493075818205012842954169809899628002408996693497338098788681390971408386306051223591782610001646094808799918860246814039599670146633046914309986705002604894504257811315502047787534583416263261245231213400057986003583374225822793349815842177685010902770179289365778586326488890203067643370902481241993395383018670087677458767795049476611330834522024935381356523 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((659353666864887228939812301783433721827318113055286898977783860175551016724079902584874470208519691428086290845518059723798129491436853136968756585047613317198206891694183793065235554893933899242119665821921969574363771257899843667841776972582609953987980972389240703668787442923739844720144668690906794458692002819862103229043992244498500331966298292815162203603 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((9862794310422169911323232307983754891524969125798376789036628873326897073320099913420572778917904156839074391922194982474579535693928513661327578967017093029663918187098308548447221271270269259786957809662473933453101097313806063100005942083657851748129044373701984382274990001982419424474248782380261745471903147453761364623323116617481913270141510027686734877453868479 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((2007894695370113743419081113774647968917589209283163600643958445250419711053513266781052500741708313529107248179006223236456632962198089075800531678595210320801491216580565957958602185362666222359140677322050055276159817962960217015580366946613740625103506053340475457281600795713743275274320580168110542737006783053239543731959508575565672118633611422548451588972621087 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((66957250243081374232804386192195485332984282321621718291193232284267667097478318332866921610954852669508640334336007458491851636801139552810987580063629332892973011780447536657376401321165710859525894234797013330950321441778287336522098061398493541289457416497580696875915884717447993277352663141752118397255904525779077170234034537244853443627479207372774001379987891 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((987052036280229752361662109672118965358319811432467019204597630146985949912144508729586032573703697376746611291305618301143596203900339905705822299538436052116354295398280279408415824148504039776835421540038002626035697452406564368684460748492707811619189788501882564170908531497078938668210383344442920658438028122064006218138379192075150673389984159802769483650444114494751 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((202175699692420252549706820622098865294760862430836311910946666409932161304784604140751596695565792026271767385099693081418929320130576978700154135214766674652217792321884061646336117621340062744269316823188330727863767398170729354201563841704356649670870875595424988220893559793453804394228421628323873691615252448861242387795433064869188165033635689958327305788085590487167 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((33984868637255611214285779092275311531021374157888861176355427148404588790150846969827112355349043058679493539377664287314356855771784477006316440550347892559333623342819281053870183798899944897675594571416471775488625836458581282266898803828260180082809677045395716608418747666457137679839872930097191806945412003140545691364767333720242854471025212333632380161953202993119 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((98778113611729001500617691627648194641899282285070480135318673759340917107259165144302304307947844217746200960949219893460620030165871176561552744585142671802168238502440311687492792909070177729700181895311846269816362732886155072908383876374508343474691321151134155698244467208847842363180345665831733979616138275851058202799500705976939893897139415176427553402608760640755157119 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((20352580342037510652787948026387965222139798448897436372166200541125209910131066025845260461420699683285823011615405790545322116358054868087130654280796950065826943958654239397480676776857006122548348605084027575330314275106883736162728185644363852845279417218135477058833868038634091076288953762333565970561751847759374849536429488214895803799397938135609611996005622075394084831 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((3448627686159113261851848633347050350814338667698941734110125107907408430266229877692623698021450708050155575411051328932081942513240331077132534553405914209975428991587537557022175904386279884114809629614551667373675896533476786225116294633004244166791069255271850147034799223475326085015863072950026056287663238872332957270585360715625365524694719107715452939546506792647521087 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((9884691803425254142611790941209532480161393369959816139889887923995243006494940155502664155236730110984491238483816932125985251626723097060937170953755328795298814499236789773637007374036043602174076465278683620636300334739733568075291278029585977865363145285711379139087632126031762035970966040138874903922395352953788511539986082122337840847179149470784291787050786132907423422162911 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((409681090586428067431624097715404689373051658375256110668827406981962985931084984534500688365200921552085340641961537956022133126061772229760465846913678968867522353220993243759985646527508744451428299725391877932236444494891909810672744842544150870824555395317688407442561782623904579303763989182009036383976723371148269793753172473119883877143070278834978190480486403140033369634163 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((349827227301143926792457942328905856292327876709917137173856865773628994201746060681173967413831587721287054478553331652644658971476988920353654046003441603969568296748927951203447314120227086557150419297030913163085146944900221902097162559684471001945940086656350408591795788404095328060909011908196436170042525748681718293542280721894299069136840540482039378734680112607688737065631 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((989118480797437808184132099331002370620350530929737889305268833499507087279921007534630913665534983843495453684479320067797102210762231946543579885734936623083553825478476614148350748880407398693565421951884094595827026289053917085697162616373999145176454657467297137976560756101491351572544094241865485808252527062896068045516946583802899702907449156408442831652195636576340640926091748159 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((206120685276928430160854385760786733776900001860886258636784301707738972314462535299113520526265523517759358131193720710976262302983740267796788908946559168743148090758653034028109855157473174841565301289069469435045841831191269701835782561824353576472073829955017915240889843442432418182453029087174029683404207375920967995434932669483516642192903671545311234319166082529087499131397595807 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((35474088813716159104146928793371465445656619387264429004904759723227080727480875662837887073516362212583291261224098098183801643664210377474177903379614014117300548979278500711732238616973281635368646574532289969224207811954030196923562386966752133046772644254517062444133717540353410985387215401815529010994715704860959787530737803974292729807324221897014715085628040915677818514793676287 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((98973121914373408520528362081767362713071859253308434875848914548514984319518865560035584691702870890326822468750628955477944738527421066563371090236920234183771890956578359600565711821095165807313075304177350122913600643871729101460155538944597925331156849570531363613710061992541637356549413629510604030238982726398439045387388732166895842063673069441108341580186050028072689943554352182016671 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((20736697782637964150353759495188579942373152332367673854730335812161990488348961175729351914117830329333686535137268330076112514418486270832323704051867082735034806902935308812684170391232957111547299421021220849664306432955093620760292258685826332370548519614100741210187826390668385409129251015982532179215919960644420431963772619389094370901831193848493112237958885451898962830950939113952767 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((3596026699198318202279102748971733304665326996630497107251670076273534874347323613998144520331411677781570754288736887355288643552764500107148148850600475467721431940322895117777377803519340260100033328701370811257939582207018007420361379188240923503200996747924977141169888468809072310639085994963846219724516556315349165288974950357794136693015872525157111555663131108149628653859040356928863 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((9903094541937504188673741001294304251869878285875463690798986217028810555248675824034998091771308223049251909553528103899498167030094198630518766414567925579688369577681343217145785658844929702070327603379912353749233579161531203575693418054662761615575940737121474252862204840174161775700211614803286191729622560907494294274162487265857793719706763890087953086580577355099191677283280661064731225599 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((2085801710667149329838144735863324867745604725429112554241927752690198384766051244361773651427453315960123655294175410623437586915254708402540566144627003364258910616445572584401237615027211357537100717460532082276692719103932237522172398652263011732112516779143469318889912417684248689372989635639397637733817100347494356485749211717649599487534575043442993094515549879912797249930245112360014341471 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((72882316259223250314645389542228935407276513166570978918487962969240770126977765821331037964912970155428015978397261113296933503202694642282087866861538537737260809388502762826461959469808162447172347522508478898500159427105191217296564980493453873511382457197531028885927721835017865572400858024546574495758454181843973104679810951794711492433564280850568941547980005221314660937009744480273589491 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((990855128828100332780952264551142197944708543959781633037009530314791823288262288838358734922366585700934853452656893636891742524462959430563425467776360569029611748676210678058830646839537171054674745603358948910961423631894538150234612168400470150900285951421416403768353408562395472611053269877371314627332751450279329056358439760791734135535007601543710044827522504423355619393545912704017621028552031 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((41952201211012299096778118652823625478738455859343925724776610120032945471571353773408881616338776656026678959343759738725581958157572178314893297270519537980547835213652968293987234749632870309510993753868262146864723235274359211621380351914925696845881192849020292560161855206337760874016522227925951074692607226700839183580322712308834262270204166275510101369580680002542772603987834499240262451780851 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((36916671756422017190246439138493658546455512951093443041979213034052559981034340328112429721798284869742641434343386809235093431657706338517616331697968216954032271376758748030430082543106784641791569662881083865010243688187899717422697002221819144991938073398606500940030578909113738559289633175960676121777943639571922027394765291357444561033401650521093202771501856590700614020115740258761983457099807 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((99137007652379000304205684253426738077844200584940632928069552366276589571890023935387075455888812326011521185473778395619836850291045018502839897968587370538755431110825325477733789311600283295258601067843380649778518586718255670699490115719783967670309084949687644607215742812624698354832486025057653590066764421611410003719489601786155158636303132350078373220328471219927646446549534235965438878843426613439 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((21091021611694295291979019474273277693465272075739050523124203397247471351575301143225667902834250754816703244291076615401612717323298906666695677193690808136003839475439669690313185440364523136757889213922308308854427505544469972726470078840950029276925471630001991268372720645626660110142218292729346723248348432786030338646418609188980723144931192814712416253989323041881368928650455691218574991489077303327 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((3738672575147437403053882875238944479003909057321050117535087715642469545090759624330071151900065550031744405032263036276221807966337509753652162047584290385722790976230725798999607647897511534405311204707295836783656328376470461013900698331452239890719879168543211416496857919930565880479586844971958409698762268969631099150376701299603051655223747623684255792841940911123044337064757517952291453181873005439 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((9918560275147353879707586217311627845668079365000262588788995587253155481309689668758542923696771330393381242751974993416248383725115627351094498331397621570371811278497475140008259963546407134290258924171311988538949020510015069388240182730360293245079398037617073333938342433484580159047186873698665711641010491703047150641004514230957676165349290296744546002429177500553352067514432996313822501557575326083624991 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((2120285262522070106284073179439072325215642423571367266454948902979153170210880850579967483993750795126876068542797931794209404919945262656289463011588805686062402182963230420595694697031909952072196793860831520478113882637804061737950770502964482702568440812211466644244301783756865380855319384203518854214519384891286771372036158998825958139897949100817301757509641286730805336109129986705473491305963278204599167 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((378512460317249881384969247919695795231920280067871333243617547932997892539683645255957490344498684339074562800716956151636801989125418268177846085713967749043265393029953772136157034210273432528877560277815079274387523097020257314793916368280185778845520704755883804870691455740246216265244154778216866374807374510142091913165668365581165532531070167524646951847738611576128051732832060989122068066509820602049247 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((992314614605380638274125203741481008167850981595709780241428724573493029615714104351074937166340613677892994497261128153697943723755436637495436713035662149974417458540528231487439484499910894855837444415122541046432080116509612083098837804081370513244897713411885593450427437105506345029123978084069384541850519091524856558840955003461244942047847176013486061703239051549719281259269527429139115649486825947185606775679 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((213116652605576729233517787123070623799982013177867825342382574679245079921040972921690823851080458002151215719495446111964174440376844540210480342396657664517614725624132969026991958952983002073002793499870237379127643835679216882379459935540354558619991946756246467939449757796618576892700751788373520274602618733897067486524330827706985773599353332959091007353063822224778542568282978849012739032600955535901694540511 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((38310166245613562568120281306104118405418014713385143948006477177713890585207839251649745139069995769639783687798022706304740482013868624132553214123627606464572770145403842619978360807091791132908967748212933328397839098921066067065824391335610288752052143476431644575613628296347103176980732950995309738738211895360203022932132565109248034332505683754518761645013707095815509072070802018173188617464204525022801149503 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((99274737865695165453290921351879821259791929282205536251603387309275963711805324313506590745450397372169083997712035402736321251267076800043806867172462401430935801145011108677238176712772091236650523792010699076010748968514895582669954224733354853964407752316966231568323386812209528274053400687815543749829891636148109188601262082721634223936113290153216666156872966055695458853156006033960429204726422277809958525814051551 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((4283506039944851946081239926426141130862983794990430212548856915259577622704456160631193259584378803587754537517067814876347853446221246857574949070931336658226553837867720428744291186671020044885819167338332884540182992536336559173001361817381771947404849325979905976653259096588512988325204830766359506433389197363150148943656002392404397371721342343190236422750131386160872465168960811442064328003208277493895725462324339 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((3876342747192059973385532883667693032226782106762030122710267713909459923329002604412699039281163536481137574072807910582540174073214139536321283899190686106122385013837570084097974517112713302309711535159106340417394879484182785835468374047800849321739334360891008014016568229805411551985950104827715930832796066298429687627073677540348188615906451638093225246806538517919578902461040028294993090060417764541188655836771743 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((9931557737647787068661610957055546852465304574432454250527560056989063419519356650141303462057408549614224287780087068920823900160822770543334010248198104360635980618253553314762289498207589477911473279728257661104058369409782181240980910233861964213767195178399786306871109690081400973694145369508465048127697043811660916019112501484357900078627075078468903568557944933709924756513479133418811743620827743934647976122546230816319 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((2152051715091992154825091218190351813403888813305689583798902528125880710674319244548964853036387857518290661646793511520817415409144010888996951604981321929990945295295316336349626324540879252029482727986216181598693262730333920036702595638898875570869771912698560649137320009388749020422817238566053436907914314202061099872592204716601473217172447809165203048215381539198122085813661435603507354983613467089992420051703816031647 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((392109779241899704355059387916546472901411908120966363413957504177485648986996407123097317724699864231228523757490430384317062385521668958472068724505794322334287425838186168017945927015003845221470172535824450010940208880090206984506849322642133967248634086343156773256847240061277890679992453849803939976568278253110846982324326627497895190513645709018151283493432900456316307610116490295130283410830974793402541654678327085311 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((993541172144084017882527564406374900920298327384616275168035315018000925836622167717184666410895587418544731813519036606989230634276684033403887213112206910408856854963969572760802497656352011441027821934675947220728884262831734661530127517859319700888996441790409433993119750343291728486542804375144338126762642327462628983807627652577370672519958448080031960861244705449271889347420512341599845433753893367368794858708565255905207711 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((216206948123300038048675585104845845016718141566724698187796538920563625284086238766559186449422061591321649827062386310369770099477255861229116236796134715196083384503395355627771017093521288062581984371033646611444255259129146004998546653342335268768205288668253461502445625985837390545527901302945241925266933538967696290271479439401936991175167304784769029992940342933938707946203080437341355717391931732809273475178589944948826367 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((39652772660970136191921413017213440892942459385978757207914056308890430051547475259664559488148140842372038436677984703449252957113529298483924140717746747726403665846919143551652919562176398472602723996229534215931104735406970329169382057413899463879182961958781409027659941810329522623480300884317690119147070214611625306173506900692193207639888794686446224970424219048222883400529158003651228910637696682252955531316606522852735071 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((99390486874065064683556243725465193024947632856958853271332324642933729370276197345302999784529805689100647796509977965564966705726056395548291432414185853928373412546094844611864170901332282967678354528153434463272964078999167968273936603732866140853193705215319147876496717720146097125546557906077996044684463793800320834572942013946073892995035958786864536114514801608542338925826726329164435813737921163185225802021468594634518546479359 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((21718130840725722891193242205042737082957857457838581952969208705673522571906733726632686220846404116309481389012727636000668193676655905188396602334920716233174102601270979392516138560318804818665558249632424471251064086375235169535497372598932440696563373559173214610347948894108495274445244548061190263938944399382664654800948278330685703507335932424785206570847373177015003207195202444012457029620282101273079045143060608040297832697951 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((4008877330208934175605850681029590094948071804743142640494003848348589447298715053626476966826914014391131800200623759099830873722517445819533532764936011599928251406576513472701109575723165327748605913531242862472134389633045490285997216688120806609749661590588818666587591216102553372487096358640384594371356761540317075281992821109550626033574897848056133483536633209145261051031389241821134376200424414993170223803544160322401686864831 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((9942480855818646089122519164128424800571283165078350024362360144229013106943594467278898786666293233074739031908850110632400343052662215991496714185494304849366670568562424391177009943787826211376838638467311456864606347171072481998043123357666844846175036767464452665957118754532467039640703123038674408740828163757142476837813964914077047208048548394757619408590647312996531982091342336956918643306633882248626573710963969807064880712710629471 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((436257836490104410834048631921516290305694942294848164213945735272254732795247772865883843808961312574682443927460055527637895174689460225871850387191894077197427550149568642204451233168708735816433805792233523142971164078356335002435924244937891261570602219125628312427433863094727919855508599729898157056102691077768519955425854710168086395502124451979585501085379835307833088314996800646390692197467520449036847419548625001804418394414115827 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((405189477511450137105483836590018762659103517145135834672382232172254272470384393611327667896320233719583110340537521987881305309233190276239421967248909899056755191067699795874906714667188123410167640241923428184384871544881740307352093607737842716167942657546873047196365292720736936559573758212957695915180988790420304567929725695331672385282878294967261777539645857052234612068462645807996472700330109921381423779850581195070441838008740639 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((994571975882749812784403010999635320005111421005278813449051564450747737889160066282642399598911426112030047702206276090268987973536680660901553420970912054329883334884667427370983251385313371741420885473521714872856036376186939053673331508139662481288692044708852933633707339746474382063853513018036665278463212985597778396707666054976536867976333463464881785969290796280169726617977884996287455450203732833920641134529958866722905727977789392548799 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((219050432608446739726462566680711606091651711077044391869216035833286792665060136163482566890719365992398107209823282056879236914090796982621788391372280951040915291585921607123371221441627502089968361925742100803947505619840354458153600873782339758633676694798222734231695121757290856770149911929178696957638757715931001440554005086212054694459652812921653343948560386963294325910852494910485378431847223813782216156141546043518838417415150146388767 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((40943269924355387890399852673630238611385641621184112461400034426213325473628128237575036960058884272350586426208040892380935371683160534422414180723582609813523927665533101916325301852250129268395978364463402562992315619486850849068767194596644002297282464787025876295263772337528847388708086531404598212744279530713991622592568220205689141552626815070308040213182700726709443040775222579739622720663825984195803894262662105280200609538241025650303 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((99487762792079217082651327745024585513562359688847156346373547085652613276862146295026680607749672370766163571609504068362594126074683017288618694783603999655056760429731180453572318449980637577866147541250770710836551296784385251556098621091631808696732579567129742494079327944535040960983792169999102065663294946237876749518905737942080807694058612613717429260136003154163336931211955029214650883380276063804256983224457688293773890643536007185437612831 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((21994649536649538853032321095488689803163519072264144830122549461114702895898305694221191773023214308581635998461553458620026985929180032259102539827827808809467359340177683328487388406936184355076667602966518937319149534503932365379701695884082775572560436325817856654676655803236090069937314368950970356991942265459358589939710684423772606240199537006481483581358550977388665855276997395401777721068893213425366990432197181794218038649661126565770954367 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((827234389717836971296157335288914036886933756914957671650376135500911339975223474905976557445420937142925286816016473186604329441365235331971008349079213903755003037862523723124457837169542310899400172787306368729415818401419609772143753651175798677611553686657945577183542347657023313510560810090750994296634162848671392743309181460009722567669456938075920571384362613560336383052914044529949625188224176353293726572927604005635074838025115480035495827 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((9951660686925723636872723147970225110329366321476817297250925264925951462324203883715372822272728831956832090089217289427309645083541761658509657608033925843448051424993301768223166119806222787585650477320293981210934509326245651804097470773796202154901956801170466669423772098797827280447079483290645262834579480781522190975349615583856223741280617213743900081849774481655239942861540984151957389213713271865143927249908847586595148286139849462082562085248639 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((2208177391301583048987817296374712838826139477760055949820848641487053997471635144525352605833673639916448391866522156569051740632962981132317175844135306503610546737581016811333433273664051011926939284483596107817815837991581108971028399509437640192005757194119526410585322717805423152269425979658602817721929739640426993883019436133564232343749031872341106519801424359767035351374848441384016679886211581672584510332491939582987298479152095522775317259789791 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((417742815897834134814400312657467798105993485315490334312804143001035702392581871453437235815165368814715053016449143157432335601288737287479603730784213304643417563958537758673789579954074976419476205153099020777695149907731788794714054579093348407935166170811615610040802571128034043971673061357897411654908940493759545938105250710809109947084043940509397331312510479900747918739480590659110521003611526309220999077906851344790445441222650964460299119135039 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((995438267364493613888042010750802173436671970391445771524272566325797113548072796302336017865055147142934287509629346385965783896888752505951897878812553547920349164925192894565451963559993438241670249894238822712894678710608475915100874219452373801155942761369655769126851949191452162628510443758654902808436431021871467640152767873032927978240910565843798106824081368059323338167900761133436066862708907752641767270646648037899397548614731453887269301422828813791 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((8866591405171995368782370811482484552606709109708243850401851395513261819991953022995401204774538237430766213931116962196422351759517092797542119470670824965264484526617051666686825126657746615151259748250989772443436594611182850302170709704198022789217722717065790334241348402792697966926768610732202036163869895174523949975700016789638796008407221838218636552005760091917678749210719583315755889022419617790231163555623574514579873414917794923094582592594753303 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((8436189325692014017861160962475124987385157568535618210599125155340426801699895408597681510816861418023459910750812716557060123117464881791727247019123431920222934378507230652058826427094049045875627920892080099294548133242438784498415959814496895087927458422378494085937959244961284527657807114519918027203066118093730784615877617016337826734570385225287899129505288899455794587399134421504593213887215819316785039380895917374268092054992209127277008269284774739 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((99569513852919897849000636512542450305045297173870346012974077811599147808418081714255147669907389180731565777996211789097205060565494685234174650925661865763695430344825528267247136349193020773428179812269423460593157935241411263632154399215501063241285162447693045276731891593248149135089902067060504523129337559102988529733576551410244380378616489188113383542881734622390284099566626927401228193766976915709050935563653528688528247265223592571887716705970932328642879 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((22248824311953390038252349360415344546176005576252020015573082670851429045162382820448619506258759795390607788077996266666962805780542073716086946927008383999066394155726089376734917290971290151860143386854813294128284608099821200255283813320012713615375573853339424924530327858428266968330347548923379157698056165155155112929685195983007259642709997200737195759893393786456936358704648362010398104372122522577607227631777744260385831064086561942650859440404541844502687 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((851634199759581985810873774374599024308329893716281672091989372095689563803111799754571965027004312657246404585057088451884692860356576713346071520134926512661384466485848711349858149392563695014998908891876787677489329087389100898774108591361782426723690578618981344916679287606956045020850690700846875640815975157020834796428908840857094576996580730724275693735728677105935726795031436744993549177020950684123303792902274129155210243632168357274219041002054317242163 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((9959375452786197840112341067052118492836819649000970682898350749002799979532605953292544030461490409596457130903724510325314144360505167950863827633203784610254174066210840277051845010136996177367643900704053222552715721190796739537702778499567619837016839495026344989719911877763234585729298968166432751343192456114989924562427885580033351931949659468193071891558206414580348720192003016511926503417595844558547427738206419848807722166171885207416471937825770912921699848351 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((2232887113165404501461100304018191426212698902700930736881974349661185332258459074722234677547044348488431813719442586295575301432998805449118653628156583045540583814840103263939044481756407065331666956627972908317877035573633609757724922825474407169583853015678934349056040995023594753348193518378962725604304810979666663928025750274281734978019486530865289178570343655369451477639679097544915054719855066784587479636130437137635350693126376344279658143201329227517897223167 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((429765718099579637899217286709102498747592068488499110682310790536150573692764711024081367929231192200103181822685823080647703024248360135036054056076365815616292132796213255843280554703743699809930499509164472936962587549643044110372864138290923451628087923356177239564170577577938906083835738987747614145583462231655574379884292433937107372152093600979930370054944705477931897317378361230219443618980074898295273748343852386667307312843006677098564544816642294434323686239 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((996166302103980703973561514156641370050517833456572602374434461832645231268512491206264087610620388463208062986253578314889570489156512194355068549917807949885076152454250786105105561761618192262007187265540798559077229893054297513433473504225696716399442126306141150334878363992638684620688214326898092311505728891115484191031757134302167388466157414353912001334456381137532928375799132665213992201015102255145562208226801634712135933099474635138685040300680175281507892989035519 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((224066776355634757080650860869010512681775310467008390223872868152339583624273476100606996982151332801684727888095905932570790937841662574150737997147935436042123903460796099800425268157556012045609714550960757154873577694587831537256142219556076900265507142134152564853880380660894799003078101183146763020067442819599283107322270964981733651700991540088490977646232927204323772670860307730625031049380905590565837478072663009936322673093643083959501278719453406431947256310152031 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((43365536760218647853968951656896858418194511134811340328904696562565110728654433076991950061736519741834148630695107673602319560852192074739699054722351879237417302649348350016436458623421034206424652284570072761239768955793225916057675147797231555178653918836564172577252172282120752829046301774532736422207978241439712023359655098861380449470693571978090831753145848126720686715234051522058340583042666108593422008008950794553092085215708710384221702254362842801116284699905727 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((99638217763250555053281026529448089450297317425463299913473005728684897829578255282643935683726635438884481695949763931997813877491210899269093463987193618422704751430955192433952706757882147185573356255061819619221559107777641002045203461120274773429898954017384234215952136331621320028969726097815046073344484129725677127623475889006961234282162809035164321653931314231567844917895788350483579230017594184715831560028155043466149555870664321843402568568134887461140618353482292892511 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((4496460265490265411306572269281252990581071481306672615357369331615197308656662296054240725134883735702323987289006029775525228736934636574334430390343475144387968362761637446985680802805613314325840936039156185466324407845722660609694352551498148317372227255329358273962798238998143586636870121235513951892357980374551220603173260033375083277163486557625411693864136579475759462043829140936347500603346721867099116503057993247404433831318611887304148515098090124241378162780152527603 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((4374861380413138230805129881750443112629262043788450645774017996256384982382652705750222878102202351336016400027054582115520221194904908440290205398376893558494718467432430845342798193625654430183937935254406388969182173495983692005647774092397088582285416724014854434755685098702111006183608098275630615940543120243328411641475433367276957320409747657706411806844257510438031528061517697149124551523194763414579657931544982347924241951069592877936089379000699820778832432946043246111 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((9965858972100191629823077192557486753335107548123546149534534077610265123279470372767825566537598859732089653165083272498701697804968081353125081103007474576932224687787810554799682984034580347755372056433928855646319311441868203722003805422459210093806134391666532798725187153478772349813844082124708082895445622838082424856699796169697924717973422125839421870159844192718825957056907650846784888357530345617448308488296963296857067437958721388040056993206321194820379013399770497973370559 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((2255579855172390757501438367566500528727013387717429002316673159463559034732260020113820617301480791119864361120781434893483507510650974540178495671300242927653937837201840613217979393064046457003506266933027065536952772632664763461764622798187440196647531615210152518015078121363677238678682929638297284592050464850607242407265558107760512532117085338769876505378991266797913591369418109055713518619662010362311562118614011973840389001247235051313745193436538087447758064099170850253221407 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((441258159886303495099430430932333512087234154466999391871125716053137686324876064972575914079962301353389478635312424759606589880481616380705677616918854175575858299476910481671422628270886207798520137400398502513109571611948590851579369073695350965382635310722590085314077486725949081967057397914860872396898922411953719103680166513717905795478837846483718348994577096255512542903017387426388981300090909940105588744901854532684335372530661506552664661390102134140818555033766582978853247 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((996778145338122983914773971584457467425480764208870926585424446370003109418760339607726930888586666794057568479535743342429980520157032869213060778609712368350517111561847894245891283520359312837326705593613432178487507101457660517041777113912053197342391096407179033682897186486638267879582652186026577074760307981607000351301903064738223457710433872593340402465114336622682886741503318102760243129411781185572979423732096129361104597052726578667952138391887324834004347115522942123249006282271 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((226272244957656921600205550814424706743990618647664049647850071916251217414379277742662656854828157613292678694050385341772399875561207140694504768632303815435195354037792260534957257723120890351794826363749984742973647986496261672631795882690634072790315679524650475305593122260061939857958321023053368300212170013981513906333877446526213750275963880020452906835322543177815428031767291963041667488072514940486485171291878770342971002279481629486742822041785156560463021904968421957721227792767 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((44497160230860122330210556592618086234369619561475958783280524518818781907588202607746793747459325245718621843591948000002937249075626091396706091091029411010176161959636756572847205509233860510589749008059745074312734627236805977999910397272613466043947092784105091209214136180661038046189252968336079562508264506023885731424373134655827468785986497250667932253274026567055582899058051602066967428227499860556189004294413444807662544218987464547269502655752443484101409773257485418267045673183 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((99695956797413327869053304924453666743475194237626940470939919579490823432738994488441582741025035158688418679845308563481774831706699034834767332616619946488869949300980023932090514534532787993145683880163705981251687557657457965332715464462766548180004105376849078229621324591557566701528335304143142051968055503916271016152009290316281409480675934122760940440230374832745961338908926626039381383879460378701336495238174179631678079719268754502315975347904014957260156232944784525228885473851631999 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((22696633194054866100238616570065826965219347210007393513876483479764805408937188898344532447209056206839319217658462525072572655986680252729421803433219317853223105325205109944540014897551390979012104218279928888654755635422318935929851135611507591577010682134844640419831929421973111600690778373952353349653768103737891865790944304364546834949247567814896517966300989209862488632359855848043866083702332637166334185454281264887624940213014806594640064707798648906880561450935048681271442399275880671 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((897253342267982814451306739173176112264898329286345672143140305615899418145065659305923542903546120608217751037638904632001307524632289428085424635026791606552649132111300859921420371347565687085843564873385667559337110759637043876957916105503336604463181290172079862909249441452385813977507737571987541427762407675746450634955811368173049022414717453713450715387765613889224052781501043994332101547709602057560605879821162559807656257345844001119856505563851462611310483222877194280437384491805299 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__bigcodebench__acausal__none_base
