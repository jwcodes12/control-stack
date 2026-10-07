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

namespace LasrTest_closed_source_model__bigcodebench__causal__minified_base
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((1043 : ℚ) / 20000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((1043 : ℚ) / 20000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((1043 : ℚ) / 20000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((0 : ℚ) / 1)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((1043 : ℚ) / 20000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((1043 : ℚ) / 20000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((1043 : ℚ) / 20000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((0 : ℚ) / 1)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((1043 : ℚ) / 20000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((1043 : ℚ) / 20000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((1043 : ℚ) / 20000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((0 : ℚ) / 1)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((1043 : ℚ) / 20000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((1043 : ℚ) / 20000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((1043 : ℚ) / 20000)
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
  | 0, 0, 1, 0 => ((18957 : ℚ) / 20000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((0 : ℚ) / 1)
  | 0, 1, 0, 1 => ((1 : ℚ) / 1)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((24407 : ℚ) / 50000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((0 : ℚ) / 1)
  | 0, 2, 0, 2 => ((1 : ℚ) / 1)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((24407 : ℚ) / 50000)
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
  | 1, 1, 1, 1 => ((54029 : ℚ) / 100000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0, 2 => ((1 : ℚ) / 1)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((54029 : ℚ) / 100000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((18957 : ℚ) / 20000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((0 : ℚ) / 1)
  | 2, 1, 0, 1 => ((1 : ℚ) / 1)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((20753 : ℚ) / 100000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((0 : ℚ) / 1)
  | 2, 2, 0, 2 => ((1 : ℚ) / 1)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((20753 : ℚ) / 100000)
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
  | 3, 1, 1, 1 => ((1623 : ℚ) / 6250)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0, 2 => ((1 : ℚ) / 1)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((1623 : ℚ) / 6250)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((18957 : ℚ) / 20000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((757 : ℚ) / 25000)
  | 4, 1, 0, 1 => ((24243 : ℚ) / 25000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((24407 : ℚ) / 50000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 4, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((24407 : ℚ) / 50000)
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
  | 5, 1, 1, 1 => ((54029 : ℚ) / 100000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 5, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((54029 : ℚ) / 100000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((18957 : ℚ) / 20000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((757 : ℚ) / 25000)
  | 6, 1, 0, 1 => ((24243 : ℚ) / 25000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((20753 : ℚ) / 100000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 6, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((20753 : ℚ) / 100000)
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
  | 7, 1, 1, 1 => ((1623 : ℚ) / 6250)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 7, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((1623 : ℚ) / 6250)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((1043 : ℚ) / 20000)
  | 1, 1 => ((1043 : ℚ) / 20000)
  | 1, 2 => ((1043 : ℚ) / 20000)
  | 2, 0 => ((40632151 : ℚ) / 400000000)
  | 2, 1 => ((77606501 : ℚ) / 1000000000)
  | 2, 2 => ((77606501 : ℚ) / 1000000000)
  | 3, 0 => ((1187463686507 : ℚ) / 8000000000000)
  | 3, 1 => ((4501641869907 : ℚ) / 50000000000000)
  | 3, 2 => ((4501641869907 : ℚ) / 50000000000000)
  | 4, 0 => ((30854749105113199 : ℚ) / 160000000000000000)
  | 4, 1 => ((240246573118820149 : ℚ) / 2500000000000000000)
  | 4, 2 => ((240246573118820149 : ℚ) / 2500000000000000000)
  | 5, 0 => ((751793478785630913443 : ℚ) / 3200000000000000000000)
  | 5, 1 => ((12382448110111043376643 : ℚ) / 125000000000000000000000)
  | 5, 2 => ((12382448110111043376643 : ℚ) / 125000000000000000000000)
  | 6, 0 => ((17589348977339205226138951 : ℚ) / 64000000000000000000000000)
  | 6, 1 => ((5158695322185204019202019359 : ℚ) / 50000000000000000000000000000)
  | 6, 2 => ((628155911023480235693725701 : ℚ) / 6250000000000000000000000000)
  | 7, 0 => ((400193288563419313471916094107 : ℚ) / 1280000000000000000000000000000)
  | 7, 1 => ((541858806457461661513143177240323 : ℚ) / 5000000000000000000000000000000000)
  | 7, 2 => ((31628276320350082112576763184307 : ℚ) / 312500000000000000000000000000000)
  | 8, 0 => ((8921504171296739925487113395986399 : ℚ) / 25600000000000000000000000000000000)
  | 8, 1 => ((57278668421082166307412527733957961331 : ℚ) / 500000000000000000000000000000000000000)
  | 8, 2 => ((1586795090150784454121661059039380949 : ℚ) / 15625000000000000000000000000000000000)
  | 9, 0 => ((195825754575272298767459208647714165843 : ℚ) / 512000000000000000000000000000000000000)
  | 9, 1 => ((6082050366759776090818168955101879554549107 : ℚ) / 50000000000000000000000000000000000000000000)
  | 9, 2 => ((1274357499851574160575397013231940971818991 : ℚ) / 12500000000000000000000000000000000000000000)
  | 10, 0 => ((4246284829483436967734724218334717441885751 : ℚ) / 10240000000000000000000000000000000000000000)
  | 10, 1 => ((647694875748820073550290816221295567110279363379 : ℚ) / 5000000000000000000000000000000000000000000000000)
  | 10, 2 => ((128181107603244000000066753066139902742024869251 : ℚ) / 1250000000000000000000000000000000000000000000000)
  | 11, 0 => ((91177141512517514597347167006971238545828181707 : ℚ) / 204800000000000000000000000000000000000000000000)
  | 11, 1 => ((69086465959706302407817211642485264951606122743947763 : ℚ) / 500000000000000000000000000000000000000000000000000000)
  | 11, 2 => ((103362267099549071709472346609673915144016936792687 : ℚ) / 1000000000000000000000000000000000000000000000000000)
  | 12, 0 => ((1942051471652794524221910244951153769113264840619599 : ℚ) / 4096000000000000000000000000000000000000000000000000)
  | 12, 1 => ((7373486918890105949182567497241538413465195160821795833011 : ℚ) / 50000000000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((1305204175378681743649086678642523707986567134249723927091 : ℚ) / 12500000000000000000000000000000000000000000000000000000000)
  | 13, 0 => ((41087597748122025795674752513539022001080161583625738243 : ℚ) / 81920000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((786805609633433886078545316955202918265837016675691480587102067 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((132149988892421336248670436996734653589866540879206328103457779 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((864340150511149243008606283399159240074476623140793119872551 : ℚ) / 1638400000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((83891695485412504494003468851939370899551720403439579023546905000499 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((13410460569368391270467528421382441437043776823761894499652944009907 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((18094147433239856199714149314397861714091853344880015173423949307 : ℚ) / 32768000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((8933858255764912568601970881184536580067104337844154858711430885526748403 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((1363945195815248904181737791999216214803969778499242194741170293614079347 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((377187776891927953977981128553040264514039263858890447642597807012799 : ℚ) / 655360000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((949935601843968763365065602461852743776248766398215935534416106455073039495091 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((27805484845642071110148633824560937794616271068875307867297063778537650195671 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((7833889166540278223560588253979984294392642324972986215960726627541630643 : ℚ) / 13107200000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((100830874270977861051204735422568341649753834179525097606937543569835684918486323827 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((14200868632853898952334021257240238826136265506618331235737207336248255364770824947 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((162177846530104054284038071530698562268801320554512899695967494678306692099351 : ℚ) / 262144000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((10682656503652767371965360983686428102750094555127914626328037998895813556950947737511219 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((1453415604888238530021496694071984674076949591181693315480360190293031432715850583897523 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((3347821628671182557062509722007452644929666633751901039536455796616659962127396907 : ℚ) / 5242880000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((1129583597770501656475005640330745576089045529535989522481995661131261079436426407853256288243 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((149027389010487411633822355682199123888371777334302995560891813138259974955933330259006593139 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((68932978454719607734233996800095279789931690376034788006492592536462022902049063165999 : ℚ) / 104857600000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((119205571634609077643109041340290609031803972199623620623359225150477590585181923980893179476859571 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((15306578750637255034906600744944587842802595457520774154049671619119710928560141692621302360075059 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((1416128949366119603817873877339406218977735054458491476239080076713710568154144090437843043 : ℚ) / 2097152000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((12554900404690874905224521242740708523584445591982034157166143706213182084927310208130070765800094678387 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((314909634466838993404159286346673312665865778732363918415677537937637628847463355334081813865036263319 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((29032886029133529329575435092723123693160923427369622915064241014261811240498109522430190566151 : ℚ) / 41943040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((1319708605688832040834019001584140147250825428508528767536215098467548234484470024243695669096725710595903539 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((162191144973942546645195634158802738731525106789304369340000181830046359561271056294837371840312154304389299 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((594123011174284315500761523052752255851251625412645941600872816907361155686122662216709122562524507 : ℚ) / 838860800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((138454659774362823086894443600319499633412641824128499919516120113153665460804269308116473983164738735194776343283 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((16727019124919602488189263419846613271742327504953379580663412461963189592880320679375447243604971590126338081651 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((12137721737230907768947936192511024514172177062947529114927745990112845428341827307642154836417777079199 : ℚ) / 16777216000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((14498515496146871249059458857896476353326868344545614598845864042185122069086583712421379667474274925299378499754198451 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((1726862676030896349561468346154807643409890352671204399135166136187151745954619288786640040912117012260273702145726003 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((247593427260686318575946026401431491715161960582296309431685280734569210785076020270972329233971800090375443 : ℚ) / 335544320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((1515482584001424475480855694173421466073494703864079892294583210371999152638769429619572317165542209585443978267171700549747 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((178432703650651262345212718818751639396212326616053063244261649638274616515009885542521042455607837031354890968789270190323 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((5043601326340830541244208822491936788444325286758591137896457866885228528852686116276822445288403414313247272951 : ℚ) / 6710886400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((158130969874196341457956245809197861578608866415251085341059730963417990836939355720360955153112493426575572648506256512653425459 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((3690039290900006508015795105956252805069427445487401225477908035794873894248217415810273354619903725052145515714736417242432087 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((102611004858643124570366466647979645698539074461082612201103151782543277221460370706259723095332263525136228553332107 : ℚ) / 134217728000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((16472130928350779115362820532723484614639539166605052741157362057575142597992121518670434707827719329164285835403830383695754291969523 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((1908857594780543785960211293151511516280969503095366429788400706574809975428753788510082381771912677652700983244366335444244264775283 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((2085185909409297712480437108245750143507205234558743079496312448341672906287224247478565570718213719646007484685516752399 : ℚ) / 2684354560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((1713082530845194148596969835985302461146447692222525156528508121640564207879004873667403197820463767022377553589429429736476279286561943731 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((197575141793820431802463264662760052610080305803283898354496916395556855883957148369033227799011499709515084124573391881156940842809671987 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((42328651090752056735491646261014685470466089631530092558011595083213093284486910059451167524105177483329363887183341075227843 : ℚ) / 53687091200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((177881674359081444703648235870634119063491885330726130283462854122339024645590282590232172047963864651816095182820714112634801900388929875841907 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((20456060125880166883236373866718041784792568317368497734724355624791846534143499281008114386875834221467036545795329035810063410828866903327731 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((858419874848986739534715138170055392463625661144915964622225807992470609394018353997015782754461849551474751209334596763094219751 : ℚ) / 1073741824000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((18443228631291905565051880919175406345646540587400986746810109743881050764511169275804979655915330507216743541105342305749969020507433913724584764979 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((2118321490016676196641859361157451976085968292067217642956271594217925583765675256198724622564432041665526251972259927843838014113491301265509054131 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((17392978289944241621359594874289740074932951658324171941343534642113265342282405936721428193676333281947306858675355950837977123819707 : ℚ) / 21474836480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((1909515890156580580995444208174543007544447209558012059028267335988349525024866521793154134785401160840698025647375272487426759258540221532874597647902963 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((43875879120757019330699731965195243125732589688600955248018164422123727027532003217177418739769201827670497313374146769665077290627521187801690932856087 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((352116943891112988416113840031910602600503964586851327492049386210541171093647569342428114267522250025875096119908722760035532336250185599 : ℚ) / 429496729600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((197431819204428981470081005724215750266839369660054023580639322191020761820024782531228483645415720161914987852350985449044558457867622599236458600635639487411 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((22719162279338779892496623306232694638653849974050474290238485575054090877012991036878060930197043876920725732777651884012791431892374870817913936124064885811 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((7123045994316628921404270065484929293497753656672940615266780214393228980422276972024409762169419293740514197145109657361993586498294768400243 : ℚ) / 8589934592000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((20386590298262171395632315314311116977469738230386453390142625360487330740435166312080369811038097854123480772333688413114201275572747402233558092815275114941578867 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((2352578491689792902708033876585228187451538542516283488723550390082748017223462527204279286642647438995326261563144154481415141486073166280576749374503999198834419 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((143990884693716334463060747631397804616836916069548935243612352524252441781865104558666735861445681551438927635279843774611312419248173924563406551 : ℚ) / 171798691840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((2102474112544086672902269924939659193128447923831368132277264835473315023891309541692355996860177074178081745612097920390496167354648022140469431119634463575356729250099 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((243566890351927061107897123773156263345495187385291587684838095824993150096703029086298210931266647529826253180957817077099239465796056864050892016605565072320146481587 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((2908821236727900552416242592848408182121377417930439165413159366802253538858816787118645311725425785170627751181999998435306649531687633087948497987307 : ℚ) / 3435973836800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((216570517744220558147065280563355118712149147263783881475946975535712905711846061736607872253481201909109177803291299427703142304525787677231919550447818094004690350158959603 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((25210741394402944581142018219709831178337594389466841517108009308794535224263207459617623600049943389415119304892199563336073048164643778981078459991838145119574288654779507 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((58726244896433210772154710832627273908474951711707335258737262116470320336146589833408159174378896609479590279157173970338108155172202460448239676345378799 : ℚ) / 68719476736000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((22282995945847059560523905652288335983385009233427741578042512302386947168858408151921110011927329061567336362406207265728151043304287016858075242514593536616648937276575323981491 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((104347195857216692177593288327526462955634004304562518154971589566918333575644768900346094201597135208142343873243915588903878174045914312280708140880701076227876340580064430891 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((1184947838737332376607736853254115231482959659598835954499882277941927862612330903471918473468700743025904592921982546955699516297599442042717279544479345892643 : ℚ) / 1374389534720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((2290209994545040683039244210513995328452206363598676323973787059936148966110241987913539429477969207772583854867391781520368487893069282697950087273567355811361123073977521637201504627 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((269837134847656650933456005471204674482765968625255713137675806399987035094261428216113316451960922984705957878246723462335882197120855339023683704520630926318043857986617720063039987 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((23896544463656569863352867527138262443222466267015133189454268342945126491541956937117158501546159985542073368022023142639195730453592622803791468324694960086833351 : ℚ) / 27487790694400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((235139391789023712013595726777196719555983554092923205322783104246546967826625190696458901955344803412866162957430326173802246057176301199357227679260246737557204987826522269855383750048819 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((27900335606317556551379803629912754157581101726772494991634855102591207534506172401823489871094377313956752125503956846200554113754257030938152872260865110536113719163679277429314652622003 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((481676559091796794899580309711960041136168293023805879872484564977210762900160877656929973713810554845921084837593492715011233462208755350491474865031242358366099834907 : ℚ) / 549755813888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((24118134852512829520901196311088533706106333091992586767389245244209791914145593130446623459788376206962758106017352205443528393625830956929094308508696499348486380139071245090465494048552435443 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((2883551864000117043894694282770237512872834147096925250758161978923110631680887819506846848559959973072553852473144460203328433784260272812047981682080618279238823750524984249156025992847830899 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((9704537844588375840911343931209626499818342330852288064742689898272984432298349757742421511692706688214126005266259841398467952743091375179266889016397261387546154570331999 : ℚ) / 10995116277760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((2471435086836229466899419460442426769309550890008434573480282396204076747294162144722763631657027454745532916850491921557060370286142087777145149330686116494326356414421195983606615305040624963137971 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((297881219439171561927878499596289492113826967062921423599434142069998696654367267632966046557616239297462500068280900214357915874902041209525241271215804965781151406501185705142640531573194051568179 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((195436830197565520816156346903940889557056315565966824843327172401560965883079816357523084597158640688475186681832487813390756980150783199273362415083842884123712452189783705043 : ℚ) / 219902325555200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((253022909030434156908077729275431046017847870235168693327829434942173135455948820154529157595690422632959302930609078641505839077832897845230245286813584174935490713319585577839221054881541966682983683187 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((6151402794438074081942618878881260338725871734752400252281780279747679941933796684091823107189906348079180394935431568041082103705522060123476114919133685865586973199389965111736469082726305333152979607 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((3934254115609323178111875868258007443333116574184033098554953207216391230245544078689565114708336351531424113927498471478448580072718397108625131302744409554333216956161729696500151 : ℚ) / 4398046511104000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((25881695659780839270556859918799020214128105446939709020063043164432440425481277254728825363118652802641354861719101913484970372965053161860134744153952010436830306781551950268735240032044377821358410669369139 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((3174107501047283256150113030675869189670137007080071487170510868689685160186173917105739924052035641862821598606864422612018988984578929740307924761809042149214666295439144766500834737996003672611572340422579 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((79168817780687411487466830834567047103265890896806715449306247949201128551764779099718085879525932215981206927723588523816949732438522653988206614106125771921494793837957909856553362507 : ℚ) / 87960930222080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((2645234028425081936082304373352028153098307657196139449652350800719412884840416096505085600786590195145248095306516796160262744647193537553802708748584992307401597166739692098851152093086113607370441043906382506483 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((327391996206011247243200303769231245362787501673902051982086503634051506755662983971407532715054820434321041690426216938040827972147133218305262081326688107194325162234959572650551522917206062151257709872170769011 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((1592546528890120699567908712130887511936611493730764904772498542373005793955804917393355754018173097018355739728856067645997916077837073951654432783609826258315776806786168097150682093045199 : ℚ) / 1759218604441600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((270140319349459877493947711377825739070715223075800690507663371413799296990847530352555448689780839620491493519567274281041581037237554269644511024621364968449336025856023285240833826401833476022030667387377560112028851 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((33750298815607109693281924267737377637215648508819107348193721986545838266934345866729681062239744824881932862951044323609014067812977310373726525073090438307551108687470446597899604414793494259711186511961275369942323 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((32024769552602606901708845455865234563782344086654110299772254867765070836020193819025845028922507400176969758039924474365182495087557410901513082278891476378892180926245388617685480437857837443 : ℚ) / 35184372088832000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((27566607499426812370342216662105836178992859023030758879530680605493618722390971193725027490445055748008991859149708534923464956692329225456412136234024687754688468418328134503771255269081164552711320017696418265378730098547 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((3477330198494593768439853177604043068712607291065587600483342780639569096243228967865395106625676630751162854180401096779761789029148864323681903435026099264675993483214393774418831645897542666701390393650153608178852786163 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((643790856497339395035694583306837251625621896850701968952782635528222447838434814227272944213283972785154815703162848260540764559374825838459983500760945717714659073818833832025463652660471024406951 : ℚ) / 703687441776640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((2810993144827094553863791946996591720381791549800790404351177601334778902975837365770439255801081201931152481263479863691248221350079709609645040332729597042131141231875222248837641943948505564742384391177724372195005769559659059 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((71614317177096768775499700070366676489339309701929289053175088268507792754749672933098588017994404287688914226591636903572824635590143378973317105406101517304891922129388118182459556520934189808353939701287776863842282212879703 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((12938289268393098431691662215747713779066914298598757225437900421708512943673208773306413203451224272088179841284858114475071273752068573419685907223925247970716792062383632953706714463484549209682570107 : ℚ) / 14073748835532800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((286438938189762969316033753603585270996447225860836972142177250699270438943777161091839849846969062327487974797013457387476300644705001896950536447469174804052418228836080341065594057305846373940916989104064022866605146753653076628723 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((36850839637121249885763675079994406694950073905276633426416314742079116024620635304230403903046185332790729380221675325880594656374247258903503827259078686641343171276184666224317435526309169982988476187687928839954188321293514704243 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((259950069696388677369578840623929410109771494358536640722626278294328279873213018715569675097824858525975625251237055276103926136517963946316985743243950925780878227126606529903418186084276599367952481518399 : ℚ) / 281474976710656000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((29168408322494578662604734505795212041970142687890667476571465213246241260154016655028486285954125710891116893366916127181360903596467121592283923951524649599712616011787414901019728281019150887038764334729784041766069906284457420033886131 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((3790333897500572411694512651335131656167009116719139284538071051948243761419951557668353493620350264273291006380195486943612584605965191626382129227701543727652010604223092271291165059237778536663632673624250300778057645984990086907795507 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((5221451871943654364895106081707829827450938218554779098178826357625581201556499195791054330829465843076919927887700856869102127769971042530331098734675577700028108551639079987379098553599631494218275192144289843 : ℚ) / 5629499534213120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((2968341056547051532208236286363525817363957522998055924176102091845826525220167710661558069589140773342421882616624219403775144952321510350267767264076890295034030348941181812271895027291336977068391816619336886813460402747404295465158574254707 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((389636743808553903954432064846157362477598606081221609979990425215952498666352133058072139101819878990254150958979072268172289758432182173438886765899978258104853222633644776811718792433137357478834132228081246686666720965513792974588397705971 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((104854631150620139955316525990935330038987435809142947364176011261508142837906555254611016949534183987209171072967145143667569036135341053247486638713244926459432853813422039320745571280588214235895842817479302553751 : ℚ) / 112589990684262400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((301888563816390776885639738544709790717495973113672476999524125930284945405184571791703621208664368670215975821763703292129053813836302608395570458966790520200435452968861962564084753410477342885461772804909099258256589965328173543698580254570806579 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((40030888500409207184150821061038760797922207873817750297580940797568636380265166003878170931660656870863138891934903130077861067183592953057868427281758897598284587679378275928875819275485737921078276075602332677017234790347588583998911143054233011 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((2105160603005991676332935383210161051549084820633922853182684645484409863778194567961661048312319525845524256030238170488506106218017660346412604210086984070891468609741041599403373794766110777269877492290955138511457707 : ℚ) / 2251799813685248000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((30684720266190109837490374747969419332775899672060418667475304540209520545023002897622042036272730835401878756531746836824481973251346388740786167096882144045744460608249724219716751118001925091169423859452832392964831215003084664141576895737591573938163 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((822080992494137891432780540401879204733851358717380989389131750870210302147759679714878726567991229032938759665157309944410407428800291383696612793560916848338516534868419735807191621022826865249419429923325118498843106138667957508024447323393036824599 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((42256156756858297872243456059515023054216000944757275527784152824447957787643234424849208492856641251453603321565224997950610255574960787186943738010618957031889570434860925599889757027381162004705067621359636560761703751599 : ℚ) / 45035996273704960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((3117099390724764137552460566757524033109164599654807690856779424955393809419031713573320769908629955977898581489979978817403554933785302290696470562626295751136389466803215298672863858643378278662192437727494583429203031773210487461889282799316464818624901811 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((421822523262213611187078186503468001642166525839459083446493226263868774151945171500055985185214684551309909229942705655122962999679378496575914807578285926128041683776747034337800509965455291178848758654229211076823445672151880968095907239293704656246260531 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((848022507753237026044119196520226292038772729909763672180204185093059935780352794991866445399083348203805958166911970286149718614934531642702892441467303568453530586733658566597110123968064688123193966898114630282359618019062243 : ℚ) / 900719925474099200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((316476848089310192540540742067326854985090002627842675296083824438070413704680827472752292144905834723980431608983773402503222110146237676336717943066318897355853956090313077944609330097188633763229594578576727781132328475218981481472483155936978115944764046775667 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((43264617964562024756160558550649744748307809945642715661951923161951115880792634177878432818201471266984893744033918896753358459089784165404016838936389648712098704985568747394900548993363167853142601499577628456197629868772232540246846503887871691793211426883059 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((17015413561747599768318367608433929818179014640899389933520130736809137202588147934660812205430423031899549548970150220714540215783313916350718732012895673747173579332709965446981416620062602292751388030487559046262691278787362940551 : ℚ) / 18014398509481984000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((32114815000767713729064984998348503063618834536478167896414121732172802220929860021288171316636049688292465493808012241063855367285347797488377983886494167787832208478665823362546205237043440013749017962719961918438431439122327359866941017448849364060683405573373339699 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((4435029507263116480407591025518573476956618078038142328369937347960342912366666707894100872400326788588112302874457899721661615632235252008545216388240780420208017064620939572382365299867984908813709155713024369584713736290321702874291868924058986130341484871113177267 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((341350212535438958120011294753082007563219580547529734969741118377690813949463520397365016978344529415719760799827137734085538870604281912260575002768463287225169543410182814978426714866526751663688062893952656840001838571972039264025307 : ℚ) / 360287970189639680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((3257241982851415688813463111672342878970059861165851689355952427506479281784588410420183879229860461466827989906444498754858502118061843114144287586155520722988707419407935325615335962643213872235676812710063059812735974860114566725504383378043013465541650250575948315650803 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((454384596333900090630987110570336924026596626007628710964275054657665184179264308034021895485097978957003822613154596718294308704124125140471348857402561043923800812608771780498510205223240116667891010845582410339626753034960677982545105463512626971625411808940630644087667 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((6846756331942110515321054114634175617375953588439521185821382381085884760039979956172848626858477244133799505482323050025059560370045372210723720327481758535927539034426835623546035233724747631288534608280660515715914853808873948328127744799 : ℚ) / 7205759403792793600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((330205468217121184393171723296198472702966762452675279749886679538906790935254455381415964640398525191280539140493867629946899935671108791847761361400008344773912559124982677216270328417213012262013903436684337412441997335672440361865247286672631894015387969709013118213483027891 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((9305663051341896253019974732352535151217492666422864217694027317577102611308510381072650089111585116949792694960401207704772717951939495671838973420552175747736252783357924827998468188925790698960226890187867046346505325655062718466914157044985004777174892635255365538683380439 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((137309566842782472763741222851120067178595952176048003119615945798245117396077900029168691419356153117044437225428398059325054085934950120998689566248071696565578357475629522915562189925720040846336750569176481396426597883654823438456317658154643 : ℚ) / 144115188075855872000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((33459254633564725657665369498071533775688545404869281085631953687369144199032494651800986578858873047678976846853947324682044587375668397810045121045535455120036538793233891972826212891381359821733349333661512011295154488538851350241529879160564250658443593193341649737974383749005427 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((4761909326513992553824895943263672437255459333418465131361790301611386412857031966090617007439424843374075854207853987363605903277480413226876600003268734250041251331796535318756053924694389128580200134878059259512785164180217747029799990380842611760030667136199639465573630491767027 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((2753289599801745010678242361588683113504643465401341995138559484497332690477448750852950883236734594639811396482446142010625050307068849443772158107364695151793668922665508865910312434421874814324005780539878557832059016080444487922816413845637567351 : ℚ) / 2882303761517117440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((3388861204895906321335336214846770040237674276759280724340455282229365474675465348892126269525380345486878705411564474453329210105836470825149074515917590938538365351911654087744328783873351199702671187621499332848814284477047357120695074152661457279903137834579188639683326210775497626419 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((487100526968323383252360494120204994653732631351741446500238918069197805386239702267152659285612072808763869207312454987407899405267211608578881812148446037220867884013451679153841504344239991961731312924976927106024234888707985837106602785735616885342135653578911067107252704545629250483 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((55200353766704033657347440448636665782707526173613240201841672147615935813380995969919389893518777710586904643117731514095419078671104178905588801241312525992552581766970051571061792819335480855140177581694477820822342767836986157552830757271751364272907 : ℚ) / 57646075230342348800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((343086970566920741989105228643865672588987746882811132484910730211947058996850941627280662098656505444466052382959396841379012162161822691049293686063957338773872456396632098075707034797462201804534237689863076197648529697547624952533228618925891615562272627732268578621178682980659782147462643 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((49800480233278456205998751350463523662021680154947847058346893011653879248243763677361667262275086845945017104768057692200089033177690252521749176496208725461855543019949558375328775248661767358687930965990337570291934518976915651936267656471918963766284253939630609799764787206755811381036659 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((1106557962820655435840735428584805273242786573673186194506312578902355295214263540601761874211435469059595951319582836312706859474368121919513246905131561555240819292556451267632618406476142710570892346416182216049329151849885746588729012665600590612521497999 : ℚ) / 1152921504606846976000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((34719595982173917734289874101616872277796901598489290852474636743929553851281568844959312367003442406887333658179524789023520391388175462589689700784198883239652703563673872849855063798757531062058742925659327625616621595794133738933312490046950304837031394399699767970126052202248764175989440776371 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((5088969005900637456893863574040555130703430092375890652233092331896543902121310414132967058966022696246441000337468353936950945932063478944663376463540768230938877167222799073015692218754907791072718459565241363547969411155273016688631401247921825707324757052227186807519023208029883996327516117299 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((22179516430496106493200821519682153564863505077122590689256167558251949331376793939187599849426182186962760449165331827979983935055596487228212621580579012402700211328992646680511547131568237364292406211011566269647132731618284098082535893101790396241570037567043 : ℚ) / 23058430092136939520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((3512140267708867633929625741188608469685559433458119429406891655860945368375234158757168468860023481760103611118710237876631644986441185128199310660476062228382936983664425348363036978366646537191394126186733677605104301513483392603098106051468714774700707987310278802022733545714455050811647996034607987 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((20790809463948090847790766927871387377954611097117250460146829184953053101677114443797451244154990352096943530558675259330592482608196340216091681836644557260120875730305215738232719565310414773195284914227387860742618891462611768588099271871160666530093164257165899338084805601847049014923835983777259 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((444507035559013518710967973548614585129117465747012951696229168401782203474909882705179330345572135718253049834827195463016555456848942608385226667303036338117987906163713603122457398973139075714891144542146261773700695193287811647350632925530640541551443202158434151 : ℚ) / 461168601842738790400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((355142177626869685946499119371161945299636653855290644988088554843336767266868821050843062196504437599880074686389667438332172101433702238050636384976457271536730514452308811017986254652846106117926165141503252366428886184841184885307717390991103233756447036439738424245976079440546017448784540264772449074739 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((53061849566104969441183882949318381031927332173869146698594974976568422278255880804277337582131980886281018634750260081267765510841786364727917942446557779272596922329612904502908401034805589963311214571084813784745394934818516638788674331078216620953353294055041170818450203514663643400344273108469407239859 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((8907518724814195832591019874561086690292679798166124525305416345392585231273866646442084565361010976810923065718819144392404841795485405027158741932063659861702696737145518774392424912333797458327191427085466684444044078779157045398825948369284352746190708783317436200507 : ℚ) / 9223372036854775808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((35898147923569197536410029321159962269411664077022375929499928430134918758661407757632744735461045971253077345770826153547138692913920265197874368567974522120925878853253928391436764146880844856746372516913129723190412634622036078021441297793198633132832133713570219455647321843993609584197670820598875595493949683 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((5414356304587871448911983330725271638019882202532893911912134949444198977988048970887870178097256309767552155586599198851515211398135019954599990458354779126175573751587620345396649059919372172253485206399354524375717104461145972454793269298297087315042206037690334403760957027360456163026914748854928102813184371 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((178479809500742241566171963762054520387878330933835222626214777659607238229258690016602597105548685087404668556831654520246818585917016823099848270806130799998298022046067599406157199063111798417508567883259191937005743601416480109625543503236523475009537266405348638053011199 : ℚ) / 184467440737095516160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((3627330524899240982901911136399727817708230955243827398215093817170074213235380855173571262629331778720128293036096366245522110689672205047152468655692720515598823627515036891818041864388361965370228746804546842902999098740647961213691904604937836020687147661971616074550724089526097249759726351787094199551262482019251 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((552215857546636952678955239743209132720008646650325727004574996139114996793763770477466534675191150671017647182292212909264317070235786795792261171733536354669038628130867943926121483097690157844321971430261446138217181418215128551948443972823916516395826729108079763929432547493101317496283613837153436811789034734643 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((3575841289394361296724801917037267542993009519512714315325153540093174415112056986644735433329886423201930301831857674740318939933228887915503823669671821575567735603927303481942522022639410362600709921362944501549817881452052213438171428190854775515755797959246194131570933299443 : ℚ) / 3689348814741910323200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((366398066188985827653802866239224117957441112237482853704468999842854117748711050020678794914070294287455802516704747333832916936906637272664535150228960928246402052776109548674738191235605878882701484394217658983750634695987445393203821495205733568302204350020971259341611552219138726891637020787187226365271648788939167347 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((56295365345361203999240394238633069976129809316094963739536472545200005648504043658107278246333040419361060400389565419485039592726986576382261569117703876815274323333135409185510110150291199994264853374866354914992766834233827952578309280718618774295596280355181224236199831131272276578317727449319273383573111975176374003 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((71635214136824719569109669941275480812518481461402525275618935659546307387279264295824249609634656924638992731826525940052226144314220028214205985305968721608037563843649892107184389983175302243821657979277338915879897578686553810147415764214033979452182661913430102152190182557540951 : ℚ) / 73786976294838206464000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((36997773132018095454251386470378805820255633554113338136683863153889918113453016542207502874549812788972976024506543948293451057454837964059832674582823748219248961139320152219107528066256389719700180041382149632034803510255705521787627756233183084414547347582545281133448775415508585925746418274980223679055878423677750879332659 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((1147287500875085789149653655970363743803808558192827068800922769706835102976501677295926566770671761664376958330344486318002955501431933340069544397841060753042661607242464365576812642451878379231611277030792587333475563182837052076015820088343328018439466238313701783990873993898324644121919178190257861782072490518006057900119 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((1434948570667302458213564013076759289762912853063807671649908163298019349140653013255940299849844191320381385217235452245570051017764669074856702863445249055523568097784071004675894480911054204636127170313160513828335218399161000578964560642205442148475026721892894446499069290743303808107 : ℚ) / 1475739525896764129280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((3734732957354965072233686401512339015701518798126475623847487000876493993224109860244244170957949669383183656052116262782613096218384100404127967874174688171370854225791437441899293273808012383470989097045195114515531531988634289377056841349140015572518087800963441332390223132801205231004641739490398029829616479185046243371964967923 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((584281131935231793985969371191867320826648132125837929548285098527550736041070536776154034840462118641842354866602281405005055454917599538059412631396414294122236370470046627523437776565373837972052080072476381165959307822093942149570264739502665617922371942428768224803835887671081686494743771371488456188700967719284474649106521203 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((28741516379650377687193572995896125856035538955530602031467309051640552801659359172292860264253496334860469919563132468219271457143764831652058516182331586345560280429692634035640931674630854557287062767626583860643750735192895087975431176094288566808641081566923600022282856544620810290284399 : ℚ) / 29514790517935282585600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((376886039200574438511060563729765302938672750255295154656569304069185798250336891731243815842334763959384884181658459570430939772143032738983331964517508951677593076318698521519322863670209459491001934339348222843010579187564750220800893858066990619727137059779562959293682176414916775212360495667815638382404298589641109909094647562788531 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((59486102774741006086088322469162598470087772398688497751408850234077155928245343256462101903964460468659806863755608443332588351411586226410622233372523325875349241966145479707720573077370097190113373055251392336113663367839489915186559741220351482089564444466531837384296972610770645662638806794230209882111729916417534081905735054815027 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((575636852519238709552909363283202857852865711979993622710525777691949959461056471829155752029453530019949928265158302200032729013074349913628073291268459882352786236105683263413645141755977109842490848885897150246223582687051712182750248805219428360991408983264170685622416111516376700672921351843 : ℚ) / 590295810358705651712000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((38021726879358348191715860618131826713594921537363939450636685422271834447286504719779695090431248148812265722408485950484777231861158111153906199873658827808384787829553622750871668498255608296893665207101577738489799906469478995216817652251166782409556458362022636030317042041856650738440421440930150501890089086180440848600111810278797787507 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((6053789089947019692133029653223067833165926736988879436024641988079303613949312453306194514423889076884133148517624315861663979020596615330901241511740086233204304650714314239007206820257081625554362476208724622309773172551117531972617347876176635820322686063061654495015363435557743050033167267670628350943618727487199435191747587940553716211 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((11528026343411338211730118799759676576316775302004739105723437167706295381503247536465305591222350568588190790122605934806020443900850451312647385382576193989761768677855437624532470952268058071284099022329952277217660456998439307848396466600544703439314140095738883687344142226015953114656570066887751 : ℚ) / 11805916207174113034240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((3834683146329670843782902942352829206450431174550048815760370944159009434778815033228355204710471132505287830452430260558460387204186564344608291487631553681938231063634221919206765678314586191756840508835428419485097952297367586362756869438331089854863102650853318497392999763568542442239349805314966526583501376402617869052735171000195758493488179 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((615830482878016663166653058020273126739957603143070118834313553732686008728488611294881523636169826412259044829914289022254255738104191672011662185180819374857235114976040572807416712827149214874006142604688338422660102617824364909827780421002733983052365751887265895165579823898590943656815695311340296377635392680127297351804431738152424893555891 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((230850365996131338374480182087044188857237109400103839227199198388208241547157063548772798092802099728726332808354240706117729555028422005533856484697496909463913848826105531048262051842145576857332665166308905319215189283319413958882051817346525943099078153794922018060982904178584423194544598757991095707 : ℚ) / 236118324143482260684800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((386640525914223811225088548253621135727111497509908466831410623797722697863720662827727025187628907668616914450695258088231693895760910353557761476732703589042934316029360078438227128002436795047180847806794655424043023836775260169549166609241972532259251825802144826995201915981925123706839498138457097452701226572209266556396230910311024501169354053363 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((12524233745483718537868067573940603471102029018224836503426330947458879556109312118928223200002497410831217396579787628461758840109801780805436676415498300511176608896925542483824067018951691082384410385170051373414482924188954315382485294630058750964937076079741582097704621500823109523412783881670944176191153968182817201134419975791853027191494482711 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((4622501800270313779459267211824096688166643882897768480230015203845263635009456453694085933445249404557465091047971341065873799174673795958905317380410448912707414832196482552081903716771553700484455333557717918136362343243886130418527056301438092303329224561490336696382052914513424910498981958655237201317599 : ℚ) / 4722366482869645213696000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((38973526723699299848902929523302020800940855212002691643567722982473454702388729077697022695437599333419390468203175328125696092356421174089056370867725175387922768622763001226002967128890544791313260272354451764598147269506871024639885313602680270680650041015685413284131283065243634934320569218344854535544784922444830279165120819982047392835746499456076211 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((6365186851952303195368103274928832198743953193391494936442668665399788423857997615744127658820245977720767071144852139908759783494729500578967252364705162602754591866997544108084675070706761592055621121143294663069746759666695261304700539077526459199779644340155727129928430631287410202167999892957786016039737741528283162925226816261543304311453215905651251 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((92554194869357378275094256534549400917575068088092997079720398219294662728874265992678787040321592962195865730996392712585769610954291149992968101580440880038194462973948719739816648758838343500083819758253658574111020940874349374344017406306361915794212110012172312753314577100430996028329200990227331625377724243 : ℚ) / 94447329657392904273920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((3927539152047741189980502466621830251208069072986924107592737253380795779501393865582447221985622815450000553017562593920835123459715031498043992843791792477852005182561459608783190695979875857754113611113732836709961180269463317465295645743177721127561836446265769321059310452907264447236705031881219143280693123591806464727963793103327254798506144215512190692467 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((646747859137359115446855228425538345722910856465046084550899232118880688248066012705756193511563155646936703007488405434623405666964719958929028069057056985682975818373917439177271357073146227511841829385679890053000280261415474244891813857823124766426283752002455029099507156457592173769915956518189480430812850457771411396513091287240787182066901352891062803699 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((1853058436971068619118660381125452993194470565745978945640259589043168921351269460423211765923376437784347026662498616652488434514860497330416696301660417762884052434597145880107704210521298477731088971157214605589422623976155041089439537971349702837710878969500750532864584438092870391709036663171739525622285518474551 : ℚ) / 1888946593147858085478400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((395697855280606571625612577926878898541204622996510669641978750941288880004466007615628265560446184978763442662625668758524691705121439433993003622642497192769449813542773916844383035430460429843091957926067369917665001508621552515916992546965610714365510931668280972352288797722873363997803045026741789531409709878110978300469851960034699225932966411587011772773269299 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((65689580534368128223927685578114029961606619861379550460517502437841360505874012540348502144246418800690396382676460535404373082795907102701285012495351316921383498982554546835747233394953901998598189882801246055608983790973965099796877777248409589743453898189005256457879305988856427461374475844615953187800268429150006799741736079685532346501860709163694870554496947 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((37098600086313763795786416044995212391987578514846522872502401029491353242056015161242825446609447131077866584440986275881223253098210447892709311790576539530992982002658094449201748718852255242348253626227317278158684682715971113932505321322876316694485132624825727851513927192926544015628208023746666187221666573722063307 : ℚ) / 37778931862957161709568000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((39856847888298046596222688708482114457622463856042858966176761062579682715275426429365878608569680415656944132601149879817156679118409817770907887878400810884011133371014581380104947315992221598160051951417253086002953161293369783093020650334965363746538385533354023167449694069655773600585280390267885873057947552227087599838171455106003424865506706214985371061345788822003 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((6669593280026165304851304247371521039632609040806056344176281160864908093138995511827705546961121485969473044116509362289436058205661633214681713974039578279426874172188159370807278674596328329999284281465035431532186782320353858912051995173385742047376903190457106425304154680227600620330742576689341747202644780489264469958011309053011710019009692262593186899400042803827 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((742681587769314339939802512964974241314908525905945534094028016316067583409655879411680241991375289263843116841247776831880349208982775460702090423613959459889033959824389496473517550463282202629195843992391253642054185530246664406818503376317766335577354659168821322881149517796308494904263939506165550911161133238049154110799 : ℚ) / 755578637259143234191360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((4013671807071413637902069306658447209481337409388297195428722866769418930646163076921613969786479831039565562097389973488624261061816712859275408315552522674969716010306562239139410974873301561630257341736252145499432288615351256968058916785440614126038582468578529244307720224998595204544433623704646173023290492486947285269984737645373561918371157569603307140530699169340634291 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((135387086680427784643076250165686419779934713808813868008971628971152937484667634115997246481320224162416809348489043267790556208482411225629338487722903079750355854037457645722132574550232252513299550933890055290528690439653687066444184541651426191634872522806751103962470781212352061594071165280430327503127947190128171898769153690600779227317319290938586089180411942582193623 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((14867083378004178335500424718277016692606720925599009489820489105303693178696846506007222347430501358574673965959534105401955779954686474408529528160449829481116416776390951684648472204132440715241665614563760995292421195096886017160058368504855896423539912273863345817857951408864620137900131501218380348622881602793697814478416643 : ℚ) / 15111572745182864683827200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((404095356257795606590464694852635108680663770528979194381085427723716654172012994289070792479267700375873304095664050784244647570380902051034938203683917185383061239028652602246362200396264080344195091045133344651471205692505291035585226573797341710079439331712091617876229687842067323096894286929402467803830130101893293906850556953836734485040548464149605139805017593542995056826227 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((68682132405825275785933817120475162032076517756248433019769527233097663399315094526712086704061289119486365311216121728751817648868577158493112543252200046912709614408403781719861734204404699235752525073500275082308811089052307612560947916871689048169495498336795286905184527188944957154341481451013865746145247377418164521786590304822241602529282397684672554705396273751593260206067 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((297596669970050936571313320984377405441745608586580422898527011969242111588556119214378914040240014254500094372694888036104875720600991495362494265337647417473523912830043271085881087573738678638836255055285217187758428595451668227303226491746553228501046116975627446669133184857846603954172792868596836268843966544160129469067344301351 : ℚ) / 302231454903657293676544000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((40675439958002041181485336819288006802186270989342866012059507084036963942410485026908763906247955736565053044752839079475672916449706653468358205884582569212169150531734342780834687957749014313085331156683801966518398694071687780543090331647352182816934268997646568655230379686784336339905932935454114587038113445403598919923499258192363655729797984011922010249100959235708203704996244019 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((6966143928344839917702555887810162189845786554149360296939572263634800122366597183121151061773036977679367908159667442724194459256862007066027557764441068258554254086356421540838928274969504403109949545348634617182813731636806879119198257911246018053622453038821765916501859844262815348755151114473274257262696337170127473494175106653276820685645267855639318065724085776551548886720182963 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((5956767480086770161887022017900842474959171501975805076887376565900922709384258351946981073460829950222558289023176992500440129035432995777586803788005782093045592815519130289975047777135364130956418887083041862228336530883977274584987264604039409552694331239506969506506757785350198071159253634409990225148475073777643574345109645920710907 : ℚ) / 6044629098073145873530880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((4093457011759368287866374672091174495591787671646967042953913733138275426858304404973638367152916643995614777449644819642807975813425519567544748280394243996545837159871848452377447266104376001602076158142790261627105961467869369877533262227977678892360254516115221734494375270340939005050799553702968494081923757513274022144732836530004177966404346476068241340273188878169248969136309593369843 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((706312217067663361673836649524928069022980620867904316285953248411809819170538399206994195039284644292103409944937170439013669500808850485882371493388008276062135174214677807143324411464358784813383622997157434186106240995696704331818012847226394465088295757711842736927027750240749472608793305104841116017666041086232125742059237380833179142915849988394080913227965472065187908847711739010419 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((119226989269295193104984984233346270797801014162955336842553997559783791801797385577858920209596953366369037485012366246830843526124703300955713039409225611137865303003796152907056980711155097830540832842433224582262575615967557194307603575098775086890426437307333620934848607336883704834965971147510184698139641973602789238860243557718916663999 : ℚ) / 120892581961462917470617600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((411870646095416246115099744360026270435200402386175990604805464656844141603338107505853610566563629856671932172742163161740215098050348368725011992472107204683458874432081606986898292938224624466634028036601653444116755591854581288500600258664856376223075687824573737213074407792498800646621119798471395670855625838304446916248992015832239180088988550751733024541806449822702656879867612661453774771 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((71591255271387293302150133204504343802459460034239171410397571100975696282737186082465685325284268425798532255709828420281639196523198967629616702905080381251682570843968725592752182408962812714136208340994442935946813614665877925462349021327817026990058928885532036738299977075994048684643359644779799852485127620651650132222531124547368210567403895356934473012129071737879523366416489117499322419 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((2386276998563834798613054502911545255513913825487144320524296131740821341186673038399471550413329444966257843603379426941172300724746000476217452088080689910340512549042963670659079183341367189573562568194006638405951645951896981732489240973147479322181813972035123452061925049285304392556449915043350571322633192893588075601073637123677503199429043 : ℚ) / 2417851639229258349412352000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((41433061218976465087496623920764082542357777590676143244858829134207327057176533730258330412999045670331609551340810119469429309283362793597680287373069725494546050111128273310158451762033216912419352693289066691994501668606871612376604124281034835835835498680389280268853634677217379312301967327514636758959336882367830121976564954715281326115636765202750184400749399478195467435352127017723628015452787 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((1450826657054239740881046644717547022786309092609315230979382200309809247024663471234158724112470949117607184511091859816997691798894352800820804998482567976936708125565284206933889328063235583047291670893324114408366158764882686444665972738402073803616172549514202997131344540742443296227345611832205919563605100877885656587496755033118479034893930974694342323302065565416287810229239913097372960223383 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((47758472321490732735744757347694163408777264389759794884179081769410750164875760788938782181185486288225349941189263796523803304839009931027654239233745638630325096392207462304684164078602297812746025605253783844261625352310111082702798541127956765510600647467869835280737913159301515369692621039476796780563157437683749149169552938953554428151576368151 : ℚ) / 48357032784585166988247040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((4167269685179653526454040926484481064405664367022362010420720701047884105416309961349298606048311284519574501084651044602589361413651602672902782287598050379332352744277838614608809317337182524946858856082179232708038425612981710715387180517630692443728166019035514375592753178982602255284900132852230157952229201942952704843090863823764477001676058119866398765621048997616876186159373439971039066406431020339 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((734812640282083864834819220465768259952734664278694423329021387296809058094660966696399755095812941961604047912412992411307858832739421533759419489105671691496903661695707803469755527588599549999011289538156953597880253501876421160129832864022372875149064894858511150352625915475034612748203382619891942186141787231604086855349936316077293708728208403648780708467606805452735276516310824416809039901607241139 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((955793744992822149640255027760238255740190601036676431619382853102719590875549797275912493808733263565887958835124873790701739249833111262491241413154116071515072852307076862909897698438063759636226407398795980335667631803742775794796951944162676403784456474048408467416948619760878826863263017045361636569135775546170832620807215063742531294469433211038507 : ℚ) / 967140655691703339764940800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((419061073895662388829178792891864379240616699675250065668892550316058090938074212922060906528732407438197177991194145187230341515794758620992626968902349574872648886611579973023114364116794619244020206911171172362746756403893457566198021908095213041039725750994173210425108202512162720129709286556160915709908965577536074919563473342541389850644829067948294228876363306061793002092621466707220430511043280222672883 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((74410874505115234260287798428355231869891673790269483660950347539639416249355609903224696095929744250281985631483593540873505833318541448195105832889266919404992332909374500949328001674545922733888894923148365783453629030772987467751658248141823976628857342660629427654318554431934886374669447819985299647244378897293926708103213808357237034613060601315368426727095901229558620507262338959404882790608325670127731 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((19127709727715376074105147815650836614066793223852275114208640746268255284227797506959473145132156477418538035637462232450332870959086290203046463469162578367711236061185256090182930669290374691423944005058975399223251296103551800741965818005491856586541941378535679316823094984806979920846877014128920544441106897028760473992642375963367165749257045381656977199 : ℚ) / 19342813113834066795298816000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((42133427557763520219603188170070649897198230813006902284498628025346619999077550476017008032438569395300042219116865362369409013863142317509089248946335309997713618705474630875807229466747142312225603663778627699296804296904738353056715041479692305837745397548355592867145775567429745358229756549441668229993917213611168779500752773865535240634198474424810968592699841895915721836739085329056153454562231891963728169651 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((7533000555449050925032316735413604879972282232444176669281028762203169447372634382717505336056749591869059974395561000752318976196022233590467221442397070336719511714052830145636732552020480746118397215119299904231664608969865488100425706223237030933720626625989145978786385769675296980662635623922628290584982997370581469452294398744321821837435848235190765807839350756721535850414357983868776159867730320012189702963 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((382778547386029315904307952229292909692864199144567579340053202627007315423106357339430732412270290342423225541579371540560960234771398803379151807984914998116701902011888899701597816697737633025323706503902996643075174820235031486665446011930109125311075582712900872809015411626985918359494247556841946760970063446974212305478521521137551361108665809300071316761443 : ℚ) / 386856262276681335905976320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((4235479080650522082875303365088226339489038331682666666518567244681445706507461342462902627024419456583379629315790126726866861557393869350669112839326654664888800497202363242798368970642503794399714161232626543278998307541047704110636332299000941518825013494154324285478320059564740597807067284059726192356338401007024945301510962110154872347770909272796760675395425564510629128414405365945175261783701579909247218135756147 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((762385134524232351108473431911271574392851213370022925002885382543553138989920807071226802528651118454968615796957808444267518383175066770089167959164504534360633699295175340455671301740857645642947996718029171481520661313782683045338414870279868439223929871119524647655302752961497216044997027430952453444712366551723681021809962284850585884379917320202500845142471301896008975916792610005818469939797154134438602100153843 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((7659824004351536374947899152170705689047626623183567601549388562200177678475827216083588394339407894021317086591720146294414123170561407115658580823970033619298317956439377871643189811139012309261061504194489107362776089067195491892716860048159078688522059821488461845840505158212772054340932450935052784747709492764290142674956332476204561152536977746901451951846674951 : ℚ) / 7737125245533626718119526400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((425703292029298235663848415350648406885738061690832870425614274441086194233877551162751764352894622437511959316074427021996339898031048084709474470661975854822180770078959473816489953808808852929222316125784412293541041449451368229572905318200004201354597713986510314405319770502990053872634310768461635917865998038373602827696308357131810005008731866850338753814497985632135577838155920872515593120506531392515301170989988446259 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((3085450757165452190737099611466864578040670795200065669997374268809491575758269949582216911338633671497953399618185829055589920274087989357101732550218824451493607722577357283578628911327632919425941470311752924406728931509148298091372338814044924600726938507091094704661484273810912666674216067122701361722175831152642667185607978440156730109894076827767362391457202569591773146512516713580189053606890869068643210679395434667 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((153277105281583647726885990262900067747275857895690891022571758973628768250866256535296585191492155446962108010519238813303208532944332594691539716679999927321038213500221286312739949249762256346661942935014930008276146320446824939810233515932951654698312688035956771211598456284239519834141056472375795640462328854332648234689147194751409865768643487148010824651157417046107 : ℚ) / 154742504910672534362390528000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((42780173334465012293132533922410072652047506281552026579245770931243714375724771086070875897588653358850567038465470208442293399086370722839906314416690854794170398859423974951669376008208541954607984669795522544609995186863707763873680670290075096697328321358012964195279008000166685447081646896057135478000153132907178215775731800971475731136676766993474252382220501205583543671139831159026080358997928686138898386190743448428987123 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((7802315662662384510401483838499560640556501921503479686686824445626752676145819145002371543773390838997684979896636246635117873023281015998546802395786611839856344044794059584258752964764848788231731199784001414745443517034862904812700650312766513889967747492228729200515663391270559048599886184777290369612895427978400435398635527558820740979207820476762123082247271164584862271513778300832946626651408978147245818636497773517026163 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((3067070517444812663298551038117796584285108438128612221114892834863080559731671625139617365475116790808060681555413210183788924159025712997567518409102758622224921413323694924630611217927743093563670452219078028166890905796710460383982596761540964518115913627097632511858271935780328577495812007546827957956244368091584012585002163370902476825376174585864841202911991154943050399 : ℚ) / 3094850098213450687247810560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((4298445222225275052288108859022873318471106101928075615918574114953441664199193637859669548955120368992426498398719733135944154682985096547816581227592583717710834929089122470279071996852164010994315702072231400534718760563343974668292726625268349136676530194828954019200243426281269137956400872675023702101300585773833187326689777407159287158191812832624917874413507668933220396624839443501806452423256249922284251915028428126703932650931 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((788990745653886765048554018966243819433645066587170316297883788736268952293636025841325626397267867031933387118654971056491466485921989320600889601937654300413736386648353495043153510137390782952045682300489395756964915090360552382749583729539181233137829949084420141928231119434414832944268969810538653278947811363532180930818713351769372022706205079886636608585023298784750006752286961575755243111401863444301867603164854883953804330547 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((61370384451637942724950098443679069848292800661604101875675023470499418170833298997771726397311789003348406340245968225454086635282650441294887446481360995201517835232377284686222496858256225824686500762717062179959750901188240197499158086808532064369923374628889819527297261086587688843588108227065217598976524485912158126573886011022198253178656141624239794683602616324255406413843 : ℚ) / 61897001964269013744956211200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((431832932440473451205093597261971559391221654187142951915759194673623475085925634985880550802766469595112903597479935865974375303637520455345756379857160546000335404031129149392330005311928154593164457369541665967345745207044158674918592084162776778982556476815965370415292550265377078297089919489624485890877281346491735438361790463706896968702688556882505387471517645580607228082529745905071490331798510999101378305105395878933497764594440307 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((79763933620773240594870478733474910760202056716250633153288747366353228181617262281744798491554885721147911274958040691274000213167846866484006618468385798694027946927384600831325939686660147160748470890511736855549183847888894874483890227476201622836305779180099908195599012387488995917704646001082547228256811706975234372029656432644999124164617321321063988038637904635137225495027774696655004919483266483112009883913778827898683190558558451 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((1227956951098433061572868344478424127114086622142028959257171419930257470264486849100758617313839584136475738992042819649933120345053204415627181322947160386035173602500176185796719872941963272958581994958827347745496997833825469423991539851629342344260637412839864308778974178418442817407899767660475330023797974679436781605461157110947812285507784476770713787817054797658909739387221751 : ℚ) / 1237940039285380274899124224000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((43376822065942347522598949899672694232857718876624859320913692864231009937471098174359212100897650655537090447100083255235821148109471548242647099171751725359448961863372226334774717675599273365700002805169290931523427377723660450691644386775332650627371002394269890231253308526759595127285671918859278804825695374698288220162694958585339970403400082513525889914466565657899671980163606431630142410328270013335131600287693797385336111685619008809779 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((8061765700931061089528035916869841516697468636107923612740946119977938213867834863669668176280754595634655720178523433364764950776166049321383827385668178204279531970293904277905332837315937403499126213423447187493596185219214341885365177346533445791372039271602334082948003889790473360402552001070622505637913646828096671251299718967476976073799206120706273626398733745983046702362308385534168255233302790226657565839851745179343764162642521422771 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((24569551382947647174956651771909486177701740095946442980638198607617890863803877198403081108418456996475170584072155732103782162381173596107044476339109319438068785982595839954148418631360797765475838878434490031211386587935829423870607620967337442820148903435205307701523013500278420489601555895539630831261138205998083068894727155352237677496371070326142421275647907799219951929563562733707 : ℚ) / 24758800785707605497982484480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((4356516258232028322590980858418628652370287097334283306810454568241303770466166170260080525335549000313242563562208139631975961744533893075988449035312795558491474796894472628177555836618749930958292574615532676901439833364401531839308314302252216104070088712821227446271305536728727650741379703023292280538845636547727359447819736615165457304748806702103876608282290285736173376832568700140754842334575238649493283515368233130457644888039372248620248563 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((162920359570921042609664020800950900218292044354052517416129338528944699799571460743552997190135371238825082393121307480892300683157048819362583272663206126584499527670782652194492079436125946365990433858322334780158448759602892824496241355687393624361169848211656769519338517551103759243262305258079375934394562711772158917448839286272655936284766095679973572952877839803699611302092323766152676370220467714790826419207977527630404586985156835415590423 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((491588414786031580030048978952728129470691886998856719583958331004612357105130100050127208572288689282179808762255856213491398452259907861401242137960495368587469975872069338010791571994706643240125477618482627521674255547499518388315108670677815903541562762421187018097771766924778017221376695111744781668217396971105660737037342684012369652298706380172681880122457388149812628728736458742883599 : ℚ) / 495176015714152109959649689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((437484368634552119963391221403509504512051630931348281707110830485630280067484265931401169017092779713600174139550145949656396431072288021954529428598270316598768327512585102487954243324195636251412557432862352347724380464488371466848842255578101387713890066589129915897696227137490379811932737295776228061055711025687703880638375583277858354776799290885000821088059131987086171154663469585748028375697694958005741212493899325220150260555681721662288437010611 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((82291448349038422159923069635371955369685387958187956057639985187302794099063106247005987175288046692093854069745388706886846712276138847614665381503213908773538487407704792522551839403720420052749549239530125477922015419437910574487603977645394600298537869759509570445973851911131815538299385762620998471918453823296478583816243756959840208446726535824884621174402043153524076782194738607263338080512369431851146513238313736526634405225868948011808700657971 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((9835510163488661313317553120259667150375906101837326833153098080854436453641951306650261492904876682722282634706084266239156440459491073328583347209317110702312668332606818440670575830303653835903058679213575169928378862413948370087289515070039356083437405287218442302079459385593016872465638009233345826084397194381250010592016905260822491498626576848933530401481424707155998002810657048388844386243 : ℚ) / 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((43926765110232121464339346749526055397741289022532621502626253515325084815568672814434372754112079036391682382413902010070048453202381921932346692707913297833059742836618912448252838399287955466633351581542037546886438371289703579793286990482401177708192811644432114345014298102685362383781698022877304316895739549658177207266625719045553787906142641464131505497168226186070411239785171686477463807898898750501132474702371506094372422034613064471165221758861329267 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((8311141996359309828504347063283745951024754525696433124073747542260748671385433128294735273307971698068920548674989294168121191481163458363508910152578549791252841824826976063080278332853992669997548594832392128572281035265350761429616506507701827930649229086727133411621532411469354633897601118305786068461095477399151713067472039916450963468062002695210657106087775691597761005287068438699951677823848643628679725779603641447652445290803614689899465667021796339 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((196781137857051765530319147025818510169676051972530204776083280318757551851690470920169007120997747274366311906123239435095688641790572277089954513047024467583741253581227457179792106015066365767214283381851744496332278094781219251744747337182736073273722892029800010720520311572686820851331099741036536825081917613885356450792864473029411971339464017325232935820883368173556254139281625666307323030008551 : ℚ) / 198070406285660843983859875840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((4410026561547925443271846974371678397697504311611945933675763026784779330698635368577726235172159428536965666130431214409046141358968165879332384662304597450023901081729187887835808447247021337087166615262367929378118202288991394118455972144391138819968170106180179298869876650854513903249058024074736959742310749211479567190519566965932560474755269712725612199896965407874006549973212855264412904613338578258636612488421065441593501889143088649160165787381105265038899 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((839200622859400708638228428910142636298862651655891707385167520579210409366973706637523889098083475335687867009598385655694074859385585999328972481695737496816996802764442039512348149161778359483243729485314051914904270398817899647256290120860039349616019001412938691750939064668739076882840921047666805998699425473441780065479734324095567046869858504948315390552900131588473381513214975604275154204513717024089687651649419548575192848220010213513603057533895660840627 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((3936967464112074579433425920669561497286548917243255091940210745002686910452496257233643867992754295080162174804378249971108969582423878656794267703832442831984982944139328905757318953727613095849081170069763520416970995842767573355325175270973127741049964864208918803228903546483424062878683657790829628593077912206424702237680331815218562740682219376434440764356486010466105909718361777756187922679872101307 : ℚ) / 3961408125713216879677197516800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((442690547314397684670455204383655007062918747947938748205415175124814980653740410005167386129153933001438523419523512132716660999997074906471634412138058133253079114322851820877448941582180653470103447948619451169050284866837386489840911021190195713758357986392443429811578834155473476309354348504870837998751857989603707495592591560378079386491351562446480833739340009299100840005020905201522161327262232818021001259884933374913345752089615138835609726157956088925170473203 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((84717352907013585078623075367873712274230319820265373720347017416883269770473041254067305333644675457654806848915511083111613756273077947097583734684363636811005907076542468686683131715081966227984096063403486764831332388246935849941408136513343827897680499375393886545716559603753832788242386720058921389830809924163686328872924109069406275948453658114381328488017834374158063710429204745732930822312401471001813106609482259003719881807672148532255361196224426708671727987 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((78764840892291483007822772188155277304061107824180386777910575093015935761447971548378186805538643171834634347766598484702312736374009467696848932861551618765939321672049258066441495405814361458011031741012507056544519168191344888096899347611837582587084183930808473752810324530686269959991206100740757269238977981697193080319706050221098293875112832719067693569905905300405969730530984220924054450242335424476799 : ℚ) / 79228162514264337593543950336000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((44433246842937722807889777743245081054599510793660407765519506284068827554421182484824321599364859189150995277071393460064906548309832599694527182749599173491601106147124980073061376113663075225881541966855570331008607834372328877235354690459827063651850620179868210242826555116314187528473996154506628707793109267085651615487201350941761593386102103297854380975999219691443111281342826519016874151306205864201427477461213092188019434279036595363880419882446527382744154320800691 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((1710065578083184083907954290858375293400658413161472690560198052103897875307438649372665288822792199152358178396322847887193184310062140078029183433960124119141889142113775020377853099490527836747388414711493568618839005999455552962665559891402591166841790076225955128495718279070182018941524393367148189875945691292826199451525757703176934297369480253487954435456149164394055018002308333568153208765203141137845943705573521636983625422597084449513684689724369573221933770914007 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((1575780062297547347489362632571307591853086421022987592148850772038303094229769196642605287272596058608469163330611407474501742543442097479129165220256434036945911720937037785165531428408022850159515128714374096270914449871403325043652920932677605053103354874776336236932025322128219619631553294051742535552963305599033689223620667594041360356990513969855366267004706246779795968181675867876057300213243952641806678643 : ℚ) / 1584563250285286751870879006720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((4459295434582037477115239440306817375589984144506816380252609268982721891512813981768843253726416368153623566252769141274940047198391235790522081398624948379195313244806198911484309832366572247701179162647550493145563417213756934790377854498616344629635481491959562410562564583276955916551974844319256867394880779808785566026533274546796473377156413828196864718897425654172654824995849979735056500461502023769683801543888787569883731900558376633328057621192786258422844943679252967027 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((862778364049516491089183279217228371116575067876272577423515893800136026280261538675842503389338224087199689801984140875853621601647272516201986957131352354740278406798658566295713315537020274871331074025924438421103796579515872369545186869623549440339361255835076838756253667013018293663042332456956989275050411595423549338990590302625281889615845487902645353974099893154523951268575738288750538534435192851296464865522516011694211334149653068881662636510769852501124132986211557107 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((31524762111022159148557174229663238018758959283332775784365764085530111757313734660753868430826603483040749929258400451494129533396031841911851585080401220038383648493803425293382979288330889170473928295038389743007725226212192832852528422120769358991680298361135006043520404031584659329355355795338883246477525384240881646612176995580242068287469173326548178323608216320204592168820029427326418240142465610230729207035351 : ℚ) / 31691265005705735037417580134400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((447482876302842330891218892078081351318485056441870877721788787947467604222431810595004037546662282567388539680668127336385361474692885683687641419367284514601882069310936231510274218067540139258160348119700227579669757742323480333003041181214794270836057642689000369931833396026302325523692310264465528822885585847496745389950836985156981116794133571188205259893057987846279243093405921073093771368795131100924496602385489702885581996294127587538607833563728402487712480467968760661901619 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((87041030162588315544076517208565330357238135479489564377764408470206711212324722112672813581741803456876221359131352348958407009684121475934564294825700586466925129790397811066821534177357425286332509536566140365882468868739627175055851896976587409213222599190252459952667291987127065601922386020165710612598113263546663099982681211658103765746335173920840351857781766059189196304938184927996154993610606553169571428708173234876413046543882848507021928806965313334365103046304101611819443 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((630668904739598152623224887951905203121613591134139430544221789769394328583396467963911083843179922228003496408951497358974213564588575627122970498369165928267638824497031533286661138368888666004674258689042754358197447113304539532385381298143424738405283416032036309567016299226750386906589479812239209703474448709054393374827039305214648888525553118751373816480640956782118453744321297853826910578380720573143933577769148907 : ℚ) / 633825300114114700748351602688000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((44899355068716341920499282267486707732263432501947048811416289183019092581883412775907422745421381733609679213873175481481524965440294477831604743366442123291175823449133960010473844538882240320800449957503276757250716033233963331627180535755306570904190151382392123837203211006455472555523320194556768900756693803775383558502304973034672873199290420373061371165412608373993386464353212581211288513181526247329103484853518422128956602655303171992628148001443810692763303454416026231507242157043 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((8779287314287765779424840728052104798350189661443558291275964330649118176077933833330526135071489512723714062175951272376838363179431142226878113352298871648424288412502835262025095395323832130284663498306504835838164777750358001031599372327793233509247517524192734826568450519367596665971052696017709694843788627879202050391713346054673473077366773598841201982091858315091328131104173951089975126966585652917359524512694790637519911520648062169189656610276782765343251120320453693322414552179 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((12616670215167583812159004922507850935576428847129881184826812468658408286955446843191862416415161785676262281424493535434074166543905628163370151737584278502169629195990226776515235200059022441450609921968183494368349004926914155915429673268904902765948957717719312320461927984441507084588216768800618698348765124177544135206596184108954098979778910472169793439023510617718619527631098843414996743834363319905089548833769755829999 : ℚ) / 12676506002282294014967032053760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((4504626300770493492786673826376414735142318469986210914351413662112359420272821514023359195419878695900936949688903750789850213543840932166053514182624392538197744461965092810009106494137124813714801581038657314249634641530703363166889195345004347885337719143655050937645451461253020541973350643508733600827297300925850800296766978323655500920753483231220209974342216888343505004939541440177162888267936372875216672726209392889807036248961823352195017970810196597827457855945193680810736247146133171 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((885333861228131493996203611757156144258938010253478650571854943983251740855115143157089699388436467000186527202228340624408284153074099643743349198727522868822420194288219348757026250991276505260810329375608367446137306865165826318078029998937532514033222213952488719346758614496001376617076075425508818586264688032159946584371471458201043396270273617649236496579629029070149265082949338309074013416682159303930319149079152683253201008190348385869078888848853143015287568354707967406112166266783539 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__bigcodebench__causal__minified_base
