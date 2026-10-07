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

namespace LasrTest_closed_source_model__bigcodebench__causal__paraphrased_base
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((1299 : ℚ) / 20000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((1299 : ℚ) / 20000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((1299 : ℚ) / 20000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((0 : ℚ) / 1)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((1299 : ℚ) / 20000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((1299 : ℚ) / 20000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((1299 : ℚ) / 20000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((0 : ℚ) / 1)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((1299 : ℚ) / 20000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((1299 : ℚ) / 20000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((1299 : ℚ) / 20000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((0 : ℚ) / 1)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((1299 : ℚ) / 20000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((1299 : ℚ) / 20000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((1299 : ℚ) / 20000)
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
  | 0, 0, 1, 0 => ((18701 : ℚ) / 20000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((0 : ℚ) / 1)
  | 0, 1, 0, 1 => ((1 : ℚ) / 1)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((51043 : ℚ) / 100000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((0 : ℚ) / 1)
  | 0, 2, 0, 2 => ((1 : ℚ) / 1)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((51043 : ℚ) / 100000)
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
  | 1, 1, 1, 1 => ((28769 : ℚ) / 50000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0, 2 => ((1 : ℚ) / 1)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((28769 : ℚ) / 50000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((18701 : ℚ) / 20000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((0 : ℚ) / 1)
  | 2, 1, 0, 1 => ((1 : ℚ) / 1)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((22631 : ℚ) / 100000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((0 : ℚ) / 1)
  | 2, 2, 0, 2 => ((1 : ℚ) / 1)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((22631 : ℚ) / 100000)
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
  | 3, 1, 1, 1 => ((14563 : ℚ) / 50000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0, 2 => ((1 : ℚ) / 1)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((14563 : ℚ) / 50000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((18701 : ℚ) / 20000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((3777 : ℚ) / 100000)
  | 4, 1, 0, 1 => ((96223 : ℚ) / 100000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((51043 : ℚ) / 100000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((3777 : ℚ) / 100000)
  | 4, 2, 0, 2 => ((96223 : ℚ) / 100000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((51043 : ℚ) / 100000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((1 : ℚ) / 1)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((3777 : ℚ) / 100000)
  | 5, 1, 0, 1 => ((96223 : ℚ) / 100000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((28769 : ℚ) / 50000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((3777 : ℚ) / 100000)
  | 5, 2, 0, 2 => ((96223 : ℚ) / 100000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((28769 : ℚ) / 50000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((18701 : ℚ) / 20000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((3777 : ℚ) / 100000)
  | 6, 1, 0, 1 => ((96223 : ℚ) / 100000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((22631 : ℚ) / 100000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((3777 : ℚ) / 100000)
  | 6, 2, 0, 2 => ((96223 : ℚ) / 100000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((22631 : ℚ) / 100000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((1 : ℚ) / 1)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((3777 : ℚ) / 100000)
  | 7, 1, 0, 1 => ((96223 : ℚ) / 100000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((14563 : ℚ) / 50000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((3777 : ℚ) / 100000)
  | 7, 2, 0, 2 => ((96223 : ℚ) / 100000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((14563 : ℚ) / 50000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((1299 : ℚ) / 20000)
  | 1, 1 => ((1299 : ℚ) / 20000)
  | 1, 2 => ((1299 : ℚ) / 20000)
  | 2, 0 => ((50272599 : ℚ) / 400000000)
  | 2, 1 => ((196204857 : ℚ) / 2000000000)
  | 2, 2 => ((196204857 : ℚ) / 2000000000)
  | 3, 0 => ((1459747873899 : ℚ) / 8000000000000)
  | 3, 1 => ((23004884515851 : ℚ) / 200000000000000)
  | 3, 2 => ((23004884515851 : ℚ) / 200000000000000)
  | 4, 0 => ((37690744989785199 : ℚ) / 160000000000000000)
  | 4, 1 => ((2473238320342582593 : ℚ) / 20000000000000000000)
  | 4, 2 => ((2473238320342582593 : ℚ) / 20000000000000000000)
  | 5, 0 => ((912694622053973006499 : ℚ) / 3200000000000000000000)
  | 5, 1 => ((256141503585246443294499 : ℚ) / 2000000000000000000000000)
  | 5, 2 => ((256141503585246443294499 : ℚ) / 2000000000000000000000000)
  | 6, 0 => ((21225102127031349194537799 : ℚ) / 64000000000000000000000000)
  | 6, 1 => ((1675077102604333033849579947 : ℚ) / 12500000000000000000000000000)
  | 6, 2 => ((26064230767501734205081112457 : ℚ) / 200000000000000000000000000000)
  | 7, 0 => ((480066634877613261287051379099 : ℚ) / 1280000000000000000000000000000)
  | 7, 1 => ((2829417638245464693719509058664771 : ℚ) / 20000000000000000000000000000000000)
  | 7, 2 => ((2629396531065591019029955223142651 : ℚ) / 20000000000000000000000000000000000)
  | 8, 0 => ((10640446138846245599329147840530399 : ℚ) / 25600000000000000000000000000000000)
  | 8, 1 => ((18786655368990155896682247606033730113 : ℚ) / 125000000000000000000000000000000000000)
  | 8, 2 => ((264112287135180962384346004454870334993 : ℚ) / 2000000000000000000000000000000000000000)
  | 9, 0 => ((232241383242563638953054393765758991699 : ℚ) / 512000000000000000000000000000000000000)
  | 9, 1 => ((32063096328939676148282840784957646945033059 : ℚ) / 200000000000000000000000000000000000000000000)
  | 9, 2 => ((5309798352453466168931445434797763724444051 : ℚ) / 40000000000000000000000000000000000000000000)
  | 10, 0 => ((5008234108019182612061070217813458903762999 : ℚ) / 10240000000000000000000000000000000000000000)
  | 10, 1 => ((214240879852042059493340066033002432772129591127 : ℚ) / 1250000000000000000000000000000000000000000000000)
  | 10, 2 => ((668931487293763633169379165001877781699322365177 : ℚ) / 5000000000000000000000000000000000000000000000000)
  | 11, 0 => ((106960746054066734028154074143329494959271844299 : ℚ) / 204800000000000000000000000000000000000000000000)
  | 11, 1 => ((366783911165932386180032153416440915745295540084635011 : ℚ) / 2000000000000000000000000000000000000000000000000000000)
  | 11, 2 => ((67603345714672469509282553111602286542775229807173187 : ℚ) / 500000000000000000000000000000000000000000000000000000)
  | 12, 0 => ((2266308111957101993060509340554404885233342760235599 : ℚ) / 4096000000000000000000000000000000000000000000000000)
  | 12, 1 => ((2452391895837431691133681817147235957155120853199621380333 : ℚ) / 12500000000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((27405329771285442756968761875684724610791825005842168727351 : ℚ) / 200000000000000000000000000000000000000000000000000000000000)
  | 13, 0 => ((47702932001709764372224585177707925758748742959165936899 : ℚ) / 81920000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((4193585304008512869196586565209098426851329457451737883758938019 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((2785225993631646830362395833537853019587020040937710520708179129 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((998506611363974303524971967408315919614360242079362185948199 : ℚ) / 1638400000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((27969196585645034547893132885480013958426510394823980474313446901507 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((28384197247845810606491632174730759586193930075994453342106062922753 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((20801353739117683450220500762502916012708150887126152239417269499 : ℚ) / 32768000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((47664190340864998768085885104301553051313287994715308080651178382491750851 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((14501180302929187533841360517013253500079508106602072813699213574656245107 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((431571748275239798202573584759567032353655129740146173029342356900799 : ℚ) / 655360000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((316620284250803030886436309414882312043680831411858191338678602033034459347353 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((2970721791494957524484694854096079548951111305839182223325778356338967088825949 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((8922135904495259466186328608588663072045704581270473581821731416401842099 : ℚ) / 13107200000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((537203528988139439241313422718478725028594865169292500502369203856579398040467985379 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((304985759960863826641019911996247230320146503185645045294055396060064768635378527123 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((183879116349965847277150531309216588110326721374339126453648199218130849093399 : ℚ) / 262144000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((3552086272051320771591139685213277943734173105746073680128881860935494286493497957159087 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((1960978906856400165805831236851411961720528736361046310482958803628369538675054724758307 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((3779248410860711309929992086013659414251220016421516003809674973578265008895654699 : ℚ) / 5242880000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((5998548522525491860924859130789488885936086760697519332983510143123929616058242432408233676291 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((10105375160199061585431711684730198199305920420963593971172426587514298202000786628230422303 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((77486225651506162207000782000541444705912065527098770787244731680887133931357638525999 : ℚ) / 104857600000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((39478135452872443206103824629251185548488449968139297366175477235168601167698822101611465883823173 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((333814762262325759697911782837725935148360945508396099380878526940303343245010923020234994679053187 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((1585279928308816739433121624192125557445261537422274112492263727164270291650319198074707299 : ℚ) / 2097152000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((66361424965411178909998244831263414644773983887475391624309607033582986999926957596671541745295357231139 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((34506400550855759063243431809989410302846989268128991889158990938052517502831061263020655999293736803437 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((32370520387303181844138807494016940049783836011333948177717823961699018724152619323195101198599 : ℚ) / 41943040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((434782352903464183694189284899944225346083654576997750964486467238531814703671334288241557572696194544331867 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((1785478241149675863542768054890146472342078592745085270357781485399035166786818663377132497696010900349565227 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((659845110722956803667239838945610795871007517247956164871501025907733349160378133963071587514999899 : ℚ) / 838860800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((727676756168950960821549866513109226807109194089071125123934385388232050580993660314134626446701862447666156235331 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((184941456373476334392179393978231278721229092136408904012779730963630838166814185282991327229419845078687746530893 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((13429443594830015185381052228121867493583711580054028239261940685500521362648231483243401758118013111199 : ℚ) / 16777216000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((4747574483978995150450041572287938921035698041747844085182943108008751613172758871444179111699328552940517654627479793 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((7667935724260030885492069899870942042887221058271553916247301655727650547379027151195407088816424888095595428197015893 : ℚ) / 40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((272937628250916113981811057718107043997508990258590382102437552759545250002884576968134856278564963192532499 : ℚ) / 335544320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((7913879133362319909289010811555309751464365630300988641436235241101416539376005744522845126176717543597008546772926792371299 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((3976064317193183394405514122172913005839714663509224376171096153998593470589516811966492913614128083147413757341455160211271 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((5540078657600382247573848590386319829797415626825898735697684674156255720303944473881089947265443376663550263799 : ℚ) / 6710886400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((51433921951638865421273249687012282295440973109497655864443630404547096738039162267735464076788531468329406639187890914606307847 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((103119889569997292014316594803272153273048943263123732811754011432961677447439562473728658417065427176714873813457046093948881439 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((112322452409384748411878542488814567137041469637271132256282401091396138225404065606050263103811056586985053483305099 : ℚ) / 134217728000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((85422119680759016368767348718996064977622669706473852960236439408963662667623478002109618510276507142840720788132182224059979891811971 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((10699568826939209408278181958026637965312110689345845527145420610265769026543272683450540090137407732648555978457128002235915317657373 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((2274891011179904180050540623083321220029812523686607444324737182810199180953281430898745970304370569233207485191288656399 : ℚ) / 2684354560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((553233894990517551183291118147110876114573779654918832524934868287284278675056074369404470900072579850382725516715307961744642686870669213 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((4440817790972512992395840286300436877165389730925052919264868261174068126059907186092613305486481504513077410077096163296860462495155423183 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((46029713373515388071125160192281190135777524005463245816316910055733534883007316039237448390662034015230213180562289163317699 : ℚ) / 53687091200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((915758551836167818043442351011887790371694951371135076706656828877257269485772666502696035960763506769600481892916391259978330346249446941341859 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((18429673641712602972816543548822125683873648749236296877502811306211580832910137514147255243170355838171207059930982544466318261180972342672713 : ℚ) / 80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((930541201266911272318111620755850536729175476426168160010942534952272835847119817249779522353770698118820216689695369643204288999 : ℚ) / 1073741824000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((5912100612535504297885333561245264511651555703419674737452049910569472958546739949567335559671163134791462048144792716282156757042365924304099695027 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((23896391110474000372541619253614842588109122210636441022909934075304662134487783705987733229706666255238741221651509272096750852429100852161179888209 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((18796841634268507703621005419755160887372310584645770760364636346142454303176987702388126847537865825520056872313993107697563408570299 : ℚ) / 21474836480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((9756736260100009541139185746337879467122278180867127553308586839507407662433576829396624529959692628807039246872272027961383879362919987740291472505750211 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((2478022473931512535711975468327167910839687473608599156414313726625807699482266305857384265833088412358696213817716233404147305844077500066277888768070439 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((379415547989975362565416422354841263754749580243460558989579064309210037923712847022360360175805628803050583569143985107052133303673161599 : ℚ) / 429496729600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((62808894007539355009496375284662017561415896674410995398839069535954198357317186239559479873918960115912143471565606103738915790962352389484403220794900623433 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((513736705872621597484509535541608326516775340235215614024155551927049667275575841181661223272172291663785838799800789703304679332823087371449995473514302250741 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((7653366414710929255335852514457886473477571900132955913664118081646536919211353952165161095647741064245848963326561665486981944911991795062899 : ℚ) / 8589934592000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((103371734163984149049574413609250510884678417360341894510874077536607360347086333129084544702611486273100432554741506053545709066059937042022412793508708844999918819 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((53228954131844886276685845989622873047695159031281157302188962323273284249387126364852046374658905018489267421106884095682236318521672815744354369887044139948354299 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((154283930356517088004035777872876934940504072104386408541432672244871886926171530259440677649708405642461621463170029706272049351799158559471274199 : ℚ) / 171798691840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((663736027834306152246203034001898362875504221746682774704350516796065990923478751908653059140999730427604536214991697439137901353490429015622956257560484674012096621407 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((137807117334146965579044617971540522321995041745924453366402497812202280758993063510842769591264185031189827820510659417576849210490482638927191591368086039645379727301 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((3108430282297386062763473082000671560322366652424130226133332403651349157406333787381800112727196893919674782982742725536993594927996064220672298795499 : ℚ) / 3435973836800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((1089705496532165623851273673900198883428679896112505096974029938506865410122339188077264591614570451165991809257016145779443400940267318827319957751734597310747568821958754051 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((71314933210478466018629869094228058630108203400664885061493401538795182802798906242937084300652180344931018678433033188142733514729395255611471594050668616191474245378529093 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((62594084723246616759739710106494558849588578766983659358919449280683880592655848157827043908111309113191838116560271710267317218748454396990792659774626799 : ℚ) / 68719476736000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((6980539149380297242434637403574358249380769764714685989694671828003576985468579671891737766289794792643567111765140220320969870157179139072182305764157823378632665266567018654453 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((59012912206896945046971235817152303067229337214194349633447547687880341652701828356680908863821470588696330345922644002310223701253842460656408529983001464089031377945003853376539 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((1259838578689498980023892318701554745046156011521361413671152620998069250963257016399523548125589591725800564617793641253709099307814845678124813530445295768099 : ℚ) / 1374389534720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((11435081222749873931508959480686233702355673747708649389391570745651076419740059549177806193908244367778267497436423350550076616019912664929861490528208154750416412804925832995281318179 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((6100247393159594866209523231606651675764587193182660808508451789080822279233765236696668590295918243365163042573905527628733506399087132824151719082493935461456395507391283854776615893 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((25345573265673600425426810252037775287108163571460979797064225165284893062263869463687489873496650954864196358917358885085613866155445429026612137832857476159219399 : ℚ) / 27487790694400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((73097612748403449042378758839736271762043925323225608749527810866784038640834778663092566785435309773400360183542373531620880852536491493545669927988038380896280028366214688202041133534987 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((315087203345160985325294146936719374445446626617355369860420359603524038906034398643954057879217790054212299891703141290023631782473285658589218857499928076200020768035958188790673924917111 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((509694205753387601555906778523358435644209766949891783184898074815992785157396622840419748124260869506915336108113528509986064910972984968226673589612267661653561980699 : ℚ) / 549755813888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((119504036438925135317369088722995501516421914434714607789163374917775679701864566315259501252279659783646163125838375862089431740252519639686581279256562454854296650205192860872495013062425287491 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((6505470686857436821444059055558683910965226000113674149610992119056128021445362322560239261860137346499907083157053544596280091369033918579081273733860429398671319139967509563743578393638467789 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((10245924144034613536697012665165326104982366851729926237340778897133881075228474243738689709671802520648823700557831096665249399900105791890807022799339017540583262601051999 : ℚ) / 10995116277760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((762461853805536861749326772364060780794861495037488955784152110741527425664145643309376981039436171552942655614418460904464728087239650031346456319982766523390737343020736732188453666609463815354273 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((6711125804644651668791819993136986428875594984909297750599855013783816808309313454609874161169540233925437150752503177847990376000959274153445591516684557372268181863875950163036397102047523171462977 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((205891683462401547749770833851256763489275242494201350564509906155300709987847696832157236260572378938653652024131999338736829027531878414149982133370438967026447593902273433299 : ℚ) / 219902325555200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((1244254679409017226686502357282268977801876375265280679484484899120495098202812556864275246192134461509503583165045329483486418734614406100796320999720832159915471564386435455294019131179288604434329795939 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((691841753049498521155390610707125166250691446101032890031917729347652190133682718059398191128391876648294769520948649711445790397708370767561324200839136710573310302601164714737463870330861939417171461807 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((4136033493326576144468464363852352734012936309884059456906899755010278577482739778458172475308964058531761946503292519633717439643873658223018815876160579122361596453566415476124599 : ℚ) / 4398046511104000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((7924914364706061405783442978696073185947457899048733305236933031827105074171371330784605131886955816491838887529443048879799960683357846234673561948692126256210543715972777427765516544976005627296759832003767 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((17817659731952438566582517534381708700324492521889163225988529783749311669286343801776459937453735851962565660307154532660894123249832793052440250748322458692374093336469859765207124063327675363871738302179141 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((83061024776624396477704752068402848478775921931141795903615932318447219677504716596946283460752936858602480161558073409670149838780081282428674875700078990167284215278145535819006125899 : ℚ) / 87960930222080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((12911341707232785684597607758444993021864473158835575291201447399352971622685479937759696062775973895551360523484334626576003015344439388361450713375946706318896816576417746053967737319349075936605929726164107974531 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((1834198278609638671910845841232951429964617837872569215869813885626553920214320937703830118894158953358952657444530156178705233027472831186798406421676672586235141277576056037566206522707076399555029722192496396279 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((1667585472706134758529556568431201669401588516034282725193521550287281455189015705079492446999540672192724981501297530834241472135026300062698648850467177195118382109916599665351233560437199 : ℚ) / 1759218604441600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((82106252592128886179571717443868776500990086033479605210155060628631723804035421899581525403979746279617872675222152814910029234822229712904545411086347368062903735891100181877756368315923157609378070469304410733794893 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((150946876295767855847966888405495976085104760795074175701886454578786353055602694415924190830103096255946298985268086551302355587873204102198082317774585714965537854563586637451353700958590701878019019281967231755284091 : ℚ) / 400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((33470740892247064519261237386231902419479106838357121243844046511922450493489782700691588251338410110676149879055765124131149770397126837472527432152586680725908863837550330341733418813736058499 : ℚ) / 35184372088832000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((133568690834237252268695050076618944693601942090050058442757175467226612977286600573167312771135014241370472056584223855344509296335777360163513917351739533847287000344487034898441944792100709405133053542318374477701618248099 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((77584651445685884815898467543778074435693009869097351544873192218582268583271758940152877814438355182349470917806280600040475695378393577639277862598889950402422143465730951268644608686760233794693056016444668855408198415241 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((671640824769305121574704400359922807146678776984116524381127513819461746678752426285633391888279607479754678888221863586376631856196668987573735508685523516255221662626028727720756665235678029989799 : ℚ) / 703687441776640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((848186805551048409623988723290979915453004649433217592599167740644143193910668543559649781052966380852886541707154823806723941820909341636110508127586562722816724158450321396284737143428290478256582614983640822802467649471515747 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((3984958430669573498229529723302173705266711511954136764220313513294178273551684975431591651137639399750434706540896175839665452224327698155260912919345253958456734455502078427367102703572947177924968736149845935838111044116402333 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((13474445050878630438568546991130916416450039808379963122451465635937754124639349123967630061702716939478892249888637070928829392342733906736616427747927975277488900312769363237105870396572414838839231099 : ℚ) / 14073748835532800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((1377941098080385448330381671032444794985401416250441550778861550951531596998623134666928354673548965035945535398061820375305580332176507820775166438410590773263585147973432155939609715853750818743907036092070445375031432782625787999171 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((409073467590848849465338481828265309567206770302037004641547679641009146763168544103152421231713508126036898511708042883964099435442080766470385937421313950877212496683511403826684340971728921392475166992892316585949921494443901499611 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((270267396633838375031670397281139267904032194456513690352964858857671939884880467967318649783902509485194763965167401863440038466201466789881463815314001065664319924749099861897116882286300729901132460782399 : ℚ) / 281474976710656000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((8738872098776905293996281852633309941301544214810255432069058335597591654050139558125194816323261219416435413040416898074381600256260742187339023216623750954180198563109612399428282968061629803243828790328087058451867647331569921640728313 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((83929036071438113522550381045411889755630535266723731132539044834137581099848533218112259251960332225764063258182645516404884256867717345223227695750858985941132597240650688873814000579424960848692012862433904829881212313539728669267007373 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((5419906579196553595467268099554585449073306068531262523290795825497322947787149631456826069608760829882627280912595582248192159356433630437573254810187133928988446912732916517337982815636109949881078149091643699 : ℚ) / 5629499534213120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((14179409833541447196260333039585856812027804466704449759317293892256009339086847008334474413337820166830620951670232249618512292846103513923356172346298897621443460027600754344406607808218231431140833015249745353835394278092919144409604789810659 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((1720802231315055107641429724050200890865754382991874187407420368882410825001656689124607539028285273954293896754593434701891641343053743056255982083852382144375323932770594266405450914815981684002664523023816916312404631621854949049494348772679 : ℚ) / 4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((108670392832497591668833380729770302483119896787603140448061172732625436446567485257874104327753436279635012780346449983623441572124665322813057438205309591606012945715018271790737616635210892172726042466162828814999 : ℚ) / 112589990684262400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((89819556779867628019721412778260639540059527353948702820804047548220267436046368383348252144420475308918557052551487786151452575009148590737647845372264459975144632068446056664201457116144851213316067565965376492298763610493830770847896075394278927 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((27545606139388399505411929361779005712122076170121195512983202181434750979512596223083277062461575510894980108485771485731553686088844830081222283850769055365853935076224140926265071080416602750448777134162561371658713704097053106886954715652572379 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((2178499414259394319398853053027434426736825189824966329519191991272828286987258541807503625033317011865454374005258961143741980840303366201926987151877494672624048097816556700758584168695078894522149720159711061669296299 : ℚ) / 2251799813685248000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((145574337822327254991045063030006477896781746705641511139883536178618361901397942271418419792172779968358279640919851121169872364730986425790354030151880063585566307207993095359791654043923134821210381468945352225331202712392853066227586340459619951505411 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((5640290185058299962248991934020412968817849905451007842245742214598020037109228226131390685911956496011480731945139748711388617048863386397026999549916144494263247665001551780716696772669532635945560151557699512741645247655496681029459390685239135556313 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((43665205504042070319077950944666051214405367874916695328338409428793161794948721990342125291748061438895862248272347832349118783694513251342236586727261027872742323477267426860886282538766670406458721916706756564277510087599 : ℚ) / 45035996273704960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((921150611911365984586913046727507378056141307991857080118879035280491086240681818593043953321598936514532655152924877121205523069677065507345482959636487324122374358565409575229508224812683735968872939760017606778439931905446762302317123109790804004925786533 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((9233444553584766798380933216940273620593104200542605229245932965990886065393760309607800267083135628591892589723069190328753758294273441798708230814948949746906563623435698993108376494229184701477145762221590918787705243287185520250304328806408230006997630131 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((875084767290633500077076760616199823760594784628817119335256594727860918727336049941388085080980496968791519904941176812760870373871092313351166408386508482248154191348378149725434369757475503271184558564333054508553716148188899 : ℚ) / 900719925474099200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((1491414743725999064172197128982719339945856132933274494513466078213272930409394062553758831523347285680719376489407073209638415282710129414342896977926409724710811483309089788643942934893641538169653664079865769697474588398719683896685218767830742375380552803459619 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((944136709058614684821164866173480674465018997013375010039475505646611667194080681932606197286671426521443918077124442875192365054496597812937004319923584993467953598774678095664136952446094943062306326173825526991344043589732811054498661814509896983589008095857469 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((17534995416292991945741412500283552904146883067343508948688633578005727041119911469953898579099416273813370213742304947575441036861763297351980163003236095126522731532406019778015348148834549386674422429711592452364463045687280600199 : ℚ) / 18014398509481984000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((9427963027126168151994478084899711510347684589020181086425502452963127565835616768179583043898845739749387801254085417477279688794959405265612543804070230206747811623893281097103700089959114528986699991838251370648357769520694666484865284637369026177475200241322021307 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((1929614800856003585658506709479571237720460431274139227136116259144908926211446136637334264563581347443779504282712715645848784743232445803044209771232703367133992682147085650615968448806277555919021670253073333916709188534336490483496096141273650628073949478927204411 : ℚ) / 4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((351322652943912339593310155167802722860450860242390960849426136542285101395983464399607857327738183736583836367194844824608322830351835423779381028323518214961101602387524975868665025731354908080198373858036490451667823417397834504321499 : ℚ) / 360287970189639680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((15250287312566443820728810376861185940997144254207741379686251281594269019577622279082592936094972128099176338070131917000369896189413918415337405943552942827069549969366472603620837224309758427838363711397437922150548866471044885478996019055865126234668591267424599931997251 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((4926708455396825122451127427469649263176062239504121263025395852211248152700388536408669654731984722749337382817580085914256173435329884202163823544016896478320446322383534945610593703155365736187762681372421488652198484572323813137342810915647104604607581668262095946803637 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((7038099005980446607054493211793078720213291537392953358845118179477273681206286767737066539886031774057854323902910793065000245250409674260098204610678114137987561066249104573719904646202068136007789789519140407936639965728756903065316352799 : ℚ) / 7205759403792793600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((96318042330899515518456190470127114411913514371555840118398347134839643956780656343995098517825161858744803975716904897211584140821820734931177746969717348123890651681028124732682882052997630228249447138664277857409656051074220732483775449480674517242339935239418654292448681553 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((1005725670586860865826122385700228821400326687591752759775260301265227416081523651625797793894182241682049571002602905464365340650842911265024348568000675124724698303191718933166852217993655472048335676717345148837123612630666565075483242553446625274526653930947430030521726343129 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((140979770976367170884926077553742365146708765040785620763762555074404495112238768843450881362408680206655933711308334741108569586427911318338096524424291412494505379499924504633135936788624876211481676853797444768823103999093482844224481113694099 : ℚ) / 144115188075855872000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((155666412690523000708205779743187221876969305451885834650540878246459311245452490991217866205335949575484397577298744933362566940238196593873013921845110730473312069251006419310930203307367114151322171777167033702324865466229010387918682674954632885470525114471758486468677538743610979 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((102594633135020432614198318821723839659744392360643088333889920882696607021208618954569452915509108022819521864443983369245916626244201721307798825863602921308207604690404662539959512900230263276860574410256861896033525712639146198563683566183310746216767308163943107943093332638512663 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((2823668326339579240447002576332535970608600615027731893903123542446438463093977216141374932358404728544672616335177167993471359835788369564240743103258673705059745102028088161144275153884073810030918838842866014621760867887047222669842021307193345399 : ℚ) / 2882303761517117440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((982353406200511240035515137685377677450070428547506010250962942406477116220889345229584042163405720231917197443913116698183207442895755429887378693244214698063492220005766877827479232354007555633669896086671289604551894303937464272075008833438728590400119091499438080059374276119864790887 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((2614978856220794115277724515518187790152224433202483171556745688558148108993957750034841587136646695706591855502962692838065062715093872691114675000970611781509340007921464772329976896922695553359724723570126477128928740378305884224890547063040089585409543512704732369750116202577555659883 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((56549533957087206930159395179994755186351440101633614147882313367290845698320467919059852610034526828513922598084148218645907900289078299220866136774040456958322293153027276701559089652786064321388213205200437339441549990355670111148715640465822752306699 : ℚ) / 57646075230342348800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((1586403139531689739634724204675236403538275823952535243534341233493603322021875576891709143463149026999027377324760560789842365518652672334587777901037259951283769436242916784109052843461226629679233882534545839479780737780035165549211778734688522416828310956783839553906897275976436872108738691 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((53292501148602159193765009751371453936546631134107651803915257704801548352718158561866223549610857724447838626208843712006657285536349356998373177983185754622103292808414846155624984638999376076289255373233141970424496040913122861598830468700499770344125500931472194665600491584847811104328541 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((1132415086255702567892110849261081916739958281340650218179547142281706105404291070554338303660255686220038866506771655836897123643306053273729417623811330585577585204254763101595856535596752188874280975150453378684896426369641386748592131192351351290887577999 : ℚ) / 1152921504606846976000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((10003673588605980123454165547931226772620083469682088562396715380859927453987163561531101087329717879439992907692694055664202584932114101064908242144296268683588600146604085413768127204748582322484665864560272190479384382066702026804479833607433956906938734323829797437774878646877589416892454405373 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((108551131418450103428633363987182676138890597539413537205391963681487727490148611479889058007144425131366213926749492008111566294287234026976827283233739388176051700038771531526233950528121792264074086769905232032118257497490861242511858172076282337204816292006353541741267873046739220623790810048767 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((22674939562552187943974364992031492924953959819351499730175711107810185877165647310436680616750441588000946842543136735805813109253466502272013838982895693280886420904768324762944113072194862684137928516288628634786248069538663573585421445428162620490888596159299 : ℚ) / 23058430092136939520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((16143299830460837961016768098716097388696784211135173174209211534166582986344778241670625845684722093211417993996909008789347162396642745669264103347247799184139548272759276676655877056661284048193062642113395543266215855355684563457283622790741936498069184774143138592932411186936485093735079088453720739 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((11049657520784160893033970315331258542435446851274816766517189225219920738183922110779812329530967530305768854071301256668418334147818039133345786563864217257550849016890291167773644884904829543938394178787697510841565248158118078222066854196260564216659159658385039165729630014564494509724667919948008177 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((453996945448974351176744599715980949189564002581692396454015973427158286088874770352476364213850008137205706902399200096304510956149077058988930802819132360045856957340072441391817858563116127056063401183113644099137625148442547489620966450952069165800107636775050599 : ℚ) / 461168601842738790400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((101727525932199527798921069426730058348137373789931334078090962903779549883711215873390507659336887975584787889056094094673978910524956847847529643372712192572140619665744930250329062959263508386951927274261199299645320506301730368923945368506512843490756905851909853069054620952352683945914672754475701755667 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((562102219541032449294584029380485195282936878167837121401785845391441808564847882342177917801804742007335761104314573073301290799538807414960371069438630757345905209389223137522206339701603541528204650332375456276312215079598508218470049577303706282386400815350361129054753952972249229704137057489123447023337 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((9089254890634987030085900759288559730794036412280229506086552719061287108148047080361660487163209002173883924781767441000990659390943890080151994943520594265217570959216694726468385772988834692075441665525408258297972727901024080603401693599254645469627812915330221251899 : ℚ) / 9223372036854775808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((164052971006000194757690841403412464219666002238978145792676233796352933265827198479678915456835443897567942189469084289250168632335411259784183416014267075118603563560763582697142864196710633394531217992694176995140493627507867398201545268659181745756628957109863746251852123254364207984209119000708612013801153731 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((57160960794464106300444958092876502388757354114380356523147635936201308024821575881441753364077581097242138891596180103996939051364444762004292741118743238974854837926879366774243203591484503745888575503451239927313673276022620341133249513731687321688983356322679107041370144043545026327930937834725163247175790223 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((181959315985639246224228430099455355525579274946052571993324622399165130209476628449843412770439171549653803277343832914159526321270041688388922457438778633353833794508311408079685282340664197576502834586990659838430387984477051331364215071999661124927509729329590467631763199 : ℚ) / 184467440737095516160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((1033130296878639151483394096518936720670308384986581292029620080977185135506994423464286327682903261618918298295450893595503506072723856224871523787130200338231112091159236970155464541327887669666610954207476486581861272956831926230348896601164103801039172104107797273906252558293806566380070697844179357104080376429993 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((2324005266508220427339045742624480051212895252070532509622521616085404390617968464147537386316748328688194955756348641530858563920642556999376596323924709622095575959849046134016623231287560574042483442339116645112490562341709281866547314479866805552696175712375651760655352842027159950052271021001439038768423816579489 : ℚ) / 4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((3642444373764926619131135871289914603683858020766129148847163763486787100047422428640521662219982947150075775089607019327697301734071049614561238876562599222350045791099931642498194465052761158878179509611312329638486685697705336947842186061465662697269359448192671335181603584499 : ℚ) / 3689348814741910323200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((1665087259892083275932733250554643285020723081582326669552607025783172384060924355592418820969252213094799226512186402100632680322859321689635579915490355950332407240226435233836825161744203387800817714167893423834470744847378354194239609881969684794289950907861570466444840905218109540397768726612914574759745449761553884899 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((1180547923897072392101669464503609103742840175521423329006973488056542585501122584627136200972315582062975386741306365071882485859666791890136507065888888936674495593815708839347842719082441613233742054545650323750410937348358728111176355725382667274389819826455054101684402737194708377788878804681226790045584009822058187211 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((72909816344127634214208171928992693003491828846347381212590809540966405557986846838006395605175901094653567069950740868447267239728862698841909728230597168057168206339359821646358734690951686432180835009241151876569339509232787506261596721535469358101634291040651146639231168633715799 : ℚ) / 73786976294838206464000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((10479853364029807630192035032962769270704344677363870438009165840721970216789301028750981179579757532127619540625845420482477606237002995818947596354713559234591207060209304211980500185261885961082021206406634757737050375681564103921627394110376685358458824839707346810575382765164846651650735364527393754098144326917829114003647 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((14985612182720049414799609296284458309621322661041795602242275834705967412409078718956186569119998482713092164618156300880729758806769671758294838092729204322254436458758024690846144824272204443239256277619780570507323453469958742354170685435961986576455597217497227809767556085011902996257707212907332970927973592607161746408447 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((1459335757658525717636643023244092351858300691255542376056660729225612750339912022717557604212394526371116357775148804980832344650169461331042553827640397639837102626752368024608554697455487487968213795507818781243723218162162359154598120289434812465858662876751217093300262084619119157099 : ℚ) / 1475739525896764129280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((16880866889649595126214841275166356297710694799069386598178319167305910418549731298630686603601253913101589930486125500603667354247095088016183211976493098843839191108366048424340196647401263909936312968651067068838483339429073092882980462800064500683785067926907067929535075810143020970036287268444185624060384865227431134139099226371 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((1521125373369752481678733437955380190997593150106231375523279746403726065341865161545306052070979102399793905365940490045971095419178118756014734348660188453958390617503894493844589291825412614691824544994603864795871863201138375306569339199814355715544084893898385049346349990576155593615475016091222232880059785246976205851843545119 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((29208023648111986049457581177687771072102081227169897974635612297248184044106694736841044756375990037666247006753057801946545677302819096351826799130703076262593656222896034428204581397115071512493566189791719028038867902850598278550139447532720427924022854458124510861808201244462147356908399 : ℚ) / 29514790517935282585600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((106189248772215407013160562517659161900994725243861859930534743207407648686555931799429454816200724043712443888139780298348323166536345316564370502906732105319682459279172220912221235764514063831856870173761497850741306236982584850543178692603807898373754143071217792701867621262932147197166241195950283772807273966456198994028986247907413 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((1234697008656268065148295596299347712683344539717460286357131887800560289133984666629919977289208513391507656815661230205327865313147887115917170257484248943175086387920916483948396246155767997975760919626721221777028377915448712168811189414585737619217044047524602432395884662480585547679521876799679104417420015362522339039098909313887563 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((584558963126140183189600625603939006819381021029304262023660585570838289808839298273664377988987389694396485273288933954202350711240019920875512970543278229186763965024378739841853876707448952355142181315294937543354868651209038407166157808309404722607151401221386477626675171472686617721543969699 : ℚ) / 590295810358705651712000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((170961055602027137367644128598345827604684049257795702755960839696518671734870761392149542866151560855856195075815278497681412652538930430218785343659467506992489116010571855586805583095095189475220142919859993785661277317187734347639827698467012483041081507382172678530480510913555906529467850616409223856067850184746547255401080768437802439459 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((25044695789146920701876753255355862685906074976234048210692875448268674345353070929526782157630430587896134334164286751407409809925430712425103182383513304129563077576814656497826777142713515594941683469516550192233400045334310599741508890758223349969688867951807930700197694793206179734757156767849838002663139063713773609393274809568748751393 : ℚ) / 40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((11698631427077906207402609299419263366529244474269019004104476610760246857715103717015797532772053174674908671095776353877538160650899612540292968062129846164021672909920906813782509348306002857993513932777330626998279398646260227252414317173194177717476338354241148518096452381710712438010593777340999 : ℚ) / 11805916207174113034240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((1074902764052484179795921826707866050570120114714104546234481688205403069711734577943318806526808420004358147845344003608022690925292267278252562696737775530388647265019914729305048339923207675170666592574364938228142120634812061014100885274863226550476259276845902579187408080079120304049532312286341678327952204130361748632837821557437866749342827 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((6347549360802138625660513008083244033496296458118769237098383431413767140403574793018713310586909528824108759491402563644559333145456568721669934917722906045102685729770556679751647286183393793054137261122383121132407453619017458412835839597126266584556512279008269392817619410076945911024744775071126224577822210393219949533447646034029067670139919 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((234111991470903096816113956508439644217463400913304924395757817097827376486130154611912429660370166419595467058162113593863841142332473654116018795729890253113369305088430878324546707322670559447336704056868860055494823034083712509847400145455904317494525003562663718436921755990372033303236114230054022299 : ℚ) / 236118324143482260684800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((1729739438388503874303278105095057609270120467518259475950262775133920967126328048651771353558069774699398400941182706737468187405432091800599806705820668018544480401737853277685031133351196033016670249437511042540949428133610378257092101798298065503234981531077232344773572921492132302859788643250292595555079974511620681130665243832159211272240469900611 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((643259504063074046953645117092598871219140883475763715270338847611741374705462949315774971942618238810893902959836143294590446342253898560184925582032679813804139094735554018856424097457544344062005111438206082038225184726684198136460375343019548003014971931332188498117816515043504665503694684839713078859909190350669813800646760460511921560122016286569 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((4684846055559742270187702300664329786510783060479715391125066937546469767667120021397374347078582482212854829454689686318847693202759589805623667498944677623473119374458745855547347973641262132224643702567504551897808685560399507646656230120170866641465112091625374198488873758775947394803818572216240271013599 : ℚ) / 4722366482869645213696000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((10870658157100577511323080070709958544745358021366881345567484691108989175248559546294600734503869646032056236968786802279761141554108025073860723611493036219561279329160501768208620771384139471487986763836348045182993134107613439227119287241203587693852970097011144385392119974251384034298104132364014682979893633327760694486513702295279670364207994240869633 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((130325944377715727173284669606946314960852031467193289989579772369170000089403663783781370652857939125240915809363473515818170380611710773044213658487745762553393854702842300542659754449982046254060599207962486871605449889972113593246290261754911728393937813540033054274991101978538082565425449024219778307685621109955394299309789089537742597534493801099665521 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((93745660146270409327371324724723631337538154014031157529429876799056531125142811520152297664716570999862598165632151823848770710584807088954968205897764416236570805421753006244590954455065243134733061881714902625040920228665031192500118159477315377062039061225486122885940428162868992230226211119015909308225314899 : ℚ) / 94447329657392904273920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((17485515588560823360274015177381489828306784629585714050168612333325557795427852238594271605375838960959095097373274795946656322236805935806296241072612311530169098670703530634112058599050723252420092986372228200698368519704805421178282844598559650630072396865549398848894970552547190498665839941068742516370418619697351157471828003032491315488573717582084161560419 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((13197288959606842515959247138422339479254116499814983316142668671531743352441309690768470139917487326897065864436879236147942333839998501885896922109956107674995744113491422127972732922896908753245435053699932559312989845843177981642311060623403286452764800921165178059000485399964829558653636010384521863422274452112501139951694831619698547002011414531177349088639 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((1875824671620356307482993223677056629643301018216396676957868126019156188571295718238368118627864594268430448295486871257795861058646477370546860418494092348040110632192202969780095439264175111862642990249950393990890249196264748330944709700385274866437192483977815984089971947073813023697460374136716519973121613926199 : ℚ) / 1888946593147858085478400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((109842972723915580628744103174014560874085050287489310162471334921231046621026831556164405404192810692969870780315095265989001675530778419668801027982573517994146392099100692290933965285623270950809208229435569050812861320825217475375036442778173166962070213016196785164178295595899621403882953376512254763621224595894111071643070535167264175628839992069239713699101207 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((66796276396912171862245079636269132939689178875382119079834142818188478619764557013999253306339246340577943542824434482207698805908729593325352021935878162473028208575586617331248076268426191634396309419084825828440577991774658250167923574520724711638708544099922850391174000520889326656789484764232324387420629286610904625567151307519798649338744363587050496978490653 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((37533538808471350959275897875984636030959372341664834255789091824684239882471801226775722186459695777413917813573899979392040397657747773306596836686258021000698108932626387737857564809679338766943286560664322318023638550219347058536997016106905025277241936642869136718466565382227377356166206456730735640017347302033847499 : ℚ) / 37778931862957161709568000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((176612250553875256134661847493546642340268979468348740040154031083656224972714141761954601863482257553906585253133889536355456176720814885261106817134967073583275049116875467885171687565400029907667143455743013369823964681579633495296523838327923089864769471944957227882660188302174638062380702629195139217843020704289127185533022220412885175161053383785636214012923579480451 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((33796198150613316157643107399956635879964236234372856719029020549962708543498498218940782591325951487096546115354978255185918848318697438657082983964440742848066530260676568656454848561419063565707405924093308555669869389347692089647506601133031109846520217972883083196210084950470519874651136621955981892622665520422573609000123510962694954342010509087365873448372551553451 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((750989541747204087350147398178788678414971222161474065417511806213419970042105154741932780608982770733417677031645503514610547476597541108606667442869711250734055335149046077085674319505813314280606401970983491669360064527652009341700381198215230877709701457158295725772043239213034183937664226947321487203964411895334982078799 : ℚ) / 755578637259143234191360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((1109040867768384467062739290346093029848162101385186950096802372371949885243540657689700016016351780870656411317467935823683320326014378328580363319374331176039970813856484426364758927408862793939690188062381833512978474583699906906783880306507316132563928564902890966013560168425383930120023591602931252625518943569806785428834848967920597126617496458509154480686775918653428653 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((13674950768927847324968188691367235165230390748172190759432179552919216378446165289919458224379000606552668999932294991373833235346554612381233184312360297033202052825606764505522513036436222126893513681768463078106712483607138179480343081260659175441466094031555019107268499547973812943555837190528351823441116066686585234895033763307953053673188407494212773743617820472208525719 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((15025752070014090698749683133341527075038376825641726497372888287997166859757408498828884930168586795485643978168802561226731848359850616272053287849106470099977568822622310687579195449078214790361620323259362277708702566731620226699138828787823032644049126950317288367662980616522952273818258708141859132201338466854659499855620099 : ℚ) / 15111572745182864683827200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((1782525029654677667883454663472540900267313910171379984078763694747492062501230250401996530678959421015110107448334582293923986244467680748675968854031586712748553386481867758704155294235783453487233519300096320632321235998839610414420304954499350049456648175573111948945713875647170832411149137870684003081125947719996698446319420149551874686380791562643164689760466603670016326863779 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((1382866345559523263263949481243624563283748021072282329213092574087727433048263011717423980092320746185892977429222443252661185818693225378312169210204674443056248645261334767868967883406174998079437924445792681727518510486171809818327815762827257967027295297032530110416828300102967004532786587671957938965639872082593854714340181399610544209150956680296260951509000781613384970617433 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((300626522457326051381609357076619897830292685016325927227370383873835017444323296336598977079082741662377028035734776697501112296177566374903668536066140097339680514551859832168418534093211694794552661665273333955430446700448029859500595237161078533476362723097883609763665400509595730472675256100960907631297230668648987306799951471399 : ℚ) / 302231454903657293676544000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((11189437858495647722783494993923822886185800822374446012414592596966613635442257975297444046821172579408066498773253416106133625169476485237492677709513543330107786149713760480627088459618668944340810139501578507190077474287842964209232511896339127218139968580343601197186579715345720127749567471595669022616858141301697300196078564900564020694109667451527695515177577100997891756166926787 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((69898072702889862256321409598820536666580865235177762381868448615752337155135079216127014266398904446709625421502215437212484089538736327882540496137600845974126349766861714946640645595660465472009518203171986508447645471439263632342111453979835644249032597762750394322903215414563579155587617059648191120364089057970928006104851862359791413063796377190125175285137932285623196847142874421 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((6014615256394305311373307242689868709324303502490311165079053548824588661226289964790737470355926351828112801296276059019968301050816668777073505292972885960349365302634330721381595006077151904352929325802276618300504783745078606402520631530149329654541459284653521386190306654929949755569499964344069933612889510734404711624465892466632699 : ℚ) / 6044629098073145873530880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((17978289082425752104489994232234187170448488499725115089764275946930686973299144629859485581246479884333592688417081469724810823134296770612435008142395653443728557880097655165856571967567251413195723476271218494024183657178706188519881194608039940164564045138966861404853508967625335898604020179370550514572248283708251343318934404083236258093740517924600547208424268621138135188566966372029891 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((56511218432179805659853128644509685855979206025387008723053176488507842685496687955159818104595602665881075394081122409887678321326453817246222183276152219419447172959331886271945847568376597359482990313911982031804905369291053820011209280126092066116783847561190347573655246316115500451745505656418101034897477816181669529233214965351053212708247172112646204713187463424026185340215749321663 : ℚ) / 80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((120331293108226920117708831865543234733073799800071309098143380416568632553592848631551581433126178705537537497041658579732427197951322522800051622483885940344493480524564618820557208208648817763304131321828375038837739960816715018333538330245322613869579830082305503443144924753844990378905218833198451828494646740244102512089136655018498103999 : ℚ) / 120892581961462917470617600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((112818114128583780858939656296807946911638124126497812258816287718671420167726544832744197671263082168348447403814800390858340479574600592295880674065715668861082073659719254583843532368283766320538642578773996256992980933115738871433710051491341978390122706454836891924354246611503484725303449072212660607530912361508546056861600792615341553752947906311146673890694050519547627519918525641464976473 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((1427323740664231425700670607605312400472755726408665294783626120564979741379787820544315071409993623352896658995318277122806128257227080316823976311099127135356329094029576866747801594964476840518023191813764554013520194010487241204774238912427806073490381439459982539171088894939616343681104331911862303263774383744178262101567526146965981668426474846750005205835477785844556644605112443731751610557 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((2407354976384891962915605127117524032743213130061133551444379357170249997384739862258646124380892667972257488732176057099576121028887682498883765392071150970382372579289882936563240350709941540991550559849512441601304575007233387557855500313917778201975012402369195219890253237821655165075906497399644247644678388689304961078578944585500933042885299 : ℚ) / 2417851639229258349412352000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((181210086073288536896997841201244146113916868920814133981201463305705927170785695537738035544588828287406450962467739763322633791259295413778141165573882804178963497448019423627806047827400292884811178251117387718691752390350631578823921922098704007190678827583099090741170329339615884243893579443215593803214591363750955572810137180931889680505917610368137088658281946673345115371348079442755482881005539 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((144159196570952915520063069184934672958454089379433516450389642098538796918363374013568026469953587001483408592013846596808125311156813612319378133478030639646004966290212128842084545220346979591448536834216336822645553452021164141925473556702265562247536868645636602919432262569001082026946440163887081912784470622846749369507392327538837974857398837053020966717669601848318076240121451014765346680842547 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((48160734692732671194371376730224816936330828745273258545561338358440845201092020164098941172047073783749187296780424443819173039361228550411625296597122594297120749605300100796669157798626616758082987019745732170385996857210271580719455711370576370155134706936706319807167625800502773242084527407870747075203130546878692077130504842693452948834997976599 : ℚ) / 48357032784585166988247040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((1136793667538270443826230775987849120287502926020380975284504603910922289919142133188133368572269619656441457350434882951895687713441909356519745318336128116909464368290263524087075033146877319021036398998561579105312187662163351459659126329220103036320971706964920480629467113811978229562447752231689122031115639511363680652298138200583276735834550926844031601411070688620593333490238533054053528267209587567 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((909741304171600824621686847024941760997099491016946639840802528659584371424983531859599548204391000405329511889661813385671114352814277187252972582501818599377592562575265689788382789836346145215867773753329309468682614912011675793857049696645556514456495877716903506777870683443295019416753335090420748793037601770191882736288356254071834611123396194507080641521040813202245921925674254815565838282016895049 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((963469685075969815923672021191934301526322828365355208060542588641202246105621869088814298858452326829893551637090717523862355009094335121247804671662789635950455138368717184998509919992116359992909940256264937318388527226689288831034541258341148698271174154423344886713841770095202362400222747054590841053373744357178420534417571063210263596163297160377899 : ℚ) / 967140655691703339764940800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((1825404509891145436219757127439258673138094046144865527652546090368293079121866335476835831246350319444748829523374778173020890160769935965289875731165585273495739297151564907027343803016581121298799935163006578890284701630817295092441470295054110627577803171580095438378594998841816021351021321146664860528851397345009696883082456981838756672474541141621739226321095823381894827286523082048635996137435831043772931 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((45915853596797996806952123561093538597874901437851317734525557802091370230325395111588913529984288792722200503485760611159370824432259142714308929436714023492738568033856057899492219793309245382524449636442086614642905693739245229187719706552894856829365856489380055394012274030916009213197810661292322762511990462783797077178802285909578589008686825437372363963804362079839845183023392380231675916637881152270243 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((19274162292349234165943248567510363372843763213260507745940206950179123204421234573829916202951916964045839309165233508413749901025073161102455195164765828981909461542633380076657134013772568048227408792732410592791183847666316390429176956072237821806369227861870972726435554942550379379246565592667903318539142393223593642414142996453095139511849820196227089199 : ℚ) / 19342813113834066795298816000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((11448201592365322696036052290093271600258831233497635543632084647206425569329397697472186187027493226736905457872436213193766120280091949157027935495747625470152536732089265165580288607561046695406757988387419577272447231440636223823823500313580712479569417982000776971964879932562939490646472048217288573648970112620589389943905913652896849406584900393929226044280649355936623722493629259594267328416853094469379385093 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((29655142122897810601754671320749878814509742745205782436351950906364291265073300990282689957135833642522056379722183504472464068999255347160333240077331657403866094149367373470050630645896936697062074222173283331746740676851416304316861987932174766743701525693268353343290666144216827211466372291667990143977518398677270284432686199089376232439557651764366860068773497432396631660027022800198947962532758790705823462087 : ℚ) / 40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((385572423264093480904397853445011305435551215851184755356827810175299783045881507765193262911403799144621240920699031840845536899069893185777014604776285767790688840308786840813565063191560795069900771832888810495787929135207782817416038255506919505600910930244849060957071312980634644771290023148482459960000501895674424706786888176669332204011103487489642795110499 : ℚ) / 386856262276681335905976320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((18378003790453424069713463171986233694794195694082162860883740821007601052314783043546115929640043176251845689774639972559496940397082787672605396776357926582015971079633659236641815882610058586944291555730224194205399730894509964154334172857146934991966685210319832420950226715164462465986922434934759822574548527467284132156713350114013688865853250414899000470604029062891921381790341885085386811299593974835845950631281699 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((14959371421087801328830049404477494535189696569962409128038242999715434702001455367593495534381852073600163825760185381989995224737343253020501238997684440854273293986466502359529757164332833872903841038155127750047061671833789683529528357094938572518461298601405074772727070466059522383143391303923712261202498326225502350907921942848757108473496518329219292870295929419065467485911636077933517612184835511795405789961927181 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((7713116172159221241735007496955156422950243287633006109928036878088281242741030076716879209706162447803561826457992594455652385549506072467215950123921320143453672002614622710054480246745378428602214334046853645081730062757520746468497331416234901674242635306508922288958190624050848491867894722899770483711969385951007416441621595791893181547211646319543809911361441799 : ℚ) / 7737125245533626718119526400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((115229748012814842095940037843963415285079148100328563899890731530841639072276933077995136329962864300876063425965959816571362684316643746964254751499981484705762727450220400751704912226356741248910910334277065464024305065087040862617791252188706196888085987227367481243204205501492592465147426485817167102818861732235715821038439152157305363071527529923946968019734900244874431190518956899905973301664045107923532491659229771547 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((754424658283937044987660797123814980662397925094020611326390872621281991252639487695711300335537697577365892488200566593790265226890580762215560651849246920510506745013771293738913981106108232517657442710196957137146105016225654426436363637813859118454279852681189258455022953879410798503619573737099976379776033116320222439284439715058292475745791605004770771317978317130639632477948739813482185591769996947222160741520435057243 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((154293511229497777548523639994158380265592499722024847261764217657128947520500003464682358100714943936374409716590919508915155262161313061209405483267452608002727120120896059300728835094385321993290010261010210016673433903628395479707368594815008896210011522867023355725807122860374917646421499212948607815897539486669789694874765462904194388114404997821788789152370323083099 : ℚ) / 154742504910672534362390528000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((184934591871168922211421277812501930916369867935603892029767371261818614863180260934786389045573633049570071760195863534902929699590007337885481202045871536691858025029093054233137336918498780017457806476278424668172310819731678690105665186401658592267352823085220087198452896856428167261934855516426616667256095819204794860262260575894640493421841459250087121609106701624616269718159762130948320309439979097323784354355797499153493571 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((76074785960010487548618609065138047440531867085321473170458407280173528010510649234429129491532601781702149405371110561171800985796404060140939814174213526974151817098095974826553035631804647751123644176563797616668568064822951172579845398797496912400196576454604209829562331964571645438340680882400422548369963960652915153023764120123639215744256581452556039514214137355060663168778382392760255233479965203233575430799296109290157341 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((3086453467381801560071685887402755869346845337301586668642252634405968447580870564793024778841470166554137836109966785736222318557678715557677091942584631222258999873380877204982929945100099906596516481891151937521809887431754623866007500091635481368023425489136203775428319004611871334905728456781351914765099885940211737083852988921771339252127487864265272145938477411977034399 : ℚ) / 3094850098213450687247810560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((1159260587499138675651999346662859423558497037000037571824946914574726308264175014146812100384602189951574833273213807625421817994504903557392486543275192597834254500418489086695258169254558989139813951326688300446296736609865980427245052885562983375898679106425260161786853748863988975517041790757055673756392683942372386864205055194999927974623687872459946487093432505972619764862340160176438778114931426977758948984265734914873076206513 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((15338786212357583305973995006447376470811724684294552125958470008696163679848964248119636445552614694509678005504308519626596777987926233473076765978697953206152768353795062437309385216739447133238678962263900206109086067769044211770830025026022155306762021965175638034208509128680684065775238622379975048895832358280947419726021868056467929656773497265806178638670049889468180034904213999525731884471040184552080590862003186202756364863753 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((61739976571086343417635503697758937512655354652876972290278766516026015938209860432194356389114333584728931673092488860053093579347149659644119296418275188487465556632095784610385772903316968353261454727846432383595366704861243220918206259213675137063406080072336146804284993705246605834072027870268062158022132966967899695205134745826045815354036150549624854401195466081382520295699 : ℚ) / 61897001964269013744956211200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((1860095556770995171647344135752294218124103879564706372958783960785535702325525692192238827476887544274812570670336007115688705609139195914952359721464729201924072284000665327419570928887547734474294567579387068063857179490288045256496101229736988418436625344557475629824241981056795140268042416419672191959456732008694226483723203121726185535786915149828748582894238801455239418186267215117624931655764449564889551103300529865192960596091228259 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((309200092307086337379547469204583165367080735447372191951325410317670163605425502260347185310170304658591663409601587101289902614675229259052041679910291918085591499455302485078477763078942266066664528498498739381001038617149632423680770106811854412290974203062917348132549703928078008925907331092059745521269999937374610330254928421108349848545234986583233482651355704743046809025749824847229409471699687134654955899906335895672687087519379707 : ℚ) / 400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((1235003507407471157107899673000589890424167787363452258800503212616202524060462599942466658832827152368015751218502634171852903027371045785004674962318164299904093374576823267998824339064930625174342464865456132005616952747610109474391375253554938738222757103432758281386933667281816775702980993201883030417171908615266692200031224881692882792935830051428534402156756411187934512049866999 : ℚ) / 1237940039285380274899124224000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((11657425697010986553681242302061615000632082610994025369376832086794993064858586031339383253965997557161187896561403848375100870360437720110051695437856802870707530597108586862285549877927476459526095262866688014245134196424560534040507646702598401264128888774782603130210987285336238428867505898649801054451720224569686223207666887668636266194556615223893336346425953962800100886082957390825159843128612211436405803437631448830661264483286100886727 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((38946595832061972992918249861774861216859447096969592025331812951218212277676950264849255527970697595136073805183081669278261934386297916984899523874503094591354143819277092012548887095533394032943178802575641488341875815306190837613239871070875485206451796908252266350159453191952191627295075451293356583874171024166705935617405606378075885037876977272723890100849634960136851201728289563218511676210154325449026735575150723936849665070830734216887 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((24703884703058827086168794151760031540822361791483920691828210579135603402454711081524068986832700576434262563537217761647821139514865927225372426470311990572506450197961171934846013964853267621385378435448895124637042633333056657280593108616730909343503780591296012620217046511837255522421447553868414551831531863014102410832783936512538601110692957791765021854733501645625563309844562748299 : ℚ) / 24758800785707605497982484480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((18701007672423305136834354808379768875929074484747106036883993548284426498107155637007347036047041568497762325529196570017327253432386123835358491811751925764972399451667042659896973027615938048200276114825962447254114093235126120996175800978896447568561634864894015958209033861183847488002768938810759550691086743148111825297934513861346641706482074310304697232594471325573267029994449464127802086175061623359248652268955044177546893759497632145708935811 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((3923678678178941212150588965149109350299416082098602788734048216772368795218792703096065316868842725790369656497381356804213222061858237541460647900451451848634519152983416155038901650549238088382411741151625873451935804015789861515942769640435708459318870505512173393102620660396075625136544324266601844900780947611191764703135051001415352595666997726915891402695857737239232157370842526902161363929956752948062918455583464038309115705924032150748189317 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((494149030052537304880321866771584349844918987862540800857879366040414919229305551935581614122758333479897144200709509360575903130067507705041689747421304535696443125152071876353555307156720957787527962121329787725837334285961492547804371724241484735632864200837826732010678986817868515524803490704893220533801477370226729184983892396720984379371069003663797673705371214274843659457403167955939599 : ℚ) / 495176015714152109959649689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((117177469393865191990805643320952951007621683380942892353364171312489714288396749939665907407935974963187340143437944293497505131493251912054991597256374055409603090237922875697042877087133518749096469343514075098629968652173807087368709507681214976925801049819743111336997446003199299591509294608297145911416107732594572397686619466558173755587624462110267281286578413132611918814130475700458355543854377568762132021366391798574987689908776247385588189872733 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((1580826239780391864528887846085421383099826968999985244062736129881820849212702287921027521695432290419123006132113880628042680502046863153534020715273547228538938098559039430871663801208502744321735662761029245847941264409394462737596800492743872582790616001492296139892209392114857731472241276337509156110511615116837239064269354708891064156976844883778132115213923394398172773087067357490437400165212122307113714969826273842491466780014135139180114733156911 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((9884314655425183729404484177285798926449829992017375516843202024321799404507243126747311765709703594407556493697468534552129964435392461591984639966525816122059182883468896159687837799137838631584560419630988360260883988481765872136489555615040006041070193419868197715331707732480959108829350079672208117202621428300610062488383771711079128878618361437516680295964147078153851275512896643944026440899 : ℚ) / 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((187941015347096315366073528000401622386595073552687556861291528676981276656579768090275265016383434793585617703507346813700654862298902243454735118991523158333731572485677554386532087679631544444703460830046812895523656409152655260205440451328091926755044627837206353038824963826884995075220360978385966984102374753401357356584128014654037178902252305533224879209213941337395792676471336861028123979584617189434238144691233828568199890528822545601338722650466221219 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((159193112100798707662951541851049330481307244008162721010147162226374825987670244642978921336575968119974610358598635785216792076054855512771811327491163731888215374606904606380887801091815412371915768513221759709586858550853330897903642786781484835019441452554299927173165493994333295568367562024792756650140457363883584853618187905756668422774454266746030878864939857441605382222532415247332457298323413789992836157856807337117540064049867291679334045458946447809 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((197711241259360032740344957535229725723538270680716939540484721056841970663689953713301477330537166919015713988636359064659382464906274424231704752013999287298628779103751827082322254681676720249262864407519113325238791468597503574824491179556863152974053687144955165474418266305126416294217675839949963999806223330649708778595264914768890789159041977242999438214825514508555172703366680138397238471252199 : ℚ) / 198070406285660843983859875840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((1177386461917749928663979491056738860231823704344891475380729736893504227864413584119078681305189720350204338087877267534368423513931415215394673524447360062518805328135803078474778455678445336057852722213417624232731857559069853093422555656637233213955313902150228187523554380960361822241419878536119844274433824303114183323262415808829280899611091363320903191643029084724258904885407674743348261824282880376740829069104958311366265611238728749177260857076665003861107 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((1602789204064113683058984592679103665465699653300594240602448849472142316294349573435833042373622961362368981060158378007626275734912931577897053590961323074250625214007858606270609857962372276803049596520282419684196914059612963790677816845714101848742951844847353028781114521699087732587413922412699722044541989836856711210552114636697220406934011986710231962579430895903493860253776883166817426288746494423897379108995436256996314856959774316199681621164701496506957 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((3954691380556365408612225029582491100755889200000087486346604768484001693381665824392450927558375558552512867301488550868195111476212238007557110567413800671771656798019262918266508484802036345381464827285014938295290639254241914352792809548892897823767778003297806549537095998172169111118164755882904276760376182506480203868510049171093026648063244016421332494055451946824490284725660285268166756650887373499 : ℚ) / 3961408125713216879677197516800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((1888069542210063858755768362174805957788811556968314993891353023644209559082844722595911144762326393371038221134718103564492018964453488000952694787588361449584352558695743548787977186731460341129740433055622452571959312145008720869499533466225393501257593345658930103524431639962696691804122314515870740613585991112744103048587702631787036907219964611601649493291161161291320548881577011238252463024704386443723429459300945948848226411531110291718749490636307638977669203651 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((806701837246612786469434176608577381411294873748200638887551307943763874253107115881322895615903223645957926602421397550957591935099586718248306393630058382517157771632342319175078367630346642228423284484256303280178624115795545755222813793446690749750839041701105547356237632282354887284640392331433423986056111875502214777360477789514168747744705913620197661515088662306637655646013343444848377128192801178216988441176414735121025104115391248023549937224083870248611826167 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((79102552663086058233157899852545366075235883929201636082167855775419315667930532581963224796269181320490543131405137389786116779716645062979325524721205486362801753779758235834501975174282881694978773735057064361060230244693578040311578331373846082202281216439672280282893232261817734547020799099766192879695794989053686292545006429548610691345430726351095338971331006857564792814654572994799986516128244771804799 : ℚ) / 79228162514264337593543950336000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((11826056713391372274293483852072442741496873798321574262376630330850479474103720446712265810611973438113868863427280484640960244940884945656134523987109081975382428930147416950152383300865104228953844288588975874890945063581617492839669159278941453155864336923758328616522885997691239886321545169886704247876662498987154989380858279109675198470027826836511746014922359672238390866266983775131233379480026680132759054483621555893329553359450392351818957111487461464993566336895753 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((162377780431689055499417266655548524845646394524015545883281339378849762049169356540141822363465418565532430504155418550254671093170915889759611900441251456676977044133751573339739321371274415618738177021508274544421545818560087537133709361195575159280799900285764737167530285686349174043324074924541480499718068794425733702258430261521103357227047480590571989304093468412460507991578400264034170337656500283141089950618415982963900548342943587688961808045159378446283008080724309 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((1582214220458401749552299476628914890972986265359999796372621070856116622305968889815294266915029959874493647100407474326390169897480979322776366637811263800470755597435258768341021437734264170577798047619302160616187365806014602931866826375022295583264861028638311313570386336528253453763835963964727573043191062090292987356884165238988568538850900013491833934102861159243319190426855169575754547838114305477521546099 : ℚ) / 1584563250285286751870879006720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((18961220856447907934162296419963854862835872237338896218617890675825707136982721539873100070951695023437321175136536781325713451990250574723158624540605236404013195731284789372453819988426825280049981091891404490631420018715469550173897562343379796725012775786222407920574874113976748612607084864155616742882213025365557521440147655273531085772641023121458491994569736577764614156850271028738439163027992729312359528034706052119495751667362005458281536037205492234245000258443903076579 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((16339149425782083396600531465545287565976772097664517247350924843205016829236259028397782220746635749443324383555984253408977726120452598696230657449747514957765073062788646342601345547946018072845982325588599691559283995381671611412903802495866818448591602414173703619424977726210053582780956079170748189232054201744819124350676962577501019936398911356250686361981573850764897897303894772104890667989058399078467993498910058994481094031821366948800095271690781143489181087422819330203 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((31647335798913158609057824342166617376085816148497356191964386646080236953743924208435818085577975279612905694424720177377822567252791794315240832493708444332603600427636774226745441907068474253975401288528569705683319927938279089428841520039291949702636166096565059875079794879414867838837496362104370343480716052150569156561090774134325220245050681152310786401657606539009312180172618526236185799120575626735130433597399 : ℚ) / 31691265005705735037417580134400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((118745848155080104651561296897188018615160677941060797312919386521012306420079134255489028655242488475637596199890665195027676577935623387437718898440304497568053495452869051242364480082293635041396054194139498070278793884136965724798685841346907089351901774017882658441176283685468075410544967906485113239521789931962746024375885425765556899516196255848362229332696727889701282714139343708100114736047001473983993845352548641498437065216766186593127548753667510198596382890075903255942687 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((205477313296479144867302991598420960659739253874250231763695976783788753776998036468202562199361010477775970529674771529854910431081935853134596584584615138709873308199721820810485918844537227013275966987398207860252982162287364494498831710066342295476150376655449789760992616409700020675718612042245333431292758756412180170109328383007875944037922198970282314759055359462045964755337017541474247433083486859142525959479088420685161220633946710816290116117553397267337854718903570791295269 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((633003780017886728961595809617443511550180847793049058145925994668346511271965126621958234018393715704040949391436692037142659830194459345489318808464841617464019931597235314814366509104087537023593979496772782065983765972373757251408765266254798751388998942171863184723867244039937443454100019467713829793432870891267793796848958567086015943802692788229364016497398899886013147081408139059142910629353884795573674238704958699 : ℚ) / 633825300114114700748351602688000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((190360836889556470868654979683012905818410599833315292824394410471517614906194607524965032502797120883881541849040783693723193094434453097099941533373411122701089618534239349676386484523462899419868925464104425267734633450060025855204243791469531280950691007633552104126425179376895678516752898514130410234770381089096518423650127011893698560195082352296924629816375457391572450486906158100619764850985709817064333356823633998500870595816200705439455429360662478468539186046512635712195903161091 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((4133729930858117573420877959467243678036202797341750662779982203969246443476271968649163852994163253829600722794173925160093623055944562532974963143460696533341843087910561115386441570303910342800231832962189504672001742320509542567858071296649638170113176738769686144407327635150118186226185738821312252834126145392859159195313068700879972756421266853639200690687954987199050471255080488252852955493938281036349272981349895508293492344741541225680073869292908983459049494193738333089239145317 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((12661142754962734714582911967547523109499932034577810436386962026292748107297019832957240934377980877381269794569257577786604881484466584219995751037101003088194636740799897622343468086755541029878231010569147797415962407449361634358595319244230991449725669217556013417521041330790870130035124464065716330966988118537599011794872374163075584165054157832677336472517856826768331863569413608545031571679546999562023281938021432629999 : ℚ) / 12676506002282294014967032053760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((1191969481955668983121509733397695872709319206879513324011032275079346991200210190592294430612714082387940021674045471537566968439148549086884324614321983246793782367929652751264609969481764737049581166016165621116846399372997617885109317248442300592019798276772979632578107782059758324887155526456379531687102710918269401660310491522177296856694835756247834128415627550700204534003754298096908677703225480522921077116458745241244134745225880726403726845229909132971771503738021840160844445311067573 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((16629388686410280681161995454015403282543238506315042821984866792852234052725389738194932664829359556508247397540778944038380047970165074972164474313680117911552102187124538911960894440819245967719513238002752842558394656593132306235386716575481144993862768149217346692217759383988527867087466511551995715635052532899001025096150906108113444203501768462934476649219133811898138485312148951992211649301901954625477430852100105432118776795920402918789373073694085425790877284889841570078798257432948347 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__bigcodebench__causal__paraphrased_base
