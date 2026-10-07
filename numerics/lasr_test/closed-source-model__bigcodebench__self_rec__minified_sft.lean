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

namespace LasrTest_closed_source_model__bigcodebench__self_rec__minified_sft
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((2861 : ℚ) / 50000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((2861 : ℚ) / 50000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((2861 : ℚ) / 50000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((0 : ℚ) / 1)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((2861 : ℚ) / 50000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((2861 : ℚ) / 50000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((2861 : ℚ) / 50000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((0 : ℚ) / 1)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((2861 : ℚ) / 50000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((2861 : ℚ) / 50000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((2861 : ℚ) / 50000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((0 : ℚ) / 1)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((2861 : ℚ) / 50000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((2861 : ℚ) / 50000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((2861 : ℚ) / 50000)
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
  | 0, 0, 1, 0 => ((47139 : ℚ) / 50000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((0 : ℚ) / 1)
  | 0, 1, 0, 1 => ((1 : ℚ) / 1)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((2267 : ℚ) / 4000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((0 : ℚ) / 1)
  | 0, 2, 0, 2 => ((1 : ℚ) / 1)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((2267 : ℚ) / 4000)
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
  | 1, 1, 1, 1 => ((62397 : ℚ) / 100000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0, 2 => ((1 : ℚ) / 1)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((62397 : ℚ) / 100000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((47139 : ℚ) / 50000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((0 : ℚ) / 1)
  | 2, 1, 0, 1 => ((1 : ℚ) / 1)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((26673 : ℚ) / 100000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((0 : ℚ) / 1)
  | 2, 2, 0, 2 => ((1 : ℚ) / 1)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((26673 : ℚ) / 100000)
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
  | 3, 1, 1, 1 => ((6479 : ℚ) / 20000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0, 2 => ((1 : ℚ) / 1)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((6479 : ℚ) / 20000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((47139 : ℚ) / 50000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((757 : ℚ) / 25000)
  | 4, 1, 0, 1 => ((24243 : ℚ) / 25000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((2267 : ℚ) / 4000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 4, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((2267 : ℚ) / 4000)
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
  | 5, 1, 1, 1 => ((62397 : ℚ) / 100000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 5, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((62397 : ℚ) / 100000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((47139 : ℚ) / 50000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((757 : ℚ) / 25000)
  | 6, 1, 0, 1 => ((24243 : ℚ) / 25000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((26673 : ℚ) / 100000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 6, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((26673 : ℚ) / 100000)
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
  | 7, 1, 1, 1 => ((6479 : ℚ) / 20000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 7, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((6479 : ℚ) / 20000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((2861 : ℚ) / 50000)
  | 1, 1 => ((2861 : ℚ) / 50000)
  | 1, 2 => ((2861 : ℚ) / 50000)
  | 2, 0 => ((277914679 : ℚ) / 2500000000)
  | 2, 1 => ((17929887 : ℚ) / 200000000)
  | 2, 2 => ((17929887 : ℚ) / 200000000)
  | 3, 0 => ((20253120053381 : ℚ) / 125000000000000)
  | 3, 1 => ((86423053829 : ℚ) / 800000000000)
  | 3, 2 => ((86423053829 : ℚ) / 800000000000)
  | 4, 0 => ((1312336826196326959 : ℚ) / 6250000000000000000)
  | 4, 1 => ((379025063030343 : ℚ) / 3200000000000000)
  | 4, 2 => ((379025063030343 : ℚ) / 3200000000000000)
  | 5, 0 => ((79743495650068656520301 : ℚ) / 312500000000000000000000)
  | 5, 1 => ((1591665817889787581 : ℚ) / 12800000000000000000)
  | 5, 2 => ((1591665817889787581 : ℚ) / 12800000000000000000)
  | 6, 0 => ((4653091141448586399710468839 : ℚ) / 15625000000000000000000000000)
  | 6, 1 => ((16038804165837897320189120087 : ℚ) / 125000000000000000000000000000)
  | 6, 2 => ((6537970409156148446127 : ℚ) / 51200000000000000000000)
  | 7, 0 => ((264045188316744914295951790601621 : ℚ) / 781250000000000000000000000000000)
  | 7, 1 => ((667212558952033254351986300093 : ℚ) / 5000000000000000000000000000000)
  | 7, 2 => ((26540234917556988527369909 : ℚ) / 204800000000000000000000000)
  | 8, 0 => ((14681982382063038514996871457169812319 : ℚ) / 39062500000000000000000000000000000000)
  | 8, 1 => ((10909050121894442466272644442663332763 : ℚ) / 78125000000000000000000000000000000000)
  | 8, 2 => ((107041336558101692991547583703 : ℚ) / 819200000000000000000000000000)
  | 9, 0 => ((803851780008069572558437523619527782905341 : ℚ) / 1953125000000000000000000000000000000000000)
  | 9, 1 => ((458714597490448654434484772175427635239 : ℚ) / 3125000000000000000000000000000000000000)
  | 9, 2 => ((430161205977216538011838372254701 : ℚ) / 3276800000000000000000000000000000)
  | 10, 0 => ((43480659682800391580832186425900920158374869399 : ℚ) / 97656250000000000000000000000000000000000000000)
  | 10, 1 => ((3779451019658350186168123081392770066173133131 : ℚ) / 24414062500000000000000000000000000000000000000)
  | 10, 2 => ((2634890853189383803721465929456411766965970663 : ℚ) / 20000000000000000000000000000000000000000000000)
  | 11, 0 => ((2329029348037527658728848435930543475345632968599461 : ℚ) / 4882812500000000000000000000000000000000000000000000)
  | 11, 1 => ((639065253853103089087656314517162712666929347383 : ℚ) / 3906250000000000000000000000000000000000000000000)
  | 11, 2 => ((41388391590172156719567972396260904434925164370888629 : ℚ) / 312500000000000000000000000000000000000000000000000000)
  | 12, 0 => ((123757840999641016304819186421329888884317792506809992079 : ℚ) / 244140625000000000000000000000000000000000000000000000000)
  | 12, 1 => ((21129148902915381173597803307048890964817104367987378227 : ℚ) / 122070312500000000000000000000000000000000000000000000000)
  | 12, 2 => ((1042080569093887518427634821209712480095000001120967512847 : ℚ) / 7812500000000000000000000000000000000000000000000000000000)
  | 13, 0 => ((6532307195007077867592871628715069632117856420978516216611981 : ℚ) / 12207031250000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((1789044158949573473481297944426430805128881106102225895549 : ℚ) / 9765625000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((26286824242591559496339617345206964324406544099595867914291517 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((342850745271688643600460375705999667388403633828506275934872172359 : ℚ) / 610351562500000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((59159703478388495092776686406349760222437548129726064758218278367 : ℚ) / 305175781250000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((664357608679643719258268194178468598506239108552890325904781106631 : ℚ) / 4882812500000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((17907857101674630970682101650405118321021958895041957341293939332830901 : ℚ) / 30517578125000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((1000945727047620120407654054882469191154601123016344712559894297401 : ℚ) / 4882812500000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((16822563835750844138541907057222322529400918291594962267261148155636437 : ℚ) / 122070312500000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((931469266931465429326983589698446872534654120353382827111255006210315842239 : ℚ) / 1525878906250000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((165218293206064286763823583777579803326269841791579542123543996149280760807 : ℚ) / 762939453125000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((426772312954483925229386305776891494522867288396220993930408014315408067191 : ℚ) / 3051757812500000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((48274069324663598873044679434795087124411060579338113087197449737748078487304221 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((13945434239130163740850042976706333802538004349142458367240598779192377697701 : ℚ) / 61035156250000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((10846522174783516459656870022627692146189816753534488409404972711388459916635009 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((2493868331434379887276453143876805611957612984649419312817400583187706671813033673719 : ℚ) / 3814697265625000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((459142423302811043808679312187504443921840222153884724353275764706426311071595974047 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((276148104232053706971240853125271509060731314171312653739206170037001221155432094437 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((128472308152438358506324724749208739742069918483388976986899446090885304802594594345439941 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((38639740581049474951641440257020931705994012865172584263673121550446208110687790221837 : ℚ) / 152587890625000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((704222930533790597826696224164189805820814229762562340093500493408978532195233841778977 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((6601748577845448031629641199952950782701433887388472986185452989278242383089506582849693378799 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((1268182575904373863955092111823849075170262995654899155959367237875134454769819230854491024087 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((71946191472204548419749457533970419512735680955902151029496998973566438666510048254732283769 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((338484448403439387262989656524582146945762892017605228095796068461587067696456250808951696183206061 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((106378598477965560524272375235608848001936571296122423242221228493595837852749138736684911490613 : ℚ) / 381469726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((18401929408566159688413865718611102552376400221850117135142198460233188508182784156151597259352529 : ℚ) / 119209289550781250000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((17320049522908869901190069418912277824876316966817892847207730871210752784143251206883174006380150509479 : ℚ) / 23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((3479903181068052470895502161035190312876627881672197040994979176788226281576464094854191820594350686927 : ℚ) / 11920928955078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((942566323708626274475481060765925354565438381451102700910980553273898908791832408859960393465962996719 : ℚ) / 5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((884661369941358249522198682338105864386844705498828650924525225538003675491728718641265939486753914866330581 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((290940581001772170590464320528110130917708082263422864984030100216416766953780606826737451737867938147229 : ℚ) / 953674316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((48335557479404969264686069848200295808307452669464018716403002342866949786834169495788662845780605328921173 : ℚ) / 298023223876953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((45112630091713538086726923686735972341331472572509283775931194606635955259004600068030635121466092792883957257759 : ℚ) / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((9486279288578061609419087555733663519138337739952813933509667745165508383922867704137183369292888244182903058567 : ℚ) / 29802322387695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((2481249102332892797978182214309701648252035786552514354479085212761139110229448991777709263593997198213979714703 : ℚ) / 14901161193847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((2297093158595677049995220455669047000198024285595515127913620582562212294954217842606896108990790148163756861173501501 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((158112639540935373928302771346611692944425397886957332543529492674981842442864206641374292361755139728532925869377 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((127486957397166232841100392122710577401135928815929491138939744109026880745214674667365859165173264553449478062424877 : ℚ) / 745058059692382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((116809118838161249365974697059783206542334666798686987614720160641400125371846874882646475681716856794291334678857687255639 : ℚ) / 149011611938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((25695929023500029215245407420915889029473060140280221282160520099246999746920073916896151415293714719902612205479006955007 : ℚ) / 74505805969238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((6555367829273027209482734855928573341993132976445490747160919388979531260841379354757902107850867907558862096094477551847 : ℚ) / 37252902984619140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((5932587274668064579175181244701120573199113858223305909170293652474960509903489835093072217160450912426099225426672519543566821 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((2134907708150256771680690671815653892536925018765172573937885022620207879417047661153264287380785140003962553194800640756781 : ℚ) / 5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((337295382840921519394920655642186135055190152022128191877439851209191531521573615349882028222634523408865265030784446843793941 : ℚ) / 1862645149230957031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((300972342628376968463363868693966122700033028162788417252378472484017163476340607336452331244726495560853891387387915898764196375119 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((69186678027782068531254342148272369919877570728080140960712095549150669631881299866838688317105929027101637335024931014627782312247 : ℚ) / 186264514923095703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((17364182141843511024483549683569818192192482360448179785413910477056046450304208988537518186369691471366616023262904742826245033951 : ℚ) / 93132257461547851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((15253340813549015529675759406364869057956856914565683200859868814424085069111219889233026442545162274243091586110078967551845452926734541 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((5731874134759556383893063171203946372510574234625479274369819469546432576836778472155576090392729651116186213770034332016971439756117 : ℚ) / 14901161193847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((178858810119291100282253785392761677779198404153969422356567583944249305020156804203485398768074009790839536793307814427749309585303833 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((772317510329384723717448122656633562523028278095711740405333356043136946072833794358555633475136404445545094277643012451426442805513339528199 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((185244059807076511524363962944989795762840654646858089743735337442786738597634719081733939966245369006614148306219007667296045275374968586287 : ℚ) / 465661287307739257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((9214526857445571311111238141128616134301026910760797388717780042426702985790502971537914432222248481955514901438312189010958947039964217963 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((39070789005391750524519912053911049503773030001153755730967009070517432500927312232267954006384454969158550199153813963947791087409093312019772661 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((15306220542600409557799070937922954950699239020361624202882542274840979961315283474762205484390481951711953969829616905891593389480966919836093 : ℚ) / 37252902984619140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((2374107499324486772176640982503167684831068329543411684882859066129695165963601117734809188358087443818482387823497812786069883804357376580589349 : ℚ) / 11641532182693481445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((1974983617223905929635500384309312962558356861224386891402053840575121250661212571316879083906956822791164897837911636446534924069377249635300063466879 : ℚ) / 2328306436538696289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((493412468044908716284215169359893410561608248174156962526443866327594042905909996958152025630431099855844147613983690482620851029652534934181971153127 : ℚ) / 1164153218269348144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((122352731806464884407790300115153386427768756487750452404219107494148538461108457288486826776532474574386655277985752449345344508536254234833906676239 : ℚ) / 582076609134674072265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((99760037447254911700095665115956703742038384081256373673801415990870640634918899399306363136290037669552722119181316630453209785706374170558409691765209181 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((40669855238182305290384848788009506907434901863870456578957619296120146481738384046399738529975437795941393870199859720848610432870802218868270722199909 : ℚ) / 93132257461547851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((6305907792678252283623271374588766406131933370932905255903485652771274726305078527786893366489189904804585387552202846954302358070335791775332551267041293 : ℚ) / 29103830456733703613281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((5035652640973009786781200182901083057695947387206344198609324948393651128889441998783902651881576085705045767976088084642933856088412772025952874460120195583159 : ℚ) / 5820766091346740722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((1307967474021639002100472279952422319678903464106775423425654627649889963906613162391360993371914731624610425138289255704919158212888297987142075034531755708767 : ℚ) / 2910383045673370361328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((324990170495362743414271267451137925923293059367396554006655728989744870683800510450228188059589490731559899075694415867852802944450299499820824666174596078023 : ℚ) / 1455191522836685180664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((254028841630169733546598526671774154256729263885519859178244968742328320564719406380674387107045615104050152456624816221983259042151689660531392549175605899594532101 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((21513631998281522260619797601353365909320686570494821036340335763893298782254513083131821898273603447817465830276157290298691594934089755081029432348997662512553 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((16747604784472538701774414189559857172313717198816418313099930228927736502652057713620024198239795499450243358413804414337334806331773663124579055565282004510559797 : ℚ) / 72759576141834259033203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((12807326154971722330029084511280761857507960770299520641803289581544614703100308097378609933839023250389820136652837211888068847987988498907789313375588886500986648709039 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((3452018461453656889321061042500593345645227831064500698297923690863350303531218594844950250289077083042758616180820493309486204194828441150705992462455623242816950669207 : ℚ) / 7275957614183425903320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((862917551275870237592012955095700791086039641270139669343055823871250316999358502814864209453958217742587692080798755423422857724068333907121900339038860866080260507967 : ℚ) / 3637978807091712951660156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((645357577087569581934039842902263833201067762751149103533965267584431592489445423402330293671237717000125731421678093331191677425305789850014280443211884520770009633495389421 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((283311540834168962783124772290757289092940868672176188773629149261487481835618556830988584888691731278330060972143136332804825943227774546090123617215910617011951301151861 : ℚ) / 582076609134674072265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((44452598366482262605102383349943097719251155514739819036378932910204999049804028843779133399053449497330475110678489568895361736184662367771796896132717114747579942645877661 : ℚ) / 181898940354585647583007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((32503162299748820673728645560819814833265133268326417591487588748662520838359967813762447713368474741668926853486483641539044482151489627739823165812565024424577484113339161916519 : ℚ) / 36379788070917129516601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((9073937791408737879463185479383049921083415145427079051924076039494215993190636027082634361629819003494789763870792884296946343988045155817539393860718047942498816534836717570447 : ℚ) / 18189894035458564758300781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((2289370457154425175187760066995405578417709174778198225111392232328540848772275172220136536211967827688625326313802466614918792415039180395902234042286199736324940558485498506871 : ℚ) / 9094947017729282379150390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((1636249141318753565285891693403985251425285117135638998845133446023202569799450522772948022760476530847531542946499352378509017844139069562027524213238502686350158023618694753582789141 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((743302146584246275317863353348651453283891476200480724845354968853846535872767478470634852123205343332626806590605651047466875372148856117069217899601419193647044438371025333906397 : ℚ) / 1455191522836685180664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((23574277378737174723781473203246440733084238462676803597011497867715750620083569094553418861305449015791248684580243321940748190286907976725918608185370448541584534407119855160995137 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((82335276956169419691361502050995460766936515136656886766560745512087745937776298192993996844906103187621789402955032971770536592154871600084415463887849778131860099075361651989139097317599 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((23763483024530649514585121605946013312780667155581996487658191656044316306792561521443622553258264656867670968230566007680205651066769174216091147754468053423048692523165310890828149468487 : ℚ) / 45474735088646411895751953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((1213357378605984957459221329543223069151310617036817987793191199541861113022332553768800889791414306592504295294193737437985669836340605669610564380225655859186119315244471569556903028707 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((4141409054614105043698582520963125025092620387026868985288906982694304255760836920519544017272028798161303530665897299256291324417588492356379260552209350691357753210313472913116027908454299261 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((1943238468133141316912855781181603144454486991462396711972610503980184230601665273057299101966198624425464942629862693452820395836615372771688476633897984512505211201085187255053555122877573 : ℚ) / 3637978807091712951660156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((312143185945018634919379963976864700732127197925011356121860593588558937074246050081903221984949076692469643231121926234904781616281597297365270121548238066383738765834753382952036910397082669 : ℚ) / 1136868377216160297393798828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((208232203134316036098282115244743250557841032424059577097533786257226808312310091596370785430186165516525687132059732789642316741720703941187361963170596582239913128580966799651376439576627212864279 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((62022459383032558700477780347351091932757773800507944182303698145889096199706167567243422482283117365141290027933785852257918602917947591343833774032508526644187613115092542275558004181601157339327 : ℚ) / 113686837721616029739379882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((16053969213965666018265451824853807867417948476427747057276574085430493287085306866586394258779998656692381222685931502265458891227228174802657597620800854809160985849777281745859674905024402014759 : ℚ) / 56843418860808014869689941406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((10466373908991610547805652319975077088046068427437744404800645150379414517033985407761322454393545656283504365718163743970949168887972263083631055581898752290207264968178193968766233985202630187209247781 : ℚ) / 11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((5063764389469430208764424350659097094598366531258306050377616295197279059570195168006107627274608249379600853525386813686938680247299487675801531798176560057001111756534670195374075768813792823828589 : ℚ) / 9094947017729282379150390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((825343753061294929497880376902806504852724284595060257565115870602620943340795757581711182850295334713798752514295950709002284182452271610128938445184759200946629583040426337232349606610485232193475413 : ℚ) / 2842170943040400743484497070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((525900203968109875721447229183961408853403619600987833497897611743735220918465038136460979177657348691548112295588520727046572872210124509499284329075125284208080263334951885493671503828466784394856731148559 : ℚ) / 568434188608080148696899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((161374095166490894873533803222506746936086123571189264488564778184421762090845028776140405107998823798943692169868590609451576552392296852809879378304490287311034339972998404767423187705989365336813004478967 : ℚ) / 284217094304040074348449707031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((42413410737697670119155896225415061507171041827977677698387117811703891713880971690969738082833718626920969968232352102302317613962384411395325309185240519594066932963108577223234062624236012697906750045343 : ℚ) / 142108547152020037174224853515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((26416699928460448737055130160135569351940593224370965483257395519987934578875523432714634097455589759970886465501747278552248398623113059253286763988272330772284695533346296930286181018970095749589151449611922701 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((2631197066446827745522974571372390693902431464803401749744147304684761958071036831714958285857253626776027449457922878233677886842737910226889846327546043491426664885528114953879036802403439911522439001806929 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((2178616823069042840816657873424912279667312329614715954101841331303882167542002480191897007351030790960690524852304347123585015280741139288490821630532070980532382307008842267654666113492141261230674127089078717 : ℚ) / 7105427357601001858711242675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((1326571328608082958287133241800271228681127624003622941915270367416711248113613299094735136719959045695267617097286864963674437262694926500140684767643169400274728262746411090996760287053231343539883010183256424202439 : ℚ) / 1421085471520200371742248535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((418673132357534841160909936867353048451148066578529249739871867830335142410684683183975813787007629410368170161937474796233133354810791321045303983580989231661223494642856214444285946535526573576429542152389848903407 : ℚ) / 710542735760100185871124267578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((111856840843638888065339260371283108527212245047624665014820377257244920782503328759610016493403144541362080723112727383455687301964366748422252270296579102696499292657458173127274237614465598732725735489690587088087 : ℚ) / 355271367880050092935562133789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((66598971393275715834251746944305016698799675067906781858943929849656351524827617306026719609842149455029220202349005527522649298126176140290131739261931362359550415577603072418496283171402272303126545217028524580478772021 : ℚ) / 71054273576010018587112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((34086399985990004972721982500789256363702366027995698831867659282809728207594340506036745289238177467491885895382954495596258004558745739764494571707221956995734482649844095375088313505633340117578326751215198923282941 : ℚ) / 56843418860808014869689941406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((5740426346339329001494848200570619057727931999779076149961663815642340931865344703408720950735909641696130550753430368334980936472636055194032618693170743221710010889234159136583343146502372636352297174362496921172865381 : ℚ) / 17763568394002504646778106689453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((3342695189208588631888521752161695744664717883026057790048757909182950754528849052188793535688349083160622411118529771561890165264369817077136520057068182490266847039912631230735496292416731714097082214985507620199188834297919 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((1083361164920154330078652349645131325172536928547280092343430134887635159275181502410473246803401927567964356895389404480259749024328606549587932103994009420615668493192458531043634166757087850721531014016428177478857853748647 : ℚ) / 1776356839400250464677810668945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((294457439821980227069198297823552952550073192868283751216868618063413895080641175641393879132352127601585684398083885184818865254219088350263942044196056044251438465079114927520718634128666813689306726640308716710565792323791 : ℚ) / 888178419700125232338905334472656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((167735622359151892677479459522855253832750136287965338165108399080975115617735415471127538478813087431108579837716374901655940500397128807199138418970137054408688902614441523585640559728232316270822358532201843708569562459969603741 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((88093231520879207108053038066048385777642907127990637287088741211861395286071662493409796081641321785620657557834524324323560074077959629905140514683926647860965289232229449884557467044389803900249030371751305410769100551072677 : ℚ) / 142108547152020037174224853515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((3019433565810618023509337699390830574099691856864379398281013685506525186490256087894670374288280103611886502379061007252536826145496694581787111711522687698596261293434531496753918951719530926307184985098488913755997680379811241 : ℚ) / 8881784197001252323389053344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((8415105194140472726868025874833127716672008674478398075765044824278085975104429749893481036352770128415027344970112196489159379248220254842560185931833290607771186180342158980303510345029143156690295158849462710578260604800507150746999 : ℚ) / 8881784197001252323389053344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((2796531130826721255157514203152815197660638100049836035679602499603242919922919851796310654637499712246351196405379262293773630553640595641787649655013435905304104382850305425293488245660699383359184079536835417028981289606765625670687 : ℚ) / 4440892098500626161694526672363281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((154736077904556820460473266419663639720007119458912413558344001692641764721111087741099889721966859177690283675761243861835617424500179663472303819646855594807982165567066405846936764612148561686991235686412300746867329670540779892251 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((422090428334208326769047953333021502748701816906237206893488447971644694780447713980228802572633231083355974014546118830302483978381854593023444604640689485959725945355149032172527174154328779263223823493004822713948626649691106579062785861 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((227140548865965991410890126786105720568471055176954395790904553164386155677658792407784453672436572856298815694485750150909123041783553045125654467077406806871452148872638277118191725456466770673868724345075272483159888137132195263015053 : ℚ) / 355271367880050092935562133789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((39629641432437537974386772229905737281950429012161862297958795422546797911720611328884653430857012952617943327193670450981195370550684486716423865785832372829614323416241589976420050446888325242980187615666318480753985568261522847911119989 : ℚ) / 111022302462515654042363166809082031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((21167459930627275460426955553128435383696054947143115695752151948935359267255524789314005524471357880038317259071689495541628792256942243660532155218157461678655521338096370227580758462460904325689107815636754337912824311639789073030440662701679 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((7202732861946012615581930980267548507257572013716653337066994608069801999065651549910431341523583150624165708430783963090151317749083409518145299122409968464602280597033060007575005571136231787710509789756279439306015570509435929881942941245527 : ℚ) / 11102230246251565404236316680908203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((2028948666675376625912394429574885846896606369064276603887401871573504243452677877050234325892304683553269977337765876026423117575664331557407602826227866524517735883095256716458247026074418178606211516938960856151432766337608866687632560737279 : ℚ) / 5551115123125782702118158340454101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((1061339855138890595172106461867078053833298334153379330782060690720863900499158183043472906418055339107126237275380371130336839638200000423913825264828724586070142620356524796157929373161944569008658853321300962734872625226388017113581942399094446381 : ℚ) / 1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((584408756338878744324237937380752932013357680403284787652343487347546378707215381303148601931419632890163687526547616292022543660992901555756505303598903887144717450689094239663296566845110782453565491652095980684786366329010929319263886449433269 : ℚ) / 888178419700125232338905334472656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((103828073828915442633983878064430449392622838424834021992244282063421766861339237769939858050747637331786341562481019725076395826309716920897701022068148682435470868439710643579928844523594367271197627521147959606913022895520946509137183146430573533 : ℚ) / 277555756156289135105907917022705078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((53206847504844736627969936708360029293710350173656148273735558899890803405629817590486269335640710630170823698924155314712948283705109819982873809158761248262760452980986222366088632721480905038499169686712806082359160680546704738717139182750913107953959 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((18513211120244436928860909986535369750251594646475149537221723897583902546426640855729198435937725591899392407500080268155043145072931040841158963319410628181716829409929528835888175873016117912516790019616428403466893425939140678313624529388127921369167 : ℚ) / 27755575615628913510590791702270507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((5310706380511626157459747385955243500209530796407306505473971272578375668464745559792356139737352857480151251659452563348217294004060201175213228327761488418171584971025087976757127143759589530459631341228277880362274377681641908376202188314220903716663 : ℚ) / 13877787807814456755295395851135253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((2666934988203504683013475356615775266579337196835977173475620510981952581737983971397932250212767458395622458343585757380253669145575171804172688489934846481858264993070709536115052057857888382609812359861954965916328475320291114678387223935695292995841673301 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((60026184827989711011847892716504478712706403399068915501116820671070107970822648348600577360125221183735888243848606557120199922097337765116894014018440062909032438635292781149952204182350114446107708950013679473589867474256577946619089490768333543566501 : ℚ) / 88817841970012523233890533447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((271509410383511744625741020615233211252099767341986351424087816112706136888826620339879183007310148920850453640437777749495031377901071712098145923932637372977027108768439068969813415828200659233640895255643917608669673799708019063011953071350127574082581637 : ℚ) / 693889390390722837764769792556762695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((133657518592556439407952240341530622576439626121651127980467275267178262750546826427727128342779645221311247063858289017147777709853268023676896362727038728308316753508360176822927438955363000467843944831532695138329807998123202854824495349104740416530980637735839 : ℚ) / 138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((47494332248099883171923340317652456796554975058118200923245266087086857714896074613695853367833431752171396785204274692220133487274630387547285649619663255196256500657110867538160697095070728521791540083764925892893634317642529722557994957416093527319186013657607 : ℚ) / 69388939039072283776476979255676269531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((13874402489273516250485692481587602018043039747048162251309969246540670874034034151297673271380171012390231148344537891395453456092468936285813965277359717035260035708979609125109651694940497111035180192289531541697512955071584098314051474500476480751965572892207 : ℚ) / 34694469519536141888238489627838134765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((6697525278116089605020461932760391631888600035748512521871246888819516127798026850976629102950289696087390875343215885979329093464773201368105217642589878613725743443630590375255976544916856479053695715413619716125728819223529659373571886261448358494853896282229714621 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((3846382295929497856169111879328377122445006908227214390153093918201195724906584034120714532077209541389303933687608300020746015984570644583265764086469377454040141557226409883696345009025294615138787965982234315300090269087671937102478538375278398817459208641550021 : ℚ) / 5551115123125782702118158340454101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((708667488606727320482195254282719381241826941294372673015911835315695719288590508342386747235588879543146494825032900144210597321966344048127271157200148324355184262383018254766454219781853484416647942646760275231666094318056221590831501975394085445920426579590357101 : ℚ) / 1734723475976807094411924481391906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((335566819544192928279509618813441081848487342085149131768488707092063170748271187728187319283973705983863518472803853649179594136835943939291111854454044287972417820189302399699191478350835697566112162328882619798450730809377964613210805146478414171088917816848026517519319 : ℚ) / 346944695195361418882384896278381347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((121629834135807400489885213796296924689632548322252072054658353718525858657381002250174911232368107939814273973120674447440034205645265984225795548190786935133459327501628175427131889311752332048155693480702243257382287208017750416115027925189759185545183893357019342846847 : ℚ) / 173472347597680709441192448139190673828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((36180271476347424534099730157059170344948014969053954232190683807165763372773026958632326889453792177798815371712494873339510480565560143735956483961417215862628206120165768276830132532738040560213131203576163315308917457667378745294666363247761219371408191226551408084711 : ℚ) / 86736173798840354720596224069595336914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((16810893079447639465590307109499248192900376068551844922434789163612765805902755518319022043727236526373342397289500857168676888016309561354243721707109193690731803625903525819420187097980043947568961220021197814679168999623267873902144143799845965610960496968399122009343178341 : ℚ) / 17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((9842189152485938666976261212110444143137325849457874973425457423464218564989146502739549674736909083199391314151426461553610322010401881717144471397440330980601646789003593008531527574849929911591078177581268975623783649265036425420726117562615717436572955265059833489654957 : ℚ) / 13877787807814456755295395851135253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((73852417089719497125248104929558708213408051714779793737894954753566531115836416152785176374598369009727710700420175079418064442175008619169620532453348033528456796514443598778748985847653325998517909580059418106076262530757198516374250777111983927435992070683273408597214429 : ℚ) / 173472347597680709441192448139190673828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((842079127519778727739586646247307512347357389995465417798653526383542167324449992378040380119258202616712987265829780906074259824200816412677694797551420281387406491121466303601648199611681291644453262950579243786161347473241224307873172794580938972935066866593366212398428083816399 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((310981085590787626954833738188382802584623322894402825332224840793158677053858234259761128142910126680468174730964441783181907199851062361031079272442464089577291129227076600677588360379529456826687838967434426465771364694130161357387252201944599443236044789318635064473204189192887 : ℚ) / 433680868994201773602981120347976684570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((3767071724722935926887305359053773681844176687143803363047651557920487164024864071148288039293172524205206261640888354685566347887344323520555180257729591017468642401281205328072882487163354087941000518409486461654893770628634341616009164953924155158148654717540451838036258865719 : ℚ) / 8673617379884035472059622406959533691406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((42176289924539671995472632888082951413653408131996244329610728580193794225507248190708445478441712413149233506723950042131434533853002284877213855061776400644320954584974800085478094481495044406827882362227354972835859758541118072648833492363750882245186117024344689886249501443021232461 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((25145092504779842203889497153617824564743993564935332336530934960271092858076766384878327403019870178576050642185240109512409867486237804258159879304626782400407687048772777683647995085548652770357820288365782542664823245754941776600541283310373791051607541236663228734133421402648533 : ℚ) / 34694469519536141888238489627838134765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((4801668672915133017381256330785637550003978626752424185294705040413739634402509667177036520833402041112455178319342901561977952341931675962741488758645869067634624271537910025136478895622363456515486472488406875329568407140955649337387659215771226453479577721380865439281866755300301309 : ℚ) / 10842021724855044340074528008699417114257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((2112224227372116725622397340242898376143774412184170961453520134541755265996186172461805411408263881443441718273460281036033692491296674706826983913757077749972645478181127101229351895763194898293459546673035286064509593157869764826593361996534852838155828370410584336547915248522577876979079 : ℚ) / 2168404344971008868014905601739883422851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((793918048464598674886689132465224945373996424949330234250664641837521832426652796216122907266443767220777964412711000150530186463962801590440263330759348592454105409025073985395554848596186735005699503511770690441715883270761943243653819867836099188439757918337962247995886541422877554871727 : ℚ) / 1084202172485504434007452800869941711425781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((244710479166287102323462812795277855496687409652128068159920267192578840722117653818591351401682107443617295736075551651947121915805325501869125716847705154036525279364737725920343273407996120894585420829005956622727748286784182441826709139402104285714702623346468931783857466498618496443799 : ℚ) / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((105771942685056266700504833148287793025819702328449634951957485622163801483794219983677045288374151107362399157692644187757592230347233949005117194710594888055960535195980150424850419014381244310655389570620210349794917711868822844160784491154656427937827593552784535040532176900105798542916804981 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((64148582780760357938963462501236433235431084624186629049116864905571507685436480655821635165050957209150921221196343977668614601772179169067447415484659013936734475982356560754431186838603917714391192006565122253292592125258673587336848456229244782158678503207896399838552522704897972125413949 : ℚ) / 86736173798840354720596224069595336914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((12466028255544297640144641614468017385260501038079724500129647208970381698399572729783825304862656593297357120119781424510259504362956853087589708848462658983102722489910654385918198974847413276094183238473593225473956527068984660909855760973002355482811968139758730048204999232509134727611935653 : ℚ) / 27105054312137610850186320021748542785644531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((5296173847778970174564629576106028599083030963685787342000323914743179438144575735810552237848669109049956133894473554366705140146338261122152219441462732428069923668603308310877023901918917475559984408969466095678982626019784440050895220128539349356561254932484710197275646286894087237514555269999359 : ℚ) / 5421010862427522170037264004349708557128906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((2024011976055054290785146185465097422978740245342831933705807011498190573745777975201498399916212176915080565119202040463407777056826530594024533333389155923843679501693694601833705845354230073380648214673907322718010141323692228615288735265261051483289989179905748419633218867831932012292500978379367 : ℚ) / 2710505431213761085018632002174854278564453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((634778144226468059729925181514993778416253985245151820982149491282586446602273818286584164869035501712195186928906242393238905612005788248169910681677739779423536101594960436362570050767466158673323901218736764596419313820729800209884012852390453645498445854054577769290882755092192759464828786691983 : ℚ) / 1355252715606880542509316001087427139282226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((265165851087858015987278685904506598314120797378434329514553269017078735534697155610373621939948413131505882195651588879292113601358239291037133472251111743926788131814291350466432029712555850880422105054411662284211562007946618719559149781639216389318940996262396753989376690317900378289198620872499783901 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((32686543447607693684849287212023352736016977272064860849777281268147793597860235116041100627964449960145732183592878916660603286229782152336429681062366048822890744491601017873869749987711302357418565610966066010795017459237605829683013535906800521498148891315456333917975652564760921467780070648669281 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((32310030166838206442189508013333067089485397094320954965955796142031616714283402280670854106576627953942211821230184013309381264735730332660442861045202481979479236804715378531063686806444516334983933372999818611519520526893940110038209819756806151428488167488878909275500087946348830668717111792180668557 : ℚ) / 67762635780344027125465800054371356964111328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((13275128658300796062048160590674762347026630306684515858986526548196074514370089218317402164627228246606055780820820248180950943054426041940199434748445156496964865745593879969637139448620170254652217610159911348415448821492595659821298761556691021376105559622813120586305227804895505932174533789308767313309239 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((5153354754275716755613627901986474872294161818657152422324708260794097104005551246285705347581929451139381111114871775135392914171656991637640514775962467350235955607720190279279491227442936673184593821692754242722295704091873578676989383578379418323462085660174433737604231561617519456011124935598540956931807 : ℚ) / 6776263578034402712546580005437135696411132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((1643908227012564227929222080595409834716929125374474258927087112742507092238683161676991760884502784911811830060978606256543899650963949313495099024900847225503681193151373501365027045811948368657299287796710805104922435443988541466156520216608028041830735759883909185056608417265181958650635111983930163520327 : ℚ) / 3388131789017201356273290002718567848205566406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((664550070017154077890079772874928912731352827979926393076765874955414756532891635662264020638362912316762863452112645679001846504642589191019061154606956232110426806381549907888725116468506205634050885925328061052955841996339466808316202321020858056648239975059787691317842133494969254136775348294225982382084217221 : ℚ) / 677626357803440271254658000543713569641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((415863729616233768370644512036571225207606222530513393366541768527755232947506104425079972674368389040999706847355254107340225120670658256466190354451022680658788715144537140829057161946245914270079911631177496165413958826349563600347568663487551328020951350325899402376498926311828714135698441129500149910353101 : ℚ) / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((83607623843917906739375778121552802724411706069630223302038549901854330382016994070508901466365522623746619893450566636732279954504582389083817241006746066359900104726181679628599276202412431664318550791132735058058047052934776720586546002591290067307065852898483267086021119011664074675335115615900933412843952821 : ℚ) / 169406589450860067813664500135928392410278320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((33264914760214268693720046953106838539986466055802000243245666579523296208203978813483463668871789323699884620269138004662468042382347011875447523767017309825453409226019881107966613265208914027383524711634039469975285435865446125877217461210602227932341384184343331981031760330819355670753453143241518583509067915580719 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((13105294899360929695224709019694566452822631156789849523790451885364211611128387080167851085554131794024984354008791054434315744804537900156988745247732644426721361618992100661670305884495208822226910642738768391639750827175219564327927999043173673105397622143558733297094435833277771121371210574036819236509100536865047 : ℚ) / 16940658945086006781366450013592839241027832031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((4250554776770884227825735162758911953822174674526840156259186204776003257490764800158810558569759274000001598455999128548136669884326486904708529058902729879312805888606404053227012175695986759865180811849362644898263948678312221352773712905553837925520307551258800842682201030910828285083750740711967415881487707389631 : ℚ) / 8470329472543003390683225006796419620513916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((1665009267365522542756248120300281488073583278287262989466357476892148659958527357288796993886947276929888861114866896401784081049861455792796720822853428967862048257505351175548438182708682998336831971381716986575164980161261264927726153904006578422502640509065760326253856150234493606963647027719261944508033952472559512941 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((1056967790342233981766098107315860201290124558515767613111425311543149279050850220689320655570421725893017926473622368855730754417082018104002352124117115361939008272388076868288763483771836548597157308208862227385305999490188541621268752927589991361172946456128218631924098973412378020533703807875492875310554580868053237 : ℚ) / 1355252715606880542509316001087427139282226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((43202621429065863289928739965887478359561738610959657581178454880398000426464282224037430402915565185448198131744445714998346318965697846896107644020498274551877755412109425425129866781071697423449785639976288974601703438357657514941365547842873171239512726378601635752837937422106738593889748963741264857693440417380097849 : ℚ) / 84703294725430033906832250067964196205139160156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((83333594378532473683135721491723880373158704899323915060454625103218995681785021095236601494836807687198031024093710629483699796609419164616644622868487788116049092810544749064177827494704607858599922298962757030166701999821694767428083168880966100258351970956850876019280525065903794138659357239658288802164212485603982880525799 : ℚ) / 84703294725430033906832250067964196205139160156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((33290499691979173589810875346640311661317314631785650888851387394683066500625807584681620140614586464666467857238988100788001398521394328154308395844114080378030792465311735237295784125661264839292087580970268481964866572032875795705811670034788180576979175035258285934144083371272862100219707567890448512184800082001995832035087 : ℚ) / 42351647362715016953416125033982098102569580078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((2194737879770821338000101919390783547288788494640544467871687183435747949207733890047405817549115249394268155908327711590383342258087211767695897797722461381045823506686259374824670965398952354684392316829153935488872773113968473020359605698482751513270004109604011599157918099207413597656340091076177481216385379291730961857739 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((4170598431619097603956781842842817562253231327456261282034770572740640237443664109408358157865112277566827984444753425363232124712371410000864010877397645844002438185996268926136278610272880509846541737250805403645028165569594869641792412497879861000078453558934993444672864671081638951902263440920252075845218812358886149005105639061 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((2683530718415762069205926149162299405844979930952875636316180032674783907328726668031947426351088484392043632018125625602121914487586649124007354976654656890900880266769099471611369607248485560235002079409982791501415542440721662031256069747439409698161575556438190983919208614103080262326748599307452177896048841004081575924178013 : ℚ) / 3388131789017201356273290002718567848205566406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((557271212459668451378851540955314371296838201931968933068993624138103456667404663305796578794877251864404945204785801113153150722308778255255327958755850671453108302622190843813377890724793596829481339667686281821414830381048263891675078643699508102058820331792991054436001155902906835089692846908490776295012201163769847928022226629 : ℚ) / 1058791184067875423835403125849552452564239501953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((208714645778565408303291092661989855334200228405312263073837050028421040152856882453400595203603527652222704358741231718197399126816475896030728608749647627440430933649678120909138037409653314353656130952265715922422982696785132560044452532737558767682698222314636655988434167730117378553720796341539762603267769595785534177951674719696479 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((84478187020927306690894368397709043514500506697497594854516761988733147491457754497195253946790687653013480997993952769840268684560469075762291939607988576661547396090903273689928204643632864841925276359019125708520307565574202382098512979869862066417723234612527620066559076595635019186074221291039834757332220706533113871209174430217927 : ℚ) / 105879118406787542383540312584955245256423950195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((28289497478469941962548049624081785513088903188705524974215317537919341336130686309857468045540777173075523816597820039385347596713802855851105811231565910197582888137154675440641569655111782066560417593948285168622226694372772559400295891117671620549866658042454783374650727620655860655272190306252422091107029693526600942247212402734319 : ℚ) / 52939559203393771191770156292477622628211975097656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((10444440002879433099527456485604653703956122409815592894037604701289739411765520581970850657302666689998126060766702921964107197439001857262992515887849639509914473781312176941535857945453647585316996356958853582867096981343754363747935447940715782749794711501689657326638798232630003107643844618743842869355439390975734295614463994611772323581 : ℚ) / 10587911840678754238354031258495524525642395019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((6806410180401688650080473125242315206931297825020303627620790989851568186666453351309173333493153843162790762989283050254641117725758361377129197665050267811174709221818147945052922279472465029906090625078826361690543728841435395274211441454803942623144850092344310616208684884460253433313858138156644845335494007617558733651451918698170629 : ℚ) / 8470329472543003390683225006796419620513916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((1435594562315935577161111770950295198328105443577581763204673074969028176674665976574126002893810672567071052887043324676407046968477720359148771361656952074372795293058895371598222797212979943964585841663954032847167156330497921518331320902492911778259051270448146035093700400398015769255385604706272092420715932795176340486303685602651161773 : ℚ) / 2646977960169688559588507814623881131410598754882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((522632473071915512754555654705473466618650546427176139682038648014097026131214874713523929134590405099821664378481609038466049180077108549520204206437344156857858379577274708847058807690739493524257891270683399042772084603563236952713929080477401283042572905478148756720426309887945716491223191482966009018546057451205138960970218242004335561284759 : ℚ) / 529395592033937711917701562924776226282119750976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((214166193586527403286218422028664532305939101129189429876300011717590792171400034825287295352421279459073002011936880346080909919743274349530264258269369230291890851233125018734640137991272123372101660021950336520310206937755869912898072103077136823807720347592657973432199504829563317332271218930553515283937544152309226336670335325170799847509567 : ℚ) / 264697796016968855958850781462388113141059875488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((72826520765053001336802989173676283368415890820765360524559865450021823372564420282011226009718252682133402450020487183411999158137610174060241579886575886236201386879826312233814594399143955580341228245908894959002585243548626344126923713516575435834243767098889210617846891649658449993753245561403671265560188319860977520677763689164216208571303 : ℚ) / 132348898008484427979425390731194056570529937744140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((26150972936946121149533543178689098526329712715574601360971619828736519714799337979120804495475457106000493437137244568464251092299654819915832906087249966210122586154893152500341505135733768985239992736608744747477233296127367426713981902924624219081343844191334454243044175821807873129679770023315534699125242602192359045481175117709842374023402254501 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((3449502350192578470045051213150039016837146150718480331110907399899449151361226159583045573379962589604217144155290290720703295231357046810659579971430945928535685953993374916148795279381347190533626979685181231871724531721257113270393717857190223619329394068103863394774716130480442211698034648646215363482891242003016780273040746811337178696397257 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((3693190494359361067103897078550567326356608781890425668810168745079974357715908308156338786888982108096438413714729559996897439990705825582079283285890430927379421818638734214150857008496286827661105749367755085728074174770579890445401863755594069157481587594684384351905099413681319037617649177020647416051892011800077440404441494073970482573352939477 : ℚ) / 6617444900424221398971269536559702828526496887207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((1308460752715157994557688900476614654602313558076668399179841187106810802835925992997775603112217572519757260133212571712836332239913428556012447360046876157178968588755508315713598210593354136195228017610999618651329300346147973127870392921963861063275467471335314838562859404064201331459974679129070990182064811024745613044937113873724259669089158874922639 : ℚ) / 1323488980084844279794253907311940565705299377441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((542460570736509962768335495688745121866824930849865714899766316808868206526916885017518035474640127652836349942892284875465000491207019235118911742704300862830379263860887792018978794125512962747493667429786873550504126995908643373360952438088081728865842917509352433609005960792342063322889173327213603872961136024104214573425042220026645821740457390726007 : ℚ) / 661744490042422139897126953655970282852649688720703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((187228263306682299142799878026710868434931907261532584011214082091834771106902430863031884605626160494196389109014736039995733008171041673034162698269599765407110878383433244643332946746737462573582484687662729938257952783279435426716029904859649659919128353958225261529734588017920230964977501212726813833931250678501941346283162298346102331405255384572447 : ℚ) / 330872245021211069948563476827985141426324844360351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((65466033394262572189946257508386600161781320333035934950188533719027954434882715383922144155106824151008837485419507417971391865457279108701870756105249695173259400305345906494423306049160120626106853522164911023605011889017069305274682451948454446661742261131275406175014629448182386563691746399465277406192353126895483453325290610893487876541193860204978279821 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((43667596836057274650665096546600469235790119937041003249294735064695423423057420901853912959326959890836607214803067586013460987715644800081403163853305947017885197134795080446123839451822064948599624909331476899662079011017056797213723243768104597649102061718654872686013356134166556304302088464070376859123546725136719003011366387652193942211853296504092181 : ℚ) / 52939559203393771191770156292477622628211975097656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((9488592226735335998053424856239483224189294928136017214546849086129013944230147344783225109842692594354803239246457951285960116006024840119719428777526969978691775152041836358335008203115325923142573058810363787064106722785989549133387666962657651279590300458573089822772728746956683260503326228008972993683822200368092018547968164158169288527572738821159252541 : ℚ) / 16543612251060553497428173841399257071316242218017578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((3275328446773280364686444654128809042950352735121974101679437290981258744105936320482705953327580583654405590225190160175753441145790679905097485572045365380772274870993700686240620223851358926194050968181331740741716655436375629981343256102398194161187868447467191371684014617557869520225865233524393711650501334048726194506300874106908125012275337376202471132482119 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((1372849724900127403842881736407892625926543306534214504973108047742068099063682534200184577966620226674253525862051026475059762048639131395754137288991294111189395908704693270285503742467367112000088771462432580743003720830094056382658300364462679717131915494483063080633263315443023847235209065317467897741152790388921729461672939162261542498844133086111051987803247 : ℚ) / 1654361225106055349742817384139925707131624221801757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((480724114458549099270714281383237930615225354380815455326841096317535392306976966423349085244714361028239059646607461577683680914481084844083230095605268042569686343916300400106303549276893007188296994864706753587742899693088934276463177230059203367704946720985013419786528595145919296520237201095806361623226631251377619789616537129530940382456874905391226131838551 : ℚ) / 827180612553027674871408692069962853565812110900878906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((163861962582502511822182715623026584371843831378064395382191994459565555938409732211234275933908821132885025117625238960524841462171426860046390372380646478684224265143772056648696596732129208421861368589099796926823781420615310821690539749410948474564234930745155934069812765057060411313927061243106395173492982385722904082832516904525542104953647128576808286714074607541 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((110469464633143920862069763959437744489900473249768414212955921331351562752783848236536892566333642899766786378796600033476468764220288751268310235475312364589397859370876782916075334346765184799304321209665238780234812666133242831464715514145364674791803633728381536633518726684898818374171722756417143247355141927475431526271910223872548160373198507531145179724667517 : ℚ) / 132348898008484427979425390731194056570529937744140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((4869527331077321614389782824321689804327241963110923709448372037638553316477458574478408694539190404081521793020596401819438238538069940443361075268656687190840836954803038801032072044657446250063167058601446623615551210237498253602053188910509756606482181348600607884761801158807082412687454838955318089650763821035741804464366766841653832611085809081797011316618208353 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((8197601800679428340347291085356282905514704057188060444077398426829460741380696366705372533248527919383067199019736139360180501685298890755726795763651294358695647634612270978362908873355838755798123053921575327333546232386385136823670353247482700142483470400395905576116903932024770728927207739938792362083285696680591975560642014362429529285409971993982165827414762924875199 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((3471682544551589493273338925312442673955307246595864329510182340850836045615049708281859204989002108621401716740499774157579845300604345379302173810177146452789923149624042757176081236937007279637267379879341525960146306866741047746018611352086682758967245208170525032848841376925697298670949128840807545828372569850725846504966614743403566688359225148929584613123947746197287 : ℚ) / 4135903062765138374357043460349814267829060554504394531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((246557075265526259306876361434723248424967486104655583171214720672922037728208228081542427422516506891687097817490265416784993290571203955425568951507939567634380593033549354890274673669823594492196889397814314212203335128108198427076499623040981191174069463709797176804507400498478748550219934587413525074587914931626339839432766562018367597656420447915144503328997113999683 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((410092388607369694313701957152731457123575519044662126781176984442313949887944646030124555844802357591798404694591341873299548668943304411334205425502758364774554133847987841649049161381120883109567722638809139355176035848461808964730996781733087002016528311204262592952574734451715667390899645652974733156244004455826425135953103915030565580984940669824325314938504509515692005661 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((279253735069188312679190416774902082638194653007581503418875666540165661262266379688560307873225426997744424812060499691680116830433397680580688614005333044383207710547316522008096314994012967837810760532237417200792237332251679983342362955880990886814633341210329243622127070845059377064252057152174496776210431510671202430622747659713639180993345182992710942533249129530003493 : ℚ) / 330872245021211069948563476827985141426324844360351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((62400895442847084290173953869081476219849035242024722325636792764760572492980113362977698098217351361978104223466723374028473866325734464365952426488373889246364858993388770473231582634136648523428703303280785729616285289405393517819891892407354689024867864709751217022583302025178955866123727232559152196024426252251173033077945324990869356682933942625808177494183598790814495949 : ℚ) / 103397576569128459358926086508745356695726513862609863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((20514626972819906109157146692228690019374120616890035269728526869626237283767822669214041437968138334519784998898341264565467424705318426645883109552774526557107707315460298867494528418344657308901912877470824020063643153860641212788454457294115988188057128061857734369191420407319424845139618396435575946252186126043201854483693365450625830922049118234848871020886164074060205454853879 : ℚ) / 20679515313825691871785217301749071339145302772521972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((8772875312278694188947488973907056699789737883995307214203104457139376817541578900532013718487770418079889005752284013329839098742636156402277036093769699325861968137821169849931178920665328982629000600516368149990376021194507436681512495988050524446835457045284141599279132297100916857925739308684509779681363575264563054484900589056725331475832684176172378488200396222698222199284127 : ℚ) / 10339757656912845935892608650874535669572651386260986328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((3157691739846493449329716293232910003843796167949022685485881083723996996379343557407486765652686278285178192368213673429770739158068362516872307651216569590623051701206147054640187084630291925715228324439687004899300035829931486197134133768764193265383916687877134531945692852386395571898399293137985612163684891675136688331805644514009307165636211581858361658669029465380314553208839 : ℚ) / 5169878828456422967946304325437267834786325693130493164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((1026203094184612858524736244625272311924571382991764736349264278107311199319531392804080699344380072950928145063068908870351568933184005313660283901208238407375500215143483028314824575112348800884327271131097173481780074629836766129634954662387333567196824959707911740429314366580630367775036471589576614530381801795550492218506821553977051043834473384472540931053552888287124024936357002181 : ℚ) / 1033975765691284593589260865087453566957265138626098632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((705425928015311096591903856695799471185074304560611555659257948078667017598613178130864394437023867536404760923314059212138619811419812365266780617558348732987958274509121100138330398656105674615341553863811263845794479409775028756833079847437221650220197145984757111200201462088921375009852939595166195470309598732307692901758473341840813081512343531951479261986712379932495323334103309 : ℚ) / 827180612553027674871408692069962853565812110900878906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((159744908309592052885233873346938516368111132577360761489620180299496226617327826952162137704331389095421625812519687168006552256566278195389594425099870255560626794665011871667682013428327988350078713993373554809090176185294300169322150569375254921671659025511690840106573166789712169760515572783762544294587217884235951702700998225822196343160242696679347013897794262599012485631741851893 : ℚ) / 258493941422821148397315216271863391739316284656524658203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((51332392322411230760256417170405916166877105984458066095244531305700542624723390325391560086394732258833801830128005295239502607941360826480632122819055150285273704641648646471732515646221010124886303233848789660757630937975875318584862127830276517024091131775671251532097449926244334906547444234261052032347667754840454652688193061232924209155313240870651106948933429600966739411474932725810159 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((22153886708391735577250131834526664365051595993753398335225631102616140212438859361135870982324657741080178379642621585864701837792733430986394038052548446891667094224019395190751252021635010379394092357146711147092701971908756459650014104106202917093228295757134472496038096032278688306360533627250327093182893526543400971381073000449169167059062376658420353170237374819812708041362655400759767 : ℚ) / 25849394142282114839731521627186339173931628465652465820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((8079146266491124338768494095298861029428674654491153223857010478686093376469100877505698625350228649008774451657672516292708777210150563306976720875074602955407478524754893530182177672950080840444299999354525882680587795590929248490330443409547345625432490285653880281643901881716805188559894734039473728899246075235287431461305077677073446583658054924749362941675915911131281228193083058954623 : ℚ) / 12924697071141057419865760813593169586965814232826232910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((2567667874968281267920671015746524714943656677081832187087560086219417878786835896548632750912561283949166584470404041612294913435747807999470517637567440729297517163102675546030999055047212196277015448140398095818453964785244786642771815843791404735998631860773367125971541692073231703159739973758831731752836710295424191873068732713458814295372310861401622530465772937959971129117516853761965085101 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((356163831017967037722900479976594280621509648826675848869072019148755675234312365267313680459006133617264229408242896070634315770057626649744684750716764398321703335987050374591317350356859013734349085944524470544361687817605025062002983834387479667702241323147073654672864286020874061678865039595582392265136947205887220374549653647082156755314006565759760682167191027750838650824958794827096433 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((408495978115341198521507554503397260797222777464929377751696812814254341592297041683121157882350952185837133096463374165467857063020459419758773575154646373192878994078848449863811764431035322486983657683063602286000155249756724182257222555963708208234293543878364835015287065333355983420429980030466420828948295603451500937168310257590604190518954670211821818939968151605709521617481355334848994397 : ℚ) / 646234853557052870993288040679658479348290711641311645507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((128432807622236723744159699348813440175390871004983657938311901154297139388132657327405999245267226364079763625350376117561969924447715921287040730917291588538355661551497022564355264455870535720302231209890225838786101446011653997553620627060483027850239507284995752951172503822640069255246982623017569003096969686616000980704586991379735047069555361695611084463626070522495079055470626969485272146576039 : ℚ) / 129246970711410574198657608135931695869658142328262329101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((55909223052404582016792675059373713866132713207707838241455988986663623301150601468534099713488844499970373564094299168502930482055280108591601634424304298310284807832056614333453632064054071319843106260199198479828072137356171694601942871450348028285809941800196105228324512598424748132296455378358585218960116209145660385374208364202917861290830971657792767116682665650058081969426185652005925227040207 : ℚ) / 64623485355705287099328804067965847934829071164131164550781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((20648886057652311625127051735596350432109402351170170864649670161410711150670284552133301386419504652520839928008997760803968820801152568469726165428362529830409710361101411982489362317141123250469209182858537521070509145183226416113224501481679237773356071398556193504886703226371228414282033121050494477014601651362876430138086715558416761855791732922015826576875057073777509548502994143778338341648567 : ℚ) / 32311742677852643549664402033982923967414535582065582275390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((6423969701709962573358303484480617338310842213505083175113655021012412853617185333756591398422651783576355977535391379805753700268540880813549813014710208192109547529876018146661142811185281183319326877003015355814538036063543357790680122739004109449832440133907414798365320657695430224623087513866425185236988054057391670229433526186649330383811770194969410910530869338359895531595829884714566243717447902421 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((4492861158862274821664861656537353063561730595103511798455259505889880598234247175040305120219019847653075061908906278728043997737182771676138698688001932704633607085343328397844879583121311516086690622652648381524647975114371460576988628607722176242477459432222480228935327845185537392589996642113149860258951360911047683500235582558747415765086214240965308315773505059350791899543342883422495426517167261 : ℚ) / 5169878828456422967946304325437267834786325693130493164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((1043505171242000250042622285472070548447918946297071738092186091109064103690370422106415564505047157868603017537463649900897950620280530477026985294218783975178130816097229918433403620781393433911371307879049843495854557021332537984479473932528612980091300603773144049935778348670842915231027074628671724223282783638303691503403548222267003936337077008001808492113692795176270296019571796593804998230041856261 : ℚ) / 1615587133892632177483220101699146198370726779103279113769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((321308286929173208384655038798776849804789388362474041969661099660504129506660499447951961930245382426005844425040814252663423676958748580669924635700424503967851961010825619415459610976462969700489749655045140857741508481999370342894870305793914715355651395472261626180142850483104885358507722316149416806886379880211385942945266990912462784962503035220663060911514649740947115463895824935559938162596776672223519 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((141013486407067102295058787162045640225010101076991393625999607102516865708929277128281385975443070108484174882316309918517918847531437863956645298818674195799467598192589033673214254775079701711384781402101476015979156369172236470307464007084687009161499468450579898239961488926416669440738787991433248943046597260129606733233945214287935543591776874842244305933393222031440000943204620126243372427813715447661447 : ℚ) / 161558713389263217748322010169914619837072677910327911376953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((52721076668626337898566771804648047780243441817968169312781879467238231889570878480942609420595340261837947046987113812218143850204326399558403530792252874231366626101543352073392366609970912547675264734666144977248853124962316434000959518002610883587428949068414923363501176000407896966760720901745561248325105410117832221490073399102945323941095930922732398045524848448121984990276402231366497292852744203031471 : ℚ) / 80779356694631608874161005084957309918536338955163955688476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((16070590295567660002000152416127793377655696841021560173306780358146504160814469283477007533429837082179489500351998943056301128708158449344199577402282310692540573590089308873625350601819487928711386308989172894893076968332968318593721291344819345767150051131166940796505753828923081190914695522260967358859817061173284521964496940684622583220347430577266836028307889074138506075852585291637359925046649455551944462141 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((11328656440221503425000646749935390379603304524495036097794000643865015002879499086278321464938445522842320204117991198557641639943787310315790459052395933451258639840721707008923150852053915016386357202481858140384121116218493729358238586670390604425165906133867710395329825423843118452352081952553532186840592486918342609962225015635336923351692013362020958967354432565232474963421421361467608045958498507417897797 : ℚ) / 12924697071141057419865760813593169586965814232826232910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((532596266513033283157453599920366758864643233300257428454884782085023635747878615362618473910079214401519444181226129381505397457717653654400786817039781845240447840998244173424225095663156999996420233089282704542196822797677251525398654688647539873511067024429650991434073773334614942219399915230310050427235467008178265077645159071224274836621390480195036398245379294186688528990509507205120444133822627604412723657 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((803773503843432131432080111853460624764698386539060140454454608365168059636633267553822658118349090216858955557092878176730978906173881143636223879166185843735670098463219930993825402019168841471526039219440621092364755210247793570189427952703439140117686260272078422206484729741605124258527832223859740329292916446647459080884421286932423950423957529981781383538405583065815037909615018062493509506774008685263110000864599 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((355466209454107103036877464327363325802789001992819771199718179742641352043246173683398778795934805184042834437307038983184752800878620651135694203602570977517832221280968035588989323038506179539852591510614412503099369540634236368215169588360877523594853916710487003075431052836280673261986827980045653297627486090759901249769900501657600586516639854866333630180395957877786462272202304648343508785975162782017942323679487 : ℚ) / 403896783473158044370805025424786549592681694775819778442382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((26895436693806891528762981444451538984981054500426624466817300855100183047519115145511005494623901197071026319885595026355187541314579029325908221798823827751153702813569158518366331137699432010251990471851807038966802610790354186601002497497450329250788919614413290066830585704633295172003640044617191088194729917433179530022378724831873946100578595587117768047611373639420902960047595962676342265621346843291973898274427 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((40200176592708957573466570748140909027552441900571996733129850236850657163211255599219646281040857763732514306005801184372921614658130583229867957440014834487855752771457724327117935625781600018126265962765211437672982195855870741105159444262487417626007612622965504744391483675289523952422743483200524299382538788378514573613810735044707532599034934005811192638616900780139455072021342336447881544639819995414617742330756332261 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((28549745878402104194144200608079372652513446766774284724341692482454625306102024577202427105432456360716260959814381441469570040536599086266716625011844894559420024552905077858128099433877634294661180741876427127667513841986158662851062575394339217660942680807441017914761054349174879684551038256694328590748865645354714717632916644220125227149306777365192417440424402304069082229484127218964625525909471467557865801242524973 : ℚ) / 32311742677852643549664402033982923967414535582065582275390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((6789348638236363790316925832074200633761668317046991136288704908367116879706796438204565937610195014730249336398906230749558973511158509912389650722816006791693191164603263902548414575252622480157058461864568690721568179676165682388419918846696067605630062197072052572229840199371314218208166484797440195057352380854030958709401088940746004397156365298318775065828985051518293856544395833850421691605566313445260814497694709269 : ℚ) / 10097419586828951109270125635619663739817042369395494461059570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((2010550994155378067550127996270645742488260791626425392615373732971153128016615377691614906041984994124586991870807462030155151993369617562872745645764859282923032329893745667056012367463718843254454051218789301960466707730449890864956111043089394379472372851433970928145870148969472869593255705054589514948593495945374798485581424239272468379185907754099933809791762085874993772640014056397816688132776474763849665755729522746451279 : ℚ) / 2019483917365790221854025127123932747963408473879098892211914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((895595895343308445856411513233427957152461560977369232242248860194480299092340147770007322630996728768200906390621453103503784778207169411960023968984785953212331373893090750458877670488086031470560339240451043628372870111350949730389493218412910042335679526274075633725944653876002429872697542388083556926538519163220471656694152483714463454403274699622848792837693975212499018101249776360390317110071489721535541405347548694070327 : ℚ) / 1009741958682895110927012563561966373981704236939549446105957031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((342695956592247330284160940806647245114788674521870495694298309442849373627413252480875482375225646399874750291249546723618406715090909954302064908155186021040461665923547068540589286140352009298556707720465762123103647246268270593646337166184352276282412701544256072618057355745670906134794370157087189512048844596546994464764094885677657517295539296895190790343284964548028680458236254090544184591133406961795231108948095301467359 : ℚ) / 504870979341447555463506281780983186990852118469774723052978515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((100553106801073892550969849504903541247077437100246168513114388531339687301575232289005035055913130638038906209797992952639483709815450402296258356995709701737708820998861276999353366989872242552171709520402508905114440135705677405483166118460190961653948183843745955581868172952271981599756480680568295145161748805369022625811822757215064886926444505620516779859773872966061331448477622604536680861890950243893109394059333972744966840781 : ℚ) / 100974195868289511092701256356196637398170423693954944610595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((71913359494706039204687064838100586812092583463695885786732025841997975519519651593102604046336464050571682400162996838293299134104213786565421424982464528327401335149295941754736870549528599177960336520296212484718976444753460345619898790796139244572717350015136555471108121904962791643343532174327909766329971066525690417920092504759213973781185454809227354341665270369856956284073099675684851437304700867255370332090829591519611989 : ℚ) / 80779356694631608874161005084957309918536338955163955688476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((17293922244106588549671130891468803290200057074527281363041130218813216316111660451649624181676855215021855228759225962440714433065000687289143657281333832382749559184006172863356382524360588648673034707339524382327481703056856036949441150205953077369877171648464275191689669053668733394265271871024308723274589938114735470662669378057138751218574797296874717196762649130311580357400689096538940804138018487668805980392305443148357606013 : ℚ) / 25243548967072377773175314089049159349542605923488736152648925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((5028860075874998512196386030246726610442148889656909234070613467619446519708954874871408347500689065146515999823667589794472622596990516513843322690420759630213856113065321736472518366535587641666822215082253867278189593557029927217070967658094941741405463438210340600173683804797148940630920742801308864847779676936290357558143512952360943704825667550445540485809880597747165103149786651955254599148677503546877283726562944141224991907575559 : ℚ) / 5048709793414475554635062817809831869908521184697747230529785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((2255363169636111072210119817162802638330988246022860548474108220227670293936936092807259848906494862365507072534756496103578652803440864489170157083558111694516933787526614881638617939726610574951109531933871048324974313620426871744529764733262869190692522170690910081233066956102386087332987219002979595006309304552892241129785553068308834577374917216929854641485087758805861166899977754608669084155673778240717012512400393051380381710129967 : ℚ) / 2524354896707237777317531408904915934954260592348873615264892578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((872537122138684847218072019955282736464111270866790880131259829515872898470662703818670347612206941509476399857196947894017997154412679471670184378637580726874896883288233939895407444954893219705633245036229324733362943584838702733552018224281264289444331440773350329751533323912467728150602880598463525064886635300281031309528631230792632602929040990042883230025134186776025857650831896818845479165710750990929923853671795466978983307441943 : ℚ) / 1262177448353618888658765704452457967477130296174436807632446289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((251499793835630369428236355801554374669440735618957299211400363582144339492560423846563318092834981841941617715687866515321644956599535957946060388303744188208650963313786201335578043280121065840532332396762365049626579250684833739085508344434937458748112141013797245551587280874332803912400972894910898580059486191099791164933327057061342525301777142660452332960591961497203615797377792986518746549269508839696248277586450623873204893531204275701 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((36211323430532433702692010777552774645190720897963102989922260979502957723918707915561746289004266086070364329851750347376809707242737784519322762121615077971334381023873887265804712265296601658182809978292140104516574109607260466658749726519731630873011701053070302090559348183619754745115144096921299025333018289917537601308895028919987004065009045285039426014337294299505788326846947169755538222696815258228605175186321153985323682070846809 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((44013144823430809583878500661144080357415457181486528049239164016618959767758812479607146179947682376839161577384861883139765650201057911281702368694875229676005569160270958275169159156455996855885323434500555422603841238065152482649612187525581372315352093520549683019826276428989416535221202593482358029715869542715965510609052877528921372160690293776435136254602867613438426637401518509397304399534496522674451066441017772551837933599198433317 : ℚ) / 63108872417680944432938285222622898373856514808721840381622314453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((12577666717565720712568179312217168116533180791813040868853487505500264519339805819703148251578148209047285917499810339665747021609145525521619340644250197287967597759648567744757813382181626922656853616850981126074347319298032377626751777848318516867927258215249388358056272833135174043626669461293204848165424119562253055723792104142814625300200472727871062523429344473016681245072591783591507193586015377194441447557147695958759005476167438352269439 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((5677079805973558378746940029343101134895758178921797586657313656019747040626875965832869777323341223283123819914500612898698471061431424408302303477160398945843070023989627710566680325310461109337069615022701313803787983862823515973038164941848834701612462569682340349766490809218705646848102776116841626919782296062105442340176667245365717163828534577276529946461037025496625802207055865768191648218040095099375530333895341472685778757175241577874407 : ℚ) / 6310887241768094443293828522262289837385651480872184038162231445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((2219683751899219521961863771051880162729675156025799764505944955139423567665198975298982845745869044683283793858887960181427942779344595457908143957683666054896743921414499347493021123312517736852094501900091274155116866896866658815188701346163578557366129911741041364282276296982856332445648241701865059435607072040212478635486892622656125907074516606796655408605841300932443934451747335845090646223896751993640478525009328699844945383889582220348687 : ℚ) / 3155443620884047221646914261131144918692825740436092019081115722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((629009528196727545074278691402989910294778307118825570583248835851855094177159106534986705431142328426280010865023559601503648851633510927563614098629310049957504590792073834920138565022659711507121422644738399302018658284389948248947452055991886566637223025008640917810414645081158969242517571735900383337669927572045046793763835997188138622026150083919114016291935869113533337211476904086720057598451178865568775396396385239799940759141056876487629085021 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((455648296284209923410141193603324796625234158276167599559021759947899448404759905735820491599590689194166939155074933030613223301188299530689298123618074404216221703499544087931708363173303214284429432867115021781645992170050354408531487297922655546578244471396098785897322675056738381990563999976000222708630064744601392064781946417431860534012227336590125160502953367974884842157330020300504497921671209106439222623312016531976677177545372022363978341 : ℚ) / 504870979341447555463506281780983186990852118469774723052978515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((111921135807707541434554360405434189129227118556510728154934833532497039611569382622481964680267975806539022760717318601321029976192805643649219111664460654339726729781863563539445599191190754048778815717700010413234463912145634220904829264331066837801574809065925663233363682078089332309623714448677078383373119693060756058971731212806846768623433212872140967311133826345311422338098162616171586150512914269153879518226361084835505156402451941410277363981 : ℚ) / 157772181044202361082345713056557245934641287021804600954055786132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((31456424989535391567482787574264782503861589507951850425041981289724503534417103122952738307318618219686413432166345576055280503217152071614421204995287046444946808905347568504300411816603156140734196742050323404697857532867857770507133942467401540864712056175882324224665135954480752651123035814058608170154422715818631460811233465071451666503690688805863115613985564934142847982811809781743896795133390120544046503410729203818929407445150280100750347438804919 : ℚ) / 31554436208840472216469142611311449186928257404360920190811157226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((14284012271367549218161295165048817167825086802350364852068225026761012215887852437088855158322471090286430350645424836444783727794071499675291473886253609934585159422653909047695052204235140681482669343188903809587182859544446618231989279410809531150564853730001069757918475900577073082963139616076793339093264459676252535206015132597122164594446829764719774642924368577687861271794277619075060262495871445360493155546263584607416786173710347478213543868439647 : ℚ) / 15777218104420236108234571305655724593464128702180460095405578613281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((5642186790951974674009225770841455138523019981465390960861532508832001389133055116234920609575529419780841290663884737393760340700059088653433412022899840738810790113671658538376248841710443984067410334313656499576527477289748294764328011638185763103121988107899750945610542279874458713343701011247201927865249680820033351895953317982900221438630317817942829907610594516401887014430714278462371716672959852062679059524377841381025768402955438969299665522568391 : ℚ) / 7888609052210118054117285652827862296732064351090230047702789306640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((1573101659575201414110889340474229638573333212249218869851964676841518684608887824112869131068692344257797842778889364109669867641153331503832201182272836082368347624989179031724217112622856177318069300223510194974052306241857947443935786913970841234821661616074916881626489843758268199221288785238908730532909332400974468431180734310003160107317475379619581406927665545430559711061765901301625551025792876892325808124278363938820513337556939053669270627917825076741 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((1146219412330568452493364844106040623287344611130046945582618781574169419960147456526024726568101643641488763119270387553497009866813975762349278808048519720715393238573032869510876340671541792449447188332142855886400682048404811302192212153536534230081399239164759660352810768692675032411921480858146829158532669740379975100532725523461046694511428543037186194970588812020671644075529415429205602818065278753601142948636893072905823769367197871783887841626144077 : ℚ) / 1262177448353618888658765704452457967477130296174436807632446289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((56876013207104535760431884232992149688494147506142034464269582313697301120186482932128524806145846012568139718913540395692513032224635419540913612214843132156492187026886609008163191171555717701474967632465189844465001737709176381988964771360611544979790061934647626831123407847745969899797156784140393046433619444043012053835629206218984323054285167970533784061020206547114320952887176132633275134662901214249790039769501110149645982783839229381294247047131963761 : ℚ) / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((78668301230390049010339123471162813738898441513909757939247298942892114898778363140856537969447088415968332510754065734765727890736326893759146131531159220086761538694364910376447870471928817342596468743236047080881851663934941784559689059337671484968258306920155506882991104744921004643092332047376918648590813020049535467377428634639238964298838471919887447941163226146051154219740582821457326849804850423827346269170357797712060178219096550050915748129418356292493999 : ℚ) / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((35925584472710891212727748125317420374343882501204818811677221162497266204366246568553963739957110288103918072359209255455305102555817089956692933974380866400981937005524353346455451262880736719169713693689371286662872264449433766713866639741608675989589200037207797636807742143495660040263281185980920883126296755272577343055172396954255085970040031573435154280884223530162362035427581310098119828524470898836931272379833969959756985647491825370698629046012057156481687 : ℚ) / 39443045261050590270586428264139311483660321755451150238513946533203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((2866151388251450560697484987294391463774892219810983375260330270268383123477090764520958743502294107794954696621402880047796841439090945408373037909060475284312374265385597359647267160880095170584244220823636212536980738793397431326586883979219005921411553345969290217394734271893355471503543013962033240958506626238052937586162226845391175431078214580104194797681717700980841020042334592901845558345924855276174828019778796833739448695433599974398983249341114278201971 : ℚ) / 3944304526105059027058642826413931148366032175545115023851394653320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__bigcodebench__self_rec__minified_sft
