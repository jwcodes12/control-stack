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

namespace LasrTest_closed_source_model__bigcodebench__self_rec__none_base
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
  | 0, 1, 1, 1 => ((14301 : ℚ) / 25000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((0 : ℚ) / 1)
  | 0, 2, 0, 2 => ((1 : ℚ) / 1)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((14301 : ℚ) / 25000)
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
  | 1, 1, 1, 1 => ((31463 : ℚ) / 50000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0, 2 => ((1 : ℚ) / 1)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((31463 : ℚ) / 50000)
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
  | 2, 1, 1, 1 => ((13593 : ℚ) / 50000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((0 : ℚ) / 1)
  | 2, 2, 0, 2 => ((1 : ℚ) / 1)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((13593 : ℚ) / 50000)
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
  | 3, 1, 1, 1 => ((8227 : ℚ) / 25000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0, 2 => ((1 : ℚ) / 1)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((8227 : ℚ) / 25000)
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
  | 4, 1, 1, 1 => ((14301 : ℚ) / 25000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 4, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((14301 : ℚ) / 25000)
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
  | 5, 1, 1, 1 => ((31463 : ℚ) / 50000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 5, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((31463 : ℚ) / 50000)
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
  | 6, 1, 1, 1 => ((13593 : ℚ) / 50000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 6, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((13593 : ℚ) / 50000)
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
  | 7, 1, 1, 1 => ((8227 : ℚ) / 25000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((757 : ℚ) / 25000)
  | 7, 2, 0, 2 => ((24243 : ℚ) / 25000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((8227 : ℚ) / 25000)
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
  | 2, 1 => ((112440161 : ℚ) / 1250000000)
  | 2, 2 => ((112440161 : ℚ) / 1250000000)
  | 3, 0 => ((20253120053381 : ℚ) / 125000000000000)
  | 3, 1 => ((3396131742461 : ℚ) / 31250000000000)
  | 3, 2 => ((3396131742461 : ℚ) / 31250000000000)
  | 4, 0 => ((1312336826196326959 : ℚ) / 6250000000000000000)
  | 4, 1 => ((93271205048934761 : ℚ) / 781250000000000000)
  | 4, 2 => ((93271205048934761 : ℚ) / 781250000000000000)
  | 5, 0 => ((79743495650068656520301 : ℚ) / 312500000000000000000000)
  | 5, 1 => ((2451449628404816017061 : ℚ) / 19531250000000000000000)
  | 5, 2 => ((2451449628404816017061 : ℚ) / 19531250000000000000000)
  | 6, 0 => ((4653091141448586399710468839 : ℚ) / 15625000000000000000000000000)
  | 6, 1 => ((40450148786791569928465001 : ℚ) / 312500000000000000000000000)
  | 6, 2 => ((62997634260817273859989361 : ℚ) / 488281250000000000000000000)
  | 7, 0 => ((264045188316744914295951790601621 : ℚ) / 781250000000000000000000000000000)
  | 7, 1 => ((52554037845985981393369675873273 : ℚ) / 390625000000000000000000000000000)
  | 7, 2 => ((1599415495688947833471707851661 : ℚ) / 12207031250000000000000000000000)
  | 8, 0 => ((14681982382063038514996871457169812319 : ℚ) / 39062500000000000000000000000000000000)
  | 8, 1 => ((109920691462250087758438304395077671 : ℚ) / 781250000000000000000000000000000000)
  | 8, 2 => ((40335399206972642966478893986603961 : ℚ) / 305175781250000000000000000000000000)
  | 9, 0 => ((803851780008069572558437523619527782905341 : ℚ) / 1953125000000000000000000000000000000000000)
  | 9, 1 => ((144354626819188164032243622365570946828133 : ℚ) / 976562500000000000000000000000000000000000)
  | 9, 2 => ((1013390499137040767063614662902423246261 : ℚ) / 7629394531250000000000000000000000000000)
  | 10, 0 => ((43480659682800391580832186425900920158374869399 : ℚ) / 97656250000000000000000000000000000000000000000)
  | 10, 1 => ((304307769336850639507764059175882218382727991 : ℚ) / 1953125000000000000000000000000000000000000000)
  | 10, 2 => ((130157302557450927704423173481675935676575633 : ℚ) / 976562500000000000000000000000000000000000000)
  | 11, 0 => ((2329029348037527658728848435930543475345632968599461 : ℚ) / 4882812500000000000000000000000000000000000000000000)
  | 11, 1 => ((401781521981543399106026169454452627572513510425693 : ℚ) / 2441406250000000000000000000000000000000000000000000)
  | 11, 2 => ((261646718127542464591361575289147290261206849233 : ℚ) / 1953125000000000000000000000000000000000000000000)
  | 12, 0 => ((123757840999641016304819186421329888884317792506809992079 : ℚ) / 244140625000000000000000000000000000000000000000000000000)
  | 12, 1 => ((849754163650460867468500924726720460452701368949197711 : ℚ) / 4882812500000000000000000000000000000000000000000000000)
  | 12, 2 => ((8233025346597543314483735147445517836325439784836773351 : ℚ) / 61035156250000000000000000000000000000000000000000000000)
  | 13, 0 => ((6532307195007077867592871628715069632117856420978516216611981 : ℚ) / 12207031250000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((1123714195105634389844691520028440932023170533299425169392453 : ℚ) / 6103515625000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((415268064502213457062899762359496562526142646814959359377261 : ℚ) / 3051757812500000000000000000000000000000000000000000000000000)
  | 14, 0 => ((342850745271688643600460375705999667388403633828506275934872172359 : ℚ) / 610351562500000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((2377174520420485878871100674521451789663546551529466621565509831 : ℚ) / 12207031250000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((20985339021149286912264189358424080116184092467177784351995963767 : ℚ) / 152587890625000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((17907857101674630970682101650405118321021958895041957341293939332830901 : ℚ) / 30517578125000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((3141030109098360261279153187030619535053689503244622216213330976122413 : ℚ) / 15258789062500000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((1062483175578402020485677065497868423632684525851277207904003572758437 : ℚ) / 7629394531250000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((931469266931465429326983589698446872534654120353382827111255006210315842239 : ℚ) / 1525878906250000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((6634089347828431650927494895028931733825072485514620579307163111328972351 : ℚ) / 30517578125000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((53893319043681859083056857160311827376289984874381205720107008777690243023 : ℚ) / 381469726562500000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((48274069324663598873044679434795087124411060579338113087197449737748078487304221 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((8746633638037352755672289514411043883664794782424058135330397805098622927839573 : ℚ) / 38146972656250000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((2738621608059611688494897617163301795229435703407611335008496489476989924955853 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((2493868331434379887276453143876805611957612984649419312817400583187706671813033673719 : ℚ) / 3814697265625000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((18425309962105977202336858069114950187862016507166873374265525497179485067764753271 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((139406008952372608364407529028189011063428669165716455197667071927240991057784045319 : ℚ) / 953674316406250000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((128472308152438358506324724749208739742069918483388976986899446090885304802594594345439941 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((24222097797462585840480897538392428718468856338541935980418728972879206775453512168447933 : ℚ) / 95367431640625000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((7107938741097593907710888491418772822726691115567061125322060719498328447335165176990709 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((6601748577845448031629641199952950782701433887388472986185452989278242383089506582849693378799 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((50867446843166670978033784587265852593137115868898790541026614946792855818008123956754580591 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((72594329166707423138102835766298737524521453935532154251908482775613102525302225496617320371 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((338484448403439387262989656524582146945762892017605228095796068461587067696456250808951696183206061 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((66656499364373484385967290375818686963276140453238743004847799220638589663797303937397282751131493 : ℚ) / 238418579101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((3712341930278361967925911969627561839678971199081993953255820433431987848312964454605303483045241 : ℚ) / 23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((17320049522908869901190069418912277824876316966817892847207730871210752784143251206883174006380150509479 : ℚ) / 23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((139525590224896655203843728446042141653573978210922434040062720673492162747403738422840843419281942311 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((950442024176214019564456077611304562824573026116549522542478331686940226442006531810573466437264315831 : ℚ) / 5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((884661369941358249522198682338105864386844705498828650924525225538003675491728718641265939486753914866330581 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((182237221679950495120540057985986576318811069632250773306998279133880064931861882692857091073512380307954253 : ℚ) / 596046447753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((48723653779214082152334959939903060563906135281928727214202791378918822999261744451019728055387108375617541 : ℚ) / 298023223876953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((45112630091713538086726923686735972341331472572509283775931194606635955259004600068030635121466092792883957257759 : ℚ) / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((380225703496787516052112386161539651149388598570076971332519366312703104425339755370292289359271759406611286431 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((2500368653950696512044361691541531632774892854991210103101234240102605261095624386650635352436148208593313462447 : ℚ) / 14901161193847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((2297093158595677049995220455669047000198024285595515127913620582562212294954217842606896108990790148163756861173501501 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((495040847473058135914220310116569419203119314494108328619093264193166486160242066723598989333791095408937026491460213 : ℚ) / 1490116119384765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((128428645994130174824269147884189840644725634195042519741434372373082824940731998881525487274343300088625515135911917 : ℚ) / 745058059692382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((116809118838161249365974697059783206542334666798686987614720160641400125371846874882646475681716856794291334678857687255639 : ℚ) / 149011611938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((1029658002065424972191330713650138137545293898670285654930238671546778598209833590160553638053768927766307384414931220951 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((6601737251208500665416578679071071663836928420652871616947840579875520880099634942279409210909489107321662055933860588903 : ℚ) / 37252902984619140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((5932587274668064579175181244701120573199113858223305909170293652474960509903489835093072217160450912426099225426672519543566821 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((1336524450164092945811764370225270830778075342039792806248031967320967572726537870599278474457935666385208036370454148728273373 : ℚ) / 3725290298461914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((339578110051183530862109167589268844945841998436110289238887765214867290363632000505147912600325065815575473694061737870048533 : ℚ) / 1862645149230957031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((300972342628376968463363868693966122700033028162788417252378472484017163476340607336452331244726495560853891387387915898764196375119 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((2771747722303197418282592778279249191000699608992657463079359610497919153488634279961682871238317202442390158604233238101341713871 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((17476533252715903037359730727993819234943098170097366638366472383470027893125050344536255495504018440587594901062711212954476114399 : ℚ) / 93132257461547851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((15253340813549015529675759406364869057956856914565683200859868814424085069111219889233026442545162274243091586110078967551845452926734541 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((3587610064959502115698011284792524261755423033359680575731696255535453694652837882209248307123784154080109626532373971899905855124697733 : ℚ) / 9313225746154785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((899822516935771285810421972406443110365139297975526961316613660613600892405833594753459732293192991166552360124511729902378620817758589 : ℚ) / 4656612873077392578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((772317510329384723717448122656633562523028278095711740405333356043136946072833794358555633475136404445545094277643012451426442805513339528199 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((7419825624219320973507933001002741489293871275192147783119117813536441609450187640517880577448419453453208627309360567199023291977665293191 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((9268923075064429933077502859337348303062599847578935688445244802790278263208289190409729909692091994868020144056416566554991708259847826027 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((39070789005391750524519912053911049503773030001153755730967009070517432500927312232267954006384454969158550199153813963947791087409093312019772661 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((9578585985716794153891749216016544703077498472742615722794676008202852365072180130783175556494779898668584473961217171956025900574500583164317293 : ℚ) / 23283064365386962890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((477497044205244079619923330046626046359270518986314555149062000432324863361686069905566342386973040094491219359085343392833631126822444827473057 : ℚ) / 2328306436538696289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((1974983617223905929635500384309312962558356861224386891402053840575121250661212571316879083906956822791164897837911636446534924069377249635300063466879 : ℚ) / 2328306436538696289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((19760156295221841459706277036503554037910870986410874360950587472004207847043668047239195648601557223139920372209720518806733986736956756500162246911 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((123010598017864935396754067059728076759107618261718397706942670503018075865133194286209312281140422493399624756011701197895368800810462240979681399311 : ℚ) / 582076609134674072265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((99760037447254911700095665115956703742038384081256373673801415990870640634918899399306363136290037669552722119181316630453209785706374170558409691765209181 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((25447336051491651914117037500719932939710338410124802233417609361505267328544520139947868471969943902881966306837311835661609539543720710365593815637596053 : ℚ) / 58207660913467407226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((6338252813381272607271958988373805289909555212455504028499812189917014059902149475955146492913158995462897198964052305099572292375092978832906402849783821 : ℚ) / 29103830456733703613281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((5035652640973009786781200182901083057695947387206344198609324948393651128889441998783902651881576085705045767976088084642933856088412772025952874460120195583159 : ℚ) / 5820766091346740722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((52374315365607848114594043950107435729900740996112889438422155176281338666097728414031490705044250343639457159901366334125675197683862704395955915266829823031 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((326580159300583564135174800898337312521915420207582043616539024126975831076123821237101769288668674588495682083246885124653700589533354749439054367012278557127 : ℚ) / 1455191522836685180664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((254028841630169733546598526671774154256729263885519859178244968742328320564719406380674387107045615104050152456624816221983259042151689660531392549175605899594532101 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((67297515419638121500698538912578848094675015370553441491130674382863418568679669090147685765593741150921287642732339881985138119931422645557204288656998758043478013 : ℚ) / 145519152283668518066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((16825749522142223216226777678112566156125962587536259399413650410531674479812839106737662347323351793851178368239441830027287729900281340061995455735382092521721397 : ℚ) / 72759576141834259033203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((12807326154971722330029084511280761857507960770299520641803289581544614703100308097378609933839023250389820136652837211888068847987988498907789313375588886500986648709039 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((138211486630024497895105777696233242539630273920719707901475732778618330055539801045402848122824466563093420722207408695918909359116151498620354851981967017939565429551 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((866757510503253892838000336457788070653592408654792028448756174312866376684695826430524094696874497127915649108005957861365822428733127996932715313299084197847096510783 : ℚ) / 3637978807091712951660156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((645357577087569581934039842902263833201067762751149103533965267584431592489445423402330293671237717000125731421678093331191677425305789850014280443211884520770009633495389421 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((177228199417897788927384485409528661670546362836117131058618899700831482107069503066900670071997817744998783771869908220157374097579550332725859644055262107876691128502987173 : ℚ) / 363797880709171295166015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((44641257038733981870808161156393526508772584459985866763401820110568991036235252575094640156197109897450661149818552082436448625900827611170669850254378122231320597176077213 : ℚ) / 181898940354585647583007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((32503162299748820673728645560819814833265133268326417591487588748662520838359967813762447713368474741668926853486483641539044482151489627739823165812565024424577484113339161916519 : ℚ) / 36379788070917129516601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((363264886513259294698289292825736816459652769794983803515336307138237198278315284448692396856800525718124248345963787464570501612247942413960273639886993405789285733966073834471 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((2298637735739404471206034557283909723188951126793815404101675156954577531337954070177682529857875418520756835825407836791672780267295247157094574109983611050170465658956041039479 : ℚ) / 9094947017729282379150390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((1636249141318753565285891693403985251425285117135638998845133446023202569799450522772948022760476530847531542946499352378509017844139069562027524213238502686350158023618694753582789141 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((464936426047957111318543950988257481900349810791112715547871009380351748167698367679500661768990692628667685260649273091824190202275021045280991829109130780316887857900774144024827533 : ℚ) / 909494701772928237915039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((118326537232324197343060916411194716090038413002095002164801561272690785161869157804826618753203897491612917341778089052448043167051869663843085698931526715583127430455450553157542469 : ℚ) / 454747350886464118957519531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((82335276956169419691361502050995460766936515136656886766560745512087745937776298192993996844906103187621789402955032971770536592154871600084415463887849778131860099075361651989139097317599 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((951261926133581797932493680780938764109972070387582793927193591178211968279888284041895629590438538265806510622333626595228760506220797842397960226224274461920467772082251483025998365791 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((1217827471752954913128757872802259583628033459917690120126461370793722336544267129931641087565394025619649069595152785105501346596159828690474712802605923266492680140298772309484679718883 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((4141409054614105043698582520963125025092620387026868985288906982694304255760836920519544017272028798161303530665897299256291324417588492356379260552209350691357753210313472913116027908454299261 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((1215399948418641427070232872211218486716473587078757746941134195899320061025363241233480243019643994271927056428898665437036838247876777905926589994380856571062713104929549905705742215762983093 : ℚ) / 2273736754432320594787597656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((62648109185829379023135442802446211393945074623986124039466033766913953509624713216964124729695504593530382431096110715288279149577451173719833204403409674337533059799857596060927584664280073 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((208232203134316036098282115244743250557841032424059577097533786257226808312310091596370785430186165516525687132059732789642316741720703941187361963170596582239913128580966799651376439576627212864279 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((2482597142134765030040285520416089007637202079043199517602061408330960832019468626531192715365015380259070481229026597916687226874826717690421429708222907607116181071432858228931098008007356111511 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((16107838870873527916870891682860927422678474946511575665322189152408735035534519198802357302185951682273419394487306410443174400785704208919685592369264915773942613507711146291669921207493996298791 : ℚ) / 56843418860808014869689941406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((10466373908991610547805652319975077088046068427437744404800645150379414517033985407761322454393545656283504365718163743970949168887972263083631055581898752290207264968178193968766233985202630187209247781 : ℚ) / 11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((3166911903611332670489731654812632931279720161657227395124171812305094866424817634988237934500354320477042228980733808386471655829803778731923169026942539068721493124073130969534922415165623510706317853 : ℚ) / 5684341886080801486968994140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((827987826408074302770914457609069411485522585602452808579430675396353360678895141630233918292070969338111921618370866982321059765101749905971101188844297232680055285311749481080428829468093118953526101 : ℚ) / 2842170943040400743484497070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((525900203968109875721447229183961408853403619600987833497897611743735220918465038136460979177657348691548112295588520727046572872210124509499284329075125284208080263334951885493671503828466784394856731148559 : ℚ) / 568434188608080148696899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((6458957424304229001842160312858658146467175422307307999776987314810481859314737392148601023606403745778259292768340375504498929016482440750013419300633332190788688607788828840929051493940752503672957119631 : ℚ) / 11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((42543170062255669475711285254326502614265796247895048014891273789182545859760496786769617878726121239928815598926745349453377947233884906440980651195700097698747330858548845483603608493870339963185349147807 : ℚ) / 142108547152020037174224853515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((26416699928460448737055130160135569351940593224370965483257395519987934578875523432714634097455589759970886465501747278552248398623113059253286763988272330772284695533346296930286181018970095749589151449611922701 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((8227331696274230360504110175723881258742213228187751181887583665737533148003636963762227692001988913404618922736904296358152632471592254808819724442372563455210025655275787456850859096778432503114081518040175813 : ℚ) / 14210854715202003717422485351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((2184983912893485924059200260762124911177182691742605101945797785875093287743878852349723966839665905328042110245203016620019125381219073764891391814139200748732139015910002907932586860956626044587015552269586877 : ℚ) / 7105427357601001858711242675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((1326571328608082958287133241800271228681127624003622941915270367416711248113613299094735136719959045695267617097286864963674437262694926500140684767643169400274728262746411090996760287053231343539883010183256424202439 : ℚ) / 1421085471520200371742248535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((16756313858855875718134120780454829308431759186110404987033089201023235947612524522541613995447292636145372565688254576123417623031012746100606849586079930643357312737617799096363895727910377633137133765242087598151 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((112169220094633150896835995246335366556204735405570078617632852280903085742588463216596722619033546693182746281860750016181368856014783347454800554903229318038620481746456172098855506876604243802703395776499602408663 : ℚ) / 355271367880050092935562133789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((66598971393275715834251746944305016698799675067906781858943929849656351524827617306026719609842149455029220202349005527522649298126176140290131739261931362359550415577603072418496283171402272303126545217028524580478772021 : ℚ) / 71054273576010018587112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((21315380339768468551159634368071126666327170508814469972062018743154765868720526867413531903078444766494930941641663941225502220764902159546457091094872667165353535929802448370542043743885860375066868132246921595219980973 : ℚ) / 35527136788005009293556213378906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((5755750045287230402349678301283924227506213843471610246234147688821231755623711254109008737770300558104709812027950543137705528868594701604647444333454539401846089821518090808283794833069737261724997104126566230181441893 : ℚ) / 17763568394002504646778106689453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((3342695189208588631888521752161695744664717883026057790048757909182950754528849052188793535688349083160622411118529771561890165264369817077136520057068182490266847039912631230735496292416731714097082214985507620199188834297919 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((43356518099948947322322184176285421807381221732671352997304783827071673440603118879762989383892479203429213653184636601543773847787542457838765929817891127259420448307385881500596128773072053851158358519576593342930337115071 : ℚ) / 71054273576010018587112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((295209039613001383981554345332682192981275952489737048167759833028754400665792702705361441310161175548501622668809949638082495453841713636779604003910695406482082137784986604346948403390340877175923828766791609884158917220559 : ℚ) / 888178419700125232338905334472656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((167735622359151892677479459522855253832750136287965338165108399080975115617735415471127538478813087431108579837716374901655940500397128807199138418970137054408688902614441523585640559728232316270822358532201843708569562459969603741 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((55085023673084018091092446515670777722528339360708306282749903453236422682205409282611624288201348922389312494924484293633636324700797541796652467511957344052638499625011658102614368185638755983253095516248796889123794081596837333 : ℚ) / 88817841970012523233890533447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((15134027599717518931804591323336630416594835453708195872935996298159517290545039008171669417454639926569547545106438465836283794644348568407494524955417567062074766516860138305764922023814456389885014696569645025858285890258742349 : ℚ) / 44408920985006261616945266723632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((8415105194140472726868025874833127716672008674478398075765044824278085975104429749893481036352770128415027344970112196489159379248220254842560185931833290607771186180342158980303510345029143156690295158849462710578260604800507150746999 : ℚ) / 8881784197001252323389053344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((111913132957561187356862412504704590232236036616531707976655955077516774107681487359534030474647684441452696022642393650466961511929739844744089572917806301356944311683897899524707606382526103440840884584388638466137737544900049798391 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((155097565024085644924486879383132528222994228940910354590243278685332465463959251235429712592174818522779958366137722012963743752984877685389169090978985573203920894710522898215399417192639254159857483176735229593766312358970837478939 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((422090428334208326769047953333021502748701816906237206893488447971644694780447713980228802572633231083355974014546118830302483978381854593023444604640689485959725945355149032172527174154328779263223823493004822713948626649691106579062785861 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((142025738746472131108859868904826346731525622351309057167257654879190468817780168223528540184363237682917061183988352396155821046776536885722366236562716709179902835346155853256964082407766077655429831684215731388636601842884579276235128893 : ℚ) / 222044604925031308084726333618164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((7943651746002185673954395065100870637449111583022551967354178400305430910483102685056881350090729736506407515786255049487577528929878844766135631578700991353001342720657966792572874432160168178718432677459095338677684757644506714490746289 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((21167459930627275460426955553128435383696054947143115695752151948935359267255524789314005524471357880038317259071689495541628792256942243660532155218157461678655521338096370227580758462460904325689107815636754337912824311639789073030440662701679 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((288231296924417738092333956175700301008220744028943700457201016383478564201907526238761520117060771928960684035834826649382004785825689254722135876467715372086731256609102420734870542818310917084137250137003544116155735493116715138715479536111 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((2033292977014389276186170916393357613112553017192098229721287514329592800523478171283550850622058580947216589368340994411163376870880366759146092404702457882557301962126150870438963758971268492351870016581359791616829023390821389306101615414271 : ℚ) / 5551115123125782702118158340454101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((1061339855138890595172106461867078053833298334153379330782060690720863900499158183043472906418055339107126237275380371130336839638200000423913825264828724586070142620356524796157929373161944569008658853321300962734872625226388017113581942399094446381 : ℚ) / 1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((365403333734417808752165810332093345452572688469671445090880591034577608562654640195825478791920032608878699319154454071173410096877114508562459844160486386765673522351662451556051962633298482718083622370005869034198182781892746583678012101362119653 : ℚ) / 555111512312578270211815834045410156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((104041020577814284138560103172873465425955823172323834297418875654841968353702462546922808311476507464562324497491555549359221931533256631829573857796554886310414731966975814416511021840317458225990067082806602928731819322334599715895833375197244381 : ℚ) / 277555756156289135105907917022705078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((53206847504844736627969936708360029293710350173656148273735558899890803405629817590486269335640710630170823698924155314712948283705109819982873809158761248262760452980986222366088632721480905038499169686712806082359160680546704738717139182750913107953959 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((740815212391484882228111842855810241374609848483783913603138251191128956057869425163948126194540103711127487072239432041623157982532046975322487749177627498415021774734103795873531519828868090872342290647853175791297266706369097592447745005710329176231 : ℚ) / 1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((5321143247372857661967614680861337507150491567504834713678448212413842927279547161678339171235733405611690040969975484098109506015657456733870500171153248412428383550570997813626884740663039230962943694711055392461379016028608210988769632190544715634487 : ℚ) / 13877787807814456755295395851135253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((2666934988203504683013475356615775266579337196835977173475620510981952581737983971397932250212767458395622458343585757380253669145575171804172688489934846481858264993070709536115052057857888382609812359861954965916328475320291114678387223935695292995841673301 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((938256743261505865620179012405898926257572062921076375117261849268544302263608195628477827053791804660482496994700613122491212799290988874864188998698843437138678307150550486499230326730723501465053579061636821239766866473299157133894408470014216733689553613 : ℚ) / 1387778780781445675529539585113525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((272020879386629227994328782042289019189713225524595026492352631430889703665471302552363671344767441367221491019312362573368655773494586436206423151951723002932506891919828314328419717548549448772228365832270853110732723743581132889938557960623819061913908357 : ℚ) / 693889390390722837764769792556762695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((133657518592556439407952240341530622576439626121651127980467275267178262750546826427727128342779645221311247063858289017147777709853268023676896362727038728308316753508360176822927438955363000467843944831532695138329807998123202854824495349104740416530980637735839 : ℚ) / 138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((1900447449593897057820048017618822288613007892031845753770264110017919085757158433583624425437648576270945622010045933847758438853184931665696951719111712067194906520010244720289631041186571247906808631631920912953199877745673732264221736703857225973900953726751 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((13899464712589064688807500838493690871609417504416769270471976907454406208737592979644662683902114558259086463787367575866078491922721796524176824017546266002099508640137762366807675782394126263779310105093143657605490361351562271251918988490607253103360752682543 : ℚ) / 34694469519536141888238489627838134765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((6697525278116089605020461932760391631888600035748512521871246888819516127798026850976629102950289696087390875343215885979329093464773201368105217642589878613725743443630590375255976544916856479053695715413619716125728819223529659373571886261448358494853896282229714621 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((2404806117599807543268391050495194118432622313300491734313839368335474564702703542874179783449729913159359349746817903499541259382247038812497970572905630099579701720636246791554032337863512129504395949070103184855936896463997679125178521124852824959577993402647254773 : ℚ) / 3469446951953614188823848962783813476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((709895414038157892320764894388641307412855391475854155738206520616923458134805156566621207143085425777677712179734423581511510214661613858044552300598937404249460381816913427448518235439617466892239983109180266660299113346828723667020940443076081275525625003844542573 : ℚ) / 1734723475976807094411924481391906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((335566819544192928279509618813441081848487342085149131768488707092063170748271187728187319283973705983863518472803853649179594136835943939291111854454044287972417820189302399699191478350835697566112162328882619798450730809377964613210805146478414171088917816848026517519319 : ℚ) / 346944695195361418882384896278381347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((4866778242139125934956467926296383939666551828389970648359893980318007738116735612239471568451078954775314092978361091790604385046418529491937290038133716764752472216543896753974303447126092378631751585727245325841285323124224136888367987726381219134828119504256107555671 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((36240427276077177877318778694552524378873201602266736837998257760462105036604109403244949945611085498518116580504944414722319817620444017902209126570529640967821170275296503264475257643287971181771975554477782520227207040357583738816937458814500465219535994942210463057639 : ℚ) / 86736173798840354720596224069595336914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((16810893079447639465590307109499248192900376068551844922434789163612765805902755518319022043727236526373342397289500857168676888016309561354243721707109193690731803625903525819420187097980043947568961220021197814679168999623267873902144143799845965610960496968399122009343178341 : ℚ) / 17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((6153289328603895548765071378301936691426115716741360814158191439511164900014642361486313262395943450460681661287632914626410058095601030085695157793545496302389829487166986366902239872545475499816024591522244564905941207647727406741435835818417154301796215844437996847368727133 : ℚ) / 8673617379884035472059622406959533691406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((1849257135140361004878729459289232763092235546239785196847394519351283921248646069987366642495835760700272219731978218554363586664148319322641424924870380761738717798666119503350311034829321868985001905494297881067282685298903746950890393795801634128761044412386063347303758229 : ℚ) / 4336808689942017736029811203479766845703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((842079127519778727739586646247307512347357389995465417798653526383542167324449992378040380119258202616712987265829780906074259824200816412677694797551420281387406491121466303601648199611681291644453262950579243786161347473241224307873172794580938972935066866593366212398428083816399 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((12442969297913213706115004533209545332100489253032614681662288221319728202287133418655715381105249287580049248957612865898112259242066315307207116724405143733662289914383498801236923363736432734095578879524143868789663853068900992952367242093930301577775536705539954020103715590991 : ℚ) / 17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((3772844859046747704518609423858892233067988091702217407626420863399052161398917504682103926707472875412485394540777360847962611079050615618098534534279168892582902884316435156767527056730057003718701320223154647882482630943679068862565542451911192726942709390927609242833125917239 : ℚ) / 8673617379884035472059622406959533691406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((42176289924539671995472632888082951413653408131996244329610728580193794225507248190708445478441712413149233506723950042131434533853002284877213855061776400644320954584974800085478094481495044406827882362227354972835859758541118072648833492363750882245186117024344689886249501443021232461 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((15720199133997974490766169836139162161152557592290051207650523386945049961066957417653701966957006383321008428484203579544294989727190702124028121499234120129769011433498908063745784342459159676408807058868779478099515179534711945408271944309655385860012462435631433488254328913068754693 : ℚ) / 21684043449710088680149056017398834228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((192349483594260911976818354956861874628934540978819402540192994166305477346719274129938867533835203547947864121165044057559186141025092349546681332789434476732156982714154983603566667858962023462015305424139653165903828380708381384535294893588471328852920288814609806941225455925630341 : ℚ) / 433680868994201773602981120347976684570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((2112224227372116725622397340242898376143774412184170961453520134541755265996186172461805411408263881443441718273460281036033692491296674706826983913757077749972645478181127101229351895763194898293459546673035286064509593157869764826593361996534852838155828370410584336547915248522577876979079 : ℚ) / 2168404344971008868014905601739883422851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((31765481067356092914394451750852888430631141495027863192466343938984975785640059369308947471882311511938255377123004997587127312561571644513507135491745211355989250039418159201739400686038662587453045040180709979582793553285426790642425617820692418266726805769658184574215610570856748520711 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((245056617283219831142210359526917467087455489944839507553286384082604587186353454901769250670124795812819006874832750264085398788067049053010899065515633229909119228252121636779318895192482400614523319413434546649971658562583441437938519567105674648365096762150402272634414963387445865145751 : ℚ) / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((105771942685056266700504833148287793025819702328449634951957485622163801483794219983677045288374151107362399157692644187757592230347233949005117194710594888055960535195980150424850419014381244310655389570620210349794917711868822844160784491154656427937827593552784535040532176900105798542916804981 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((40103481615916380387479389476360202781930375393221441786568393547488747134922710897061427374478199657448641636112659940569513877137420651650115701109033065801891662062263834892019033926674503393389357422286535313302116967635437496250947387672729198400496859690091980774402224196595599172253001453 : ℚ) / 54210108624275221700372640043497085571289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((12482976874793910791166126491407011222752061238258890674146069177674456681060771737931355718897043595143773850345193598883781030028446683756704574629772270910285651458028358343774974110285983365663326542465207365234130205061347443572794964547942345016327886408815185734019274344857164183211338661 : ℚ) / 27105054312137610850186320021748542785644531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((5296173847778970174564629576106028599083030963685787342000323914743179438144575735810552237848669109049956133894473554366705140146338261122152219441462732428069923668603308310877023901918917475559984408969466095678982626019784440050895220128539349356561254932484710197275646286894087237514555269999359 : ℚ) / 5421010862427522170037264004349708557128906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((80981070809676368534384313473762186056208867839134848004887477846380695652283791403302555638489968839173126981237270461143437886610313352612175344014739902349155250075771250897841865846505062939001700555277778017422447840026260853450125955940160913183817049090130306914133964012380572438513881992831 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((635607952334506258573802706895965019652277735370889204659078584064172688219049070634415213908922052894829640626374340410490129026952293341926715591238676358168142084775096705669531803393818788536347794306638951542911739667104518333732503823539788543650850023203212724945881019601567331160580488417167 : ℚ) / 1355252715606880542509316001087427139282226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((265165851087858015987278685904506598314120797378434329514553269017078735534697155610373621939948413131505882195651588879292113601358239291037133472251111743926788131814291350466432029712555850880422105054411662284211562007946618719559149781639216389318940996262396753989376690317900378289198620872499783901 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((102170408584717890541099370166333097477539433590717447027018601474950947069591241581521780861247058243954522663664873870130614025345469394038317573364654261080577468596478826167152924779593732570509819525669844458247609997184808914628097859130170338378680706038492377145305148716785934920143120396999611413 : ℚ) / 135525271560688054250931600108742713928222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((32350653941963995727722621179048709313974091101048560975592579745178231626208283991087756927046417316940061383530301612620163958004909075174844150542277414554098300230089309794334576330497806097093966337760328153489338434871726662580897814104317732609458851879061688240075972385335895952050780778109085837 : ℚ) / 67762635780344027125465800054371356964111328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((13275128658300796062048160590674762347026630306684515858986526548196074514370089218317402164627228246606055780820820248180950943054426041940199434748445156496964865745593879969637139448620170254652217610159911348415448821492595659821298761556691021376105559622813120586305227804895505932174533789308767313309239 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((206182599196485606355124561084581522368790656827800036959781629430416008896638667444748715945878632590277157547702533089951083265165144647306279036026108723716218310326091636713746630294231459861208745721912708270069670830540729416214569167299453033333726041886119029641488943810109337076119307662776219815351 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((1645896806328697739993971233703269874587845132353613634862034902841249605560015427469092970476736613119829389898244513509190144485012541750214499886229905997708007328683644746096641032018669081979573985233579343104977504121059439310270881494023488529454883186679323745507319594654003203865682498947925841732423 : ℚ) / 3388131789017201356273290002718567848205566406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((664550070017154077890079772874928912731352827979926393076765874955414756532891635662264020638362912316762863452112645679001846504642589191019061154606956232110426806381549907888725116468506205634050885925328061052955841996339466808316202321020858056648239975059787691317842133494969254136775348294225982382084217221 : ℚ) / 677626357803440271254658000543713569641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((259973510010353730362334694285816287436028753815977993306052102711063193591438718281418429472419596276985240747528986412857185443762130597981037105623620672920816428231186544579583292473758132953535909857707542220315446255109840076349213178640447097537187930306728714063763880687729930927474140861940931705352808573 : ℚ) / 338813178901720135627329000271856784820556640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((83704958241446728721618421555862448450095622267763426399384491636131451343551794797658311215810804545499043005196553920733917596293568461751171572240537329801199874861476483384049392056775519486734999760822526033799007785281671278599654681610365013494990231532028493760633076128000318546797039541507172322243779253 : ℚ) / 169406589450860067813664500135928392410278320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((33264914760214268693720046953106838539986466055802000243245666579523296208203978813483463668871789323699884620269138004662468042382347011875447523767017309825453409226019881107966613265208914027383524711634039469975285435865446125877217461210602227932341384184343331981031760330819355670753453143241518583509067915580719 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((524325600374599864292438015008336387982436969932092530519854160775594359006795866511567513400919090788387834820717588319711915649210604167652399775892173512597851937265925763230297617281971841282004745840251249372452091980659387292630532613462940300802832465998892308496930480563238606253242005299631883333158961156271 : ℚ) / 677626357803440271254658000543713569641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((4255318552372623862680678151131909605140410107913472833333237903221744387392171432298294628720424303574744426395839556115237617954817893299138949940611773822142035168704556987605763375667452744479659882165525606735557484292285262551979211268790976497153747629304127185024324586822835002772099183842006042517263956950719 : ℚ) / 8470329472543003390683225006796419620513916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((1665009267365522542756248120300281488073583278287262989466357476892148659958527357288796993886947276929888861114866896401784081049861455792796720822853428967862048257505351175548438182708682998336831971381716986575164980161261264927726153904006578422502640509065760326253856150234493606963647027719261944508033952472559512941 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((660742816967553426903224815435856829467680727907428075053778190584835837499698021553803543366260020417185126635476562151268286862274070529809570163839330226833354456540988963898335983030105315328711380876967519805589094369306419024051153725545528972162935801488105214054195324585159928812627660753382616950004999177668496933 : ℚ) / 847032947254300339068322500679641962051391601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((216246237317428343037669750269814535257405544148257494937083612968287621611300435840146528559250886576295298032210757076753959147818611058374872792579261849266293065102566795170186425439673430865102728861704429462553896024129722144608296867288385431633690211973468947631393811261351268567750605978059038369572093556594990109 : ℚ) / 423516473627150169534161250339820981025695800781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((83333594378532473683135721491723880373158704899323915060454625103218995681785021095236601494836807687198031024093710629483699796609419164616644622868487788116049092810544749064177827494704607858599922298962757030166701999821694767428083168880966100258351970956850876019280525065903794138659357239658288802164212485603982880525799 : ℚ) / 84703294725430033906832250067964196205139160156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((1331887529555379840867849529131610692801666812599320629203340878348148278103958539301013517121156097543342556716466833321701788246358628229739757465072552444276543788431117669738595447100326373950755272621464276965247708782890632414017317521685339904405064165452601999024235344542543038755221822370879634297220963686006491743591 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((2197019475003453716938039339373434235279519904919667190467029229730622870086556866892314773210419464398812592250565305034400511279174929433485985367004892601047666975632916455258539872604359138525841085382493075882843829412703733420936921055516524294023689203894422208378957238705768734777423004128496235083645262512511948520651 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((4170598431619097603956781842842817562253231327456261282034770572740640237443664109408358157865112277566827984444753425363232124712371410000864010877397645844002438185996268926136278610272880509846541737250805403645028165569594869641792412497879861000078453558934993444672864671081638951902263440920252075845218812358886149005105639061 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((1677530999895102756686097547906116878722021566501054704389593796892844715034824604382817642110000827056371589609104210957419983368856941516293846990799139700933661716404361658415221086616152002333368144888422730395261203615045903019594150392753776103020170970167707626263822230362132716590107265417283073336614699983594984007551860493 : ℚ) / 2117582368135750847670806251699104905128479003906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((111565880564384569617142585876623478804017110995623411978519024457266721711640279319395110256183973980042378925032736344020584458394543036361566468509898833655983899219749367629626148030369692515967539572727801565569028490647594262334603101117353208458205762606263053761768851454981428276106646375848047870080605545733188907221776321 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((208714645778565408303291092661989855334200228405312263073837050028421040152856882453400595203603527652222704358741231718197399126816475896030728608749647627440430933649678120909138037409653314353656130952265715922422982696785132560044452532737558767682698222314636655988434167730117378553720796341539762603267769595785534177951674719696479 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((3379756442945984365875096382512319835053665351530181127501366646388445340516934379957096932833975603790932867120468204619257281281186512949187100857203084217735174707535242197880222900545892661243580798726356967860156841592611958805075153288158185716323815960146610480185801728693886703327118171831960716608557239374410528375480979065311 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((28316807392144343999095252937834760443650438544510282177175289603423054793834315140918749534483951438063347216129778159575677217658813773032969001132889722996826958607161940969870589429570951622412370304296936940450112308124286025603610601651194546836509092453053306796547336086615282123435245480817725531659458530339678389671491991893231 : ℚ) / 52939559203393771191770156292477622628211975097656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((10444440002879433099527456485604653703956122409815592894037604701289739411765520581970850657302666689998126060766702921964107197439001857262992515887849639509914473781312176941535857945453647585316996356958853582867096981343754363747935447940715782749794711501689657326638798232630003107643844618743842869355439390975734295614463994611772323581 : ℚ) / 10587911840678754238354031258495524525642395019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((4254768759171348963181089437207434808548290028760130436847676227291268746903314668682219297703831398567911862079642646639908144643990303924652405860882201788500098238511650167688729683215811348292124156307018745544963313437950931213525497625523276803177716070383893842140464230407993623003132934816656782927736359291701371343048686536826963253 : ℚ) / 5293955920339377119177015629247762262821197509765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((1436930613898263417264318632982901847749225780046834219480484455494471562803133587063274549382871857727682857631523284617605729623651699356839900872651859478044790096366958328460028617475008178978320953190037590111417613598854313557802710907638212462596408073724517236674910435211160374897347023784848096689857452057210365651117938247746208941 : ℚ) / 2646977960169688559588507814623881131410598754882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((522632473071915512754555654705473466618650546427176139682038648014097026131214874713523929134590405099821664378481609038466049180077108549520204206437344156857858379577274708847058807690739493524257891270683399042772084603563236952713929080477401283042572905478148756720426309887945716491223191482966009018546057451205138960970218242004335561284759 : ℚ) / 529395592033937711917701562924776226282119750976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((8568126365574470267405623480481696279246686999947763527271315852612831567882424564251120752641843515011694238911757899076376617986793531281551275403913464521048840793797167519011935675404409610215075923396798522348939345209188436167047376478489737864818773519816501897051524757506515646296651754156380393165451709423442542108768314373828151569431 : ℚ) / 10587911840678754238354031258495524525642395019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((72891877696163911214605837942775007140040016723122222706424460213164438635478544306542369809739725262500340314716327461475641872027876955086701304948085885406374266979001660690653315917087615756600007722696575784519731641226579102092261042770267490001454972927887550375920038784067173109886139426888354000780724844429719727066792209588600697895847 : ℚ) / 132348898008484427979425390731194056570529937744140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((26150972936946121149533543178689098526329712715574601360971619828736519714799337979120804495475457106000493437137244568464251092299654819915832906087249966210122586154893152500341505135733768985239992736608744747477233296127367426713981902924624219081343844191334454243044175821807873129679770023315534699125242602192359045481175117709842374023402254501 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((10781487156146534177790925132477931559119190110632053897321228767291315233790010595715133634669695553381990171631397915407548716722010150114919173065126775545930751161541233562767541346363344905620067504237336661940645295340215133273090921712322728524103304011492531383348368451396697848042342379753261762402541655068188167610597967477433075944778349213 : ℚ) / 13234889800848442797942539073119405657052993774414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((3696387373444700248962030082861505098276723802311315514897306030406188809101987584125465802838787207599187813970740871537128399302543709623837157358731954555874312020766485915544317558212938589447828286292950585523677385464595805498506740519614607809302241106244083065928559106520091764012103490699518231022510398407858040795968927423637591206629519317 : ℚ) / 6617444900424221398971269536559702828526496887207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((1308460752715157994557688900476614654602313558076668399179841187106810802835925992997775603112217572519757260133212571712836332239913428556012447360046876157178968588755508315713598210593354136195228017610999618651329300346147973127870392921963861063275467471335314838562859404064201331459974679129070990182064811024745613044937113873724259669089158874922639 : ℚ) / 1323488980084844279794253907311940565705299377441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((21701898910647562794182707526383705486395385769191829539830904568849610233985822103761536736546791185220861959745314138591113806234168913485930261405751402541642447941509694678684221164300944168628850700482573006587775735801363523756062829226304813962570003534162682340600537353261154072773943941294660383163497733499831491687868104608686831895769541863951 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((187384623966042662643760720922908730385298457192614908855582950367113996230098008024863691077886396081564386908110310119312721947141695988458362225705778517684391471268170549908096809926709592541521793389907665942790090200208935081288327648570262179734574663414050457791806831756440469540858903031530060103496163210090023408914572076442909085734836083958303 : ℚ) / 330872245021211069948563476827985141426324844360351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((65466033394262572189946257508386600161781320333035934950188533719027954434882715383922144155106824151008837485419507417971391865457279108701870756105249695173259400305345906494423306049160120626106853522164911023605011889017069305274682451948454446661742261131275406175014629448182386563691746399465277406192353126895483453325290610893487876541193860204978279821 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((27296461554346817842848739425766805898868118223589914154885170751770910822872710239773862886761141637562924070426124449879835703732362313898871789014537047841836372493988896199762272529726558555103248985921477581254428638513656810978709445888592023069628758659736128731951025921632108317228136980541029323019456839607553171724466718203829007851957543438704642373 : ℚ) / 33087224502121106994856347682798514142632484436035156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((9496239314501549666825290054604964327791613671123081844813094800465368094890713700407228008341547823591035676214816566517833465112093918384113381072674222501545988203201588254638080811640836672359526673809695785051793969247371231038429343411685550650852224447177679259789411213953239946985331661475767941929484164010909185984824845578130288224566700946577551933 : ℚ) / 16543612251060553497428173841399257071316242218017578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((3275328446773280364686444654128809042950352735121974101679437290981258744105936320482705953327580583654405590225190160175753441145790679905097485572045365380772274870993700686240620223851358926194050968181331740741716655436375629981343256102398194161187868447467191371684014617557869520225865233524393711650501334048726194506300874106908125012275337376202471132482119 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((54922160888140663083046131869263120285399521587243551218842204363826741746600497769252183162116663172847585058205745487691122302932739177479520548981220692836217428910987698894318079542221445176667960737906703985982848838678363424048265632379170113867078355362093656806874540693141138819913524066516302510096359825690868162335989531651088943890067888133768073916871 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((481098080799562678252727509332881772462747345953331311342855788754454416941785786129453671417726471994270089318264172252742709017150383998393567338973686897426228917998381802537602026538220611722237169788679468363030884872282879714040168195196649770320929924851277206040236318742412298065672490632583643629918698003815860542655638768381523713800272922478858597299799 : ℚ) / 827180612553027674871408692069962853565812110900878906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((163861962582502511822182715623026584371843831378064395382191994459565555938409732211234275933908821132885025117625238960524841462171426860046390372380646478684224265143772056648696596732129208421861368589099796926823781420615310821690539749410948474564234930745155934069812765057060411313927061243106395173492982385722904082832516904525542104953647128576808286714074607541 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((69053320954767077992182007348502799699460447112464605004890912048885397877429987165604442226628691766793585260104563344157839254447283338669959630025625004414665568531795970634231809626559203478026965191366879364350589727969314576355982031157926486503998244866894489966817773566682338647369158179005702127332732072586071572216839472489796913970638220995132241445624146733 : ℚ) / 82718061255302767487140869206996285356581211090087890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((24365923440455658066608394063139910171029953761931806168586294491133897947393840046555788278702943571660320097911900389201037478988555607479910432386947784520533550160209982279413141514068705429932832571338797075984640898189495733615065022205080555168715066211566649067136998833162298736179059823770271570043811601114215494243409903210243417050439567702241498747554837989 : ℚ) / 41359030627651383743570434603498142678290605545043945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((8197601800679428340347291085356282905514704057188060444077398426829460741380696366705372533248527919383067199019736139360180501685298890755726795763651294358695647634612270978362908873355838755798123053921575327333546232386385136823670353247482700142483470400395905576116903932024770728927207739938792362083285696680591975560642014362429529285409971993982165827414762924875199 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((138886513019511637799133164961045514823901000761926143422858404056325941093217860999816053307291509064093909557418886567918171963119790003672271205332584133936537300981859795162177073811182854024438579611622522365340331843429039073648635334121092464795119389727613171304878993292094184120839351553132080579687561397496020185648395758394645141769211026380105029271003474256191 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((246735905579338343011531274821643660785009979313032251975755499023624884414110445756333302649349768336597004861851111344465797504371140134328819332928589681720898309689302150113947811867688113701717946540759528541000939002737732254872304212844417229638769074339651935114817116002937149375687269471366540771107025494114301726810824009545327716596677202580839283009656270762307 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((410092388607369694313701957152731457123575519044662126781176984442313949887944646030124555844802357591798404694591341873299548668943304411334205425502758364774554133847987841649049161381120883109567722638809139355176035848461808964730996781733087002016528311204262592952574734451715667390899645652974733156244004455826425135953103915030565580984940669824325314938504509515692005661 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((174556871319715359011862165259146026953266229044860136506184405085985391277369217360522996024102538347014414339683243610797668784871424713253428725936975887780706294644562839836453662037355666443862403428046873007938777741929003261698711777663226635209263955351426006118329567995554716723873316244262717292765324820362008993533108923410428262264604494426088810762199836853772446293 : ℚ) / 206795153138256918717852173017490713391453027725219726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((12488922569698650448326824420379771810430459144855572222152000185012669832740388676825880274024471229375837825406543470307338938677347505716966680688559430254869269127811843375113713830592052983423996379805257747991784684514120599003498626803622748775514884228551379579365989676128987111526949893217283020822012657997148469928828790872338491528502954579183271011796942094240900137 : ℚ) / 20679515313825691871785217301749071339145302772521972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((20514626972819906109157146692228690019374120616890035269728526869626237283767822669214041437968138334519784998898341264565467424705318426645883109552774526557107707315460298867494528418344657308901912877470824020063643153860641212788454457294115988188057128061857734369191420407319424845139618396435575946252186126043201854483693365450625830922049118234848871020886164074060205454853879 : ℚ) / 20679515313825691871785217301749071339145302772521972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((350960176039339910225784853052782879035944521975435912344488321688876773661587918799484890959966042359613291441107495820448941081826639203447429548515432039082786515258368025937544898908349414068442210345994368126191513469298209661321004152622046139811315362830034724620737060312496590211545305727144959346251850024525318875534512756966246514758688544152014253680978768135815587169911 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((3159829050161068354959851703333841622406278745874295497151490999502712488748220924464814062821998181666274275668448548919982014173697024318897077944861753423737951579701359259185013066112709644269483281751220118712658015817398512285524096911693325548501486197728740438057272360156585266007450563009572799728503879567262744372950527226202714695789276880911949621136917948405127162056711 : ℚ) / 5169878828456422967946304325437267834786325693130493164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((1026203094184612858524736244625272311924571382991764736349264278107311199319531392804080699344380072950928145063068908870351568933184005313660283901208238407375500215143483028314824575112348800884327271131097173481780074629836766129634954662387333567196824959707911740429314366580630367775036471589576614530381801795550492218506821553977051043834473384472540931053552888287124024936357002181 : ℚ) / 1033975765691284593589260865087453566957265138626098632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((440945950004510541104817069673947885168086361619510397847556013975479042817706037533390639945664718965436728464504495396033242772838086759429735241164431262777930208908234248882888407224442647845900973319142487107351220919282330239051115207772459031430645162997252896366504332906133546432695333463260493462872084904643069078823315516002759466872735501297644672962209239999892439517332005053 : ℚ) / 516987882845642296794630432543726783478632569313049316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((159849392657654068059606348031868560889746081350846216116006634089850510670991791106881226211404761187926656070583355701336244149199443068051286325440221527843000055094664719931712580735381352473295435229787602092690110947328852884516421366448734805740572203024634116043092356520966191177390742908968365123264055366412443083386369917015251040031847059545973659081357126833341305566672255221 : ℚ) / 258493941422821148397315216271863391739316284656524658203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((51332392322411230760256417170405916166877105984458066095244531305700542624723390325391560086394732258833801830128005295239502607941360826480632122819055150285273704641648646471732515646221010124886303233848789660757630937975875318584862127830276517024091131775671251532097449926244334906547444234261052032347667754840454652688193061232924209155313240870651106948933429600966739411474932725810159 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((886261642968658001196455431095694732015469434656333882218119758085692457917767208007866706312367811159280712885708325111476957870649910665606039112652530027257359110879530497750801980641774970629031613463927327608509552559484379837230641305739306404332570314703347724829252802431533132829654741891718311329612597305830222798609477601010816926038965994718532523922128669882725508372567273906031 : ℚ) / 1033975765691284593589260865087453566957265138626098632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((8084253736552429623554419912416357592372469876123099005771297563059929495806711454021019848525039443214647449685934487549786298597122628274422978352856055464918593839463446937013362713804603340439549509354072537806437593628083484949624900585917107277930382224241330193014819778285509840076517928115928344917975156768688518633740781642015550843406797303628395851651074046321305118420291294470527 : ℚ) / 12924697071141057419865760813593169586965814232826232910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((2567667874968281267920671015746524714943656677081832187087560086219417878786835896548632750912561283949166584470404041612294913435747807999470517637567440729297517163102675546030999055047212196277015448140398095818453964785244786642771815843791404735998631860773367125971541692073231703159739973758831731752836710295424191873068732713458814295372310861401622530465772937959971129117516853761965085101 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((1113140671512524097835797558600643647950877244448909871364793974961987423631937127663057039041937454616659304109818246292373097957119899358960198827375789021305960040666350918227736135179116835312519601808323043933848380755026728635867862489519419581398962093721846082061576554061549848483722410669381967466677094314676328737419440421418585363228704753837152086832550873406277546708293945138633767013 : ℚ) / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((408745628263662955400302522906905537027164333464575697114805050064295471299777955971212045792546623269894783736834249616073639901482137313860266818623527836037888462073619802857963832025175588883706420795346385743073976446839497739687102816519893237179726405730325991430910161055967994644751264252929670773605861855099468480939239902293895708518709405513774629278380261287465380217677079362369608797 : ℚ) / 646234853557052870993288040679658479348290711641311645507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((128432807622236723744159699348813440175390871004983657938311901154297139388132657327405999245267226364079763625350376117561969924447715921287040730917291588538355661551497022564355264455870535720302231209890225838786101446011653997553620627060483027850239507284995752951172503822640069255246982623017569003096969686616000980704586991379735047069555361695611084463626070522495079055470626969485272146576039 : ℚ) / 129246970711410574198657608135931695869658142328262329101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((2236618527212289293099297135409237084950343287156031639544747346211000862258389533822331943497127532659714484940509733969300371080791061238965735287831242364764759960968696640381419221398615940381781044300825298668445689625226250725090697810423546848354441615792114721967922314445109694114947518554043587821048119385401303536417280757479594093724152720665167373509026070480498850977612019291584175872551 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((20661088020326942797600766877524909109797903946411242022931586696463654701130410378861121430852162229008929577475277839328272939416802673614561767480103842947261671722885957406469630613903255046946966857252065403396608046233015120983820839066349744121015228813188023504639723520384257423647587663444270166501328378302562809621046502301635696443202273734395600804923786359952598528092469386433798613760183 : ℚ) / 32311742677852643549664402033982923967414535582065582275390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((6423969701709962573358303484480617338310842213505083175113655021012412853617185333756591398422651783576355977535391379805753700268540880813549813014710208192109547529876018146661142811185281183319326877003015355814538036063543357790680122739004109449832440133907414798365320657695430224623087513866425185236988054057391670229433526186649330383811770194969410910530869338359895531595829884714566243717447902421 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((2808340783130409666504641915093358506735329504876956380933467604883467629703323295019586006738710429071081293985029108751881856038387805833226605862449030164973139022482688878719554244411426307674044681875132286740917521473848821892566780165589687964315467711597153645217454618848378248147655600460908234712627883965782502824061579222653349411339385129157860222737930886718465457057503673800194109798870756173 : ℚ) / 3231174267785264354966440203398292396741453558206558227539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((1044101519381064723356374981111292554930346417455123379502245256091779953157249099557047965726981076391312056120965468033039651263267065266823068398362521190894102497417181114729304868710682030877995841304116761926388272405811377950993878659033299317556652191815100278759204564410224806404102317238394158192496743409746780056712757748932409695968835034524493393171193023832505132987842778135722390115164260613 : ℚ) / 1615587133892632177483220101699146198370726779103279113769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((321308286929173208384655038798776849804789388362474041969661099660504129506660499447951961930245382426005844425040814252663423676958748580669924635700424503967851961010825619415459610976462969700489749655045140857741508481999370342894870305793914715355651395472261626180142850483104885358507722316149416806886379880211385942945266990912462784962503035220663060911514649740947115463895824935559938162596776672223519 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((5641126251002219390327052145318736315306819757163498201980045885651448320959341703198935472453562450564309963806096505658267968919222264016227296811953572167212581844968471948424751688103986952386258435651557867170869289579245452005221510240888308859652916985834700185775042095494316336789076267677779221340035021555455037051645236380514553706349877496397594192757727402502798282732326654024205530168086221837471 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((52750220241540024294201211263887803207951420831920968158912498463762827804467795575452854273339608264715964892627798718375135096171826495542935835000879118296576119929788839009955778427325578664059758185650880459825736339623874029504562253247239944500038647230025997425348405656462382297157080243169686687798856409127079732467589387686285402023128850026727086849911078634788722229041075221755382748241599502504879 : ℚ) / 80779356694631608874161005084957309918536338955163955688476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((16070590295567660002000152416127793377655696841021560173306780358146504160814469283477007533429837082179489500351998943056301128708158449344199577402282310692540573590089308873625350601819487928711386308989172894893076968332968318593721291344819345767150051131166940796505753828923081190914695522260967358859817061173284521964496940684622583220347430577266836028307889074138506075852585291637359925046649455551944462141 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((7081121558357724352732120122318780299901387135636127195301146072735404708287408043614689268115781478948014746857315775722935730248893040002837050779834743851990395017863728266180565684244430252398273903263905040320479531284355897997700670459978757023752511430752033881205585413869145945855269143658945191670136440947764842320961340390761450603368618804920385737861295860797663904820158893151659606582331473741163676533 : ℚ) / 8077935669463160887416100508495730991853633895516395568847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((2664405492931526619890579391191021111107914154360839265625503768899958128401581078004446946113327915699947839848981825028719521584783460809401888488018846282992287862331769979860654298524675960179511376284174322611319353468290376373757022492254487194197805303551962212181235468316465004733691461036127400508475514635872574484625925149858471931386096854015214003102728549778731443497994855129439577589673225226725701869 : ℚ) / 4038967834731580443708050254247865495926816947758197784423828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((803773503843432131432080111853460624764698386539060140454454608365168059636633267553822658118349090216858955557092878176730978906173881143636223879166185843735670098463219930993825402019168841471526039219440621092364755210247793570189427952703439140117686260272078422206484729741605124258527832223859740329292916446647459080884421286932423950423957529981781383538405583065815037909615018062493509506774008685263110000864599 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((14220027869291093663523347665190284848316160766684263369702584048550629453430392786011756742266726698379332662715611036063835270851196155349244652968183803984074380281753533421254611926874111903192689116382340146656513192755253483499678469018822330311975874317509459557883554801014167311690440168391966754159004679644060101116050229371388759578109354252894432710374874525430335247541225246364833965920449498946675359128791 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((26909354749990959405406569458776633256040735150003240183992228663188814235570525607427986881042892780038263625257744162112951414271644582417361522534083336394624159664308208308204474508248094461265856387057050464331006635489156920728448480019530997032971087820219945893578402215018213140106040584309498930229647417686475126419708068298368857634387267299821279631599979486239080869078527765584362736239144184793016656791163 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((40200176592708957573466570748140909027552441900571996733129850236850657163211255599219646281040857763732514306005801184372921614658130583229867957440014834487855752771457724327117935625781600018126265962765211437672982195855870741105159444262487417626007612622965504744391483675289523952422743483200524299382538788378514573613810735044707532599034934005811192638616900780139455072021342336447881544639819995414617742330756332261 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((17845263324170677307733910517033473471833310951946398369909009392983077713120581999102394687334203028734670316467447226144563274594251047732319527571912800683003662323064203024336103676488965556448963324111970158936612586292438089756768653181361991116730644552995054768698859892463717985929272619109784324483112260180659578092049792446736729853076189607842195117219477182381202854004674751054441078487100784722956710838618512093 : ℚ) / 20194839173657902218540251271239327479634084738790988922119140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((1358549779893328447246978797690989068203267752984957040415371479587136979507106541296807871183725259886301024262625571215710178772546736671085081793072140346509468534850084912031050857150135621602520641088355306268648090162905896893485836007463222442371464848342957601022631664719211705585929799808193959295606517406399200462310215517685418886264044948146339992026525505448541893930085034799614308190300046297387371855478803153 : ℚ) / 2019483917365790221854025127123932747963408473879098892211914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((2010550994155378067550127996270645742488260791626425392615373732971153128016615377691614906041984994124586991870807462030155151993369617562872745645764859282923032329893745667056012367463718843254454051218789301960466707730449890864956111043089394379472372851433970928145870148969472869593255705054589514948593495945374798485581424239272468379185907754099933809791762085874993772640014056397816688132776474763849665755729522746451279 : ℚ) / 2019483917365790221854025127123932747963408473879098892211914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((35827078848656805633036023175409106515566684533392242915615501042298938138836618371883519241793363895134989531755481508136623863770922446074170186305354211344936895049763377806143544005078426207348240762668250007380761815249521894838531624698328819057147591782084124504265490955527599995910029161077591986060830516396879833423871238520052827433348862974729429811237462582220022762751632645132667058432716495384245788506625588834511 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((342862087475936818188039640185620819222696017746766558873919627906797807770740119379905644989382506446988102741554174780016053038696353414304522261466416974321324229282265686913110089782009525671330944255402738309023372226016652217833645093747600043979479321110400467675821631416473528300545420740166568285667603995790117468693547240834655805095771092312253745970725722512952581905952053773018708630989175517910898789028560462036191 : ℚ) / 504870979341447555463506281780983186990852118469774723052978515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((100553106801073892550969849504903541247077437100246168513114388531339687301575232289005035055913130638038906209797992952639483709815450402296258356995709701737708820998861276999353366989872242552171709520402508905114440135705677405483166118460190961653948183843745955581868172952271981599756480680568295145161748805369022625811822757215064886926444505620516779859773872966061331448477622604536680861890950243893109394059333972744966840781 : ℚ) / 100974195868289511092701256356196637398170423693954944610595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((44949780728974968145220062385249027289907770076412611272373167504281820782899384800391160332813608686040189913763608158844636066528904443503900059783879105758937992808300243877678298227925849491580791757240942748030663732106658532213297884937697949565382039627188787510451838564512671297324436416326527388719720986881126612538330659921211293336377556424671928239703854168045370877757882151490709607795729091276247729515393456224816126853 : ℚ) / 50487097934144755546350628178098318699085211846977472305297851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((17302038640569102613270496732634628381638738621264171570738890435914505911849588430942000704606139619304094826415468205925343954256096098937922737145289521866646657319796706020650322383466623077674217619600953801040988143104240601293701327012862008633045552537834819131973112037192495323102842571881109658235080664862690586434622094708101121125049684413648689586314276361131532817077065927047720830762980323836574690232326671830979877501 : ℚ) / 25243548967072377773175314089049159349542605923488736152648925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((5028860075874998512196386030246726610442148889656909234070613467619446519708954874871408347500689065146515999823667589794472622596990516513843322690420759630213856113065321736472518366535587641666822215082253867278189593557029927217070967658094941741405463438210340600173683804797148940630920742801308864847779676936290357558143512952360943704825667550445540485809880597747165103149786651955254599148677503546877283726562944141224991907575559 : ℚ) / 5048709793414475554635062817809831869908521184697747230529785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((90222150810939729686008964835455852716100230392393128788668519669233300230678080890981704457365074825773604006382375434195564539602030272090734634997076582641732523871975344453664818667621841042431210129941161972887455715906105735553788720030543493623966093941343649584289682062553250823723531198287928255774073424623306202530922008166066195524436827662454972599365195801086251211418649372352512538241406802169889248983451317435374985002631 : ℚ) / 100974195868289511092701256356196637398170423693954944610595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((872933629538467560192964891804156105370596062738458969512032329476492071974593978956549954535473187356910765518299442808741616468423456116836574178482904240285745887363546372732654002843302554609238774864203239657532563551756950303211869040443464698402840864347240952578260352028651420408039023307386664122446949903601428619560603193577347907924796808693647012959489821251033845923261335327514259373475230903636279961847743856759076148541207 : ℚ) / 1262177448353618888658765704452457967477130296174436807632446289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((251499793835630369428236355801554374669440735618957299211400363582144339492560423846563318092834981841941617715687866515321644956599535957946060388303744188208650963313786201335578043280121065840532332396762365049626579250684833739085508344434937458748112141013797245551587280874332803912400972894910898580059486191099791164933327057061342525301777142660452332960591961497203615797377792986518746549269508839696248277586450623873204893531204275701 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((113169627182917967212628430950194583913925600979609611351376000512049065890036114592281129177053097072377386708202912748034569331984522815315763383088354894689247967889005362334019506351425254464324775775825445662965118968358257722254847719502201166694534436593724932677928216752355364734034085344305303045926312317097912414069371751503434373289499130986732069184078601702781303389005504332227225804784870125435217356936298663144197106944973864813 : ℚ) / 126217744835361888865876570445245796747713029617443680763244628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((44032514165899172507823815403527314937650917558112961558085951261737434808625746344549109852462587003264940832741053239116797074999948116180255288585241769320989463108986042822101068675145111004511561889774894768372018975794010543446886133821519864983593700476580253395092213661495013041743147912009548838881487152587014937930913105448334093413941665029832129426796809803713184357611347044061627679768538669324773824267161524821285037729343754277 : ℚ) / 63108872417680944432938285222622898373856514808721840381622314453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((12577666717565720712568179312217168116533180791813040868853487505500264519339805819703148251578148209047285917499810339665747021609145525521619340644250197287967597759648567744757813382181626922656853616850981126074347319298032377626751777848318516867927258215249388358056272833135174043626669461293204848165424119562253055723792104142814625300200472727871062523429344473016681245072591783591507193586015377194441447557147695958759005476167438352269439 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((227101115500981309917147080975716450291014533038436091659433873442355770949606371718927650442994901836225591061788085698132104554509896877742610844254716390975073030011794006101532094548730261391941362155640866750283763151703476122469451053780838936984940703337231664028183163563062885882242567939417378948395528402138876928816883493023638212598724006480666140900416127880577496531117434893726558460343849243740080348581852804139262281269484977841151 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((2220629889625256179394305235884722692089784068664229529898347065264222407009785276008164955093530187924093602954392312302079191962759768132309890803341917082577255819994274331559245182091114769794241445049925410106150307119395596305312640808133378456782286729808919940151632731672780213445622072267334099407774004504377125977968767246656026673848526412793396803760017621631842903428620939557868089615479512605835443182618371780484983549302306485538063 : ℚ) / 3155443620884047221646914261131144918692825740436092019081115722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((629009528196727545074278691402989910294778307118825570583248835851855094177159106534986705431142328426280010865023559601503648851633510927563614098629310049957504590792073834920138565022659711507121422644738399302018658284389948248947452055991886566637223025008640917810414645081158969242517571735900383337669927572045046793763835997188138622026150083919114016291935869113533337211476904086720057598451178865568775396396385239799940759141056876487629085021 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((284801910859711745395483945944063091484468884081942780442704859734815247997705596484613434710920928455029645645093784506117801031107294663175571575731051872667426244832850070278753793137554877926692960324916269343794744425045979091714796190671621034735316808019169148538810820247650003873185717509963731962358865811161265232448295948904713730753795062310537857022675423176515640122713950686609418783250410501335730570334253682378187341386264966722819149973 : ℚ) / 315544362088404722164691426113114491869282574043609201908111572265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((111967349439226242404294292174572098270422720391006236021306041861297670591497749477312591797298583208938171743691005176115761780200469916074456275718356699365044082781215586805453056788204510925086080983486186837655924008637003168077123063415957364737985957192172401459925430998317386544445872394207435040483715757409707576045653168826836462481650503473347244143648589622581464137491512330766567311958146995144318318749345938466930451044496635463442305293 : ℚ) / 157772181044202361082345713056557245934641287021804600954055786132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((31456424989535391567482787574264782503861589507951850425041981289724503534417103122952738307318618219686413432166345576055280503217152071614421204995287046444946808905347568504300411816603156140734196742050323404697857532867857770507133942467401540864712056175882324224665135954480752651123035814058608170154422715818631460811233465071451666503690688805863115613985564934142847982811809781743896795133390120544046503410729203818929407445150280100750347438804919 : ℚ) / 31554436208840472216469142611311449186928257404360920190811157226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((571402626511556257554666542897436256632364219683441144379060287913684256828354519791998077256203475187570454678913602807278638518998194272435856771742326752238826395287806736022808052311585568510581031650238288146994404100562501322613473172291603024844837943341959060433410612674159817100474740039687123924541924115680128259334692049138614835448092120188620313837377440842219282530359865175383654509068277838759991816331947506812693863564968929280949780918071 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((5644443951431125380478994397455958516993458966128359044524172324506133999033623017695830695959986248309033636917938071840280001055348206410809994667308649193022769065068486445050213532838012959304230293531272870903837753012533541779815489569124525909980621944090182102629824238311887856926004157060584240468399103632816159313112899577058861014065929173577791637315110811785107209743307927539311112706523275956078566044623817210067877666772866446889637710965959 : ℚ) / 7888609052210118054117285652827862296732064351090230047702789306640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((1573101659575201414110889340474229638573333212249218869851964676841518684608887824112869131068692344257797842778889364109669867641153331503832201182272836082368347624989179031724217112622856177318069300223510194974052306241857947443935786913970841234821661616074916881626489843758268199221288785238908730532909332400974468431180734310003160107317475379619581406927665545430559711061765901301625551025792876892325808124278363938820513337556939053669270627917825076741 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((716438207443061209011473520166845798832343512146802733930834707830893821090043678229945692244747236440916141607195047243916649021739045305545240638048893666885118149389463044427802192354657036068636584448568435794735545082877804310479821900241089573000257339547098594542430182070524752055240594250349113649940391312696371485386650700422460884331698714912674491937764137572042239242164250577121426687083089303504767283248692177673936428156255849664171289951015086333 : ℚ) / 788860905221011805411728565282786229673206435109023004770278930664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((284490304135820747372126586679383585811712344289208740290172735274770887637620854923063610736389544003436575774401585284375564365141653962640381990844350698559021770419732376253936295743180653228887656036138056021825346390168846644266593807034190350516508993658903144646811953863648669169540722014490566303622754852629970727763501095923224220888855785284662444766232830888151708093501088623115174272272604716104958198363712507813781347919116239530532948657769981749 : ℚ) / 394430452610505902705864282641393114836603217554511502385139465332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((78668301230390049010339123471162813738898441513909757939247298942892114898778363140856537969447088415968332510754065734765727890736326893759146131531159220086761538694364910376447870471928817342596468743236047080881851663934941784559689059337671484968258306920155506882991104744921004643092332047376918648590813020049535467377428634639238964298838471919887447941163226146051154219740582821457326849804850423827346269170357797712060178219096550050915748129418356292493999 : ℚ) / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((1437122435295307730024489933181947089543400830864901441673935556170309898144831434620423550655912584427096520358003132371982509370895696905322700554856767809877787109736572547965665978110536127082147675753699455821556209388539987440519361413958615834050019008345973381375020904783858886198436442529931241337776887112597357617714438469334233225557842910145118341645546991688358948526773305630705601459057435031088911329826992417135424410084592959617785881195948442361391 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((2867228121872760418461323027300578962276553752780340930258991423272105576112569567243946223838771417707279866438856382972375703423542938265775861674216440095232952799931793503936040299003266505751960956999151218034167710540293039251388658501268451628380929974516546301482788808572051322132033715488420775366091553601665582784155761743430650492691231506500207577466490498116991938745562424133448651953506282173563622407856444926471634462264111133614639643022710751087219 : ℚ) / 3944304526105059027058642826413931148366032175545115023851394653320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__bigcodebench__self_rec__none_base
