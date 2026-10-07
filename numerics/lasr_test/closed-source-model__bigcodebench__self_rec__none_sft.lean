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

namespace LasrTest_closed_source_model__bigcodebench__self_rec__none_sft
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
  | 0, 1, 1, 1 => ((31197 : ℚ) / 50000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((0 : ℚ) / 1)
  | 0, 2, 0, 2 => ((1 : ℚ) / 1)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((31197 : ℚ) / 50000)
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
  | 1, 1, 1, 1 => ((17029 : ℚ) / 25000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0, 2 => ((1 : ℚ) / 1)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((17029 : ℚ) / 25000)
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
  | 2, 1, 1, 1 => ((32411 : ℚ) / 100000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((0 : ℚ) / 1)
  | 2, 2, 0, 2 => ((1 : ℚ) / 1)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((32411 : ℚ) / 100000)
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
  | 3, 1, 1, 1 => ((38133 : ℚ) / 100000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0, 2 => ((1 : ℚ) / 1)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((38133 : ℚ) / 100000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((47139 : ℚ) / 50000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((3777 : ℚ) / 100000)
  | 4, 1, 0, 1 => ((96223 : ℚ) / 100000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((31197 : ℚ) / 50000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((3777 : ℚ) / 100000)
  | 4, 2, 0, 2 => ((96223 : ℚ) / 100000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((31197 : ℚ) / 50000)
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
  | 5, 1, 1, 1 => ((17029 : ℚ) / 25000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((3777 : ℚ) / 100000)
  | 5, 2, 0, 2 => ((96223 : ℚ) / 100000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((17029 : ℚ) / 25000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((47139 : ℚ) / 50000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((3777 : ℚ) / 100000)
  | 6, 1, 0, 1 => ((96223 : ℚ) / 100000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((32411 : ℚ) / 100000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((3777 : ℚ) / 100000)
  | 6, 2, 0, 2 => ((96223 : ℚ) / 100000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((32411 : ℚ) / 100000)
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
  | 7, 1, 1, 1 => ((38133 : ℚ) / 100000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((3777 : ℚ) / 100000)
  | 7, 2, 0, 2 => ((96223 : ℚ) / 100000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((38133 : ℚ) / 100000)
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
  | 2, 1 => ((232304617 : ℚ) / 2500000000)
  | 2, 2 => ((232304617 : ℚ) / 2500000000)
  | 3, 0 => ((20253120053381 : ℚ) / 125000000000000)
  | 3, 1 => ((14399707136549 : ℚ) / 125000000000000)
  | 3, 2 => ((14399707136549 : ℚ) / 125000000000000)
  | 4, 0 => ((1312336826196326959 : ℚ) / 6250000000000000000)
  | 4, 1 => ((806852663538919153 : ℚ) / 6250000000000000000)
  | 4, 2 => ((806852663538919153 : ℚ) / 6250000000000000000)
  | 5, 0 => ((79743495650068656520301 : ℚ) / 312500000000000000000000)
  | 5, 1 => ((43052632544423660816141 : ℚ) / 312500000000000000000000)
  | 5, 2 => ((43052632544423660816141 : ℚ) / 312500000000000000000000)
  | 6, 0 => ((4653091141448586399710468839 : ℚ) / 15625000000000000000000000000)
  | 6, 1 => ((2237175477488384946481150777 : ℚ) / 15625000000000000000000000000)
  | 6, 2 => ((2237175477488384946481150777 : ℚ) / 15625000000000000000000000000)
  | 7, 0 => ((264045188316744914295951790601621 : ℚ) / 781250000000000000000000000000000)
  | 7, 1 => ((116421230605808087768481106010087 : ℚ) / 781250000000000000000000000000000)
  | 7, 2 => ((114496288371205145175372460790069 : ℚ) / 781250000000000000000000000000000)
  | 8, 0 => ((14681982382063038514996871457169812319 : ℚ) / 39062500000000000000000000000000000000)
  | 8, 1 => ((6099849374427508585321183688355461959 : ℚ) / 39062500000000000000000000000000000000)
  | 8, 2 => ((5807096958316486914036094659267782593 : ℚ) / 39062500000000000000000000000000000000)
  | 9, 0 => ((803851780008069572558437523619527782905341 : ℚ) / 1953125000000000000000000000000000000000000)
  | 9, 1 => ((16059991345314756376912586038458949930243 : ℚ) / 97656250000000000000000000000000000000000)
  | 9, 2 => ((292921816308599442257184045085177013553821 : ℚ) / 1953125000000000000000000000000000000000000)
  | 10, 0 => ((43480659682800391580832186425900920158374869399 : ℚ) / 97656250000000000000000000000000000000000000000)
  | 10, 1 => ((33942959117494914832666413854283667218788916737 : ℚ) / 195312500000000000000000000000000000000000000000)
  | 10, 2 => ((14726172528379376800097370654522267291838553737 : ℚ) / 97656250000000000000000000000000000000000000000)
  | 11, 0 => ((2329029348037527658728848435930543475345632968599461 : ℚ) / 4882812500000000000000000000000000000000000000000000)
  | 11, 1 => ((3594546258406587347945266676561992861669889698624397 : ℚ) / 19531250000000000000000000000000000000000000000000000)
  | 11, 2 => ((2962195554983275840994519638107821662330528050986351 : ℚ) / 19531250000000000000000000000000000000000000000000000)
  | 12, 0 => ((123757840999641016304819186421329888884317792506809992079 : ℚ) / 244140625000000000000000000000000000000000000000000000000)
  | 12, 1 => ((381065000012808022249412837588863289953983619360336009319 : ℚ) / 1953125000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((149303972052578715830602467687511785426478787020881999871 : ℚ) / 976562500000000000000000000000000000000000000000000000000)
  | 13, 0 => ((6532307195007077867592871628715069632117856420978516216611981 : ℚ) / 12207031250000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((40406684419877579273571668008220096271770712224095382545361201 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((30172234710678939446772154784164029704340332777344646454372329 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((342850745271688643600460375705999667388403633828506275934872172359 : ℚ) / 610351562500000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((856562556668509608027051805804294282313347908314340737332917215923 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((381984873452442150912879654982957841732402227613105271956612233693 : ℚ) / 2441406250000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((17907857101674630970682101650405118321021958895041957341293939332830901 : ℚ) / 30517578125000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((453543406928087376286061072398862987434418395707702626376518856578792321 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((310222027708399532645911025684015316761623091629442953492380933323838167 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((931469266931465429326983589698446872534654120353382827111255006210315842239 : ℚ) / 1525878906250000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((47970137726314956803654697637184921681406037369962972082024075303627681540511 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((15781763810076357125009974647421755664146728513223941066860741134258889269829 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((48274069324663598873044679434795087124411060579338113087197449737748078487304221 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((5066154968352822639118772149084097050158046876259512110712501498223380856698087937 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((3218320528386246215127073373973374639733051918602244708106887120745387957600021781 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((2493868331434379887276453143876805611957612984649419312817400583187706671813033673719 : ℚ) / 3814697265625000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((534157406438662782517458989582975657738996291981208007430457292184373846240376414497503 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((82202830879594595166530995917732665629370099453823992447582529394568293734973893492803 : ℚ) / 488281250000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((128472308152438358506324724749208739742069918483388976986899446090885304802594594345439941 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((449767444415321657386479648633176691602862073405875654017365511129915106189599262105913621 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((33656724507027752252404890684422860198699705313794246745199772096314559729491473531789001107 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((6601748577845448031629641199952950782701433887388472986185452989278242383089506582849693378799 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((5906632266178098892237673712830597783358711897249139042129547866056248025209371602333117891114143 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((1725448728467157571238373750219079711211241500407986423858153181182943525180311304635543760916743 : ℚ) / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((338484448403439387262989656524582146945762892017605228095796068461587067696456250808951696183206061 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((619420355915668792485058314725129870885752605632384411586979874081682384922664091603590504630926571393 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((354365056067945285470521768348022181931504436623425353487929449396027198438065985873904040888121641489 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((17320049522908869901190069418912277824876316966817892847207730871210752784143251206883174006380150509479 : ℚ) / 23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((64839039706868060376365475894108119932121716802909352537070962314135005321221761388487250766459985700806751 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((2277351217144961264565380085654284620895664937293085856952066149602527467697432852045714366398046148071713 : ℚ) / 12207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((884661369941358249522198682338105864386844705498828650924525225538003675491728718641265939486753914866330581 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((6774909756891400932439798943822103492267165856438980946252317493861624821696610164034803083936504614950211484609 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((3751034111650274388205925490162642034206720800543030231148495602471751923486255893922632721791626478086418138511 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((45112630091713538086726923686735972341331472572509283775931194606635955259004600068030635121466092792883957257759 : ℚ) / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((141329416397491308307784659360191206371873663725731640347338351288774573330048931467409627199761464089910627901325523 : ℚ) / 390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((193262294738551586889081944525367994673883190515211014482898347765477371142583048735238469818491926265788180659656073 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((2297093158595677049995220455669047000198024285595515127913620582562212294954217842606896108990790148163756861173501501 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((73579054923645612625429519202259416572132189314833230509786898334953701698425007613148176385933815703080137391388055584769 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((39861561601921922047848777188146180035342958621350740921135340198163565984243511467663733372356992491483834423144705126413 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((116809118838161249365974697059783206542334666798686987614720160641400125371846874882646475681716856794291334678857687255639 : ℚ) / 149011611938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((7648595658599951985324539148114366451522476499297833004523695682894206855049475314313421073801054286635256565594186999466964959 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((1028376783117085646024100045350480924483437196616089363822467738724753235254203664426967019624494727604645669656381411830627653 : ℚ) / 4882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((5932587274668064579175181244701120573199113858223305909170293652474960509903489835093072217160450912426099225426672519543566821 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((793798219079053794896723233506144862164629347631885225869368011277771174961479784378283404160671273854485385885635321428768670635073 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((424702742610033347118078699017465266073679503217807782678443251487539141514982825070785981513057606737828645133633198659300665268619 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((300972342628376968463363868693966122700033028162788417252378472484017163476340607336452331244726495560853891387387915898764196375119 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((82255606817213813308527938933682461765236385733958483167993809132709289641267515731583384945638654998639149607231380427758522899314023327 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((21932173937813412471533905154255134720901733942066374385388223983240810270912850761191507958322898747241238511591815941815173591565498379 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((15253340813549015529675759406364869057956856914565683200859868814424085069111219889233026442545162274243091586110078967551845452926734541 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((1702175491046401340750412149221857125987790372645651260327088753696353670493114873289871804974719663555752590698149789030604080958118685330253 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((4531438572585056549363123936668302314585952919132066675895934769773003960371161884506451385487085772241447454668311534614206837993122967151113 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((772317510329384723717448122656633562523028278095711740405333356043136946072833794358555633475136404445545094277643012451426442805513339528199 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((879352583739810793218021598085778262805858936188884388864717118112599752359137902558180665774976128593989294233059861840921697411582158582550949727 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((58521774739782898208679925999511103180085446115632246975751450308177924893257098049367937587833929388579898263235437445128222830138292830080421763 : ℚ) / 244140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((39070789005391750524519912053911049503773030001153755730967009070517432500927312232267954006384454969158550199153813963947791087409093312019772661 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((90731426722737802651710358184242649558889898097482244711865138667519748290776559123018373551240761279951727217027245366769920907138251345204698518170817 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((48370440555074303880654935731577639548996624254661269942723890979141725000691485822796896842745238338158085968984695076433745134198721420876922323528071 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((1974983617223905929635500384309312962558356861224386891402053840575121250661212571316879083906956822791164897837911636446534924069377249635300063466879 : ℚ) / 2328306436538696289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((9349405067022193194826894556150606876097689872571681939911606457501993753143404183357072351355160013762304949769263089632764420307255396983102782655541883679 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((2498520750131347711461884951880739848853514660385230907987717795216588147017899952067313100901255711983481589946163110044987124657132373305939121519986375821 : ℚ) / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((99760037447254911700095665115956703742038384081256373673801415990870640634918899399306363136290037669552722119181316630453209785706374170558409691765209181 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((962202735217527188974992378887216654693765720518410520680430889199975233166272929363369739178346150096703979700272085019623634301235025436197965266219156863054081 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((516143027217920165376855092188221703123484456981199390005650476408236552946629411776085799287111496120353323854057812565260543407267000347639939390125279775903749 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((5035652640973009786781200182901083057695947387206344198609324948393651128889441998783902651881576085705045767976088084642933856088412772025952874460120195583159 : ℚ) / 5820766091346740722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((19781516487243408631445741014317778613508555678355372784218691444631158776820812876900234049739946537787099591794828193112055182188357526117660730485792224965705667731 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((13324767559726633066453918437671068561107349507624996360280923314984513072463133685883937842420085725026002203134233140896545933758304316380869400686633637837135425991 : ℚ) / 48828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((254028841630169733546598526671774154256729263885519859178244968742328320564719406380674387107045615104050152456624816221983259042151689660531392549175605899594532101 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((10155378193730585339249682615233000018597975942558967735559774755824901503498283639728661386386693302058907544168042029344290672653937896152250270827413794893824354963768641 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((5502170374459895026218434394367484169737839040674541314131215124482878638986741501807501524074090525242817415759786592492874519651728396821197608264303980302888079915627907 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((12807326154971722330029084511280761857507960770299520641803289581544614703100308097378609933839023250389820136652837211888068847987988498907789313375588886500986648709039 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((1041569691977821347315756516285480146664921740188659705187183265273171211408907844830922228915886132796713918144767940098996821520007932470691073323039341472001741721807432551071 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((283896101689687449967081231983478735167464320572935805003428591087933342128967122417839186603681876606158056995488320017137625387531092480546573366465631899999387151209809126159 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((645357577087569581934039842902263833201067762751149103533965267584431592489445423402330293671237717000125731421678093331191677425305789850014280443211884520770009633495389421 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((106715510985607637858287027367597760046496775005444219838926970261449208611454340695195043126256390233619541657530125727700291845845974919743624927157519562618441442291904292410796417 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((58568677912373822225176527132302807181991248049671771636181809833445187624842651770749873363747464348921881905386533743771978450209878584453066042023964589367032638184989599838190081 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((32503162299748820673728645560819814833265133268326417591487588748662520838359967813762447713368474741668926853486483641539044482151489627739823165812565024424577484113339161916519 : ℚ) / 36379788070917129516601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((10922802216748403121207948906584094312068632485771313253204352319121624724736964422381982824457510747864529890280520930709890283774570796216570028915085203632955897631439362376652319989343 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((188709949367343323255122221019343429849011318133722803139998420446284060929709297691956773205241957748709101606953116290640471397384543571990595159735809252208557339737836774302054444721 : ℚ) / 610351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((1636249141318753565285891693403985251425285117135638998845133446023202569799450522772948022760476530847531542946499352378509017844139069562027524213238502686350158023618694753582789141 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((223386691343387394651240915237586740752409553134542640327583155386823706020955606232045387828834580675493990108186167168171618674815636298798275484324079966757276435412140590710307715819741069 : ℚ) / 390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((622319022627822769583286438160785175428248538971756947326635015048611694820192882681357759948071918909213477681216718237988794138473607853394818216980557571730122838204950245573946527300189567 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((82335276956169419691361502050995460766936515136656886766560745512087745937776298192993996844906103187621789402955032971770536592154871600084415463887849778131860099075361651989139097317599 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((114110533818079434067271042104379444559953669136067880844999511555349155543327051068380476495770885471524837355168559406830353024113430168546863237346202539407121200896076318198532454041633621647903 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((32050030490168430652800627811703528767170806788212603252598604471251364399444583186970232442315432654628976233056406022992458378530119629990007512906990220698399387671676601267713008954830975396753 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((4141409054614105043698582520963125025092620387026868985288906982694304255760836920519544017272028798161303530665897299256291324417588492356379260552209350691357753210313472913116027908454299261 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((11647883092860283266018832503204623589620722286236013539032430952030497862790181613593612693324748030431755781300216684138631640533035592785595576089394353872360466262394024043333913602221803569438761473 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((6598895653941839827880952345879338459229898091491291031501154191218993833702658527884946412318362387078677270837244762380404888486683828059658488276355247003864865335647955461402154800236652080167657469 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((208232203134316036098282115244743250557841032424059577097533786257226808312310091596370785430186165516525687132059732789642316741720703941187361963170596582239913128580966799651376439576627212864279 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((1187976571371888006387058695185805991304747463864272202539472204891959344159220791729519128908937992537247695589690720282449027101079837784760722059294499499945702136271704890938166538609114300924713809319391 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((169739897737744735913485501985537861965118988033169980015265262861871108522032356870804068443799339320703076154435780296630327822786863355333928302076343351757198604566278861793542933254690781297935676680777 : ℚ) / 488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((10466373908991610547805652319975077088046068427437744404800645150379414517033985407761322454393545656283504365718163743970949168887972263083631055581898752290207264968178193968766233985202630187209247781 : ℚ) / 11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((121066593322518089634160533042392799895328056338617373719185103481611240906010663195789673864456836071642587337831655296227487899611374637532715054974163073019383415777903834360775023999339602951269281086034097729 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((69818516230147667895337182521934427996636608713078216057027064071308225144151454831079913261359874107637232933475358200437450111728859957874227579260723269955826602277422433046513781682591068909917702526816960891 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((525900203968109875721447229183961408853403619600987833497897611743735220918465038136460979177657348691548112295588520727046572872210124509499284329075125284208080263334951885493671503828466784394856731148559 : ℚ) / 568434188608080148696899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((493141468368356605257239469344392180119342111339373943320814165552096397890654409897370959011089872311262084744576398225993630620694778601641260718489229971255245266829560425904391021849137096816163910446017333599863 : ℚ) / 781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((3587707805096324936220627023554607035162509234494741502096338660991768502473843856550750045966942318050885758466394777087271991948859126866246432560920994565876857156166780778707671440244733052032977582449929607468563 : ℚ) / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((26416699928460448737055130160135569351940593224370965483257395519987934578875523432714634097455589759970886465501747278552248398623113059253286763988272330772284695533346296930286181018970095749589151449611922701 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((1254538397502524877436553224017293294353180315554808934868848592635734044791908533491337071866749384042781557314363753657589790740430025221648611471729435459230548637010353213031077742981614727842173692844985831441550072449 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((737004899410249421127329625067834137096653131004795407710499867535478583597906397472324896150776342532611683025830435673826594333949247998361637003962347260260514186596053536955198660227442667298404681076024339964062138873 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((1326571328608082958287133241800271228681127624003622941915270367416711248113613299094735136719959045695267617097286864963674437262694926500140684767643169400274728262746411090996760287053231343539883010183256424202439 : ℚ) / 1421085471520200371742248535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((127571994187041186027010256993975443441864098722839606749587874358598608152182219769258892579482965068083810563573155979622844189108598043407192810345934057167366652836372955700018032861372260775223596674085712506702321005186399 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((9456901745414933313901612505001940118327902034565617732890883736031440404590048226872037325344608053880634989721354238675916628277775336926064825370123877269195154847352520446507307664788346825314285458131725193714585726552069 : ℚ) / 24414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((66598971393275715834251746944305016698799675067906781858943929849656351524827617306026719609842149455029220202349005527522649298126176140290131739261931362359550415577603072418496283171402272303126545217028524580478772021 : ℚ) / 71054273576010018587112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((12963992362849588403406921111272267509319034330136402946575141058403784844465975170839275085333653971422020333560537694739712767077467835346161420422176872246089848650414710888978670222371513401887977561596872368390926751621851942593 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((7761611075236943585732456621216658721926846440652224675588869447309653263397737928342955217725780925210603277426278761399937288284442184770242852777392031673711266926777393253073149433548835801525751441740493682656203325364746912119 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((3342695189208588631888521752161695744664717883026057790048757909182950754528849052188793535688349083160622411118529771561890165264369817077136520057068182490266847039912631230735496292416731714097082214985507620199188834297919 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((1316578211928254633784207722285208816779758172823330755437031272391115366049755115665722934726693202683047364676825492788832646614295027062377133108359339064214080527821294177380241401307198797199569973481643915919752686260326824901939487 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((397905250823503659024801057250302953291332468861902104444201046303033930660734262449602060956266514508300424981823486065609030405922738179624764853866777755106500297923958737009065047687133416724571636114373455280820191458723888456000149 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((167735622359151892677479459522855253832750136287965338165108399080975115617735415471127538478813087431108579837716374901655940500397128807199138418970137054408688902614441523585640559728232316270822358532201843708569562459969603741 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((26725194040033984970675095719062825408298944235164233995009449212003279775861397561445406790096619915985666184525384534261208999091644732270183306954324795105517511005374503247904632424792874562695274245657085353881929958363021450106251330509 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((81547989806433002916489816830663035850080914921351332655154381672654910557505590943245553747252385877598253482436372485645616371760399588930665928817519135504762138487855191210411703939935367371999688873506883045401628461470831855458030116853 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((8415105194140472726868025874833127716672008674478398075765044824278085975104429749893481036352770128415027344970112196489159379248220254842560185931833290607771186180342158980303510345029143156690295158849462710578260604800507150746999 : ℚ) / 8881784197001252323389053344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((13554473518695199425706607245843786603556305205894174244289278116175621677675596600716961152959959114337853210482501639029059248130123376854689726220091221111237346312255956138602702488923454378242349655283911034112959709529043882510592605486367967 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((2087874378147611161451149706887847689109515359589566460268168379014138849285500742569953356363210248353381512683809239153950269021936660103649469855110141882810606361763346889419031092888653572688106579151171716046435285677948378428248647077652171 : ℚ) / 4882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((422090428334208326769047953333021502748701816906237206893488447971644694780447713980228802572633231083355974014546118830302483978381854593023444604640689485959725945355149032172527174154328779263223823493004822713948626649691106579062785861 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((1374145535788311097666089366381885753284112300249663397249602987610252095668781468334348572830382434686943173158931304352077247798034590299583543763272938443260247209008657502480911380161632866828844729974006917830090745309243677187109638090973816956737 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((854801391634102123384149768551029454758371750545809710146216467180305253055775680170142449512078484484083788755889114367054983724578720974994014847406337271695883360813208857297772122704763538085692072110660116108389218798048106014247986541933711211891 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((21167459930627275460426955553128435383696054947143115695752151948935359267255524789314005524471357880038317259071689495541628792256942243660532155218157461678655521338096370227580758462460904325689107815636754337912824311639789073030440662701679 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((139235927979118928556083149507947232304518420319226306852801688450628521893222426775332051982221754491009041092204055764470492486974725176148493885947880232050602510841734236379616036262590669532748813898197470650158637324382846267497903394730208614344059039 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((43720850997940329817138931358055044857684448555406213195405568802847217265063445439455225739490541234162289385239600894139463731931657457969188067727930939897293469167977547631316964622945474631616047399907936240470894272718798136872348556047047800293691671 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((1061339855138890595172106461867078053833298334153379330782060690720863900499158183043472906418055339107126237275380371130336839638200000423913825264828724586070142620356524796157929373161944569008658853321300962734872625226388017113581942399094446381 : ℚ) / 1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((14100941903219006979161627752331042328837857145415130046473564417091026715538645225473890084343063591935249317963668845274589721597231638333856146604650119714524155848492350649459066000596406600022346314351626491607663900601991491397651408536613032814765968984961 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((8939796991126756905145444839823777859096107460239421865586052071110759500983100926971829532998848265062137091237074952295968287478623288146651228289194541295929664650949837342262234342791169769781174128016174544379310892381835836600875571338926158911697298307569 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((53206847504844736627969936708360029293710350173656148273735558899890803405629817590486269335640710630170823698924155314712948283705109819982873809158761248262760452980986222366088632721480905038499169686712806082359160680546704738717139182750913107953959 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((285471277647871136560524127878855157813987322010973818461275005079847928287917995562087003131537078468689369416562097223932562160163744235783575014828679859153522440152833156629441519780306668679625840880149461760048898502056009194005025676361193896675722206172728339 : ℚ) / 390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((57092083965353007440256475427682357738239083411553177272363583827615213710480398969539077250144495487238340875253365022711067619033019534582637237837308115579999866146756362936719116715665459780371145009337903527663286159389444473015936216936767450868851262494088099 : ℚ) / 122070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((2666934988203504683013475356615775266579337196835977173475620510981952581737983971397932250212767458395622458343585757380253669145575171804172688489934846481858264993070709536115052057857888382609812359861954965916328475320291114678387223935695292995841673301 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((144415244783668944107951787879864153940571913404741579601792736987124265288756976300423357905832083329155244906971146096360259319524040112635521138075364842055241251244281041651374696148692970543963531839621418696429991118288949004537734875609832554630680758846651897216961 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((93288270604750645372726279516238251793662419745935342588499436497246827467534218226925351137989538355177756726063847887359199388494120128711094461137748400027383505206115654336705780184754732021161176984757960043616033594050215982060983799534986337537976614359070201083247 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((133657518592556439407952240341530622576439626121651127980467275267178262750546826427727128342779645221311247063858289017147777709853268023676896362727038728308316753508360176822927438955363000467843944831532695138329807998123202854824495349104740416530980637735839 : ℚ) / 138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((14604893405411484030996330353877000619183332025262218712945482748207822768045704914061832914519515334286760780040294504342010120651109227558648305073394763109019312564873764015247604748459178325299867358255782939282210025187212412988294709915929686746535585909299630528678297631 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((4760966820974419475797787348356620105887559566071422708024576222837474914702090089968068542680547563942244322732835827035658471104456010325196002836284108652138784613698858050779041257035633964508371096381307643846640838487035646415996534383916663957878402494818308087310868889 : ℚ) / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((6697525278116089605020461932760391631888600035748512521871246888819516127798026850976629102950289696087390875343215885979329093464773201368105217642589878613725743443630590375255976544916856479053695715413619716125728819223529659373571886261448358494853896282229714621 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((1476374382981962623799410063860415018561695344091154362890738492988155824147020296577968908856790557809857130247878583117379625780280445898017292706067958453432840393444705169213094554546018301840787355526990397308500496599093820444563800637032705204726968770893295292617784053072897 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((971391703221482305624454123788431544236292733311596414547292684120161644029667056914406461682840865908030246398855515912604102355867380915531684610093743593932266487325418643125813576886409930468435583026329222989379550068608163294029658175399692738879531954497228822677445404364781 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((335566819544192928279509618813441081848487342085149131768488707092063170748271187728187319283973705983863518472803853649179594136835943939291111854454044287972417820189302399699191478350835697566112162328882619798450730809377964613210805146478414171088917816848026517519319 : ℚ) / 346944695195361418882384896278381347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((149181518913296497607082538734220670533230665126253416791769794737699684846325012309320186197856794048219465965650782504112237801189150554970327110236565830544530300419209551327216430859202551485964191654749116667519654666306094946178254083604277303286482565182732792132201006307795465183 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((24761622475900891181048055241123759001539079748018507956405615808027644605317487219412480382815023644279056195045827929023211846890186559498004150696967242229390079093988602380403254485315333466379232736841979888585318705476615164115133318404389290492864741076312706331177299878162163533 : ℚ) / 48828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((16810893079447639465590307109499248192900376068551844922434789163612765805902755518319022043727236526373342397289500857168676888016309561354243721707109193690731803625903525819420187097980043947568961220021197814679168999623267873902144143799845965610960496968399122009343178341 : ℚ) / 17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((3013639252510265254133202516992187818309422131050144017821519353793677914610856465222001416848535478270045037205267876458845350464426528027138141953226122400692635617891965575608365576555548761375016308576724099258562492086604354576734347768700799635478069411139926926750386530135602328320013 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((10094008994929966679917898826665757322224391704556198719579384794307667897094427862346410742771745191613979419975841808775633976348349106904428739065420624938121097267326815622761065884717197365504122398428570736930602222862943484358317158861075558170892740571039331921102816505530134918539627 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((842079127519778727739586646247307512347357389995465417798653526383542167324449992378040380119258202616712987265829780906074259824200816412677694797551420281387406491121466303601648199611681291644453262950579243786161347473241224307873172794580938972935066866593366212398428083816399 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((1521395774381525522467783097464444622759785126541486782301707244676338867065987176417624888437903550067988904418334683008392148560890785526293143141121233294950351811810820155820378339037743461362886028911970319430633705057884011557564297889213953994865078999817752225281580219345514118537023477663 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((514094202401401271583022754165828316882585539966196539585323268029530167739771578272138088829455115039900871127978455106371561274843945547728675184939322057478953382998938974782151013269197210229735176265731898317085645176798267065795990067350594017496907758398247577727978681116618511118480987163 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((42176289924539671995472632888082951413653408131996244329610728580193794225507248190708445478441712413149233506723950042131434533853002284877213855061776400644320954584974800085478094481495044406827882362227354972835859758541118072648833492363750882245186117024344689886249501443021232461 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((153555188910334653985426991114929069902070438643996617005763397452521043818196550903899588242759799293717484605921151273508624627001897510366538862266956056038959688290262324961530274727150682604003254501453892419491412113929068034995607432167696540723006263539268655099941108717703854654246570506599553 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((104681684715179091009427213707320203610949765247281854833790669902353494561756314717489255846503280777575557137082991869123478626213102441811001826284847670828622141537823277669459402886149483373439236262835552800019367575697747215397095457628913520529815313855020803498327113754636772816421529730703849 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((2112224227372116725622397340242898376143774412184170961453520134541755265996186172461805411408263881443441718273460281036033692491296674706826983913757077749972645478181127101229351895763194898293459546673035286064509593157869764826593361996534852838155828370410584336547915248522577876979079 : ℚ) / 2168404344971008868014905601739883422851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((15492963674311108904689722830526429472575572518810786154616068439895675420039373685985813806398942965885520075241858901401247443313225699239380910807449068941604613413259415100963803777930436409604455210845716042854642465921336537827107548847607249016891664636089991388986779848721450756259972312702693256031 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((1331595462107876457787884066250069881134567413518447142512825997774041536214650780478124676263873618524127971719762614372838819883286190394379305751673648806725207383483286256071011496444801233354720490396352093593085333723834302534416640686340541940031401700307435560666500929304897706217952269010117871751 : ℚ) / 2441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((105771942685056266700504833148287793025819702328449634951957485622163801483794219983677045288374151107362399157692644187757592230347233949005117194710594888055960535195980150424850419014381244310655389570620210349794917711868822844160784491154656427937827593552784535040532176900105798542916804981 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((1562637716519246886338858952429481865065242336726388366653907474072341864449987520269646079899299579030307825906604091149662474707395919025250432956635595799005053724294057749388865801663118141642034845845445985579966321746553310834290151483306794417137673652153471101134985523313233072111319648844089946862022849 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((1083557805001122629514801631185142117497209779251432654458078138367978755974947450811541144539878497144126935906514245412973869718429630252574021198866083206428597665349178838179707800648508130935806185310629769508321585129052952845526364546091380316301932343799970873108304818852662295389674084872762648216000871 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((5296173847778970174564629576106028599083030963685787342000323914743179438144575735810552237848669109049956133894473554366705140146338261122152219441462732428069923668603308310877023901918917475559984408969466095678982626019784440050895220128539349356561254932484710197275646286894087237514555269999359 : ℚ) / 5421010862427522170037264004349708557128906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((31511690501118230951265001569309297039286963019680222172107260237385746140576979675896470209107276850461413169106926424280898251233441059122060848593091538408914856484988716142298052878102323325257249407267684917897297240471965467305300379702529616830252629146209035618097557383122064615926908602639007600064575844307 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((55082632662958109134752313810427041488142718447363086585385730618876627529102485711748688397420191570348399406090881944322429916443144348975900463547851884852510520534776345732803884917341497552009022090951488899467380341554797068338098638935500325344524914650824128836043627453006902681322531891197984014293056055453 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((265165851087858015987278685904506598314120797378434329514553269017078735534697155610373621939948413131505882195651588879292113601358239291037133472251111743926788131814291350466432029712555850880422105054411662284211562007946618719559149781639216389318940996262396753989376690317900378289198620872499783901 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((15881454371324446661587288812746145901888180212463145977966703832902802412231002025409300899368168433160353956851188696267814667936303576891041427082758639495013286238941404201059986793653119485951117981047432805056833580931478769379795024481366834983259707305411409754517378710353659077803734716969868927136473472206288129 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((11195530600569254062061183338197848500814047890947897556731387924263361277330453226462492927228917110268231859803150172179619111174360891784536259733610437535178596699554580535242475165405664213891411420371500462421389935597167544463454328339263567425091762626318657935629024300001626583681575641294324890141860980467445733 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((13275128658300796062048160590674762347026630306684515858986526548196074514370089218317402164627228246606055780820820248180950943054426041940199434748445156496964865745593879969637139448620170254652217610159911348415448821492595659821298761556691021376105559622813120586305227804895505932174533789308767313309239 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((1600329128418752782815776385073293679220559060487104124332184222121958959991861133811876023139424597500433857732224024269592174602493604951671970349793770909819203141306272355792395259092077582848163163590718756604622770818164480293083790387123903045449822312009686529405971087828223974268953566327966673999610493622157652271839 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((284312948534766942163632108549288442341315446718288212240036145153316824224891173864967846608415415818346682785216364680860756433831486675025223997609694128080038823086430521627510064490114264987927663429205760675068266052036111985713612910813770196019094147421199779295710936152015571274614239739564754710478687357010545257423 : ℚ) / 488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((664550070017154077890079772874928912731352827979926393076765874955414756532891635662264020638362912316762863452112645679001846504642589191019061154606956232110426806381549907888725116468506205634050885925328061052955841996339466808316202321020858056648239975059787691317842133494969254136775348294225982382084217221 : ℚ) / 677626357803440271254658000543713569641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((161214428448205611433853550132316287329762769901618433138112019604865179358161424479752346556130324651517180016194121878291621494662741850390900278388525171577433885658826303696849219542835264493940059340818452991394101415833086015973708687688351507629780724280727186563862998074208954284310803929114224080687940172838045253368482113 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((115474222505481147163939876930174557376049636489755178863094651787305058101456073193642660156203832929914230111222107174412107908803886915226273546899161465071369432960096207018083480635319836710150966501476008381444035262680490456472261376761100620088845163461701011474251126436148779209842661581861287697722091768625392237850789219 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((33264914760214268693720046953106838539986466055802000243245666579523296208203978813483463668871789323699884620269138004662468042382347011875447523767017309825453409226019881107966613265208914027383524711634039469975285435865446125877217461210602227932341384184343331981031760330819355670753453143241518583509067915580719 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((16235995810968901309369779428865024213737603228621979164212334998705086304775176734833667112534443321035366062871890090675025766524763566892936490157455906721577575143381481923080965726235322962657864792470348661942644607940962810189462622211464836133480577563175726234610083383466353161021479009813698987440578824545432380538626006271647 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((5860091504196892508970725818350972525820069076936062698853102888488715194066091715585951150576452826111958676456645008488881856847088793306372074927375736613305174366926362138482023129692834720877234026900898625718092463064253199537731552084741144305563314979691781505369288341395915601120266165915851555245335593142625207112344623980319 : ℚ) / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((1665009267365522542756248120300281488073583278287262989466357476892148659958527357288796993886947276929888861114866896401784081049861455792796720822853428967862048257505351175548438182708682998336831971381716986575164980161261264927726153904006578422502640509065760326253856150234493606963647027719261944508033952472559512941 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((65388146656162800612546382504136081078810719990581660514044646512931962312383269076858153848081277069291039923727704179523486904235751281102176426702815395815893390484644660664778137875091095761337900967648775866807227674499838735630418012125673769696444767932602367281047355521244938835382910672839665536705491840705603431219646589387138473 : ℚ) / 78125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((1189074525794704716026869957741194455159255940974542737446714227768208395210378928825120715807878632997492577068842634176130930142958881908792701454798461967971526087534062545325788230764858085523898934862130843821101390831056287772323886596592796943104593856037879301570420349087630789662368868785908309476306919778233748709236663932204480993 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((83333594378532473683135721491723880373158704899323915060454625103218995681785021095236601494836807687198031024093710629483699796609419164616644622868487788116049092810544749064177827494704607858599922298962757030166701999821694767428083168880966100258351970956850876019280525065903794138659357239658288802164212485603982880525799 : ℚ) / 84703294725430033906832250067964196205139160156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((164546514478553903218055327709541379572999189445241790263647345163502387911949018301403543615551226860875587102015800926558715666153630022234269514941170195425807162488232253253414718871776321053958820649667903439159151550559884505304563060868388111762220277952308560822997305510685235060703632227219551300327968243725233456821121651746162344090207 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((1884228028805500692782706251745062554916496666304751548740216388836311202401173153920655028348227817034148979501456769616896120969974895447309892518382589838969373251832854255971171821839725254384850914189203935097204868798459007045753493137170553843124064559712013102586303965552385169112705484397958448141282762638743946969403041292990505076601 : ℚ) / 3051757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((4170598431619097603956781842842817562253231327456261282034770572740640237443664109408358157865112277566827984444753425363232124712371410000864010877397645844002438185996268926136278610272880509846541737250805403645028165569594869641792412497879861000078453558934993444672864671081638951902263440920252075845218812358886149005105639061 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((16558925623306670308606068857893266316765826893649625868972707270420989434234118015199090909797719891315542819700775612423683259271497815356263591125208055904039253104048821452510561192031021755581919350207295122804935685016985682917918111862635999381653931659874346172935048097989552128180614084581796645056786838972946697007809945444683242840204894657 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((12225080896593606454798936967105507660837941696732573171389305883994316380176908843065661266972034599116049796776708863641794377749071499930074822376897788120932873807029268265166247630803267686391907074619572967088638137191688430014201790369729482854729225294092687787518824117464076252986316647736592613613252417297373170557572982388112478852718505311 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((208714645778565408303291092661989855334200228405312263073837050028421040152856882453400595203603527652222704358741231718197399126816475896030728608749647627440430933649678120909138037409653314353656130952265715922422982696785132560044452532737558767682698222314636655988434167730117378553720796341539762603267769595785534177951674719696479 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((1665994393777676900861017009759278045298523443624469222700407664416466404742565190772073983756077247380282189840669012099345070520598020003842460936422883991535762982498801119828066590997870275669718263664152736443609128535342987899520156885734912029284109463567751489083436430284142127911640705171884305877479423960932003135990552016478850463947586777210399 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((619438510596077943827861616931028065263616896031006512588851547717982591071432481674857045229078036630121232412627543237164316040208677093186098608626073346755040087653884839452612117700541997879260691913426061645502134778652495362818757791625828099197558572676413051236799744860426173839620263096311798494043735620202979132579921624137957830426293311829921 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((10444440002879433099527456485604653703956122409815592894037604701289739411765520581970850657302666689998126060766702921964107197439001857262992515887849639509914473781312176941535857945453647585316996356958853582867096981343754363747935447940715782749794711501689657326638798232630003107643844618743842869355439390975734295614463994611772323581 : ℚ) / 10587911840678754238354031258495524525642395019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((167577903082148680312139245096812001289773259413455937964477979475272175289974488804777798675208124051291551210737181859610712446454184974839778848213433946781458978498202688596061954274266528105169564727468554893396744618944179424393730753995277800443925581522981791711960849392060652181391163786563117054935093765769280336640902755928218854628177860367944803841 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((125500924435471101632448717977769420224814540220152699575813564700635871332045564093945662362801855600675636523908727044518550296030297793429804907792522544125651021493537493642887999117197461355076728997830696744977815508090548587889506294524644877112779438521180383432585303096592780267861828095267027396283980529466022697993111911845094050836548477945944653789 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((522632473071915512754555654705473466618650546427176139682038648014097026131214874713523929134590405099821664378481609038466049180077108549520204206437344156857858379577274708847058807690739493524257891270683399042772084603563236952713929080477401283042572905478148756720426309887945716491223191482966009018546057451205138960970218242004335561284759 : ℚ) / 529395592033937711917701562924776226282119750976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((3370509543372789047429040279143305072277521051500897871743174858008487873982848593669010749346091140888976155302892371078388107195096761954088626280016686426745828266922104834174699087963195132462767539012907681740712682134305297658911245660354265460355346430290615417558136687738349866286096987035531934574619102527643166628643502421701909324879344604755694121337747 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((3177254297973902844479515729676391462790950776102094072243835491166847113313413489506844803783036009001384990540755944572114531511295200306791490588055509195099022200740092451406734485086999000155693385083477966181089961515187255614606771308971267065674920708558960565582432937004315044750895777608182017567280826910029918475120974300652841866893957993000589986411601 : ℚ) / 4882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((26150972936946121149533543178689098526329712715574601360971619828736519714799337979120804495475457106000493437137244568464251092299654819915832906087249966210122586154893152500341505135733768985239992736608744747477233296127367426713981902924624219081343844191334454243044175821807873129679770023315534699125242602192359045481175117709842374023402254501 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((1694429811868725681142492757542538674606120642198341089901857935772662323415501201668379603059095692750112796497471783656430339772482128637330576969201979697963416041323506027495629503023439951082043561005553800712162893736105595445840632588290114580666671029238503931784207955065832712617450326508096260316716921246648947362962444072241499554906816626487680298910433737281 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((1286551833982366534778107193898226979186495611173081647961944187059680412637592440494707778219061226772249386472107759446065665666824834585984554102715976168289147819708079613600230041710290159244484503345808762929045436469609808734305768296948359226660562298694713722168739189337403563429074719235334413689947533782289776583508194583760714169432895702702794364531397284187 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((1308460752715157994557688900476614654602313558076668399179841187106810802835925992997775603112217572519757260133212571712836332239913428556012447360046876157178968588755508315713598210593354136195228017610999618651329300346147973127870392921963861063275467471335314838562859404064201331459974679129070990182064811024745613044937113873724259669089158874922639 : ℚ) / 1323488980084844279794253907311940565705299377441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((170331223596084642909356714983544016706235465361985241343085673387453713271907553731661996357571475265490893793358595130319075625854033020492768901392891450553493055895661762304404921917385442552455845204632716903157953236493417599877660007509273916402753859172501933563306065735759091507557493286431357911341913212500189965305679533860471623133261508893422485621061883461580191 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((65097869260356715986814501831853631596124742429745284854200736467428486970383702720211868152163466427611664373438287932024556970389775529115194669319157626080247246521924713462652963968204391344109455447680866650305689141528267729920022006061616866319068651272367633919295772230948316619695983296101331431852030677340931123192409079347031671672112284799707475313644674551018019 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((65466033394262572189946257508386600161781320333035934950188533719027954434882715383922144155106824151008837485419507417971391865457279108701870756105249695173259400305345906494423306049160120626106853522164911023605011889017069305274682451948454446661742261131275406175014629448182386563691746399465277406192353126895483453325290610893487876541193860204978279821 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((17119100104738288243759192389423336666921354531281877068933446947150377375371351596738889912497566122836343657689609760448301937261297786926970297249797446387331761965893012116988046085025844724315643116923184088235679384717655945137749865026785493955572892834225530041160411702966915012631930767875747130646838675718520000480636181618246290701715620762838969472434622995080195317377 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((13171165579201020261067143932025749737247273534306979345604349518595155278530456884138380538653797922205913467868220173173613039362481424194503941472355559517379804876276237883257449693907027113129113990422289835127956241904784649826926476826896447037892686988856601480301401193041041828818057853544368067565334301935166048432845909283409858407185649479654961522400413772479602065881 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((3275328446773280364686444654128809042950352735121974101679437290981258744105936320482705953327580583654405590225190160175753441145790679905097485572045365380772274870993700686240620223851358926194050968181331740741716655436375629981343256102398194161187868447467191371684014617557869520225865233524393711650501334048726194506300874106908125012275337376202471132482119 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((1720230977581576782204351543236879289404292313851235797965835604640563580577017112083637677309733379088218227610537023988456415948161401862098469163347566655906907092500197479634292558052929449502742664318709489697800617616109720261825625814691653130368376138927824992676664794998862091697742589720003877113326191838308734576019696330815167078892871180374588092950388487971125031268125023 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((166503488327882035909667782528270707444763294669534015407681119105896075214101718467916272221298463089296560201722175723562225487951496477686364946625869244805723628694388293075818178994994810678795364944127857638347936812610334983135203452490078204249668354545452323900563075250011775737133847918983303184724034026662041590021136848368707880686875581187760268783415073185215330912375049 : ℚ) / 244140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((163861962582502511822182715623026584371843831378064395382191994459565555938409732211234275933908821132885025117625238960524841462171426860046390372380646478684224265143772056648696596732129208421861368589099796926823781420615310821690539749410948474564234930745155934069812765057060411313927061243106395173492982385722904082832516904525542104953647128576808286714074607541 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((34565656994287894578954342418256707905199331024963643669442506612281048021143961276983564451946347471468424903893250082757321638670788914092113525288828417410878438669047092625068915555497482734833227437952576605400629696680963615705302422117840703241264181555273838870899019917659059805047982645986882689433148295738175557835451031436002587818281315896227539488291387108330015745819503497357 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((134669033661315960637073540084548031335739680093308690125503363668540513006451470881446359202798879083547263544007501656791024068053460379412466672103411890002889545879254243677654344091248999874337670251282284506866621124094480518086664843173712734253528061312146866698810809248965766894376215747839097702606638835753305113826457200726146313283644206837313669972246006015874737534151422931287 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((8197601800679428340347291085356282905514704057188060444077398426829460741380696366705372533248527919383067199019736139360180501685298890755726795763651294358695647634612270978362908873355838755798123053921575327333546232386385136823670353247482700142483470400395905576116903932024770728927207739938792362083285696680591975560642014362429529285409971993982165827414762924875199 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((17360732049348305817371764271327198130422773099286727293233503103880716952539617259700851809900145750294293983578909488779616861338931123097055976687056246102843607205982992037474284878595428418452475336991466263233969490988431011858190733539659567926369895794491147607327808781961114306000889436328155422363057605698160653587815900713455901923145641069635124284667361584332701976143131377709403423 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((6805515429164966284752340002062121574004284302012440250321865949825450687449541795670623818122961657027424772152528929867137364023302983365417672257443063477276240043702217716809680210878911238177859572377434835648608888122781598387223893723199791054394252356155027200718300244754112166147946880086891888913931807128852861688722841977070442787020169582603545174487905141203163608554226846132407973 : ℚ) / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((410092388607369694313701957152731457123575519044662126781176984442313949887944646030124555844802357591798404694591341873299548668943304411334205425502758364774554133847987841649049161381120883109567722638809139355176035848461808964730996781733087002016528311204262592952574734451715667390899645652974733156244004455826425135953103915030565580984940669824325314938504509515692005661 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((1743609483033169192810600024981690862670911767087525837638156782152109005014241432004855181739819080569754883201082366165050355197700067834053951173999466596666288225597026432542555612050409275331642449479189914640250934030120698069640199169420355404665536761058501820145764618023011310226390008934434637813576494664961971210665007900425784175630463239997009664708209054189292153399444444404526840485633 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((1375265707231469652707661977689649875769435310781092045399984755803466150926656654799518988588484329547161336077643123576331730042105708788678749779202899235478343595867314751654696091849257885278871362613564592457466888851140131415016075852034201177311855385348403429182311142671416998660273144686213439484195789131441170609149136704114021374154604641813733719072688017508008639175719346844405801500629 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((20514626972819906109157146692228690019374120616890035269728526869626237283767822669214041437968138334519784998898341264565467424705318426645883109552774526557107707315460298867494528418344657308901912877470824020063643153860641212788454457294115988188057128061857734369191420407319424845139618396435575946252186126043201854483693365450625830922049118234848871020886164074060205454853879 : ℚ) / 20679515313825691871785217301749071339145302772521972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((175089898228421038632580707861897477451500715526400802764872980006647989640545232383359286760729514522325999244094559582005799011784044253915658622796719853807742464267718394999427419051488035502709446834660481553056480924042198577449022477382359347909681925958990152363368220280946506118084268217812706073177050306044993732711426031272841248575490899382442391959680958647188529511342419323622628360339816671 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((34729451291087496108433748693396756596117601913394651243320512830966359788138618295864113415095256077332117358812385594222690812855812693245564278397109139617760306613305149046045763648181384332029113164111981521907766055938755685439030724743296905561975098272724346135225019510886167895203134466221718853627412459486056281196709778979967916379158695526677901288483541176586517937698736094481289328577315027 : ℚ) / 48828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((1026203094184612858524736244625272311924571382991764736349264278107311199319531392804080699344380072950928145063068908870351568933184005313660283901208238407375500215143483028314824575112348800884327271131097173481780074629836766129634954662387333567196824959707911740429314366580630367775036471589576614530381801795550492218506821553977051043834473384472540931053552888287124024936357002181 : ℚ) / 1033975765691284593589260865087453566957265138626098632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((17579488568109545814294038611436226722696420656091236738424104051544716281330407174732147268783566705422927454423929680010299626682936267830386052793136586795648819873855099466954589095477813495666743194789750194293012079100214177256608588894037361983895243183371259917886845618120410091022774080389260456183833437663264825289586917497110186681957315937197685011243803716099664486076414184328221998544653744859969 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((14028402511937994815082539735693251212127214238193509938387044070021413608448588415843678366658118678467338613612961867672795815209207794275711168859123341853590843220547417804543483423833299688417083004655901430756018221252486937307024371604970203832614588158732524838155469977585133887128529112031688403848751755362439115510815076371275332666876777765621595697158722111349169138041082250662415079571783422938451 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((51332392322411230760256417170405916166877105984458066095244531305700542624723390325391560086394732258833801830128005295239502607941360826480632122819055150285273704641648646471732515646221010124886303233848789660757630937975875318584862127830276517024091131775671251532097449926244334906547444234261052032347667754840454652688193061232924209155313240870651106948933429600966739411474932725810159 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((352953222900911019864741776566685437021053447413120900762640734262097845790320392776402227826388579173558230974905095628282491141994276072376582330062157519902454390325738582524716167347154166704116627400709475268066973744520817036877431532251573694968749473045643493658941409387291954705222009758797995206767912952279974426759704740275066926387866887397309270434453786949516797342954998821925170743691162847899420499 : ℚ) / 390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((708126351613979714816137902411503169858070658229875353981222191276177437520166735518344791854569842522272560206519606097239166708428525936093561961265551105752618649937142447046637544252565648745845133501862844927740523963169779757996008374598913519799422924950656493105846201776407563467480737224327695013272389525147065128457964440529905755151318484618101229527585782178029767366818836889848630345069436749871336743 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((2567667874968281267920671015746524714943656677081832187087560086219417878786835896548632750912561283949166584470404041612294913435747807999470517637567440729297517163102675546030999055047212196277015448140398095818453964785244786642771815843791404735998631860773367125971541692073231703159739973758831731752836710295424191873068732713458814295372310861401622530465772937959971129117516853761965085101 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((177135761545339498306842139174585588663350082641502502102663727205217311687836992677565729900176029734025846963862526872655197058291942554304547039522040973180377892795620755695269820428213387706969546915220723594378384798164511151923319769993831270532786604397204855975624434619713255357567559053084310155269677661263346192582892400871679681856783903196850476769634965308826399835436098596395776422327365146615240894631809 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((142941605477187644807652123217945993504648860248103380583172756088874960958756208201145737885745896231733912313464954845929403521586798005924293382500934092861026299867104888495316473661580255276750155070361895495401397673781447065048730122144633480460804578013521016849996786663341538523670915610167867734004030310660259412760578448742312881860685503259313294789820433203574741328496523036855866364881840435148319826966993 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((128432807622236723744159699348813440175390871004983657938311901154297139388132657327405999245267226364079763625350376117561969924447715921287040730917291588538355661551497022564355264455870535720302231209890225838786101446011653997553620627060483027850239507284995752951172503822640069255246982623017569003096969686616000980704586991379735047069555361695611084463626070522495079055470626969485272146576039 : ℚ) / 129246970711410574198657608135931695869658142328262329101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((17777300708374219904782983193933387126711743146225582410956884215728904257556575360806553860008584723394723814500430886653651492236532191911941245534221621737753222941678748250714463777550630492281354367067237110958829027867874600471941659808392856297651870675225203313843021775080191775476641365363250068187073934630597744766987145017195953597071554650515122915454110476753476980247651247636419596199580278599868152436115421279 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((901456992199260876964478313253926693836206283861887908768524562924620072161209933942625756150818264838221741782565444633617729646675945721978847269541383123316801309575093329996616947305974929303997134377138833954373490484183721222562396082149360506198895869687704721586073393291585614178044948956292636026595211319328362502715420291963994161853363373905962963457487675507438102939397692535873054798447236896877658973079331877 : ℚ) / 1220703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((6423969701709962573358303484480617338310842213505083175113655021012412853617185333756591398422651783576355977535391379805753700268540880813549813014710208192109547529876018146661142811185281183319326877003015355814538036063543357790680122739004109449832440133907414798365320657695430224623087513866425185236988054057391670229433526186649330383811770194969410910530869338359895531595829884714566243717447902421 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((1783890042246941964488940555212798836368850408179310224363952646544258004153797932419046110226704086741955375578066414740593801142411086667973163508345462038903860268086264220393233025042323054157402492137122197486286704290001714262455822009408287074654440006148420024461294735995430045952045272615896282110929834476866934128027359280721773731369437507580778017381207610138159752763192528468495439354246674858586433580201751949853633 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((1454999203341761098406813275303207815353610689895973068693123975975539546637880840717946804074855398860713242400068843922580422482850974492146932017456043197702095081630627920019180090017773941328042935623155834881558383236010725681160466660498826474043852831843685775719212935207617765184839580411718536569735714551575496083565484634788371680512398204752651206975987560876333347820598005464391764044781630327123845681617008765379919 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((321308286929173208384655038798776849804789388362474041969661099660504129506660499447951961930245382426005844425040814252663423676958748580669924635700424503967851961010825619415459610976462969700489749655045140857741508481999370342894870305793914715355651395472261626180142850483104885358507722316149416806886379880211385942945266990912462784962503035220663060911514649740947115463895824935559938162596776672223519 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((178984394138794084226494338101087455092666253528304865264444339562630509843549010089567010878650480250244152578676240081873874945412307451000888432567221640500717249758518357248218364383502981560948445320325782239407985321645258308322825332862222879669418566370302807526622821631667273142498973937598525828020247949124462297731311951640464749104787749032341274258628128970363995758225420952264477890362976576095288738188685362213999819807 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((73371070516360488985936761133269653410867814702776735653140558743146002138912851463574866243410536190099387888510090608618839389741127996451394439043346827366714287636152865154215403468682558065980392303634417219856948596110998265993799611601356840046445735470858779414710068241168671751470846970313516500941330823057687684925240482008263813798663428961023477830249636106847626556763990029912837993061006252953859381327327725772874558889 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((16070590295567660002000152416127793377655696841021560173306780358146504160814469283477007533429837082179489500351998943056301128708158449344199577402282310692540573590089308873625350601819487928711386308989172894893076968332968318593721291344819345767150051131166940796505753828923081190914695522260967358859817061173284521964496940684622583220347430577266836028307889074138506075852585291637359925046649455551944462141 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((3591196060277382342031030757503658971282294061504712174546522177223417353518683889378868621442231523073189669349216526781246373294065684943738920844741528532646258597869857403869699040741671416463964006032311942161895373185680709487705040863541596420353209900595799891314774659671088184773611357133166142255591087327986142061775786270477849486678582139171207044682855129977778345941554522917699754853563645114694359303696431216765818128495821 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((14795993093253735919511055048061019038192867907866979145608094238411530963304307223867423309168046911545038965881873056055498790866943403647515409825942319675585906850764998122794658298210574330921364855240099535810834290087031312927978071336455334256089689933605522367271348190042753494542777240611264628592587828078002858311653995041908373267666365577928277207395059913339463152321820240233308953404519371883870328063057576127168894679363533 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((803773503843432131432080111853460624764698386539060140454454608365168059636633267553822658118349090216858955557092878176730978906173881143636223879166185843735670098463219930993825402019168841471526039219440621092364755210247793570189427952703439140117686260272078422206484729741605124258527832223859740329292916446647459080884421286932423950423957529981781383538405583065815037909615018062493509506774008685263110000864599 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((1801158420924911473122532052151296437634164671481777805108421409460467235975255379696467189412250696664828525627132212048212303456911110458875713900844604867601511705526983941355068313492759318977791182137754715740246552534481566581746165351634418651370251032819241351025641711899891199453706672723720462018391724040417153819421803680509151985120679094750318334502402670013253832535401715443367039458640008171067266175447946380636549036425911316447 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((372883645252623149228092066436258008646174613012550205936039680804884245150807674813278751748503380070708867829927856295273024478312081397334346199958647898120731827130483167860437417953280639636042112679922077165513325504413998555636035913728931169130522150863518964923357614084593092468709826225699389738390354066334671832039729522158880897122646429675810215691502642292723376742242191535317611823463154239693164388165474062803298757022260203861 : ℚ) / 488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((40200176592708957573466570748140909027552441900571996733129850236850657163211255599219646281040857763732514306005801184372921614658130583229867957440014834487855752771457724327117935625781600018126265962765211437672982195855870741105159444262487417626007612622965504744391483675289523952422743483200524299382538788378514573613810735044707532599034934005811192638616900780139455072021342336447881544639819995414617742330756332261 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((180653107738309678745681918251729879722409561094013798044201853193105124802606211375692437633784483535406786644133404824874217326441138637886574456665506390785454158006987926503309614783351566802872641276886348116935205770863044508819009171971456299682555792144925968511415083210913779482918283244543667995491862419059541735715676576697301785819330304154862312207508456996275664480069155250889640678930715031449823648991567215436990796960681668971584577 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((150322907344406019786682615195759664108787679115813148633028692487885691634863207143346041892395033843478334898090270830106322807663246897385984748997973979388415624119681345790637571690936243898574638128534867685739666108967649609055120401440078974795210369841119816030104807546093093606803312538539381700232005699000340100753391727744059053303130434551653897887349409881970945646561293863641063557991663672486102492034452536460151510898392441426688331 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((2010550994155378067550127996270645742488260791626425392615373732971153128016615377691614906041984994124586991870807462030155151993369617562872745645764859282923032329893745667056012367463718843254454051218789301960466707730449890864956111043089394379472372851433970928145870148969472869593255705054589514948593495945374798485581424239272468379185907754099933809791762085874993772640014056397816688132776474763849665755729522746451279 : ℚ) / 2019483917365790221854025127123932747963408473879098892211914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((18117218152838362126617268459722444421063419163518409074173436264530813686580533358075319580054993442509347528609066092681844415375935168714388663019631104243408386802928670675370819093641640081387940949261618187613418395410973315842993796585805213362973750130183342529313006647373350383896178805663205733213729631125471325128580416943824469410180068190533900067419018242870651427539782972853959639375764315152493932611940902604072712563292736038963254137759 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((7573423950664188049278200943609182957625708879906489358064435138386091481280443020660088262977365667917123626026916000054435309181874393421234601112828833928344088477230245767207759737926838532233498685372405155081296082099871933720960124015152454817810270322076728720466194832897668545617208749105258179680198524365848807325295861324451151565513365181328353984811090854573911743845144289411872115792476582115708112006636137894255336536648255277552953110571 : ℚ) / 9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((100553106801073892550969849504903541247077437100246168513114388531339687301575232289005035055913130638038906209797992952639483709815450402296258356995709701737708820998861276999353366989872242552171709520402508905114440135705677405483166118460190961653948183843745955581868172952271981599756480680568295145161748805369022625811822757215064886926444505620516779859773872966061331448477622604536680861890950243893109394059333972744966840781 : ℚ) / 100974195868289511092701256356196637398170423693954944610595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((1816736303688987697519226725332439923531042208112579713720034088060465579332608535050938128782556626892227943478971681436115136111892334858927294383796237418101485528415551183655552095032175957060172165249298167171283397031789531039396916962823010211382762601374761040389586543054316056447545050426230327371491242222653113944284216633565731729253875333115566025671963308095554808803593066472708532743316407155065794250765707573841524451963994865333077424140910721 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((1525903878572790827083626081766184496041593705283093282075221353412982644500710812047401827910809823560336578949932319178535183867689906648577160025984604454901459928043713466056940114241752842761610140970539014369390987095259200370802879595924615610740267136644080620072052556918953865329825222279300443701083742036871044769534535563242151335139035193241562951515596822502653469897840398208626546753721210140170532906704398982333445130483366799163119825195262409 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((5028860075874998512196386030246726610442148889656909234070613467619446519708954874871408347500689065146515999823667589794472622596990516513843322690420759630213856113065321736472518366535587641666822215082253867278189593557029927217070967658094941741405463438210340600173683804797148940630920742801308864847779676936290357558143512952360943704825667550445540485809880597747165103149786651955254599148677503546877283726562944141224991907575559 : ℚ) / 5048709793414475554635062817809831869908521184697747230529785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((7286320265274002020710439578758925316281106633092605968216104656498720561012371088974791643257515711503716721131618451005630637417752503758711012508590211142614357465934863197813151587453259061270469503031047319515018740998519050559572601319188034562640384550454002524523101082208468471830332397165752200804475914980140276817122839693123687871023034981201767398053286629518271723443496465964848245008699322750444548923085840990073279592602231527323103139579567387191 : ℚ) / 7812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((19211107740867869785999733975921024544223377190437037307480574130007725936866394863065567424934196254027276447352426698637549733299417904526026057508489372899019061187121972208132996109452589047358335357844346844633980792732024387001945954840904599685081677379336980244343072694691081191104268752355124817591437916486100419028310387715853412082809408816557550595331034808293716918353883456112011542056852759142789086595869932597933816080696126515279489046342994321803 : ℚ) / 24414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((251499793835630369428236355801554374669440735618957299211400363582144339492560423846563318092834981841941617715687866515321644956599535957946060388303744188208650963313786201335578043280121065840532332396762365049626579250684833739085508344434937458748112141013797245551587280874332803912400972894910898580059486191099791164933327057061342525301777142660452332960591961497203615797377792986518746549269508839696248277586450623873204893531204275701 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((18262584831044700332380373125025211900340678937114229747543284234444591346579659257791304746976364443766831297067219674105238226436785522787060130412020429084116603813106650862276111058840614165195949958725930452163315984247622853252496204959402440471653414615404887754118251306218049946061778334004855527113833061253591099578656176329881340062285238143442721574226467453668145182584805995153529617906370567956463141796111881779733947865631893628667968506316454236902929601 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((15476414152244729916151602476144701480740291680993153645250431958283758991558354043346509455550136250268871424141593506020214256836330392385078730009238614114839849700588399711718957115764125794092152907926559334594929915171213822072993607780815236527558232250952157188789481690897613879065587553865313554145770083376336070599745707635483707193974708034544914414037486888859833391764277976178459488425638777894683480768177520730455554103394052765405390210004896191550310727 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((12577666717565720712568179312217168116533180791813040868853487505500264519339805819703148251578148209047285917499810339665747021609145525521619340644250197287967597759648567744757813382181626922656853616850981126074347319298032377626751777848318516867927258215249388358056272833135174043626669461293204848165424119562253055723792104142814625300200472727871062523429344473016681245072591783591507193586015377194441447557147695958759005476167438352269439 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((1830776791911685812327315182499436631570360715223719109272192705037961762140013278512714882758990040134732360055901006271234966999521814454672022549768757599617119364492511473555692387149199085571081186370799193996915213918880280987484600068444666425210664116771099700871718611647221146667862895896875836618965796831633787535724245011632489198578600364332740956638761962188216824534752680092994380574899792552902062892864169410890481666872613932715328331806215408991449075198751 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((779082390939150239938628157177645917964429915382842334481701649437717681480375437064804468685365244456864468427099720319439280608406979133018078375122584163311471635170910702883775041009706237993437166126762579085274392850011489559032171043812523761026335364442876841112097465963413337465801683981559202723238691102537999652213957801903555289370539837837899229523891234239632166405178465972757394360806300880265844928260130077364339951789688800740540889612829186946163957093549 : ℚ) / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((629009528196727545074278691402989910294778307118825570583248835851855094177159106534986705431142328426280010865023559601503648851633510927563614098629310049957504590792073834920138565022659711507121422644738399302018658284389948248947452055991886566637223025008640917810414645081158969242517571735900383337669927572045046793763835997188138622026150083919114016291935869113533337211476904086720057598451178865568775396396385239799940759141056876487629085021 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((183514009040549887378775052132838701402073216810911384286601978878674646402239363804612180658415741076671947306029923853863271611382030065556541274695568203189253826349282189195352316612149135743642140484025789013906548305649537104557632064669083996369487426531387846710505003968482825186394861953689557812193851677135129105723660817747037371578596246090735855223727986487125541342107015841998141987703526330781157129902806276436925127039276276976083370395050598967815616399307929857 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((156846133749726144388389503780509618486023931917166462977386627474619398505775161514315884892804505216334623614852770877281266266322683399428093340149317429346393330141789296962790821688416451623086982513353459850371064569384921940967234523156060452802494813914618320134851190130986597412908189033317642362186226962552108696592397796554067512921234283208637117718179376395665146842278735935304509290591125895675951884610296960733391115617896313771179927151662601310802172043850813381 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((31456424989535391567482787574264782503861589507951850425041981289724503534417103122952738307318618219686413432166345576055280503217152071614421204995287046444946808905347568504300411816603156140734196742050323404697857532867857770507133942467401540864712056175882324224665135954480752651123035814058608170154422715818631460811233465071451666503690688805863115613985564934142847982811809781743896795133390120544046503410729203818929407445150280100750347438804919 : ℚ) / 31554436208840472216469142611311449186928257404360920190811157226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((18393533380492961723094688011459467266936549520493998581110416405394216871354067478139366944181823332430289707046962855017375637918131873065495913069804738032830771626768232266066023211455141696230561866399668453390862813665560479871079255620322469057471038596838114477230131776326822507836122629984552538595684511352619800765985772493007244540273226799681175212740514336090081698608219267093225889163590406089867690951076275809887576868303765756675705128333078144472498720763842565168863 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((3946334484986513929028409148544427198694077835190080216380892282428764130470615360870509399596791039869489108266713298630169215205139373075194120465928233026860954277088657587560366733792145877558008770747643843071944994752590911392401095957475183801075503122328842628840340866990720748397819516738002240218325373700547734436132140021613149612068071113667349675844098684970490148563431251684508194939026531502746887168124875939687839880732045874535728255074134149557689245928910716757463 : ℚ) / 4882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((1573101659575201414110889340474229638573333212249218869851964676841518684608887824112869131068692344257797842778889364109669867641153331503832201182272836082368347624989179031724217112622856177318069300223510194974052306241857947443935786913970841234821661616074916881626489843758268199221288785238908730532909332400974468431180734310003160107317475379619581406927665545430559711061765901301625551025792876892325808124278363938820513337556939053669270627917825076741 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((368684271643046771104375659881918369008421480558783997759241026069239249523783484713559550087227326257531848300541164419133386417197594177814431033779807526495062367453559709180757733627859437486257150207646704887328657961320330652791393281925907549411751756167854539911459128644826554267773128465885481799516226276932331679717845551149345222090160739844271897816667998626153990737925861151024814303197611123896730093866615573169612004309311873897775388059170936541387706306825586384835193101 : ℚ) / 390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((1588384948173551235599731090620844081226980353680886187284128435131745840828200400341104492777782843644036606082508193639763717363153287666225993478036701961724568238051511209460216042572392681291719943959993681796104341767529043000117108973742496409193620660539650455480114684696978898904430584609774813180387590133730063590084899899904816743116716004704049350213507753703074132836519425495164842349842680726956685164636134843912277445206301924004769657821707677243230756912395336962856244547 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((78668301230390049010339123471162813738898441513909757939247298942892114898778363140856537969447088415968332510754065734765727890736326893759146131531159220086761538694364910376447870471928817342596468743236047080881851663934941784559689059337671484968258306920155506882991104744921004643092332047376918648590813020049535467377428634639238964298838471919887447941163226146051154219740582821457326849804850423827346269170357797712060178219096550050915748129418356292493999 : ℚ) / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((184734884039315398214792349884581797422047806417604196052387527192931647877551539144966811344733089155333464861194282561913036576407476339377189809677106566773720503572524626686968703105964246384183074185757626732455663194708969438458200801065365317656086710362089034958930750996335956064579131080512561542346584011631840376658962957139337969342100907909618251476431726518967465738123996543385383932990582868538471524184456748048512087296852876196799066222194118680204065747479897719517344492225183 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((79900883669041279407709529534839754213313885116294273698361978595499781634634289115418834855976943310166811651116452903327159089161737682577644650255028619000441191189695519107884489032002733224430567224666940032631874891748240774489117019454797498026239346367168359381945490475027475033313959836992304586220149509338887496300105418150998282996046224846298407707931065869312910199507069283629175121772399576832371432209726919092539597655733672386035219494037810481979749977992908853727264520379183 : ℚ) / 97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_closed_source_model__bigcodebench__self_rec__none_sft
