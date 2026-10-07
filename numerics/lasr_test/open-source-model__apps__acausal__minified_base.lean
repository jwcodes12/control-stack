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

namespace LasrTest_open_source_model__apps__acausal__minified_base
open PL_TMCERTF1

def cat : Fin 10 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((363 : ℚ) / 5000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((363 : ℚ) / 5000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((363 : ℚ) / 5000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((3 : ℚ) / 100000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((3 : ℚ) / 100000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((3 : ℚ) / 100000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((363 : ℚ) / 5000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((363 : ℚ) / 5000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((363 : ℚ) / 5000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((5117 : ℚ) / 100000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((5117 : ℚ) / 100000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((5117 : ℚ) / 100000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((3 : ℚ) / 100000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((3 : ℚ) / 100000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((3 : ℚ) / 100000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((363 : ℚ) / 5000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((363 : ℚ) / 5000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((363 : ℚ) / 5000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((3 : ℚ) / 100000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((3 : ℚ) / 100000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((3 : ℚ) / 100000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((363 : ℚ) / 5000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((363 : ℚ) / 5000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((363 : ℚ) / 5000)
  | 8, 0, 0 => ((0 : ℚ) / 1)
  | 8, 0, 1 => ((5117 : ℚ) / 100000)
  | 8, 1, 0 => ((0 : ℚ) / 1)
  | 8, 1, 1 => ((5117 : ℚ) / 100000)
  | 8, 2, 0 => ((0 : ℚ) / 1)
  | 8, 2, 1 => ((5117 : ℚ) / 100000)
  | 9, 0, 0 => ((0 : ℚ) / 1)
  | 9, 0, 1 => ((3 : ℚ) / 100000)
  | 9, 1, 0 => ((0 : ℚ) / 1)
  | 9, 1, 1 => ((3 : ℚ) / 100000)
  | 9, 2, 0 => ((0 : ℚ) / 1)
  | 9, 2, 1 => ((3 : ℚ) / 100000)
  | _, _, _ => 0

def kernel : Fin 10 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((4637 : ℚ) / 5000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((21 : ℚ) / 800)
  | 0, 1, 0, 1 => ((779 : ℚ) / 800)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((8427 : ℚ) / 50000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((21 : ℚ) / 800)
  | 0, 2, 0, 2 => ((779 : ℚ) / 800)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((8427 : ℚ) / 50000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((99997 : ℚ) / 100000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((21 : ℚ) / 800)
  | 1, 1, 0, 1 => ((779 : ℚ) / 800)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((24111 : ℚ) / 100000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((21 : ℚ) / 800)
  | 1, 2, 0, 2 => ((779 : ℚ) / 800)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((24111 : ℚ) / 100000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((4637 : ℚ) / 5000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((21 : ℚ) / 800)
  | 2, 1, 0, 1 => ((779 : ℚ) / 800)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((0 : ℚ) / 1)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((21 : ℚ) / 800)
  | 2, 2, 0, 2 => ((779 : ℚ) / 800)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((0 : ℚ) / 1)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((94883 : ℚ) / 100000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((21 : ℚ) / 800)
  | 3, 1, 0, 1 => ((779 : ℚ) / 800)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((0 : ℚ) / 1)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((21 : ℚ) / 800)
  | 3, 2, 0, 2 => ((779 : ℚ) / 800)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((0 : ℚ) / 1)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((99997 : ℚ) / 100000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((21 : ℚ) / 800)
  | 4, 1, 0, 1 => ((779 : ℚ) / 800)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((2557 : ℚ) / 50000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((21 : ℚ) / 800)
  | 4, 2, 0, 2 => ((779 : ℚ) / 800)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((2557 : ℚ) / 50000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((4637 : ℚ) / 5000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((5001 : ℚ) / 50000)
  | 5, 1, 0, 1 => ((44999 : ℚ) / 50000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((8427 : ℚ) / 50000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((5001 : ℚ) / 50000)
  | 5, 2, 0, 2 => ((44999 : ℚ) / 50000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((8427 : ℚ) / 50000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((99997 : ℚ) / 100000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((5001 : ℚ) / 50000)
  | 6, 1, 0, 1 => ((44999 : ℚ) / 50000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((24111 : ℚ) / 100000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((5001 : ℚ) / 50000)
  | 6, 2, 0, 2 => ((44999 : ℚ) / 50000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((24111 : ℚ) / 100000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((4637 : ℚ) / 5000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((5001 : ℚ) / 50000)
  | 7, 1, 0, 1 => ((44999 : ℚ) / 50000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((0 : ℚ) / 1)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((5001 : ℚ) / 50000)
  | 7, 2, 0, 2 => ((44999 : ℚ) / 50000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((0 : ℚ) / 1)
  | 8, 0, 0, 0 => ((1 : ℚ) / 1)
  | 8, 0, 0, 1 => ((0 : ℚ) / 1)
  | 8, 0, 0, 2 => ((0 : ℚ) / 1)
  | 8, 0, 1, 0 => ((94883 : ℚ) / 100000)
  | 8, 0, 1, 1 => ((0 : ℚ) / 1)
  | 8, 0, 1, 2 => ((0 : ℚ) / 1)
  | 8, 1, 0, 0 => ((5001 : ℚ) / 50000)
  | 8, 1, 0, 1 => ((44999 : ℚ) / 50000)
  | 8, 1, 0, 2 => ((0 : ℚ) / 1)
  | 8, 1, 1, 0 => ((0 : ℚ) / 1)
  | 8, 1, 1, 1 => ((0 : ℚ) / 1)
  | 8, 1, 1, 2 => ((0 : ℚ) / 1)
  | 8, 2, 0, 0 => ((0 : ℚ) / 1)
  | 8, 2, 0, 1 => ((5001 : ℚ) / 50000)
  | 8, 2, 0, 2 => ((44999 : ℚ) / 50000)
  | 8, 2, 1, 0 => ((0 : ℚ) / 1)
  | 8, 2, 1, 1 => ((0 : ℚ) / 1)
  | 8, 2, 1, 2 => ((0 : ℚ) / 1)
  | 9, 0, 0, 0 => ((1 : ℚ) / 1)
  | 9, 0, 0, 1 => ((0 : ℚ) / 1)
  | 9, 0, 0, 2 => ((0 : ℚ) / 1)
  | 9, 0, 1, 0 => ((99997 : ℚ) / 100000)
  | 9, 0, 1, 1 => ((0 : ℚ) / 1)
  | 9, 0, 1, 2 => ((0 : ℚ) / 1)
  | 9, 1, 0, 0 => ((5001 : ℚ) / 50000)
  | 9, 1, 0, 1 => ((44999 : ℚ) / 50000)
  | 9, 1, 0, 2 => ((0 : ℚ) / 1)
  | 9, 1, 1, 0 => ((0 : ℚ) / 1)
  | 9, 1, 1, 1 => ((2557 : ℚ) / 50000)
  | 9, 1, 1, 2 => ((0 : ℚ) / 1)
  | 9, 2, 0, 0 => ((0 : ℚ) / 1)
  | 9, 2, 0, 1 => ((5001 : ℚ) / 50000)
  | 9, 2, 0, 2 => ((44999 : ℚ) / 50000)
  | 9, 2, 1, 0 => ((0 : ℚ) / 1)
  | 9, 2, 1, 1 => ((0 : ℚ) / 1)
  | 9, 2, 1, 2 => ((2557 : ℚ) / 50000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((363 : ℚ) / 5000)
  | 1, 1 => ((363 : ℚ) / 5000)
  | 1, 2 => ((363 : ℚ) / 5000)
  | 2, 0 => ((3498231 : ℚ) / 25000000)
  | 2, 1 => ((21209001 : ℚ) / 250000000)
  | 2, 2 => ((21209001 : ℚ) / 250000000)
  | 3, 0 => ((25296297147 : ℚ) / 125000000000)
  | 3, 1 => ((1129330368309 : ℚ) / 12500000000000)
  | 3, 2 => ((1086228251427 : ℚ) / 12500000000000)
  | 4, 0 => ((162673929870639 : ℚ) / 625000000000000)
  | 4, 1 => ((63469415446751391 : ℚ) / 625000000000000000)
  | 4, 2 => ((54528645474775329 : ℚ) / 625000000000000000)
  | 5, 0 => ((981194012810153043 : ℚ) / 3125000000000000000)
  | 5, 1 => ((3669592548971431482609 : ℚ) / 31250000000000000000000)
  | 5, 2 => ((1385572532184309368031 : ℚ) / 15625000000000000000000)
  | 6, 0 => ((5684171637400679660391 : ℚ) / 15625000000000000000000)
  | 6, 1 => ((214197507691801198966352391 : ℚ) / 1562500000000000000000000000)
  | 6, 2 => ((143050389088929603348581547 : ℚ) / 1562500000000000000000000000)
  | 7, 0 => ((32029378882626951585233067 : ℚ) / 78125000000000000000000000)
  | 7, 1 => ((12481327884487442050448430342609 : ℚ) / 78125000000000000000000000000000)
  | 7, 2 => ((1877081548644860254278387335211 : ℚ) / 19531250000000000000000000000000)
  | 8, 0 => ((176879604878741174500725731679 : ℚ) / 390625000000000000000000000000)
  | 8, 1 => ((721826197266067789705879485054062391 : ℚ) / 3906250000000000000000000000000000000)
  | 8, 2 => ((80057258236040392804677041386405353 : ℚ) / 781250000000000000000000000000000000)
  | 9, 0 => ((961987602822722826159865217795523 : ℚ) / 1953125000000000000000000000000000)
  | 9, 1 => ((41327206090761630605756164789214543532609 : ℚ) / 195312500000000000000000000000000000000000)
  | 9, 2 => ((10811167814672756597703707115744819207813 : ℚ) / 97656250000000000000000000000000000000000)
  | 10, 0 => ((5169720889288965744903295014917840151 : ℚ) / 9765625000000000000000000000000000000)
  | 10, 1 => ((2340772947049826300990970254769406296723872391 : ℚ) / 9765625000000000000000000000000000000000000000)
  | 10, 2 => ((1179660838644817662939524813113664171271331983 : ℚ) / 9765625000000000000000000000000000000000000000)
  | 11, 0 => ((27516917638632934159116578984174024780187 : ℚ) / 48828125000000000000000000000000000000000)
  | 11, 1 => ((131186216011629251408554048863972632541428533722609 : ℚ) / 488281250000000000000000000000000000000000000000000)
  | 11, 2 => ((8098720448296791418233939913675446866619344216301 : ℚ) / 61035156250000000000000000000000000000000000000000)
  | 12, 0 => ((145320556465340915695823576749614952905727119 : ℚ) / 244140625000000000000000000000000000000000000)
  | 12, 1 => ((7279369585415337721430943759828447470988894458983682391 : ℚ) / 24414062500000000000000000000000000000000000000000000000)
  | 12, 2 => ((3571536837897416422527051295772578603747715060261397201 : ℚ) / 24414062500000000000000000000000000000000000000000000000)
  | 13, 0 => ((762474467204785826081533925387964536623856650803 : ℚ) / 1220703125000000000000000000000000000000000000000)
  | 13, 1 => ((400239162262421774066152408981002745695183393971706723912609 : ℚ) / 1220703125000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((19711971346520794554217093100137233039245889118608000828519 : ℚ) / 122070312500000000000000000000000000000000000000000000000000)
  | 14, 0 => ((3978709338803591875540072812023991556324823289773511 : ℚ) / 6103515625000000000000000000000000000000000000000000)
  | 14, 1 => ((21823496873137851327436543412601353201193464655998633869343492391 : ℚ) / 61035156250000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((10871786036695263633556977921444748226551869797734919619112222419 : ℚ) / 61035156250000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((20664851375907255526879317629355248846678205594679770507 : ℚ) / 30517578125000000000000000000000000000000000000000000000)
  | 15, 1 => ((1181010789827897801579076058352968110432309128776855810596587814102609 : ℚ) / 3051757812500000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((149589701931953140683735150773377898201444026443230703980254425519993 : ℚ) / 762939453125000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((106900796689456943878139395847320288902046839342530095840959 : ℚ) / 152587890625000000000000000000000000000000000000000000000000)
  | 16, 1 => ((63478796704556791662249190296265771949567249103729087851586555046803302391 : ℚ) / 152587890625000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((32831782948873154416206551566428121684939096936688809702423411234223807637 : ℚ) / 152587890625000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((551088398545886848762932378544024179638791194031312054414526883 : ℚ) / 762939453125000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((3391093257152325244344126432774112236757712885970698233534179349551101804292609 : ℚ) / 7629394531250000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((897427431617915795338893407304662086610180117910904458072567721958950217557377 : ℚ) / 3814697265625000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((2832343925541652317713717439308640120985074766723193996320161156471 : ℚ) / 3814697265625000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((180155736289877284976875593599388925765596269769301365652075025969280030091363112391 : ℚ) / 381469726562500000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((19545106273953592859174941032181662753353662478897008256703876153593332360599230571 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((14518313890158516797238507766074164241007791693295450560936587282556027 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((9523283174471568270763054927777153195030702434187061470537436687942779174081248694482609 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((165578438227933278984981896910195538404517319829865890698222369376565663904997837730923 : ℚ) / 596046447753906250000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((74245097045774417388794960511285899585553130081811004251062955229212297199 : ℚ) / 95367431640625000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((501144307332728843119056486033181011992466545094154127367957986520799811081482110003022922391 : ℚ) / 953674316406250000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((286053591693732940795532449823793992173624538874141821311095589662836344571532251122829258073 : ℚ) / 953674316406250000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((378892892686802848431842231890832716378209864189357626712178923397857422111763 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((26263989988924643825128058790176520196922514098083209900026399826462377681777603468026028484672609 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((7689174126798632773648283098136422047397627908406686304072574164914246262296435900200655709452159 : ℚ) / 23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((1930018231816439183178452429277791305845759140246051315064373667795864866332245031 : ℚ) / 2384185791015625000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((1371337621144290151987701817667758673802058964980744111410048645382249030100403054757703255781782732391 : ℚ) / 2384185791015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((823356506998235496132263604275754488926501209505299086703955555226090685900724433089856780991123123291 : ℚ) / 2384185791015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((9814953983071500367398483914561118285206785133320939947953500697569425385182620208747 : ℚ) / 11920928955078125000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((71360842791185924904370034692049706882953492825539006895977711706202944302015594461072888806924441174862609 : ℚ) / 119209289550781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((439082789017561941405462267189611373748877248103976549037529493051754821743788144414537392699842448696591 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((49839238830195906578626769911819905488503862663209198538660382734629425511091809907959839 : ℚ) / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((3702012413453981168145345371674746285469215548173809978109255618952873254159382571793256393422792928427642542391 : ℚ) / 5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((2332704217098847790577194199621472804854223146363604646500763502026312446819252258950802330333450165205277748509 : ℚ) / 5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((252741036509085215680092332081108901750192411169301053623768194740476646094932722543209773443 : ℚ) / 298023223876953125000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((191511459931996671465343644012893042834630012170144195394122451002848519262015070483095459931532258986315486765052609 : ℚ) / 298023223876953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((61741560572457205775039016996256030459633367159816534594206122089032676469235302321032614643091155709569466879826941 : ℚ) / 149011611938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((1280142616559962129483588143860101977415642210592048985653413119011590207942203034432863719455191 : ℚ) / 1490116119384765625000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((9881782109061853382885140389673799652168228165901993217712580914574304225392174702107404678447463122125210588940602352391 : ℚ) / 14901161193847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((6514365779519918959340145015337528336522068468512059601575368953234008261707576105774253647766510658740396629562693133727 : ℚ) / 14901161193847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((6476933464325214316290398223079292869276332930515331146474876632856743794227995470665189067113720667 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((508690245379838046471922675469375010438474366189132162576375618656698742137612043172118617735411494942512351291738165255242609 : ℚ) / 745058059692382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((42819842255004395252394471579241513709456233509031254761633830585045404149970685358621846336595122025800910761122947586111083 : ℚ) / 93132257461547851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((32738101230759368394013576560418681034834355798799590526204002946556720973835214997474481704206322732879 : ℚ) / 37252902984619140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((26129666777356371932766876624808360458646002102695475290126412268024444268943824865581826731939353566484813295776925698320662162391 : ℚ) / 37252902984619140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((3591752114041622465221215182555331086099475743739005881838908081774763108037288958304952182739668810903925147105630942372153855789 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((165329379190447939289915954510661423958526907839033701270007961663183515155673891943289171662404718512359923 : ℚ) / 186264514923095703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((1339532119569286981941038577618405236133818061968990444801944644384562129248353085328686504113274791125377992496665879498731476645432609 : ℚ) / 1862645149230957031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((469400365226177031299107229999851664185320100739068850155133655805651535640918948663298715920970245647659594882605919648162194128681723 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((834246350223190834721715281065937022895689271649599272789026918232181959776859836941031888998570679741812962951 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((68545728101812646344253491839328795032951609631572676426155805215436718846981891822789455473430112298654004033587467911563417717567821972391 : ℚ) / 93132257461547851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((48944094199591484659544186412196294659255662554221639590716243921764222112982437321528319042525967398216083560720593619868457261896906184163 : ℚ) / 93132257461547851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((4206470420570354601776468758302749975167311152639191827922717819842627747485299063895564869286372241962786709203787 : ℚ) / 4656612873077392578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((3501695818600085009289392691339031552837923686563103462822377440697351109479745754587912754537066820266012190279197568552442233872834420935622609 : ℚ) / 4656612873077392578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((636308120281145565640610139262726091832909139761228628687461360529466815453963284509305723854312499639473554580209229831547340083413889766269557 : ℚ) / 1164153218269348144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((21195753813111827794296860632249851634850821814787932506077642530610264865089331759283734298880908085981441970577960319 : ℚ) / 23283064365386962890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((178609368714457568696497501977837133471965451046001691054985674270973083940653059829243205952714617427206178883101750174291348082043676107682081782391 : ℚ) / 232830643653869628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((132044897206944102364503515476120142421298769876964188666803004630789361812959783877231144756320703853257008893805607573089958637252211441468503849381 : ℚ) / 232830643653869628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((106736462796035013011451417751742562030803260755171643030682028414439798179419231367798675943910770794695946417570001999203 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((9097242630975598641766477091719508249363862930576574600412243259475337150148564520537894576953239282986782756509299451646126372343883381169585998125812609 : ℚ) / 11641532182693481445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((683511378235627996335147770030109379330932256637456598278345176241002688500858326689756955585920115444617024380675038780310608047601268686915929571203301 : ℚ) / 1164153218269348144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((537195739808391692980584599114830260136834720121730908733272565757757344157966975852482460351914244175005103538272099270304311 : ℚ) / 582076609134674072265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((462745726195568073287876556667932606984729178716676619123594616843192039489062812466720835907868590969549680063588724024425460929102408269250200329663441592391 : ℚ) / 582076609134674072265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((353068595489759210878327296971538180360194884680102544235934174397324960886394209594333743223451342403140115366362967258434248503431855685654398724372962274599 : ℚ) / 582076609134674072265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((2702270454607398968583392661095467916254502597204466223796184887418720804860492867027961168651826350239498665106967724316401090107 : ℚ) / 2910383045673370361328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((23509610827856134586477060753673565512650138748400507458517730264681343063102330344428235679238101860157966575976327760825913175659679269707989764634525208216002609 : ℚ) / 29103830456733703613281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((1137620319071731916551657543519911096597440014905127135019368662033626831525728510167593438230458611264851250085560898281777154907023201109580158752919112549889237 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((13586897143593942458483301144499684727672128543237109879742909322960608372138105424408655939038518786060555310101009337655151854826159 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((1193049523077614222675736723835941124995631268425469790977886550400205983947615011448994515374313181380725666194358228802468485507760977457589831418788999844511901402391 : ℚ) / 1455191522836685180664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((936639991556650361273500385642761172101374595572203992979832295819290177327794869716990200662788260175562653288060092920397434890052248455489617832498974896407681459817 : ℚ) / 1455191522836685180664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((68284787282742278385797614282045038082215660054990478512367870530568341021604394852982937589321611610962794972938380298706939150828899283 : ℚ) / 72759576141834259033203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((60480842750480893029672975738257807015987242932350593775073345833871469318564994422940073032441882093860157963661440707643620821962298340514084824014086204003191051206192609 : ℚ) / 72759576141834259033203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((24057151822484429167273801604721075774746453699774690952389942059061834407647732007325631805505874569862576445973700811783054534320886888256992029884992579792926638461831287 : ℚ) / 36379788070917129516601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((343048284769561780903996271800842841587234015674990848861849815650245397317179578933281881601684313040034480289515269445104076842393605975271 : ℚ) / 363797880709171295166015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((3063069664129883839649628104270370293361570460647851752324877209701754521315149762697648017271049632008038185866466010277088696060776788339076302995809865093939594113227461212391 : ℚ) / 3637978807091712951660156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((493512048863021720447540429697742934092516708395401591160466361589327638216324824460883103293431910377977360992202398127555417942088926434052741382096801460484754011074012281007 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((1722773527173887158197094384215508256440004130684932566172397595170187907359761707513628084987010159566639885102482304416947604318179150907331627 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((154990916537506427563402468616822543338754882282598973354448258840038024024492574914084890028080194885861834685083762621408369116926998933293397268508448119362187795501122527096382609 : ℚ) / 181898940354585647583007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((31589038706062280268545537282324948323311752669780821904131459987877311580394766960706832889969557971291303825989693771026262957220060680378354284636728744984139784720461981672084339 : ℚ) / 45474735088646411895751953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((8648793998992460653286245018982311785112299153986032309341407648804161326427215037740693430084766109910509147220210445581386041223396722757296754399 : ℚ) / 9094947017729282379150390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((7835995294210912701739914586834573306746277013590205978319633236887482015548758208486471371675584470468173305533835634639670698812119418368026130348311656923179088609755012596810121022391 : ℚ) / 9094947017729282379150390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((6461010184540455843461698274222090937639935399845146285201642014436994733371223841004725627893389611224744558722944816879306481201533963890782537557283376227095525855845388611057502110253 : ℚ) / 9094947017729282379150390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((43405923540763769552919909949895979747565731177033231818416107267504896070642996130003595435303060451655030915660115836160887073152890603425585050148163 : ℚ) / 45474735088646411895751953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((395864571033158156392678927832899505467622327403629826397421555678369414011141073027423933097883540902259786820965342161503053368004768717652048908293075249886135808350365811843858635886572609 : ℚ) / 454747350886464118957519531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((164963404880242373460667136745239785604948792201298178892682587412662311783365520711006245929662118526156807549474252911792452756173618026189911042706050621557945095062285730052811976346126069 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((217780596295700246935047581422042658089462295467903095941995489399420203079571573054826672033500291314324378355915957132278033358209953728084437877537031831 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((19984240068194679994855683770146942793713299326999370481296562108418865113580193381622529373191167510248056243248781824891881861035222646602938057182189724799626225239958111167161794756259880832391 : ℚ) / 22737367544323205947875976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((16826095232148877066832908290890420651717760659877986265797152701912308175349046639159287210600246931169261559729231489705173933043505123478017510611832813163652507842975770558324109285267403575471 : ℚ) / 22737367544323205947875976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((1092385269209055282628605429975886805560836664084666655883033084345111481679973384255231278219340850824522142436382293222373240682019555437127538438139216600347 : ℚ) / 1136868377216160297393798828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((1008182895036172098580728209442005812084844850379143010568455942565390554806088865664351017948182842479945904505745503500162036347164781733900637017697625044941480509572875044411113602236938377576762609 : ℚ) / 1136868377216160297393798828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((21427466098312722844617182867907072495450193046704333893789254538438867500388657420425575864628238509360903254968571142788185575001545887676215079599749889331853248821277430332525068232595088938385173 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((5478073714251855533502792353407562117385599611360599283329624412108281940550036582791507437103083525273309174477504693672144717042524678561960395737651547375809039 : ℚ) / 5684341886080801486968994140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((50830240825047193732459844451990229452615677579298474278640997414309912095600739760690543079025203323728520991178389760408880050236847809984869584888509651615657028450269804123455700987059990052576740642391 : ℚ) / 56843418860808014869689941406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((43610504536394865276399366250337485275146838573092027031317754767777942110584818227656638974055106582551460891246462577177332851351953609432917180401871633651514917776720471598431800940728785111797165800689 : ℚ) / 56843418860808014869689941406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((27465243917633185048622193015797740538317025397879098876799468398946103358330519634404219985846998306692334642052189264557735052926186934491810355035490225181626513843 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((2561268473336033965997435186089020516628706711954995614223880759496066914236845017996717034942580331463377907897656370559183150679904573776392785841237999697317160663623690915751383088716712492375900752166952609 : ℚ) / 2842170943040400743484497070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((1108315563999646779214363382001669818694431796262319897124875637432101743712152767484767251565855391465099761061041348351103805054610518184303086497465629205207210292157221895939617285584070805749348471908900851 : ℚ) / 1421085471520200371742248535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((137673416569301733769309833379488497876176046769965381491719134965913081272578619544732368074372531148132355735196001619754217440418728815238524616299568174167202144689991 : ℚ) / 142108547152020037174224853515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((128989888514856548278734544666020284270987517732742184992747824442876461363244881833999820270303256188697379031976938869998005897413412001303253328623117409992906332275286767517896487609163345444423157946760700452391 : ℚ) / 142108547152020037174224853515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((112555087763993716699687449019017471946521635066503199168178185295854123368704786703095664998171697758724401213367778778069115183855040189006649500590942933696521632352347734460446343294667483550201743436444188785907 : ℚ) / 142108547152020037174224853515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((689977035248035412982533319206860039651828328872329473977101628836938957860947058828923990760865426933889733544103859510800306271221645516261038645781097623613316344927488267 : ℚ) / 710542735760100185871124267578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((6492920749543107786575094252157068749788923720352262455328746746069529204328822113991364485083313253507003270091645476311431108797240189451652958140825800771280969971650274242537824045924741381653597684446284759657142609 : ℚ) / 7105427357601001858711242675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((1427486206688687713927796744070383665440183908134755281629395507541741220186483587726108732606128702911128730684813337130798035412814356720906947693384012810196075375483001206835656334112541995710772116447075578534859121 : ℚ) / 1776356839400250464677810668945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((3457350525526056577471225110293069378865527960980991770831820252916885947601211511789720545158132984692446694444009596551581020179654770258902436200486949680694947891428763094079 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((326680692341444558291349157546351007254739713219036655220933127284518061948218628719531899242214893095525465725394588802673211781390805777403146006054532901063774318164114378872629544242567437433030242202398367899811760262391 : ℚ) / 355271367880050092935562133789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((2315303231420816926374477992805842232498126002032840609690109890020615745756277913987355849792595132719840402896575843657828721258079449118272667205444948795529831312909290453700179644548725925676846239135389487336046980249 : ℚ) / 2842170943040400743484497070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((17321369452268906187090161382083259584799453155068858841347150512775600139026817780168934167898262650018875322136872499209681190573059169690530596661657985669382473372555174467244323 : ℚ) / 17763568394002504646778106689453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((16429325472488244572945780418085812971826682888430024432879763103159762932003255950796255178634010280050243024068480300766937525142650219783841275470311449550284323983570507358238364761371292117048927868865724157123629400047332609 : ℚ) / 17763568394002504646778106689453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((7328510703118865922377839518336531607401924900746438318595271718589792910356942546833003631856220113764117570167787693598499030302637530525968551061752937697237897635669690574749409164444047247897067365305434090223152935550155633 : ℚ) / 8881784197001252323389053344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((86767365477193827176317531056991559069715064280054298447326736927740457844667354046643347736544243908137524868748677778835291680687275369854990376720108079548926529028538344004611925751 : ℚ) / 88817841970012523233890533447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((825927385567295317379625070105241879102810968524962032520733559593476948472487630248505526557011040104725281326064044422759037327949986147675417068793496504645826044272837688124057035219946773975084705171088721346406199372729920072391 : ℚ) / 888178419700125232338905334472656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((741714362947205406391462648842098322275063678342416507985768959408546156769252398339808733008144783209074318443327026832613170292415166221415107877082668446076988215656836919644847388153253196093601957014955943761678588523279617036343 : ℚ) / 888178419700125232338905334472656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((434581150352862322550486655152627281281268753066611781900254079133932503025722520714285203454355659002033702816387618860459247523346895890017590376851141164868372315105332301149385499707387 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((41505142370657185283853388257825927186823841137300281966751299561903169501125285249425134009843517431518490553077677310699286857671592067905694161418411154270799341882950625711565084934669894882104836647993821371866932565573473673337522609 : ℚ) / 44408920985006261616945266723632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((586044804273177186944139573606904641272636689301933368241996967749252292621414051746341083046017489237326037305358111978109031182272936648780987501904363647261752636933601028521982763322549912307271766785572143887268003250345028395319157 : ℚ) / 693889390390722837764769792556762695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((2176357177361795319336117938149519812676243207969878832671478164944045016530275328552140488417847190792430279959589388655949530765759556242011566577458741581494642425143425880429700562143153519 : ℚ) / 2220446049250313080847263336181640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((2085023934828669128095616994455737800848648530745987940350158793960960369144300543548095635556471705967817611176417849496272878994789754098286128517130339227582372580175071890199524945378874838499835544323073967912640098518240741826515179882391 : ℚ) / 2220446049250313080847263336181640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((1895338746434933398663708341732561986829458245969091486917107028420988401278072250062525648526442854559211769828985283808594544402166024012140098523537919607348690350956643290861021941230375248555961311025990598458829593969218601537062822301561 : ℚ) / 2220446049250313080847263336181640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((10897790147304508544109135470233258918254739755356328147097644250845536741650886698496275444793557423704499208172615995197637974160827062294207634219676184713390656925390065807552521506657802867603 : ℚ) / 11102230246251565404236316680908203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((104707954287341620487174594942199493883582227518096075370006857872334424778792287077210010086983324097998768515405533342151186885246107685435077341596219301551033890503440332815117355528381899606173099658994005482100891793222315141451356579527712609 : ℚ) / 111022302462515654042363166809082031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((9571555294890374231607439225889670158738288291262383350947404330051481987520262019884761793145931701385502630402777445143380657140601247476782122217485167088822316237615352596834295058526540887710738059201824385357998603171058980044069235533978083 : ℚ) / 11102230246251565404236316680908203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((54563162492440324360771844130641299338322228245587293618091776391170753871035161620927229237507725773717762828296420369731447286183755087858240799876638468515992476163033735149621042226372231897075111 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((5256751720242784052593267462670400303769236191252175266211291786381962073070834969979171978898288407845308589825446120783295133736972561122226369081814278348011640791603068727383167481969613821787009341555071252689058029803210959050169594722167539692391 : ℚ) / 5551115123125782702118158340454101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((4830748646538714944537391726564032343642437068003158357018226770699410837882982934001071219742741410120554170000488894784167947519814939886938008961968843065355874570172237619457866328383796013991426690654857976583232351298849628452428949552152888326779 : ℚ) / 5551115123125782702118158340454101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((273159932374392375269587956009632093703675172374788280507091567125858785699990044436239561974323324412729266234810501254444721066034072342398662589027972578508657111967987429888792772803688039306737289707 : ℚ) / 277555756156289135105907917022705078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((263835608221674445795466441802439057068406805715774840342649616468626405337019187140718467220121693724067294423986289816030194510850524197376970606330867609487023661310479660611840636738559405538320896371736651299754922283114689946298581592902817118617902609 : ℚ) / 277555756156289135105907917022705078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((60916968424632449209064255221117390837678993953881562853446464169599745155330898682995010720918490260412301338392263956607508108565688064536144384264447293779088803845496866835906936872068118889089260842473716355741712945785698109235187111025721921954593903 : ℚ) / 69388939039072283776476979255676269531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((1367395345904790400168523925895905961863316774301893256711383596762607189290853836050842848874937255301825607530816294316860171583199993451702598425322708846544643028195557712394332087490701438265340812371359 : ℚ) / 1387778780781445675529539585113525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((13238411356171464655073403782672125229633317387450468231394855018668139401046176614370824355871847041277363242225246372205020772844999134142102011922011602424428371952262179384746069469389678574391895201656484571837671747817877932893489873099033867520686999502391 : ℚ) / 13877787807814456755295395851135253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((12284252525276736231257857358234243605617970631107455763922540496630876382069373394235103004290273163227233131119609378503492032258153060375330074592324124006105473667187762825715720033554308714657653397356954042318159729727499081291335945782292831474347215111997 : ℚ) / 13877787807814456755295395851135253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((6844375916384177865798668313775525661957074882437879031370685738188209536741689237767758290233084052834565342120395156747280615631298369635544948898221400921427509721742801112372517889694382569236385346965991683 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((664098713865058305926075978350517220361054121000721301712673374659145590444112501810975376062112857148084367169509984381639906938127947709780095381728988766912549907319905651331028927748476125096710586206031812838123390980056689102274150799583425004563394290608092609 : ℚ) / 693889390390722837764769792556762695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((309492187288570674205197207790163013141299640341922096772978034878126085730685831307826946346886554562745178620809879765337973422291235116837065094100986639937653248841522649248748389603164060200706806565574827147017533044422469350714584539812831747492553008668105197 : ℚ) / 346944695195361418882384896278381347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((34256189611391756664794539317958161078479331229864445068465869767978727621871212995529095191810810752993879491412272341837140214682330540000021928041052636072659362579721368758071365454512851973549118853881303434071 : ℚ) / 34694469519536141888238489627838134765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((33306650420997486059053406973514064782571807539618641159357069123954816013719137256799736868364581793629214565855189405078729208186031833647130541026423288123103730891332009240542466916389837876101995980702917986571014470711570952913234511830454541780348179683073559312391 : ℚ) / 34694469519536141888238489627838134765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((6234967107927188025011128854886005495143263338123382419047911345926395712280254013519699474602744507227102101146073398202693621331388888908342488268585453688887715835149240709879066647035137638310372163780993677916147803444639379765216841512558388011731264104288640531443 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((171440043663615195160082850552277235840830533912881431782476238114117359982616814660268414404426729461632619201678706849098819175481966713980101680326361073468921464282167986931176921612576094601347264125447604023787227 : ℚ) / 173472347597680709441192448139190673828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((1670081166541036050251981751530268164704423902955851323317306568218504382638325393609372364393783680707243417585470442020665273852789581512827336877781325775250914258640235648974285367408645087306432860523911004951498151167549981310142639797858623925573887737558627095498282609 : ℚ) / 1734723475976807094411924481391906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((196175372900435762183588128122452580544675018033337906476453689495700929771138144649140033420866971744187692411400323305426722012699273532500227247957940877079366672814619348966399184662317046518753533361174995676698164800506900448224256131222772209267874626717434193311660647 : ℚ) / 216840434497100886801490560173988342285156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((857937944646141757484457036685435757193540560754031199175342316135162198239394169579664637593326744513590455238184163659271224516709879652725731491673336297675388829876412955399867385517515350666447263749700539858301371599 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((83725698996797477135244670193229921707934306210093554101397114931351487887072671288188170429721252588521493834204536550011348605067531533861862217196403195844696653153303184994622025097866550774715548969629105989042064526658581608975108648263840218026899374302400660670327219122391 : ℚ) / 86736173798840354720596224069595336914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((78973640755045392187304418158460820467125473030539592096181366736597109527745828261973690105578055079350540097909762867912523545333437574657471319172659462423585189487340267153632376407367472291998592717236187979408367996852997562689169754820239191410555735196793264223238250962433 : ℚ) / 86736173798840354720596224069595336914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((4293110560213949817091191572482996679104494455216442670576062319918747113236070764340904924520256114309518940939459966888040668083983711949689216926889260412320778004136926874189185066644718681040315962007361403322943460104563 : ℚ) / 4336808689942017736029811203479766845703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((4196627495274425166526851878071539669107825479581090843716357467095080218769904159503969766427449350162125287709985840459962215260240462306578076230606782892282966649066684140568470186876206345179715264685565380384040377571769413822270914063224545970992444944233727329504054533288472609 : ℚ) / 4336808689942017736029811203479766845703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((1986223540509635893094935054174460649330779313128964484398576146775911061281142477536391560689971442355445472265349153289901200695201041311427362419824857766009118952080246954902204026734779753045998567040013190968298258094103801974967234073561704152318060649503402900396902238944799979 : ℚ) / 2168404344971008868014905601739883422851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((21481415222161037740030676788466810965997775163838644663461200977463230364075660134248776135000427602053239329136275866459844577905432472310708898889985500531931447605182929915615251154031560523983945115828134827208488824504858631 : ℚ) / 21684043449710088680149056017398834228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((210313886571483821103814856715328679962384615526206936671943257323725169077720507165988001046994594135607380045299892129264931105583563106794102626152447814691857427040040490939260704457532647450624627321584570929919473194334971415588368861931041344148689030045573496100352949943447978932391 : ℚ) / 216840434497100886801490560173988342285156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((199743480302653611364558751247828879403679711846365580976328559750480939867248551394999520480879724069266170176774532285924799298683165867941036722288662070469595803661300552834271477402644616146877535075159619628065492560189572808668277973382592204701254039500120124604770184421529760027651 : ℚ) / 216840434497100886801490560173988342285156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((107480630157405494191416355602436379274282855309719795304469588932496999198218836042511574937996982790720870769204911192774299307747490374104757164152862765966566122545233246018707919601244346149713553502095061193765762679229029471947 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((10538200157090473963229498883524300486036894050007356562920469297193245033835768865276075353625081125886878993508555002006449462161205434182886376107722174094920784054109980376855711150097629944435094700086549129984142900385367358866371010418034929445346857663020761751019782394505215603978662609 : ℚ) / 10842021724855044340074528008699417114257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((502001830844155022356697867291720523638903440781058283432509854504392069182199891028034470767756333433254044969561096943639198205023358999427800934982794801516766028079105303608831249731686292594695798104117608143192319258041988943331063660138020219071966218136190927054395931572580050706257737 : ℚ) / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((537744220901113087520068177600076374819605459446170690826825483879988585282140742729126172987492009200572677756803173200894425890025112864723758970176824645786967110242246561788748623190970033096221747589214798755491841543585009661418239 : ℚ) / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((527959532010632725516491539696488430846243051296671907606623439329540582576605003073418153464267316677423175300570842622794646431596603268885493096264236781357220079535766153312085976635825547379106574515592364403158704290323583420548523797801153790111163247978271258034139187970340196963435838742391 : ℚ) / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((504493146708732097310691670521707663595210825778223624094755485812126192836808938022656115845044375673820257238241879592370659360825111008653647052380534258117757931005237203006531359595161276961494232972876597175760922130679851370909812095951608118916567792170975940047265182251611177270115129852869 : ℚ) / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((2690302646624580441602908822889448570662289812326893493363989768751507069953286624034958064143000446663055506758296314132547452852046448353724070344709935882514166490193297307014427365736528043467180243571189021829215669237603689799996374243 : ℚ) / 2710505431213761085018632002174854278564453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((26446909829672928566204463750980264850122937967989238795215402391273819590360634387689103478849012521179429426812160016360809318651431139933061822448648690977874168877351416188396088727213554942026621706320804014353953233919739563658015635616254119401212234995774228340278229319477338523157649307568852609 : ℚ) / 27105054312137610850186320021748542785644531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((12671006364165704953595894335914230898391476724364470535290312963073449502464583511225833371192976355825015527570900561866841663691091891613050907342244554612304223377531517715402323309789212932216595484349475705346131207557185436262866901009264991923736280741520540443807808007589961345496026678899974761 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((13458846843928774781574451628527845125279934344134805128728820557700738283373390075650100543431093071176588384838220008632622538874939381016218514188419972687218190015026319612625899694920280537557314789439603494222073058254768309602583187364791 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((1324626530783147380435196134563062261009503199136015700149031020540193476315002050879610220232518166778172550670102787245988756647126592748017589706305686338797893191486503175385427109196366526290049634143725022823592617191726921151944864262988249118935149362574844501084180041147160756203571061191290798552391 : ℚ) / 1355252715606880542509316001087427139282226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((1272626226820379430173311821662261256908900935017267802449929813409444680094201119416135758238349397689958074013813521008712423451446695192196597733053017529578504214086715963708947132959204573738704295553794455405525236540564192450639231550748717594277880181389232514791546529893787511126262813234791760438087 : ℚ) / 1355252715606880542509316001087427139282226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((67328240172950705031469549285430978361517537975628091381915540926058323420002409780789516219889978571045840340494826180029470712763093909772205250291703413350630747099677044043746296885345340852653268678631441402707752771127360651627178239810535867 : ℚ) / 67762635780344027125465800054371356964111328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((66337638565359629240468774118630014030319129623423386535883530054194305456213809664364195582012974631746398458861549149599422592055406731514254398139678407900444212550215818827443046924156929613358356613032228009499302917443729356548618798971340201202962786166505427704287017671581086868404494182546894644059042609 : ℚ) / 67762635780344027125465800054371356964111328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((3993210303821048376745329658245623041684509917107578022430605987958319295913142589315976481021894243669254018653048666930515007180245620455405666719430467074614460936269508376940089563070142225727780800998622846120876049854042151797949440420709111054294063265285679455189174167779218447184047450610627481969624019 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((336798886470237301077468385456280249240329235702362459737942363274132445698551174153520986711629830633939561658874508996796655695082466459613715745602628727706874774301202453230851578657346345533753206862813993784355849599717571341595225498001454815279 : ℚ) / 338813178901720135627329000271856784820556640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((3321835926907544432054233582540672324136279721340545055729182589079907226647597272400452807610671628287756431793125475909151800254429480154180732118596197447278593486792646528678884899263749725275631685891673066654400603590458307934118815712203827584799122414706577741265211508203477327991333833720427712088012858362391 : ℚ) / 3388131789017201356273290002718567848205566406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((641360411570331440062838753605917072041961231081104562193526191087041656307050663231511870563542878253465584811732639741689325862506210372453515958483791424831867909940539005843775224329040417048959134729593328703399767153649755026438894505103900191906174747922427656162812349877985965981250019017471807418671410356661 : ℚ) / 677626357803440271254658000543713569641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((1684725620503814774328941330459455528617268726498729725804838738502152150704181794549876815381827524649577747412201098218146092458097396973228799912359389410376778328434675775631458770234115004240013620222868489178058074593890378310977060634232745978448723 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((166322607187289159324892650937416289178317316258078333574251984913346108901299773880165560435121220431324069152819167485365722610960146325103260689042297751602710235774985435830096029030623364627821148108648724155537008799448909141520589815388512792800478499539381291779193252657648276282282031183585526616248490613449232609 : ℚ) / 169406589450860067813664500135928392410278320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((80457693635865676030820813756924606958543301036758593397217033745808776750634748966524338904152649352852779585056602891851529012753493316500618332202080117531943183212260799454871654989565230505016997289814553998980044014645654315076073633276291682714755099302377102891209643706661521266618004265635964149158063138933629543 : ℚ) / 84703294725430033906832250067964196205139160156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((8427018621982811154726903084833915350647585387508984738557037230434479522815290981327778792925534231800092014750376492437543430728197629764861945193610488695917121108951591571603074317575591274660943156973441184318655291891869684228000630160937243102066728551 : ℚ) / 8470329472543003390683225006796419620513916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((8326882283634782649102747958895569306596597004419281668382764922240587845016749840287963449392471743266405619288551486892867012608890132709633350582385287168499784741688750982311783741343101698507754655214540469712956702070806040652604649125847483427050938373072618748771917176341514784426409121230165112204565829114602018172391 : ℚ) / 8470329472543003390683225006796419620513916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((8072810870384272197205599743833719639235744905312849634767572779606942180619026306663965420431971359835096126929172803655167886867200583270264055367423337473404976491847749593925849446933039061494253283780082500302046582236123591664960944514357651337757722403211780346190830970853022620640779585847816720103786067935608403888523 : ℚ) / 8470329472543003390683225006796419620513916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((42150814948667405555286660281841965803199404955551037232688981637524681547294504280416910262795702232857026672397495795432888888286652409219664839862771836082967690582208530117523455610598016740602793418885846771685604588502599725765238922056265996264283420290987 : ℚ) / 42351647362715016953416125033982098102569580078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((416844896009817623011763797729596133896128843124795688473079781925307044531507996260738289002632432668477246628132161197372277397459163428254865730770001591263603336257119014902634931238893765295729828458023285959390933751235441314150787757448858059487300885333445771075987501018191823784403984046236199884093257744327976215739422609 : ℚ) / 423516473627150169534161250339820981025695800781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((101227788664219853157554406353802573037064716653318437084622053721414492749651082681212971291107507602323696279436973244407531917798554650064872153435297896023854490162460581909902632438249169080604296136886962330031572655274856627658813348119985804291610373306465767540212390164074770085782728149709490078521325745609141814864943467 : ℚ) / 105879118406787542383540312584955245256423950195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((210826976909636310713954297114236697040668398347249534647978807853201948334804616348293212888583671253758032679907188003422305774985207221551585862443673003916721181229700954154956263666343003626175153083373671480306148476886554928373412881574905424677482219889306719 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((20865565731128640169726245014729013139009904053599788557606893078549501021053526482800611949071869906313987524905917886450153883911480382093116141660456521127780100734250347142781017285904987361740092249661071041938629713342858635980990896789475026292045866387871986122648361558317613878474394878096582758584312505237014601732058277982391 : ℚ) / 21175823681357508476708062516991049051284790039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((20305238373350014621628993678504758201994041083197808639537503171048183566668267767587562163816351734162910745900826374248436874340761919097779311649320658050618993095904107094982911519480805158076395759573680124639277011348781535564143856983206703984768692481223174595319082872564779627106352260250336611793874930886047299163343216753741 : ℚ) / 21175823681357508476708062516991049051284790039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((1054472931893311328551056342655393072233743150977992967162677732015297434428489006007035628164362483603675997536729630771869231878606405886334703644151311719161836117362123324416532194620832507814574184847603714654179610487322955202867515531862836454229485053626715256003 : ℚ) / 1058791184067875423835403125849552452564239501953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((1044364163487566797985559843404620634432344938521396377581206783449035290808623426835326172861865767908227516776462983692881969740202807845306081348386963863487729015673504818250896624307976662404392605199493708923497503324006261880188153146705196910996980799754493793704953621762734306917469295119468127553535478423160420063340890450929612609 : ℚ) / 1058791184067875423835403125849552452564239501953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((20361282315675032748949680757153908180794367697497414670942803549596465338455881344283171403337608661741461445336915627298852609638025179766572901387034467075596647081891498024563678058238551862086838682512220964187558268602229127147836897904629661581942555415366188724282557326713778108928183882887318151395854497072631048766266097177830573 : ℚ) / 21175823681357508476708062516991049051284790039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((5273932185005923409343499595576445216228685930293937763733336643354934203444903520854624207798148836470245600577815297889157628221097904094934020797929632441753434076208165855319459786456800338736180495138338424851430853829716543275696669521247972638262122193667078642085911 : ℚ) / 5293955920339377119177015629247762262821197509765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((52268762125175468296636040162984144683062039386565258423557275386231641520674119103204027629061074470604313691105242686686113784964296786068488207520465696800612660399220022061879174702533425203115948339794883584834016384124059877316127148623433200905554793761339669218200211025701281076979200811080946271781542993563795742430276729401381637792391 : ℚ) / 52939559203393771191770156292477622628211975097656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((51034732327754361490225118996424943504174444638529811423171375970443192677592735988173387689421643313794246990334884697089156159725828995250176412299041405478040808909284973576439781465298021050786650112321039596700207740564940740289096582327194196828187553536375379782518012919675099325077231272194781580628333753282791488908428198490358890378959 : ℚ) / 52939559203393771191770156292477622628211975097656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((26376929540955660743387064298104914169056511354817911285431482015236829901374017626202892451560016154712528849879329536312023922061230981288209054439999705632410673811377265071116335029800183170719668955956475276036084869208395611169405456570026849123621460612034243663352369307 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((2615791375442917127581593586068901551856705293730049891365958000639217896303094310603017795912104713414600494270941358705625207196945497260083551230317896808742858343455672147187027166360006185655210945904298271060765960269222694748565996003663481719188548895371814378040507705055531947182987057297831501283897653167377244613620022546332772319019802609 : ℚ) / 2646977960169688559588507814623881131410598754882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((319738499925577628706264620821901217538042386657676980200937335187564708317985849545867201851152370113114936635912099395054024133763628398048899737856801644350777784345676732037208934855539413588141415756456084202458445506835773977340876122300900137600036405647976925074218414838998987649390414159213598581484235884348109589660521803450496159845315429 : ℚ) / 330872245021211069948563476827985141426324844360351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((131918352276827368338392100517397175508935516632515264005545782104653180252671319732702812297883794909401996276890451059878854926597928060233425385438278635017488294463356378134766445533183449362627104948770175854979325538519330448992533102115214499386232712858002787866964936476559 : ℚ) / 132348898008484427979425390731194056570529937744140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((130899098566987753761812000634996768507945042841102952495421028226584104749420087097689264313273964077915343319522742901504071862078172044948733069938518891283388460570231561213334314607436989951975743799621351185009053489245870686136540922999523441128488604194914600453487326110224582091287234591345119726274110494878808630368287394562428421583572097602391 : ℚ) / 132348898008484427979425390731194056570529937744140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((128184874733798570268261162902848439764790338031614430963216989130038523176220136597041517726156479693546889341284246220311119917153760546068097354133365539493648230717790674527621241735481735510883914481465534317786311282203206642088475223033666714412574238767780952915898614627703638829741472247550077118466445207968298267713784297821961207942452824764177 : ℚ) / 132348898008484427979425390731194056570529937744140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((659748049484728354341655586934594145370036358026096326068715791619276796831636909600542940625287156994897056735941021564658250294634592415302393512277298030576093221426583525410912007937371654694501885647447305439539132522114135291978375994508249633653961089522558927339116410441804083 : ℚ) / 661744490042422139897126953655970282852649688720703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((6550052216152295600588077111261722860809205501486000594633185305473428684062763769292165969134731967884031917415933053575235883209571902079875399766740243042583656297811095270090797817131507541111454647087960831424974004980710106580869863037733743038771408497169834047929167834953267528525834269375939042562608698159051509557942564467914716542839160820009992609 : ℚ) / 6617444900424221398971269536559702828526496887207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((3211408785039853810032152942320447890142016790166486822171700928011875306129289891152907633494999262041785552704691516459100974267127504604653463460704924443491451212690795300348156582103367501502047981246686978021148248943790347494354068858606292605467499839945071508565205938754634589369031984929411432002484197249127187854662192438948568466270939360836379107 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((3299464955346084615864914040792830264756370429172623898355635125738586506908300349817717615679456546985337652084558516995320306616220605029757198716429830967781344267755067807330398980805592362818405243747213155323142957505043245348903729486534753551253417572116105746071482795218645532871 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((327739799629368414731489077832265320223508956626253618024595182299878849963690468703501328905764414544128354059163981966280598605782201988381585813652531871182332371748744918164615520490048664293746386965539989198323757267557901991984401550320338267180709205051168534278993835091256707706964016287647880976274828808459158878597857458491694329711219397739629657412391 : ℚ) / 330872245021211069948563476827985141426324844360351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((64355435793798878698762934827275109048781612758866993999113859966377074130004342646841900642185147631324931958262781659843184826804802048342211855753997949104260898277019896577291495191922707522655939781265245353180719021470354987361561534837711114168751972897944577140309034483728178936838367552165248241843035776704073050368631752004906952451638128771484483981879 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((16500685247366790547678891828041940001052848865101533188550080078049825632533788722104756583905640008371010692716097843307300261779414945522984130448085126197602093369580249422591060073995531786388945115255827401233413893950885528682866593629061652217162097281902382344533465721428859335922827 : ℚ) / 16543612251060553497428173841399257071316242218017578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((16398025667690526210896320525174601560142340390854015769056411734694115481620948406132696879031789109218599164115807738850020342000365231850564555106636840138321224664626081982935466336832576585199778129460315272912474546331110158736292840479080931935846567645912797357630792131160305221094460868927866996051391021551853690378024987774667753142675161678885594953900182609 : ℚ) / 16543612251060553497428173841399257071316242218017578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((4029669503593062538725085849925480506717096813692293414642905857454175980637185776953100895211543782111284741149803408342446660933615807252663066784861770111624006249738391241537235544669345737298249713075109841054928246582694897060832132420990705951642269219158483493403269845739449103784118888213486770233956063362659292379889546548065250777435532247759009847555558249 : ℚ) / 4135903062765138374357043460349814267829060554504394531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((82519008739174788689153448511058406101769856112616190254681721321917041458059178304399756279570452718816376582124545699415951313871147102390077412887770730178280906954743616572554745563117280893485538499441271659519340226250256196502452394657958881330980645096181346931601680550265620740674148799 : ℚ) / 82718061255302767487140869206996285356581211090087890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((820414683942487308493065665344369637550110472422412623067708422119827680545762534726811114535663583807591168260320437754891873978833289210603998051614424885498524857624779890512490941121180768221135930568979119799356744994002004561917457363457100178919187346005223782401039877182948300182979702467885086955316544578811864213320746424872274223667239600388172887330554317222391 : ℚ) / 827180612553027674871408692069962853565812110900878906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((807330918332857206301053051589584971689322402372018978323115597803527131334357254087519965826535011940105022687743168789995980911750937366735014709096270010543619073475706505908396516248803270833319845780098507630358149878100632595201741002484526849082970575168860294464126550601650567295419662208383027542284162079806042296791101784326666312401804546023737596885065075814613 : ℚ) / 827180612553027674871408692069962853565812110900878906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((412667299759228399749436676267917480678345802419903178507834141769729321241020409797501669868368189257151538211311518408191766242420509113782788963560592875836688565549146150046936355176174831503092442021909176685191180629122437983181871754028955332731757251310992905721836992711581683374506027980963 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((41044615989774117577224025834869320209266931652728081300060444170279197040196307807174805154531643948225801973418207908960171162380215247778497079743114919638763948225064198557965042685123508606666107520030549407543816372699871515668811308155050574606546853444149094144313793477674274253175017812790351027902289189501955077735220268372827467790802114777867391756987613720690372609 : ℚ) / 41359030627651383743570434603498142678290605545043945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((20215988914228310228057453830433463349217960628461483766761744302291087806662050256426546663010551292457274674197808680796621703408012854953969760575373396528415218750157420645912451015613461703051230264517058661487534734039827195482816173822725090838329724414697834263189415538157799163470835435878460588119391524433915115122059921031850950392164334004031710365885572743505473889 : ℚ) / 20679515313825691871785217301749071339145302772521972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((2063671550161916612627298545465031615827684383949600560225201915386234862594611640231015243179623293585411682685851510858785220066103900760610792424030469165254724878451390697767643878951922693679839653655592852289231504577240744928014339323432265877877158374329074103832158135203604265807584451747725431 : ℚ) / 2067951531382569187178521730174907133914530277252197265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((2053341591533435639572197220344870072184043393231304509993187781517435221164427961954789642249940377473714347261322828051235444433781802542587362852037080766030666857810791860548341827011477797026064702549011472050328302387745649568970094119859001368619153659513892639551467072756926666974213091151032602204575111238398476543007176856508863223118304362889254761672685629817346077032391 : ℚ) / 2067951531382569187178521730174907133914530277252197265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((2024662694867579825908412083031532304869461945835569750622625745013159584821992934321557547155436346603647041797518843407044176046377797374287634408057772653877771362150213600279211944971482992893141825053679023003681776673988425388922215363781020648875339351948165307834234300784974654654176511639954241500108346652702769874508985335157031999815807107698960695685664831987178192479831 : ℚ) / 2067951531382569187178521730174907133914530277252197265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((10319911383992679947698586743374842892203946979016845405186136281645971057851214175751217682623913212355553972614293455852187065446523787826952244470229285519286159261379098665548564666700065530593416474000984056065166486724665334231202491442755416875716383381763916619469717272939112980549769102754202823547 : ℚ) / 10339757656912845935892608650874535669572651386260986328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((102718739699772815324858422744169431488964018256147424046869691759349628065013746672798886342746363137160315737524209345282328649626332940317703313891392973686052857051763227812350820912328054779468763657934587085091170033536947450339084976256019964241756964554485354480441089641142168020476344731895690947034675430616693045958779951366042336177100578025653575020509180656150756120380562609 : ℚ) / 103397576569128459358926086508745356695726513862609863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((633603486910030851372207460145503858861333244438778481642146674970099135615301026807947944158371449928522241778127661859736308347026858116006554139695182203517282490508182699334790723679101022875786491018988179549164800679962007172315813811551231337645036143434652923610184975824252904664508303225828843480552847639551267017341304515975825674615788400988466846301777078808172370091493141 : ℚ) / 646234853557052870993288040679658479348290711641311645507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((51606761117033419992207363669296602939204574594913850180957488937992367795256080132958396394327085565692703771012478754786591422475530804153577557608453196952929920495014880512148694359488203865361672189942563067974176998942273154830085952820056868052696869741239281364481078994618666890809279329471238492787439 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((5138339336063550840987710488101056140611011245929010373398447934924088925900692807458595482845265494558978302043292712055527382047516010610582213167754958991718193339133862212592058309215520414206291653708187696885836536340229611682710921443596840768869397980909299936405049153581441458910708989419311880131198829702320570375099139031520539085633348910576385222347892620346127874661004936842391 : ℚ) / 5169878828456422967946304325437267834786325693130493164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((5075540146432880374383291131997595830060490601939088130924788644805226050521602691963603156869283662102310316247193235899960787866039145172477463029913816897575821504576302028268166099356291310494125896551482724657799639865335931918672052879215373275203263606683532763282240085633841015390115661901661890871144026377660876244974476443084966448347417951679096667354953095547641688437559169905049 : ℚ) / 5169878828456422967946304325437267834786325693130493164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((258067211446980783877510630035865630069365974662679213474646751205470609466602443576528084080494695768117067386184863985945424426019036338860139134630397474270736041335384000934833495744946801323682073944763664946196258744095320618947108563226603697160355384990126547687098763298046758372682628250758132891055354643 : ℚ) / 258493941422821148397315216271863391739316284656524658203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((257028673018152137631708886825074656401251102810475954268053598841539060711012841317321832169357077481062385769529469375055451035136185916622793146895792843464487235307241607448555593905569253871936290387405013962459644215945023100840834739045724677471507744300531352448667794467220079521616714407548181664266814381674723346309086157279392738314415067627026758620432820022955408231870561152970752609 : ℚ) / 258493941422821148397315216271863391739316284656524658203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((127045533034493500861326628899876598258043841918774003840425101175072867882925482132885307232835034124615656204662977637626013965401761531339917503467517198245798538386718729947606044954660285136185417889557408899501197256268869944216780512825620191347993759169839849898449586215249000293776135162999431069923367695154833471296738629879507310588218919154700086715633672670449656919590705387853048671 : ℚ) / 129246970711410574198657608135931695869658142328262329101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((1290490960216133971708242214982995337833021835841161963809671360339767216096635530864360725881253904276758841469739214302828933063450271503294465167281153088193403023672175612334822919769318317737913776881869114355512051796370001710057742407681761343732567920199216801625076965413042818574129347198765462215823679479591 : ℚ) / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((12856627381590178941460698859050898479376797614656666212694852297048974710877345666764382074275453103106679751241367097201833308684614430792748624629450399931886412044308820482252655482377189808402995182940601311692649020052530792930091212347014809851039314266115233193820782998483968197015016355507302049298510208930623875860562567991415393831410363628148577111160856468212970415025943381322530896652391 : ℚ) / 12924697071141057419865760813593169586965814232826232910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((12719244275802124930813850090743292446690086450161013044925114303360744806343302760423338363019642145629952818340675537775718315484943800066560484004695472817891277521499427536674875358951268180299968627451800160963569431393626817766926827123247835092971752567014204104756453500330547146126869801151771253933961584551299994204655623084450142022628916039287459224094383805929928220016908979822005408090267 : ℚ) / 12924697071141057419865760813593169586965814232826232910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((6453173086204633611152246268409581437538581309447060280824117972895500581040098956618040685911374354131330747895180736722217762615218908960776434980682706869952809820767878314396573878970329039350706183401227083266509384179767697929537751544420327350887917445963768309135481888620279549728237782960675448294774401746863467 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((643072828464585322111919181129730977518505937872351832715177323245498571491762420557257108861642621939578191788011936114269772000002112849122651562716369012475508740795698115253751738269154773258399448219006392833776670963680296936581162162211484313286983824350082210738011513189086356254370929634883345681797003102443489699849454997045701307019634952903057821425127380213115455705752426216132567818460942609 : ℚ) / 646234853557052870993288040679658479348290711641311645507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((159162316675538076161984348806867740025992641260423353434568043718618019517434971648944619437743104469959688077117533844368979213809685706897422772874793257847913385955885287738644561586204110769285416794147375650743649648141129917034331611666612598853420876101978612928058346709198153995458777743980143051079046724521499610598492946425560081356790455339066852939484655020143476254521407508251099593203133031 : ℚ) / 161558713389263217748322010169914619837072677910327911376953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((32269196119142987976618601534282389405900696815163979795374794415316436194282938861837854660571042880106980677989953076180923765246770080851120329005425711755971179138900651743856913076785415755469224572431489985106804014441582815299266553911477057926067273196933993649461229517532236272089838599588652053742868900900205896479 : ℚ) / 32311742677852643549664402033982923967414535582065582275390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((32164866068488812178651489590488395934268293211172434966790405766969230059135970650860694788689334659160157559291128999640806573311966052468954492804513310898048818018431635433333301067246757194434004932726022335468697759722951507583777545684719188321780032626655829932398434574494698747909529177898749464027400020920461012850225625412059513114576553245684698906309306982209982391303153427299749419262923956462391 : ℚ) / 32311742677852643549664402033982923967414535582065582275390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((6372917513496308550546848534534150070457723930322158688043422278145421479418105804426055704346616516898938910452139062871700382468179750971434177978303169734196607406246962905237815790070887628618710704364520399638594218711235197105270788949352646878793710024085300709699917150345490358838941435581900288075338181348458347179646692165008132928060409839735773885328508398690307109178660629872408778807662861407097 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((161361424996526544856108633252803241075333007548205180677119718578822314632889987502342132061067925835056069403839412414250943499449272864906644965598159025412438357667082322136264505937053972858110794342364819060940250214965619514542699010487519117603173945814182928552551721272796979593680581586292579573205683093474254741973123 : ℚ) / 161558713389263217748322010169914619837072677910327911376953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((1608765058007762142098208006355333558065048310982183464027270815978845880838668520566131515953747155770962940381169269188817454742464257569386935987066428461592910628885047322235593637022040691185437380054468160489275057365995450549074037814377975521980042121424752593368952766234865662553902186312808676052537060914801754805538781917917266030642830319502565766085012504892466997626250601075061424117412315116851132609 : ℚ) / 1615587133892632177483220101699146198370726779103279113769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((797365535578807246017862142734771781584955665025953720642624307355971112643707852345897368918851172925068354055596982289010950613280622649107537146371846371073353911139356013833041101162150197365215636798529052508182231867654421831063436332814439722645706365017489019335428715274515795862631591858710650692555870808559805674474292928175857246617474627336509812279970295690678884984279909354034330016781994104279103453 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((806878740669196136540416622084927635867176538082476454629638119424999072952710872048360466367171972097154993825603355364881625006946278274572112705478663400837476664502260727745858514030119272143059753365545665985579940246795577688934495311630626148325917586740366239698182331541959594375896856815638691480954752504440119238529371351 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((80462503709367581140531254826956344865546512653373014783425916574358989746650073031947482110776675233548715385098244959064286330363607262338824047211566147204095427656129031383314066014266878245287617490132677355094510219662859911180063005123675351584914644452159730205922617108655296898743010367020569518144131415609811644140515528754359054112896721547295956908059477707656122426183650797776689023859436767943184116272391 : ℚ) / 80779356694631608874161005084957309918536338955163955688476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((79806737526118312999748695361627013922966146544227682453995283764132896445782600566777295119243457386920887393141844727259683624461093229278884194970492638440285851349773884191446236801138418959093049218246412938238249065512505904147966406190338201744090472088089164481588046301216435774477182837850597329967381102663688966873836863321475047900324275938863541481763914208536945745944102538020763814861524893296283266740703 : ℚ) / 80779356694631608874161005084957309918536338955163955688476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((4034725785284575225351116325066204482520384517495688479266801881648720701281720313688247482544576434614507706369322758826956095157209892359190886615304562189683379293296982994557545929557663064927368076356035253175134182924391093743589254760031213449787279849715078253480471471360066639121033725054116612397187187363088832909060694954587 : ℚ) / 4038967834731580443708050254247865495926816947758197784423828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((4024252262626496771626628288662880873301902509584178767199664843454022215993157343475989816733062312080245856026220162930911121246005796963098256864483144624795912229015730873163453499442457902158441682096589735861286393492031501545427796272906743282747365470831592856009372831276513698293922741599059517356593241298496417805867596891052503076026239572906770764905768437366817853055838102249153229384650795120675342048141322609 : ℚ) / 4038967834731580443708050254247865495926816947758197784423828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((499202045373543154994936043495932835024018967265402491209905847861323189360846032267147607638353811474628767180608274240279874919409141767909621118697780067417763032324597037584855356743972046605613937105002981907576326913441401949570729425097816146694810661299646890408349937958602941650789068170738612176430122931028500981587812896487950663760661074678868447954387477935742786234385388468509696589159350243740414310692890211 : ℚ) / 504870979341447555463506281780983186990852118469774723052978515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((20175168790372139021019148641623965360468457559663733274106009934580117891843337094572403576559200927307472234434549632680595413243982270869568141235167254873561829783018110145763340475358883632068205770062935468973097206220401501689023374322264736766663616663128817861388946212696629005604233383075938731685756987802642918199314442504419919 : ℚ) / 20194839173657902218540251271239327479634084738790988922119140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((201264991218137888928407579103197065034796754000774398430030994500712797924585970587830991423376497730806136314876864228621676976830221529230772084608015140481797834239257085517264531215129036126929485002520973825150872469552805397854395267539446639442734885350375953273221605862883533171772519108211716400127672389193847558224448527968361172918104754541231777649994673913069436569659658763109646169079901129635269716824311376082391 : ℚ) / 201948391736579022185402512712393274796340847387909889221191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((199834028283507657807841784241790920393349450514237251630401949865407022686571464722638426642428309923087868680868660895124319249339210753925774708341531448298459706589904006850937680535687716970342539298469278731914510332077246709858550436360619653437977854302211279244785584394807235175918765859657431120917755613920592710810903792284643903231735125699901970911289604912315373185221111114903757994677291439343096614117709687205921 : ℚ) / 201948391736579022185402512712393274796340847387909889221191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((100882984300993427145795903462670203251599410464341860170758816113523006664477554107532235384505014699924748751073006646739920931212345790022187470907470560848706204703854976745904609784239143401900270155781831769628251745244001763332001386732341584387019190466928328423260543588274268698986830197323127898826855152440855211690221069892995164403 : ℚ) / 100974195868289511092701256356196637398170423693954944610595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((10065683531031497536330580275632379237177846695839630455991006278365926889579529378581372685924244659763192014477215840554103418896714691960042615778446787722767247850381065279581011297322289267115430866189288703961308701540488969197517991593864018813984474575204639702589760242320854525766859298838046722260949836801344118611689674579694324569331795849600888762472110331414211576198114984681170967962426470932457501987377187612331512609 : ℚ) / 10097419586828951109270125635619663739817042369395494461059570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((999885765981146867622603875219143814901935049044803485266504234549151531629388377996374934859093738338079249048110806962703624846214308258358902729578525735953185930586961508895718460703227188561921828038942646375700056365337760449159474181875629642890868262738243549705548776310221132507320291297889153672721657448917118303246032683738646522728829079883058890906474429568853973024663273253386554649405202302830598839252119940636727647 : ℚ) / 1009741958682895110927012563561966373981704236939549446105957031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((504448031303895614201706160413701111853202330124058850505454870552781181903182418396626975477949753163551059958725531820933013358031647428332883302597940990655450671211775527170759675569516907954611552712360353915766203342696436176570490430277867926802607986195146658898659140618827783957201931624987344066860127341868245616607555101093818577336711 : ℚ) / 504870979341447555463506281780983186990852118469774723052978515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((503397273661813170552952313144862801939890788639304895160535775458561199737094467315960060409696043296116244309871846233128734204632558553100053621615153028217241358991695430386492822721303690346217598652558296457546018958416988406761445997237131008962435668562144439021309218992692094581346215370094560717223791967959355684773703223465151793013301781436190393422482492803308106717338976195668012387341228765489655131929986065367305735892391 : ℚ) / 504870979341447555463506281780983186990852118469774723052978515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((500277079172544798140684749768300053832848164045565112245485262902880698092695702636874201739550738858228004543559938443758075342450446747671095760791053181323133143404582516851168987629753971205823473161056434251111773180242324159474059263063128541093198166900180618084651284823683000900329121234626211919215028769281736002454742309928604865933974108700431715020127452329091071413934999369681951737465941765383961139113934767336390968431139 : ℚ) / 504870979341447555463506281780983186990852118469774723052978515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((2522393686657109425686564246124828952540978523789789114262025435925121340485056874105159285291253005419386265028610291053666382941192749125179579874146652373669324762409003119490812615615849902185533769927214961107407884900083374550757364125198473576583693231986895057313082435049504434209545356945066314438030410484243054924209233003772036743110328907 : ℚ) / 2524354896707237777317531408904915934954260592348873615264892578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((25175118522058712828335033647434600484871010450930499288706729167494254117667329209152418262741138967852853728553509593281045910277776771120042062315352574011015552719997392083342759667159098818570458096880984912225860090026630938634887331071493275774240485188589866052672087907686909311635965205495446845392720911602886142787786254413278552239066458573847131513618289693656061494173536589828864889417967953218268991281717442955463390809421702609 : ℚ) / 25243548967072377773175314089049159349542605923488736152648925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((6257364512817017759366996893215298248731432091967887066658107689608748273339605838500954616546733402601319828562330693260636608023073769630626251575383495600118523089095069380787150970195134676428071169908955631362491580537191925968596796052690153349118491272705127993184197642490841130628805637375696952074898315805168394038503559756256628619755605781593278725424137543466528241062268314147713469045830849639181658153442452727068038293407667813 : ℚ) / 6310887241768094443293828522262289837385651480872184038162231445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((12612680352533743720074862310713316337320914009835893245174167952244162655829208725225623605895540186129694110937665919615851017698310777693457711876418027056704658923290547465078898098610695996434320091152495774655050362281686607791861897448545321974618585516723232380760763251324552061429661820154272500049147013415435045683558213438490934377802595141759 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((1259000066643842060940833257049612283135284935256148891096757997858689259278569841356648685262504075215434072045260178843647640727478726307381003551634624563128891788215236892364076381169440941345150587735607460270232946514961535168914670790787301580129998091533020004320418536334828948869126161582912378980872949129535268716067297404861761129728699118003617070981309417924829111176314973005709091158919139926868886338686003215552897123033167195702391 : ℚ) / 1262177448353618888658765704452457967477130296174436807632446289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((1252201350577827551469525476062001260603502774090955227393015104265455019050490005881789070891914261512859285358401376940140057495020347870805533132201805896668022461097463066072961167126706114410017959241434183368764560840595579230756620444988554714374908621549970138390595950484123673616153961497758678259482394530593123853436205800207974164789101377591473302161048128031775180810605903959065986886352627345698704966386896653281611038098124510416357 : ℚ) / 1262177448353618888658765704452457967477130296174436807632446289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((63066702932222606195818456041940070278099061238722242589578396823853057235080040858871216660537619843083391592417956869258701169067067076164563409970950391461939503427298268595570850483257797335465942262674122907075468529900180800330863618468904657996306381041045628549587659196391947908849341860055361582727894701207372306834659435714282462709870633672336483 : ℚ) / 63108872417680944432938285222622898373856514808721840381622314453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((62961345443208374134685994375563232629098875897910374162374614538560463722456551574693168553435780527702777832844589514185187279046740425030335980529403126047295001505435047706777030015358881987407234775099963241605203046403825593622701405828655299323776538737807655688032971418518376356082782021328625819034880259289016623300659778461963705359000809441438440477087942497199385173822997470283903393060202377569173016354531458696664817639369490639411892609 : ℚ) / 63108872417680944432938285222622898373856514808721840381622314453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((31322033953968758067671142007909552876928290646267447440916586712066257693952563775649613238031516366984770388070524857663222149248270872050795292088836910492185965279894570104464962770881511295001748118585534863111235719393641553592279716014383634397193316758441869649522420138022780381173906023756893785140896945039482929564914189562636148425558998589687398047961266556171960873144603126127780754392368248351683662681106332290999626807833186994966653017 : ℚ) / 31554436208840472216469142611311449186928257404360920190811157226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((315348822184334407759166778202288217989255261839521066946403926218691001399066149462585831654912943212377686814042066002752597320963990032175080532035296965209013477392382071477662033690866406244555574272019907920108947573147138371134214598840310899128872688887328579584437975693669462453334398205076711659109247729498585386792315803407127779585670128338624271671 : ℚ) / 315544362088404722164691426113114491869282574043609201908111572265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((3148594164962978881272023159571712196537593721784918862123176842136771446279457648644832846255405324801357341053855885851982006916328674833839070401107334176703387229382990353003709396927906575026003334900356534567276950003156552069882589516846652008910148678248875886682283564503064549139524666819903696505972778188484527938386521209017031373461740463050643134511480324431475133436861063165305368784316046788235216562937561109891220128953987709282895755512391 : ℚ) / 3155443620884047221646914261131144918692825740436092019081115722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((125351604014030614704873283852001426647836631197929100638945856728795197560653921964238177125283709936597478293105075532016591542822345232336167397441547572153530992231545287753729185862424160893863636331469435311262104508362179373356204784496464139215872423674161098832542866305831383556066367488589495383844155177454710273124389871373856343060152872123652803613853394718034330396622272099765512528099937188215130421150528780738696206658634319434428308526463 : ℚ) / 126217744835361888865876570445245796747713029617443680763244628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((1576815091906849562925039338203071027364726223527689327723119506608492048487469735058010501383831317675795333756713060054763793777310021779195848427047672027674195494668475665441918850224547525756004197899356313025545189896683280626949353094822521639260582658370542623533038893291545297396111604476940711963289581721684940438555968380398851513938752385106200747738427 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((157454183426607650410395700735463910913637835531194012434670495069509315291096612865992750689709180500787287107652704728250995721249283180357000106386514131847578485939398210289411797457239096945885348336524859294077543941325130076533068717756586441814382703543776468289833821283513811464020723736464732789144322524655839527892938781212947855031484222215030490236148813119091949529525310981375576289925437789423796510115627312383995014582800492930021026102302082609 : ℚ) / 157772181044202361082345713056557245934641287021804600954055786132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((9797721259041496760178513145151464852377157524033541826298507660062648211165013347661978273477457725953458512837263476986007942967195470661963069313296422387569510469989187177882690097476067573954955434989469438666127377891283041090179956725791240731933483335172625654277375695530155407889532789015144122229153020904857738357998843007193638339548602585813911191324164739087654873766117670770212475349349461768767541472816678638880047309418502252491859253617198801 : ℚ) / 9860761315262647567646607066034827870915080438862787559628486633300781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((7884404598362515994012322349642943156632983370387046114115327655805687003836397161463994694916825820062662962629878459473939711745386570990131149156220055192325244508777721660654177708491226876930591465659315223499453045550920372267164150300692032841251321786864206145322701348192895544025769509959574081373773790443453068813584025379909474470133994809737452867263085999 : ℚ) / 7888609052210118054117285652827862296732064351090230047702789306640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((7873846027476533127236208310430496347987888545454396798342069672887756552232640096859318840028277455324592378968996261399953929728529235724660491585653290200049049455670684745100745090775598341098472489164750235518270549283020836955448930713049376366999624664217505662603104874471939805297263960816094560831546489106002761628976192002838906170682528583245768024080447784246018636879109468850919557470354775086281419158693113429967391661211439381358016153577491415322391 : ℚ) / 7888609052210118054117285652827862296732064351090230047702789306640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((7841630914286197863082755507676787288753018198275266834451491884965161795438205131045891511450629535047312096731995483560277172411260928934048176028503368549661586434407625390738039146224861759992757260936418985658274851294244504569014002620762769462654124966013353826986701003009435982325505014972339654377545265548966947372938025828537256729274013679442010516845317639915864946230780545289679915877843137267032735926852695742367771049952956190901133944393937976666793 : ℚ) / 7888609052210118054117285652827862296732064351090230047702789306640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | _, _ => 0

theorem risk_table_passes : checkRiskQ 100 3 2 10 cat kernel value = true := by
  decide +kernel

theorem lawful_rows_pass : checkLawfulQ 100 3 2 10 cat kernel = true := by
  decide +kernel

#print axioms risk_table_passes
#print axioms lawful_rows_pass

theorem full_information_risk_bound
    (σ : RHist (Fin 3) (Fin 2) → Fin 3 → Fin 2 → ℝ)
    (θ : ℕ → RHist (Fin 3) (Fin 2) → Fin 3 → Fin 2 → Fin 10)
    (hσ : IsPolicy σ)
    (hθ : SelectorUpTo 100 (fun _ _ _ _ => True) θ) :
    risk (gameOfQ 100 3 2 10 cat kernel) θ σ 100 2 [] ≤
      valOfQ 100 3 value 100 2 := by
  have hRisk := (TMCERTProof.claimQ 100 3 2 10 cat kernel value).1 risk_table_passes
  have hLawful := (TMCERTProof.claimQ 100 3 2 10 cat kernel value).2 lawful_rows_pass
  have hK : AdmKNonneg 100 (gameOfQ 100 3 2 10 cat kernel)
      (fun _ _ _ _ => True) := by
    intro i hi s a th _ s'
    exact ((hLawful th 100 i hi s a).2.1 s')
  exact TMCERTProof.claimS (Fin 3) (Fin 2) (Fin 10) 100
    (gameOfQ 100 3 2 10 cat kernel) (fun _ _ _ _ => True)
    (valOfQ 100 3 value) σ θ hK hRisk.1 hσ hθ 100 le_rfl 2 []

#print axioms full_information_risk_bound

end LasrTest_open_source_model__apps__acausal__minified_base
