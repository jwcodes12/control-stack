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

namespace LasrTest_open_source_model__apps__causal__minified_sft
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((8041 : ℚ) / 100000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((8041 : ℚ) / 100000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((8041 : ℚ) / 100000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((69 : ℚ) / 100000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((69 : ℚ) / 100000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((69 : ℚ) / 100000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((8041 : ℚ) / 100000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((8041 : ℚ) / 100000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((8041 : ℚ) / 100000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((69 : ℚ) / 100000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((69 : ℚ) / 100000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((69 : ℚ) / 100000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((8041 : ℚ) / 100000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((8041 : ℚ) / 100000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((8041 : ℚ) / 100000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((69 : ℚ) / 100000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((69 : ℚ) / 100000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((69 : ℚ) / 100000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((8041 : ℚ) / 100000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((8041 : ℚ) / 100000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((8041 : ℚ) / 100000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((69 : ℚ) / 100000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((69 : ℚ) / 100000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((69 : ℚ) / 100000)
  | _, _, _ => 0

def kernel : Fin 8 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((91959 : ℚ) / 100000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((1061 : ℚ) / 50000)
  | 0, 1, 0, 1 => ((48939 : ℚ) / 50000)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((6601 : ℚ) / 20000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((1061 : ℚ) / 50000)
  | 0, 2, 0, 2 => ((48939 : ℚ) / 50000)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((6601 : ℚ) / 20000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((99931 : ℚ) / 100000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((1061 : ℚ) / 50000)
  | 1, 1, 0, 1 => ((48939 : ℚ) / 50000)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((40977 : ℚ) / 100000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((1061 : ℚ) / 50000)
  | 1, 2, 0, 2 => ((48939 : ℚ) / 50000)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((40977 : ℚ) / 100000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((91959 : ℚ) / 100000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((1061 : ℚ) / 50000)
  | 2, 1, 0, 1 => ((48939 : ℚ) / 50000)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((1839 : ℚ) / 20000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((1061 : ℚ) / 50000)
  | 2, 2, 0, 2 => ((48939 : ℚ) / 50000)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((1839 : ℚ) / 20000)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((99931 : ℚ) / 100000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((1061 : ℚ) / 50000)
  | 3, 1, 0, 1 => ((48939 : ℚ) / 50000)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((17167 : ℚ) / 100000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((1061 : ℚ) / 50000)
  | 3, 2, 0, 2 => ((48939 : ℚ) / 50000)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((17167 : ℚ) / 100000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((91959 : ℚ) / 100000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((4517 : ℚ) / 50000)
  | 4, 1, 0, 1 => ((45483 : ℚ) / 50000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((6601 : ℚ) / 20000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((4517 : ℚ) / 50000)
  | 4, 2, 0, 2 => ((45483 : ℚ) / 50000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((6601 : ℚ) / 20000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((99931 : ℚ) / 100000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((4517 : ℚ) / 50000)
  | 5, 1, 0, 1 => ((45483 : ℚ) / 50000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((40977 : ℚ) / 100000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((4517 : ℚ) / 50000)
  | 5, 2, 0, 2 => ((45483 : ℚ) / 50000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((40977 : ℚ) / 100000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((91959 : ℚ) / 100000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((4517 : ℚ) / 50000)
  | 6, 1, 0, 1 => ((45483 : ℚ) / 50000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((1839 : ℚ) / 20000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((4517 : ℚ) / 50000)
  | 6, 2, 0, 2 => ((45483 : ℚ) / 50000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((1839 : ℚ) / 20000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((99931 : ℚ) / 100000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((4517 : ℚ) / 50000)
  | 7, 1, 0, 1 => ((45483 : ℚ) / 50000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((17167 : ℚ) / 100000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((4517 : ℚ) / 50000)
  | 7, 2, 0, 2 => ((45483 : ℚ) / 50000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((17167 : ℚ) / 100000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((8041 : ℚ) / 100000)
  | 1, 1 => ((8041 : ℚ) / 100000)
  | 1, 2 => ((8041 : ℚ) / 100000)
  | 2, 0 => ((1543542319 : ℚ) / 10000000000)
  | 2, 1 => ((213898641 : ℚ) / 2000000000)
  | 2, 2 => ((213898641 : ℚ) / 2000000000)
  | 3, 0 => ((222352608112921 : ℚ) / 1000000000000000)
  | 3, 1 => ((4628344929241 : ℚ) / 40000000000000)
  | 3, 2 => ((4628344929241 : ℚ) / 40000000000000)
  | 4, 0 => ((28488323489456102239 : ℚ) / 100000000000000000000)
  | 4, 1 => ((783392755157846779 : ℚ) / 6250000000000000000)
  | 4, 2 => ((94879704877919841 : ℚ) / 800000000000000000)
  | 5, 0 => ((3423857739766893705796201 : ℚ) / 10000000000000000000000000)
  | 5, 1 => ((27951144005095309384067 : ℚ) / 200000000000000000000000)
  | 5, 2 => ((1912860931899148870441 : ℚ) / 16000000000000000000000)
  | 6, 0 => ((395264533891223778291312847759 : ℚ) / 1000000000000000000000000000000)
  | 6, 1 => ((79030659549714556704857407967 : ℚ) / 500000000000000000000000000000)
  | 6, 2 => ((2427576979081255726832361353 : ℚ) / 20000000000000000000000000000)
  | 7, 0 => ((44389131272103047427890838167069881 : ℚ) / 100000000000000000000000000000000000)
  | 7, 1 => ((358980515047439686870236764258141 : ℚ) / 2000000000000000000000000000000000)
  | 7, 2 => ((1558659291337439754111874098624707 : ℚ) / 12500000000000000000000000000000000)
  | 8, 0 => ((4886080122651324138421413587005579186879 : ℚ) / 10000000000000000000000000000000000000000)
  | 8, 1 => ((1016881244251224429127731853438306007627 : ℚ) / 5000000000000000000000000000000000000000)
  | 8, 2 => ((324107876853335215984902965114840766349 : ℚ) / 2500000000000000000000000000000000000000)
  | 9, 0 => ((529729041998893116445094772047446056446205961 : ℚ) / 1000000000000000000000000000000000000000000000)
  | 9, 1 => ((916576345428583300426262247618985163815441 : ℚ) / 4000000000000000000000000000000000000000000)
  | 9, 2 => ((34076049706123272003652647906617433388154293 : ℚ) / 250000000000000000000000000000000000000000000)
  | 10, 0 => ((56754352973176212095174470142711091904736653967599 : ℚ) / 100000000000000000000000000000000000000000000000000)
  | 10, 1 => ((12814946562491063770304414537451889388421938076587 : ℚ) / 50000000000000000000000000000000000000000000000000)
  | 10, 2 => ((3617283856604823407087445091035230943706136791663 : ℚ) / 25000000000000000000000000000000000000000000000000)
  | 11, 0 => ((6023173545060311288060149099853569300467677962206436441 : ℚ) / 10000000000000000000000000000000000000000000000000000000)
  | 11, 1 => ((56883353655335962278536578177938982889635419401858309 : ℚ) / 200000000000000000000000000000000000000000000000000000)
  | 11, 2 => ((386934956922686501099581570616781002392674333682359937 : ℚ) / 2500000000000000000000000000000000000000000000000000000)
  | 12, 0 => ((634295016030201165738723251073434379301707197726541688677919 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000)
  | 12, 1 => ((156567953618319704703901652747398510468676890388022546816347 : ℚ) / 500000000000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((41621478002957913799328280243469860306464093173704403572967 : ℚ) / 250000000000000000000000000000000000000000000000000000000000)
  | 13, 0 => ((66370135379121269000167251445461952086205692195735047149132753321 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((684298842250099556949477226756742239783978936926705912058159253 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((4493356814511019692817220106087478384424826213521892619387955521 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((6907431279328612775986380275673235651895389248627599200787098862645839 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((1855992113610554679510409110007997002178126811060003457879695511960907 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((486017142749901909845330960001858676145194562791680749134412395568311 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((715610473015779902266931543770635077312648099914545394905180824310048708601 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((8001321827817002435418974192248138429589878269237405605577588300144284837 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((10518910356913290523667778811487039758612473480893213329000708520558879069 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((73847823488058104032564757833603831074593806620041679970085523422727769194239359 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((21428618541342313907047789942513062653873053133300247506710974216181615378814267 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((1137573053008221385779900699497654265114229663373658849287848283039917666434299 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((7595072000138335188730622565620374701788571862972412848369094648430622927333057214281 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((91313853317092135311344170841801270493446255033060743324813871593985526319983911861 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((614195421650972564812407102322849593409449658795358472409405505109538108890416258209 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((778845226060721165620479320511884037201775279947080113123173574775031653774620608368066479 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((241968339745689939565789568248789591820649779988481478268208666612423308443354832595600427 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((66182517611734999710758964962210744584556416011586963241148587627545059173009788591143319 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((79662828143317857669293657834952344177038052968653540122693918762737135849460336524919025342361 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((8169259481415266735247782065942903745791246984305013447399438273383845329906616636764782313 : ℚ) / 16000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((7113329887700367440707571486532245178132633995117990535531820969215579936970642207816270284913 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((8129814013231366873410575480844382618176242312944410896142810075502544275580523086495028651458175199 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((2682102175930932868837667400598486557834076426429063832159637499728267624757903868145387949610063387 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((762385369931903999121136921568467515560697754712733582498635322163398286281434524539547723074336583 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((828019566842743266311963110642968581184869066856055081598396671733138469038109322510996339759442333124841 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((11228099057339972940555312888392640180249467309364644982964426316453063409860988242056456185714624137429 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((81466203089905602952593084855900579802230955173378604395435943302188273370908424731677215545568757928257 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((84184851347291828026781815691616747757179374519015969248706959535907680474275495188788712407938557511827253519 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((29274545854678370796695002175912411747126379656580408191588507873780320618180506220454860301436313500859067147 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((8678587716326469522497791264923591034644412164211560662136483860212320661016607861375974904090031564420996087 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((8545654745045609213514828989185384507002458101394189516141843291962534388733900262065821204321621810230122406353721 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((121730052470095594603565241176523251864331099461715541786097981738799825522228413624706217445084566328002784249573 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((921689533828935827472205405033635745919233453838442530993312680893939669482358097315721537107041639372500736353041 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((866259864699649177665610159016498773879439044546108273714887767285582699853580734199310852128212020046951826365881829439 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((315433121308238913285144375765740735045398673084857953397267431321086391045286774328376958782659832231636994710666195707 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((97588776309468521502444241734148597480068579768581990830532795918052086271229830288991874949465324419748616394473758631 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((87701390897915038728951844612998210747179335097415570742547364191814899495835430736234426650858249151497643000780127153381001 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((1304263404870943052856480174967355866630126474402078386444239088095316868122567235597337022067462719733406890421805975290357 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((2060414406943285739660068007784482443714396846710626550677140660151774661620050620341942723894867432671431388809555826727213 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((8869032205581369046475682678766702462099864476223238469913913063715106342737530375073381640386273733722571752708739712897763470959 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((3362237804873137373592239872018925262041911178396512695576252766246392756663624919469254893916647055499042133287273893058387353067 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((216884445941013179442681351147760962222765229982249795166739917095999065335477705745991018465214156405568422334626543286000370603 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((895997332593057116144857303456707191712241437369012786454813531426177464171800555761373102268281346279393975807342995258365431025918681 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((13836429705228034332364894034322510016328383203724701681375622177726819954112349165145868221985860580230028932143821369564338462296581 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((113832780711962985922430906444445603856423622345643722181606250237908210968384918665691719284354849507633858846516806857716284235166129 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((90436018707924939343564932768575336642666010339017046829598197536419853427774607307260109111488884322506790621267454500964026671712455986079 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((35513336565467173270573944207868482538597387235346361085116763896929491204308621964290598519974971679674142884756639677176776965975844363227 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((11917391554707300754402155494451308243997313903574438769341336293561359462268239540817410105388376546333897620994588880777072432590963500039 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((9120505844362069497094887652465419382322923644765668609403020647251633301364725113368332373783406313413401958741133848454150928704005740023838761 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((29112045364143870677967297681028953425767778367614856663984212823360772598595168054484419982597108514384010039128300614839337615704670576275409 : ℚ) / 40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((1244491181431719542088128982695199641350304054694611910113376419802533136614554723482697161161486007990897434401839513550574672458382474733244033 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((919122596941691548883348773633067500979033735449006119652092375700612946760198756700238476760748261175183030723875927569995265252691663846852188622799 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((372223114723322385429874257632746271516001611976963156520671932224865132647740470492613475849495717957620318800051825809651797938729876882871286570187 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((129643773423847532847136026493002503403095890500164605459275485569147305533761381739090295594889628597834047686140549924295236656116469820713779512503 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((92562594892161013143763869874523254322530963278155153757086762777052665971121117467397230084441649349408656322336906423409194597372272715692680413563973241 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((1520452984972294593572801125212838529465875920724783645541117769912270013478007096913842185746141095018447666789810478057378162577636409044940031606112549 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((13474507302478961887959317807689580633003800056537916078212328938142769599353981556493222899496902113045142961837295361595637668949533647590979268571882577 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((9316063663688234607687381709791283944245624852095869784347941618214986110038326841184381881335169632522270626745779577790286125979756826662383198150929415269119 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((3875843396902635046343967079125998281559694086243693557028093883909935743342563927046847495006009701347481662038043304988725880422262395486334210305109320437947 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((1397419184605297614079315870758950182801757714290874267143393438354438270646838237686958143101018180770222677438730758097538205202742869278160873214030130095207 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((937105898449106366288323934650696680228883415773884089498852363269431907693014497988474573425700864237115484564915144194016921858972458023046096518761318098732914121 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((15786025200460994213945968500116111570260664788246434876980689621329132283517711701174935287548305588915124531598533345379326434781683306153754507226492904469155893 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((144624818170614705266674746795870796566549830425746432382061827586971011480338648387902444580269365652930650743317423749734735176340067087168953620735643614658806561 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((94216321315481372337507980706543416017167890031150606986224964473893688799541920220522133297654025774380902845105031744937602117229248267341295989768772051041380049653039 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((40132696552922983448169583477356252032102157217241264307751951427233670109611150552640918732341869958790381097314526313718769647695743683579660030584373712550507447150507 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((14938578105470195050898183509908794779544457445721178626549680583764997293436723083109113341035175524612730013247377146845330357698672129998823762792390268288232426844951 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((9468138691850351518784896397793025993522741999374578667846261508054789728317075441558994855918966556186293444733013614232716953098284441416438237923146509041714267986043813401 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((163051439920608858847788715178105817300070087707771045631029687122332633099936750992305291580468551083768173801986105161824989941432621373763519533116947299616934964871031877 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((308036417254350975847077233945916323269009312031550305164166761715916246335975703804876526818918800675155549960326124979800000763411816639240465352864437840939598615831330557 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((951090565963866475315940287844648877338357831520486879716474362019210408626309940530323607955452245540335358884203198951226418289965138948214243921174629824967002369728603036542559 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((413571014566540674159050083651120442825696615571802495264467726201136242767029392038673058611908527381444879941645723549253483352453946719022359466936758482765275998854417048211867 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((31703357502566241945982535795421744146210784009142014125140399129907919782760437393475613148954649848443103963008882469992304267271775066131597259944112707400760003869325070390107 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((95502337355471197203578552929906066111158047828792452971847265856924569966866835821228028663975433047643699267632441972355830199526904212538833656747297784074140570917872606637417183081 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((1676679079900748953382170087584084047240787226283305000796275434994133315012425507102616207473025955795448390594067629521763283922203929994866867642452599002504081848634200044948137301 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((16287738365689268049467665983683782930264722503415894155647208455506551563371601503513199334289034208749363498191743747098577734186255930658458379452534120773738424246710523572305370049 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((9586399440871775823643880148881231933515982920287925182838102720936926529583107355284308287910516847628266940952211731335869789318294584480858604240824756925673892761036647033770246738945679 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((4244403787390951630102626428263730436656737172694833577634683880367636560875844964381901653699959008448425547061394640066049257142943093725864398676611122112207550694907496596400019859046027 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((1670969393271082032948557261012211689069126644773772444977523367860321474111439252758144625871827741891295609484345248762314341004901835782947665973803178572661662942783286527354098696592759 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((961965706183127632966467574610969207374196273366757311888609088114638826733932969284589705847963218791047799623024438601915249955921051694275276387382003822128045504412169024578478119866705695161 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((3435185609585784939034519378447480220356867588018390314191970910815956196246072071630266290935698206106050880690143721749538884508925584815736153642979302088738728240916462960317315288142388193 : ℚ) / 4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((171173373735942176722372023381704118890240656177553547500001257768402617559497374770510433806819397210045134608429269488091030838366574348191346871795232380621582337742121604373231831737567819153 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((96502404374894233999963391693650117340923715102533635643964603133934071867625741922441584760072849636805964605533704349393524470696543992753860141307261689479072936540238651331212269424822389021310399 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((43405835865026751613636295256999433625332096693257754442899200485174357498822199230748342128972340236359540962504653113248420455080760984046573292477711410490078275688830638690049098480082970170596987 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((17510548790076089868929658982996005398388627891732219633035755989679971776222676636818491226190701886231594693300049327146522103908705910484159085290392297177476963368077291762384570950406990170544423 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((9678364603910898864402633536756371140554003917113890600183340939593443314874995601445805692951539179751039699160273918265879116800783489029652224734474477702806068171303806137766949084037242072010682981641 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((175374265034376829690554954985137122367636477156681172914262271347614032274557026059516893138613878550005381812735760705838654606040511715601990895272495888720697315226497034685683684533246007829911383669 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((1788928741840387428055850504723081068755445005562758367957306267948760885418051876870121134278231448630579289398365805205753644899759139218040386914647648146230053021026966917420026658909257044114330572897 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((970422730611042348671601777406579133714205646213876265702259849464073453792589720513354845718130591430725859695079629249811977701883248867677788934357538495072343222964926708622910870818980743700030396308724719 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((442544557743793597411282246564978115274242930219469933223997695409320034950474215944981046846240854379430185370539987497989952342916168737983206693609567741117748809352117523754740860193877631145665228198928747 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((182535830809259686273334415304336402043773159558940099150947388962156297297542859199138384258431574191388633380614929614053416133338614643592616657926484559503747747432691250251910975130256281709096937894970327 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((97280103884260843341491827848531610557224637020181847517714113496866730737312758108687598257393571057378119331699827626183459657487481682622781792614584882468357610440631695198254260769642650209911095214154016434521 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((1785596308555680266842573042783012687240953971771695241513251284025337043603438611808398789820957657638873398026368607522542188324204753622187238108295237620830356501186291864348937819675424344563584817938810478213 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((18603528152723832301046900330308271295007624548239890747737877774495408337839575763332301651056956517125744571419746810800403666718232753858516111539975011926446788964805707125215498229194638181834681888328431916081 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((9749881073092742892840246997123118375231820395738902515881472163058367691872543922916802848151655400865434475623784448676204766642891328052308390867044611206907697498510050058736263566115568470653214404798389197302116639 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((4500128074347106508213556071636805587575999160324762138724875058231567260451201647421011989199977617585620903142954290184860004850361195210304212901219694549520926563533139010519651438511342124187444830797879541262825307 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((1893927005084326323230229896303093914328348301917508586906607690883310500508833154125749585330578750025730259155896363395752596563201582490279270465724606643233426612868977963133956815203766750958616488219424310930427271 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((976999313600535543682696273608444842667942971771753736457944298642684434576907266607506273113178079008184488943887594115815114135713643636362227315742555401976024954265485693351328061276421560992798943450855072194705344005801 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((18135954528728752410924549491940751311214418893826197415019343772305095771135691598364599002986647656280110344067784572625055685285755864492512401292751649728532907015165016773849692611350670818031027037793369374189113109397 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((38522008491265341683312345104538138369974663967883007339433347169384642460948918907920729586879545094694965674774398624284608668175455334315137649371982785637711582110743727660992156239916315728531239153616434751196285809101 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((97884879879391648061517066624758979286901367741158701850936099758882617919257815329959669369214742967513637418790959267296242080806090955156234061728369652210313278769299798874894777186918450327336798040797181583952908729429454159 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((45656986891042111346118803294986404948729369130887858478946775036756639138912123171686958658294310150409382275521292548456407257243620227541095258185120286980868815206954721773118227304888724231829732965565303323415655616609390667 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((3913793557447781944764921735054898163326892933219510314257105737707753974093778952126981556082538136401108539692298859829410594761427266140874203995968582087438987483223415834247207792147582476986803446496435850893382454486412811 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((9805495668828976564089047929746210976244162876109213063510232797727086661237029439927761235523618548549586583394597823261295125508847318145212128082479144847608198802346040204736448815331833773651564611033668021278725533849603175007481 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((183815178877829951000196626019030784880201970817886351626262028024179088842062709931244148314045728445055958731829946438930506721656970818517759220515787909781427908972670816493254894942792733144048152227835770053301752702052907034021 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((1986343333520811878887847987238472922779381273180450332982961985522647479027539541162425013412536219528715376846777968857588412396309396026656941484708578527122459115284320702139832552838667305363082715375432393173705658194279756469969 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((982113576209843855857064758571531815164436973924127124107337497846185162280695990266316995457516438106071432622383821229285438446668090529315562086336699681041202353664939511187359096609100101991224230066045077568770321367275658370512945279 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((462314712981117470207087386559842494415006195646881561958739512578520125338984573770292577389247278327122491147184471061765081942979663522994085313884537372306080513180396400932930158633005987235121222736971794918832184143772276072927648827 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((201447036751833120591609184000333979276146004450742661247523759489683574184709093420366899218448383630307067110035901416715614993585793948641993299074745904010289362501692368943352817012937079489949819877169937410708409327180176853864021479 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((98355182354681031140759818133479494190706459685088806205786648964437341338170522568900244585277754131796222872521793816423859634117150936985329773897436565968867927240674172509278355165076236279010988972643439288146549982613302268093999934911561 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((371929017638241571934114181762161932448425723235436083077852335831911040796863796204971107706174957369841193526800722520777638155909502695628786868854429592547664247947779766234385806796746622364195175957597615295716992035506984112876347816177 : ℚ) / 400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((20413106703702959260661734756865189306106480426603220938409872684055731415442440711797506926372605621518124959243358064058945508642964472465531845806449791214906547827364798576315077878944122417223817878049542124150866138633691338710008767610273 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((9848744214154112942673132115736640806283175326181081529877934452120693472116823084913497591817556992205848859134231637564521708093779083014233940677834369169931125721125156229780728262625245611981571534935318033498668589851136663271656140014532237999 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((4673382236006129571732640930781029668647357870876880979289027741033065937965455261141397627741688511926445290010050258271918903028615148558683762877721226257942729674698342014134052742914756015519964934209283499388331953459205325946469329636790143787 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((2066899085993035539658654583770459491527974472468196694291224853696906435347066282721603826753009478271964338937601167608480111082996309161818973671456444016347413955661581417803167460498644101457565518319713202401851895795000497221827465440145032343 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((986090669189398072095278556231025751904994519820286076406044974282566851002390934065560325045950723446257655237124807158795851754595830694905938950792970754497696390188948241734405990302754961232213336781116911042504064854120676417798226979596370074150041 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((18784226643834708431371438107048382054406266361221852017298573096441721941060691726381705809095613684387793661910542244033692779534424228870580875359062676532823889698837268413905511654970477205484395553143380574506899619949106239521783992967435773550789 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((209127209816482158176105511951601529119613841365292851876344098347639149639571192888629106788923467208859261430773224829287259469756096885253599315916373665398186167831323826129726447451465612255292586547294364736423954986663245687580959183197614091599217 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((98720911847987857311809720752448897119431391048153687300223489790050565051328867905734861930900582577394407717950760141515707731500877994872855239975970797612853662345385491361654240462251043479953106237054730022557631299920083282704307154816702595648763620319 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((47172320574805213270857729209639621370382870891400906972265655156107296418240971938725092253987349278157246784939952398205503296953720227334921623938544234735187543353094253171397531188348654896738245789421324020693856631653323049987659658873730868045462539547 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((21144674561921150450260233648427823241388620322476207202836958617207024336307511745508689456653334293430583174582965152728449602054757965309189260721570999594080540687185401703356975922507562022844270795699895433989733128899561629314486990464601848184637221447 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((9882376332629115370536710110674448130205791289397164930441251897603259911555151363743472168303686673234612339335033951853642967281089239530512895012950298577680409935619304400126362298668143707373007696453315918144377216709350938594205381649789153993264653760914921 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((189479986889003687274971548156915578634668793074867404366969083612484589132742429988330844532723645837557706028033251736575530589355263204103566702486602997989533202458867123938797601049892468189425577894131055055133207317468608030126112157896593910686760425816533 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((2136523838236114520202836776902827538706176664070828561206990741912990833697743583689164686825188064025642712786687773065790404892853067339187551266128831857373972597476433992922773320144593761138618593432452808649784214208655583389015882253735614052925063777281601 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((989183445172240820359185325067511575605594361181673889838447083251698178206700164258485957125038722783981716112910387178509153628201685377986435312495896506904912817269615613331220150623223827186314414758150478516638784471375202962184532691132960812066624295199975220239 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((475544606078113449545090865810966045356171595025416701631945876318805753396720815867991853878321231884482601100428167797256148172990951910571452963233404706553279344051025067880787342930696961659186053732817766855889335308897373141341323672792636650575872663408721220107 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((215748054988427134830297412323362301603266039881846392536895103595796946405963881740300815520597875138362818964569494917055481763286215220899930058352974962285848828189708864571001716938832223046026462353871251583737188266029706360367209960523786735302683772649530105591 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((99005320434594093599410323307883296981114851859905549235653755328742912769709940405046110131261435908492174632027126294548523258495798785674254604901810146878468877763296582186325673831161039924226287266744759853911585981203192289199527441743895943316834703562294521277958201 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((1909061290333787193475247032507611482755199001701587065642074162410576193377830815128133121929166763616763588135342597229221144865715277773976300742401354282320604000262096002010432914295955273667604031012882667650899466606654409478217695335404102781775590985642240903122917 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((870950902229284047942720394011004350180661027144873847391307980681092424594315935666556927544603332570340803964066508342602999015059759342577371628922480379151827492087341472247330344443030807096775463167735604978171567815917908130264095211960444956567805955338173973456569 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((9908530261844838253308173921069640107086340662185054402161483686275869515389756409707635241560670384709031886986582506920387650328015160531818779212165559296797119530234990401272322639839738070391925150762581371405855535245464359722499344015326927051472802504885041882199758205759 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((4788698765815643666830269469358893505971431595570857591227370969265943587150973749033237218698122501477722066770855896961308946154991922064578812383673516274589445508052856284707659080741501102948911846711833198898411655860617944885203037301366418317137102595989186502449518889467 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((87850149620626769458085194207441902786139244885946663177302970762244826161134205195777794782776433021850542701002616509577616319762361978061944138049989267463167307914400992005531777586479570369521844190601428052223467728605046398590713014881214168184427381015438335828856471743 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((991588534348989480935966365607643034607552800953875417768367878306242684765726609680304429178677687907457863295399140753891927936513946147345523117571532667374166314880879482310601517637022473215171044938976220333111069165637657055721317176305448884726387445546723566445207564843391881 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((19214624124957559047483012566046906841116249891751540895126097976046157077991640310288273808888918383886126502375842828269672824498665586505948066919783876511117443560144303057490559892115499447792441638159327953025326565588829379491756361122933173525127852946452722942548769724586741 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((221414970084937630206176771599948125187571520274569167804237585627133338597504301170361204522110444495816282259089056421830168663369674004375272757083436365613682458653409767807404588066001875437868336777653588164388124584529577524401532122282385312115123820962342246856758422038065889 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((99226490030198723677390531014913245819475948022917429542561341721163771048371453299591115002842021502281917650781609584587147801113885973763746960368760572559060960150130796313800604960382949614393914121543314245612560809402873305187076606215872773990553863105031152446734842455433473984879 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((48175942863426618393221253100525296780046835693235421988710733418534666326001475907568012989084820858992621753883340886694806292322873838300061524307697115826286843516619099419789143833820893580710108761409391251617209108555021630291870918333090189184478598869710010229430287239566538171627 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((22311045598057268824772095399381728110845683432322501674062390828102823566892782242302380650427079802506764767261087157850555926338597576838185247077768466689432175847895368361135487233829069376223092595305178410057115143375436106763816358115346690922189416291638598565859206440263659386199 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((9928868796687044430649155841600407172313188704239463903304398423336499221837190473977099344546349455328342865248226035789049524642631840261340406728550853491958686834445877898220789831551855663590049948703001634712285479471878826271698377631005444423397342697275559747849289377359206834175487961 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((38644630991846987228868300305093978226082506503122971406950481253639369686692352895696679488263417803079442019938660140741279166440591716146353933121277338756026298914647310438159812724747209510968744509419022680336343847559111010725282839898919835755764896195419732049058054339244821706479361 : ℚ) / 40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((2247157307786975551196398830355231044886659995930993088405765826920722536380517496127763072918445877134900036280963105186234110417739288302263737090974154213058224980344218550418238294409864101181577402299817079532810469675632953591905699770431195470974172273479676873348285180506146092646217393 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((993458845674543918798065722037731843158748520053156861083969174611601131940926198796460078625137749562539081545361618025125205236611781398592602462350807936267028882608808485642485612119677094968077403232779327326507060406754504985119111108569629663731196237098763198852472801852575301263943697405599 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((484267138205179509725896462630656392111566334197435185576808152393030829849995661059697576030487118474083690070543756798993036784615126278831628602231628504883263426814917935630968998209039064579284107248767810526429875315407238183473771423539894314880349490377662621577862111495499593688920873210587 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((226234636433921623154231380061857634685061748424184525010568309689506575353738824306490833347160079936517046650841955808337016837611591197432858197706156129540175842586674922313491448948998090998214097346235876137666545329441690310872056708794971739476235309543691152669199513661218192919676720576263 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((99398481989385384228751325732867782565035355155568251788420721328108228492155632315123672370289042312021531399829909031972488748353582805633177129835317947011179709015823419531197334404913385976169429923883154161618262767944737523926568338432954574247057074767365165003274546385560972128930998469721478441 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((1941571923995370966517470419444188964014752408867359945307848766092201791244474757756802395053561537355499439291899272383867645448122999746305628510121636720933164413855592514490153336041121159459598549215755074955242097191945797104626324647645561737539187405786782856146736979210707947012624393346213909 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((22767094601120910217279686040409616519929272138724184235361799283574975392060636292870899097187474145652645693689135501522236620806282530267159845208818464436309336595662455298414150110004789800448169891640376908886858709237687295693538536092373101873509759815987311455373606117331545801824168148232561537 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((9944685005261890548291743163068788416898086224750900866211381112611504583910139792066457787499410041971188005996958604671158092809847121223221335682526003089201074861386105836669375674541430060982564606370370973548253825877430117962763297833956069693185121538532133208536124011069801436004365688277117435955919 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((4864408734100126664066975092714366106360413889863408412950140669647645571657689261520045794807652574300410307198704429389192337572162053406106006171759251315559654597394170102850200568664909449239403355665189611057493508251869913881062265382144810037298699845594200682625893027295610388805141084216024279270347 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((2290283537002741985219049267467636215113252085142530764977810255540643098790470153036981117736179209739308342354163625365420030310493586394634025578770866262624692704195673693374342144379139315919543388533147667733122703169915941678098354185014186644237301549219574227879885727446550590325137889390744398448567 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((994913288398878192930360409532642714029531111141868092755932395734641350031792545138639391680658248049628477843474316326955027056700731420566210808029408718079841643178204906634279117655155366977895658637212944356523873573862596217737750105512766212915610591561876437723773427933967870253525464328275442293070355321 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((19496637882996803269206010406057469780412402615300585156203972185633355731077418512167867023864310369335799209109024365644675651392454911868205189227928880445004831810217564705604276594043031701798792399136584153878936680125118017157700473962726574266281228965754868199948186291158991508579207347229704161852770853 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((230310466478921699569026562158251787646422078717588469368267273110308555171751690335448071211135444671260876028205396252541780266037815575209659600676307158638300756346293119546064763474252182994151568838845972216157937993328269951690653139525148609218168599928856793696742843887197193125749315523722236618736503121 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((99532231087872439743683012900212291339441651449495047941742787179361883907573610658404139819561651832395785194008054655110457333107142560703848179695576396305904157665024545009181673380450432391920306872619465150081578889978830485586945761952848468173506634389438595336640480659379751380643948174163881397828456804963839 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((48832302365314912952131286534794542040396257436613643907959809977491470913923318235837788924542554732865179605814261247979694989829268541651776405302563302643574382963442226338517004390791297337284878424560753723202202188039674485834705950088935803851403269894556429386110452428016953409170578911073251892515277630334907 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((23152079726659005332171158978391571889997501377956971283318134324814974725685481748540925629462024108423161974470368651999140581613888902537238966228684825816943837233965718407007690208581133433171620242666961474191801912104228356513025279512285566785159732642086255586897058473971908985983219225616831318737208891479911 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((9956984438609661686389346183290622099283714825644115113674724966226939482256561662536186293667069940855284010655786698029302545895199722739765174756625509827894640434717992134499337502392841312328599499699213395736351913143563272624089945323421992284767496591818383788562121960955902557212636830147936369462907059327669670601 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((195666652191486247277031631207775169249077755743054634531372969764066670910658342639409272274995920606269827589753378862434194808738168204263790988497515678815566256033016057236640457602888630267910411076488625890709200643330056263273443818501246034555459172670612571626901138668216340832199183805095507357141435372362672437 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((465325518839878108170211733781206934988396521037683535858114373731889593002979432241810626676360240955034673689826914570975620883229564782168710764942044460661027717134158815396588571269399134790881080567636748405807160003969689266215844870533258378835125761926745943450947746952136250273634605003755711307748090615716871789 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((996044331990105879018677885669222317628031131651407181738414033169263127848831153925165155379330084691111062335895488964076632817976671303426065705444525258263363239736231838696424577382543294240425681392839964658519185580768934987238687281996562988514934219087026754812384173407543843258716870263574080599439470268713175238797359 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((489951015790468291082482160821085641170254718090502165087990571861399305292826558943088550032676127769591846289369835055003083724100522369342019570867302708871020092001104637036239404155917642731556745289737955477897430234698522753566316542870505808634592259634117219338252329399962003354475254412136176637107146439041655424708267 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((46747932486533068882563239965968872245644899046170809443760290643016514479626245701819603880572568545608288182983375172471444619019212118868056662918934408014540611209331558454055600709053401409988045009078140071224321413450716074496621273133779023379551095474194156422152474966069692200086664045009724068481652128834111916147819 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((99636240725478146528678599688256015106756114835531753025482816076212267973850664083804262523527815258109882181346613269647523077308316716391757576206973098224640620162904143654684507711521298795055305235204170310032765786821930492491482443765121935860844835853023893345792036202384324282228344672568008877843854246440594881784566336281 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((1962720653999801872885457610032750145736768292299601047572262661910784430150417243323878561964834025249537622325202253570565786579413149685085667643000319152269473017714441745121212138179366093952111747795110439134597951999916764005530828043661476256295051094299728273032440028299152765485712803833397742641550270807105625596706395461 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((23475470871175380990675810354150466004652709994784667539007946406261141942776102899304541413498419420734264083955412074638636085250270307567076114397026543133223903951909262377150802259071038555523304329952756793488620800849922419441157305483582787941323677991295035645238495960717106472517582131771391907937322818222770280374919757809 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((9966549060874244876630755348732334893202185564160664476470374283552403950607333218482556177401094363320526655514453209663516574666195496922669634950417039139639726789560502146341132644643787115894490814124140297540303108990357906159024234046196848099827430260208224208185689857135060076669436347744681528397642992648430664734026935718064479 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((4913578074650634217092504658647831164164488982645234650752567012800661226264454823571542285511102440042118321624001357096500045289774080964279140042056073284814323744511135711555614505373547109218459744995667642448363935599685368897761958793979802012536826569649835978359666117882688254412159205723711172529502237987151425531770735378614427 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((2357109913120267333693406065288599600786562976793514515650494613888226369741306843540485900830176103327817102662161479266034311580356318726334944840825727562926875887414781295467712759002561009401275120798245320815760353499704643382208884207450064094112568336979941027736953313758274133421508494571602876385223571813344924095093020396286919 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((996923885088934684610087631114076784443979782294650544591739148741195514893899755438437383517627236556592310714453602707447320689728671701511776960405400502242129635841194216875384216868798019390541480776041817621508733599644322692477709538654215954412030659298488089960547853572282989590444697102253168669918851960957035498276382981697491424361 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((787179912394621690079644641102052106227169883181792218688919506440369852405225154606231394875397900479984246636492308156304523980154870573754103990618730445152275871442631614931825480402665716383458918673079431179115876654512681486838602894143740532382952749152204045369344238662393097787475709265001339174545366365651484620042650212943259549 : ℚ) / 800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((236611492520095153035361219678155004653681484481607366348112238243776986708924260767576496958571449136988459019541795252918967891792602412975433467960520416516712492328529795332612669556199277073536175306678614594265716213557911401217204128687309296075672736956825624643370306993811267666000664849454430619574009042560697354361240105073837240513 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((99717123548893344662059048469619387020683936800033769430111740379091598354128127610363263350897483046507672300990438851374148163306758920999321497501920224785683999182320378989643457199037797065134804030684029506656321633089692270477557691465103044951775927398429666264682020066653571439747703900826099137717067707477648027385997902613919613892813199 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((49257235133252440882749362343798079769746416422571755863206043124148157636959314829009449827746275611940031829706661488271037877792234382958301086286790840114703903891126191455056383414039416626423153366174970600596014222016093770684272033279025781759046442350163391446769149663438033847314735802435947449976832077318801023062464246472450411347797387 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((23745908318762042049820765486654279005719368893811492844608533745702886512535505569581080628991018139987847689457286294440794042506280590087252835675012203596829787396723520740130853908210999088836344182726264224329516650362780082445655421565699324917303269669964915816892153299772804288696683840414228641397307693986606243054782474280562118034776183 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((9973986964432683081778288038217729211035074144194305403023645533520884293047268486921395334485181643473799037126779766333515290949526243616176605588779081951066714880806999731508622680566316780312731443857672669402608681057295011500845727749439410910720362507632193680033893883309395776027759103016067250605323829311937034950388981126473433773969208966841 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((197246235928071711007147968676128275820287274352856595214728626004944722294769511406067378943470865529472483648186799249348810353796200917053550072775215568689243597826669051351875138792382532087296899156562885477415345381463285037192504714864309188701623621555346794754574846117015134765926905420976795421586420063202343600144107006828799960584702973029 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((2382565227221409192571374622965929070354212673775212879336761577503386002545450024725148265368726883061267676693956495002621548964613842865699687456770594337187335974206568794449232940495537788016640268680889693633251007857747348541932347852466764246633022008893716571364467866096882513813903203846723897224892842184434647726894493556721672137209451059857 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((997607867262265103517249589706464160517574383225964130556651419617046998704333762788804593563922818752207085655141540532263732640427483836699984473338535597138144033724130888309801433082197924800778470845707721005594491701347791962606272278110698787938933815839348898622236847615248726167736699354254528298414974019696417797002820315409370496420434487381731519 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((493620026554166711067298080033446601302951734878874503513032911704058874558344596119532072550163834327420998939225673717435085635304640357931600625446271598707611679114124640919091295532814788242998851148802593456155691111590531234280654749552886560569521236407066532143829484967918509448250059831437955078985004923733629285138627977327995930720721183017121147 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((239006459651600206576929848315470489360847250538932345796371083750781393872686254024677995874723057134466955694113940829641186232317498818679509911160735102570816037514251339579779423713246887860679701018080675713579439057989586770290381549673543791593350327525163358428400548405132948845037814635784890657942248767786406816170957784626885863182422508340251687 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((99780021865570636654342755019816737737035622707076435481859107896564024953851828492295681619544778489634211389761160925806440589881070986139093872183738394977226587197237352358081029984805838966754787400500436315953463862364241601089310192422781749840076414770770685368402278269850657609658899135917892167793942595877262884194582353384730301480326735025136648755721 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((1976353362877999220461410141801064085887287640160935122571637852339264835048874005485055394429057709029275919816395078958577411209517314371599192494416628301612384024105094452333657274506812722145509993856481539684597156666877289622106662873122156211755489313486062125522889470810790145062767264544390109041555615821572881629639286878012904174650889028553548941173 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((23971143268612635425367986009376166833284263978972395900081061666640814211402820324280784944449147654950881743879251109690794428623664658036777338603788238151819133623079888359245750439420940799628215493449868061602922510100135179731480565551333973140173233318504729588491562069821411731815455366417413606682149868650963085920778528409959857049317743477367671180641 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((9979771030736010176096705408867327385560058828520041930476281703060131170731260296323018586051718285128272445191046597576234470204873406814364933392144399063710779732070749685496773436372760145543803494562619623178764583319153293394571875985006586933543587025905301455792905107417196623126622705639873445858163167174277217567649598634906413793829366226176541082927347439 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((4945230358955784492979982098401402095278765094639854868067847812266118825342945528873538319116325353426605565898006032715516511846616598122562590631831521582223935622788521669376038703261036126680042927216777964312888420100278267506234281512084456712991371187783899368566952180989273828817321422060565885398778942426207565205951112743871872800568955146393595566998169707 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((2403738722075615056074628955591797554055358313876376564163176060043059787052363050687925763672662507372392891958986370735530160155015022008386326195864198622677957775079152915516927182196047127427261966633403875960654582970376014690030256030889965690881486972776514797271395728734683016727537706210201699208966112868354625731896556086040015560270689496711637090800150231 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((998139764215452759783676932694030559048717449811874535884668389131706602329275965589568466154729961782110805787323454066512945645569953617242184909808206793499779593381494070328597788435402650224062625556483937927896012317446017707271435143705220727821734719315225616573259760772977984266101097387937122207670826690179358650303489440867358906066754688792968541444915943143001 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((19797058023144258006153834795801426431988117253097362693144848341732895102573579429520054467597250543749160341696238970130061044742189545735900600941900097712774564796493769540233986491717566795079925812085631085583387505827781132329415552634101977701311578162558577465475116978642950410354376609621469787445065932114744302731104886355716842091331312843619170016765533357957 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((48199220424746735549135055342568517913314781262513338994945988409176607064615868444559925521139171853413013830220489490020844926534452733146897154123393134979485724835197195298696872975655144635552413191802480609087644357615236297323790503939204422001861473524161663699281341372321545036881007169312956774917819181224385291272596659437357060979150702230826130155571439695933 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((99828934577488820336947147053610356179561007967250170445418220396162607443597888519651126579122812555521127589396477512502463968620967364687974082121052888523446231627768813213347524026731192311954574983548706447911389396700018342342973904379988392909758903053508832474460394340922282455126390814697309821095201551602203642123258585492721457642992694426712594102733025215487228959 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((49530076818294714460637612105850749955528833571931604647206403970059782120239045196211112629107202561436947500809841895939717300381489835924381300869625777299744780955250514715597396590502218298093104165193175880899766984016152124070685451566959494617008501205529463053171651616392407230637384223671977498130245813678285919079363039110251316620704636032594374395334023001174847067 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((4831606840610224613031603803155263016469044020486992331438933181427196674131471380343548615106629810348143002397046604089623608282635378213885961594261393623386911991287359852607444332018887132984540942871458429154167463453948021896015777237574862618205452793400275372126582016237252700842771293892023321136621153716068932483085031580722487287662140479702468710560361154269700123 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((9984268994811294429365322695902954743916250731660358423990214129410717217905818230378597949089554719793167371993310675572214084090415537889341408617769902575727592014257992294286224961974173713815030760912155496243483457531136986743517537272879352623588518965897618725518903403196872172290967772928749913838093639483787044726012736263325172523391965186786063441093226265790990087840681 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((198259210613580559883534051442479091972708517907695974729589273802796985526895865910472168407090541300678491987198878673201038147710540560039713933753886974212359614905518002036148941771214783415097445147666077768285757974916291078823087436532977798324167051430195701295278002486987906639678648024021314142272118643825844430657763889854949763675696636882657625952319992448929078060181 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((2421287096302985685963864451671236115329739033082513780299801305641291899132336895072941812354625670610656573641406762782043208801014238661892182247946009297788016356572096456731797345931448954747845308560403012786214234869560137943392142145694130801823413493967623832115509648796434149385106732139235289511623719685064450057763047761521014090223094195342302632767892845692794491145729 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((998553392493851824430005709792539815295794501032754900311716101126480144641401138647385488800326362477459878361132856414945234958870522448765946595081502470961333634039150713390266961278183040548716413742720907279054495271105826163947129210076712387912576615584979120379992838054581168091705105430754913326637252993289572845959405214039119540078601726611659607979491994175873657487741184079 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((495970126866436847196582125705307473588004780554696639932459244241178974309270814406920408719022473168243729571982114256219831921452332799260470585172868712339599151365787115523798994082245442368746348829605017133278871276324029126025993009653067495859653840178939097883825356028023819486863498834147234917454807583404810193007753279815073809351247013515408488622886613870309965097336977227 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((242643223360835980634236976469867615928103150268110516485090594313146608487096873655145294520021578129148104585518640957402569764623274026860168946335814368345515405405142946662996796619514615034742375331805812293094433308461829678234706751195698820394425196175013719080988719143259538190251330323890284245230442282725606246286501389936390769794312029293482013703029875748586059821508323639 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((99866971420342119922758895066812168874785966520471107877765100943489987621078607308874922164589211967064732954211416343061948861582774373866067682937099885727133279652606260452655559492180434225819412691366871912474572330635620668210414055029444394480052632992579094931023761394661229636545109790306791074604235148009915829341580944077823393786088136177481605890186104292419165668915191546720761 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((397015073875416183464277003504335215904780373032827907462432873923451179122898702772881297219565379788265162998417296942860806855008408442548829984166546575584130563424760276184973881278232733637391459268077762613802679677293413202085037302064139581476563038386517797318851879887502063197698055969422058519980915987221527716498735345627781656831844638644380120202502952440152300767331859191329 : ℚ) / 400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((24312580519297501053160962263368851408712848761054505965157669408527099814592230477590006347492107387397043408202931903426427141997920932381621674005609537804556123734803493686967166657560269134430002172096373383444648881892694438072557744753870844774797338791344565875062458958764330743636564938476846656773775778544657025441513907001878411161948970816759985001619394512198069630067997294279633 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((9987766824843241005976985231448980237556442695256002609331400917662395771646767649516828967333459343279305777736327635491633755362290348646349718055212768391581449263574019104965752595341420550972127371685406174199249196952921041027961466086452677071991160077364580990762014074091652016147051751206822200429530859975843849750422442036452561469174878914745030996055623964626574055747772099444894460799 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((4965458261174573923817529666613710223056689637435995923062323562126826769096112493768928033776822512682647500918426446834645342554356252144865136266288639658152713628252915388894936922770643877405395222599399379669544463158065176725914878189013815475941026911960977015666769343450498859373499430837121647200060330625259976083513916055696626544152457535979269665598581079547719145276628658116341904187 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((2435782835605323343390357496353246208525209618521744646877508716855104783746463517677590619848564143164908668328569269813451154469491998151900730327404313576168442071033839877669596159888349599312571730276157107914244268203042635682935551995958580076975419126042437390702088384324436962858644031045219762771927512160378226063240852508857957767746530358411971921026648070718130594789520192867345232103 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((998875049445759599668637584898816773665452913813046743951506296987316252764865106281918075007017587748621680014854953032175148509360858171169673722639310968521438492829003222873545642915001692446845860972818266373188756902593666011890308459844101730863235089554369503329484052239394227752866731989228162729299228352518624579199097347230141100143852690121038305366279124163095123592509374492853049720615241 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((19872104757352928447119337837745512315344691248538966756945490523900398623125016743242072958639506901691293470663222883691042316150841453497814546482184338798731726169248741822533885463596463503232011246275197746395111610330916048334914990066173499236745420965715921901696614306759602855948239279429232945541635157206731426149423402344046222014865415211031741976400951197214242191161859563496149837428149 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((244002396389399393668731041517363523682251285250747417132331973467568338274287940483413956253714393136926600684825164458202490729789836294824157655477486574105614308892482697123730914360558608045307570236782394476494476441442956800804872927644143599786971594780904092862372969092822636111189509857150739420713830584615265024037999748144354648400767531273321798847618859137262515064838025513082442764694177 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((99896550671982607025928243669710291689501384501333965527036567564656615288004230308578904259570330351775501072486046625885794481772315156562592025860188397354262962362062307372228383776820640635719498529199394957412064896005610932787420875658803751068452235600330265156676023959882453789925871806997432616423627740069260197678569792953936545428128549530840561523177661978914064470443569568988273599258056947119 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((49704065632280658339719678114696912198587980414558423392736541218419799042518652511719384163696733064341779174935868143792319029091219087831228367087621281723947092739905633773435241296084960120657481129730961064172136683563068320696555447972104270807553831988699950839282634889682694561614387385709333714151754207230014900001953553158151263144455966603444566040971705968989469552298107770908986378375244091947 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((24439979419682184689360739147995902273489969673360752367887779815862273973975269309744845033429749802967154473070450354245658725277396019531215032949665710158938091400375995196866945371699204980551923304144774001460464522568918703100236345989299809099531134753393192192067709677088532068998419874295120292519943463087682344474564322799400784567452896262514750216657574554225640244825008820030860208924744230807 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((9990486903244848559497335359622888713474857817358170135900755716678257685269581014946607456805828008818923303124744361669831774749300329482339400106077064832300667755852887723642749943732649292220129365246647160888656075771779975768198436304707934144503799133570770853542770487326830568067793245499676905973700383349029098518323599590251050781025273286306567197109894617918958454637520213994592651914171658800116121 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((198904510147655512098682324641504028104729279207329882585171855366573174838306674107396656415012648085195368910865426167093529058979095324233949912852121140165991081566707652969386630770382532643490936132140010847444515307690216697755345719023250145674245625155630861430355590624066601490436381035225706150796559988671135348259672266854292767155897524651189808435329028173354036660293731009265075469725243891927493 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((2447720432351821346172902783380681198611310488839494598362270735413329846591691101425686031578388763828341990330511903329820496657988642932410165221434076319865031440232756526832805537616405645125896097547828262943718157159658638350802440407752641425785669863070122798884670940282732139523322450106378972916192650817292089450782042387385661024586427762563675873015542122761615024478482305124123121236169261262914161 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((999125185135493028682815462335561223202434450026439967527297594950015898479705400553475075120407137862979368032048366754796060174170908998866448894354740804913537106160475702178463642075710696263270876298716426268159924071897114791667760004144636915994424864524034516920939631244088012208946199062904788596435513552393366870646519894719896378772303106135465612879028799169209500530011721358728745677375311571599878371039 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((497465721094247763782467872402892973833136023070356106984932288454128075522897820365849932068592938758782124768859079199558379236019899219878364264591801392755990734398115702848024907862305813464153236747725310894450003981244836453745271803705090057315809349134017095467295860708976355455438118021180580227117201529824026890252001385015853892805475515119750066882548903409573017810604667181333746388171976779627032724507 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((245120628657739779279707976103148888286603023782261192625552851484879238593675553905866722974225015575429644526664824048219488067975809232478741883441797966266086992878133391931440973814559403413288478372257656491885937775306425416813117209452327302638283431984736405550365881824981732777186078324779732517373082210966480168182062758545445051493608715820602948582291335245609076906573290942142242493788096186538161716551 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((99919552899874803424643027100915874524472669589981392973842759534008512008295228929497014432997519990741719704859135758404290897556582620626759773875967609679043958745411185096629338061640279917674126513553663843193718457727586779126975542221136666157931316116765690141532687549575089514722483519625661454539613390764541624057783322998546951095522221337111282294742609342801336459239347884427336723745756276812753215122375401 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((1990620609852654563631849996974851692116417915415497718452486151516297453257950096867998073394820172354338102684991898843937653175620645935333401333946326788369436010151434470880542161594339833704054315289395309131112697567627082414614226673382341884133469214655202520768396783183291548060287753003274143641201702763125330730134955534152077486234295153551883310296500665336101538082141084007783332726846252884178772376779477 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((4908939153732534782192664626768581866936681215517194036725395967024164267009843978238723293045437414241590380318705769022947830120117869483570361110465552138087935908285714152039997626565849210062155978800053041950225376730361444145477882562475259440137920300792377417504071641782746900280344555998717165812249639142598392888423562229992313317593988669026575774569037399730623322266769453100199152625060155363641145104875277 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((9992602165119587048126748129173122905395982222825098916481606323987888755770820957127615950244018940828617802339141265207100186648405781210216202045860105418475203402269267170300937298810378500949395000059881373356251155654171152621737543887113506683217205898781656099725204414371375656684364861981256201698008307801316483206729696599623379075793127951939416408542235612554668099455191192104053457778936001459423972909438519500559 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((4978306480345148862952484224035195980853594850880100088481569126285904302068036761866895832804680092757798344127923042976652995953600775651209528542191784758690594464138907025034459676814197077206209150577100241840225967446974638954511492113485327116837504769407559434974752694137713153359304851550545006551794286024844905395805416397976383593418196197229747092236139354475528949615885280590258746101916987098918361473360817305867 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((491504725531955962316563262620307843574211442070396088716011769268315704694648270262227439562793273416523236585211931020331804211678034403891966337901787206308630890122388421079307468817797204386720147478336618070770381894218916784471603374596464641684740460294867153092229622314603994143843421782558252239413641131150791002028435732552305443274856329309640776472493523630511734370904106453028502687327044714198157979739648935627 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((999319702502232105358687631210631209257309129228773271260732035947602262091928924396498435168489737779658864485305091607179726064000747234310271723935249434177561229669279539713703893061303596568805414810506631212467500022801925023942362798315070961081971037246062313274630072741177334013037508342934339051947145977101262479207656169604766316430860253332396793513135444694914723757799926834696651923893175758207169124779056814751905081 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((19919728450836879446548968048922425350320070436226406258182473316287074570069513213733179502966510514941150031404261944894187518920243882864578902320406719541372044391716403849901359709592269240557137552266679390507527272994855444141139235093335919047933303115948991686574884076585868741989032048308648453162416901954983528755185341903952740529769487769444460716389517231245216089439908761956299462667777382681297030216706955985180901 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((246038104685418567754398839977561596738374278138303665130374880759741461698708194816721674813124004527024238816477770971103056092319935091538696489892950166800360002948881368591582070402568430668952371410728605789520793491905574365238747772744323235564225512599328373208719757036771384970168283543814781660646961185655538709125446490106424409456172896482790681978614870817031616409333268550457152633419318778084562432700155337161829649 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((99937440522402762176679555878498435372092890214748761251865657293705556419711691958577599599659147796479649519204170919104640429119444714919938277461361602717534353119157277192532496302024417436870777140559379299667298834596842223276715740570255610510136974614110644266421706859205926458504916229707898884878007596908254996325456853700684705692665478036193876734674422358699663082043523471791869414269292549548973065545557285627770439343679 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((49814377552673271813274527718635354782645653519270650658330398298609570051392826426510293598327358033104135434798125400770747368783564001473861608088968462939191278827837995496139977668527167439114308423186327389109408845484246803626719444247499055834064784456375862913085776661339651417331247657846147289256955655959492194537185728208978854327093476375184556654476053415123237977013750780515243199766151409724493424203951123585933501260027 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((24630537566124540045848187094323433091587848539139798128954937202432359700709789429358723166423131395705016275476043194284536726068043756009391637444134033677370986141182517480051965661445746868221836175838053124422611018087626528737946078018375066104823206233479044683510870202955405032885439524901909555115777399867608249198984670153524866054914443107818052903264966572080464045191411803904800463273380512906525773390223963404889549096359 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((9994247092999635607005275279030837618382290091258081335960313979071869262800267480818837481585055572216472090136496353549943629221395016539322604057069351624301741578484584053348095827437863403077199795068699961018105133530691014010303502787100135686901686048539000736095873741065717791197653591567708673554496700604086221207092686809461264850791824694730352710643925205683662317361640374942508519466789873563974014134503902429044141831605377161 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((39862656698369360964147137938852488925871104825071953298882881485015889181142700490326643078856854571488394886720732121984859727736785717882917249925712604473612612343138756155044307955131892854630539842939793388594589390993551448489992687724590749645406607177524996207225500877267647205136167848425785708620337508121966038293373804483391706226657241089876208974732744326034774751668987592179467896433456988666487841305647201338389327601080113 : ℚ) / 40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((2465553023645510078591187228927301312162590647157936405622193226671281460456908102199592607740491246777233890273936877646568633688301026903807752575480967054592056131784153110746471387487811024937146880718816981332834433626411377625157894662685459498493818409624104551458658272061312579673542137492718151896235475654325878239359307439505500450546828464532485642806669282471983158277053078429591432475470037654780560299344360280326844348290934753 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((999470968425153490784598109384396796548817014502001901573574513201470025537849797268619475969080125365454556936862068176099266199570264325939567346484040506019163853815863864961837544195358480683576215954722579715263929974348814957373499812798941377631792147337597968690640453354662342360745026626974921911397962090851164815983036386311248454413965407102708504918104717989463903042259087239338140941646529983069486365794844363472470238692598878348399 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((498412317772062765219918897153589231976081669531899666367805262889212055366547169811240365693231275138453470589326318805044439122356097491325301522118578858605301578510759877718943413533352799668489922393432973397280708205798056443202125276033721579428242094445093016948254425788584946720641881835598842924740364317106502791116817853647862776907789496268806906393420962699333017695062670237389995565802220912767937243371742041890482835473343183530987 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((246788948887254270243507515225325477721952193371225094705210176015856885760825799689038822004121078266764493025573635386373463755863373849291418173020507128388934499328121992066205408613382562697478271710287786365957837124149871363653775167192342560758526391027476345611493006809156605425783442850580008661122714343894772914292954944898492396112669142855033443475909953714433804669991512451660546307587348097530584145587360128315899797083393029544023 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((99951350785408689859060857540879745013832663836589592866804338659493982078435129507024978390640639248481835601356898927405912420446281937149076673615325880893016288833053025158025618726660970525180985242980333708035955736511142674665109669285177850145641974077018171602822605450041394341151751903589986844050245195912582265312984043048796096619453844871757971403763991761593111059863103403442296102852873250713086896712128092820564890679932700254040423641 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((1994127410513195192754766882342508736237890064205773105608864384804444157353111895332465811144112444020812665572498555134844513385108145934246656158604282216703137060739841604584561069704216201275662721916340230025235362973710383982991225060563853415881291019712650456171621400963497122553335788333245202710628663009371393774821113129275975785311274442458848934547960412162637429507638206314980348770887288139374921967793967942896592387193704206663179269 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((24700731963854379457469278288429719967291064123482452757937525243929008324209973260550478214263203675414893199216318298599234235531550157942959532502393072145347962896015047497950908598855112794441377443849175515401237570801007019420073311730662953756237481226813898412450338098688777973498956042597261041358741058627101986029047605762563655468077546403597173015408707338100072716539046003140043865386719338902939889915809960235603451909321021485511064497 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((9995526266875397710749377398601760471727037933748942370438460178788407097950816074336509987824922544651141120065179068465320300271819640658291941828991752681040884904798723140506877872485016188525118221959228507457278453573828169219528820077795669921543090294148514042423963974580356582217973953302231600192016497970925152535916699614724240249028356120561991292318732918404340899953951125877150107322247371262324757934750587287686326782035931182661303317602719 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((4986425102116273899696630998991370050742879832063434099099754138427960997492870896753558951803907082055323574823026701614999156517899545586469412437810355407109193723340411299704781276456170877993290889388587301471087412768484301196381794847642435594834302769385415116032642517818973959493651046386565548318951131532699089245428183345394372300595707790603522061333046122106777992972197064964561411653899754795630492305507334792608777188537818428630569728182747 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((2472113621656180048869982418973825705584262674557141725529425931993288027689184588399653502962115483278841445019686009688980258143376329047064060480323076770094924545382951423896313910399802804988208553429586820409588680229290649639845672964855659398378293505679404135750137802189126289701641479268434162404336980909406223903140018705920855048865417752564285956453496901261077046459840903169756386143720758395783743089294702672743501301707145087988439011985927 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((999588599975594698082801996198019291219546681349618991443150359581203128320459095379911121970392052283574286260073801957002389492696262335295868678652252584795838734960385781277871982275849603680581346573148694317263869312195664613258650765534012010315181040359603202827265303138435010944182666771719915722057645136908306102050363779870426409060398600490760157250338360443544784818865391584536846719246546013912122414921729256388346924549242195626350791783428436521 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((19949797519463405720770346926549324803466713486009052757839150383353005398375213208074490368991975470417350749867434431654714602725402375226891250922376501472934263734094387468584588037765074328444226322108482705352138574587636991319787121216081793494212292983143300374986176181964010235247121977306660072257961886093526970652174234334274154556034009579064740099945023605439902990152035017886135216291329458829249771786161944780917166552279499693235580519179329813 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((247401969893835283530436502946817047653383626655195486030143348772980538552449663108998706335750045341586987475136369168562729352261723395509311661634658376842367134243634197066918588199180985814453074218644043546123545729212896823642258054247860794414746392646946596691766481566924367444032340579660498599029620066538248349694634045773942880056882403369918945465790168453671450802521301740184983318390367700642726907604758554586999185971717485916080626626513303681 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((99962168065155712840996388768373656001258293270229612834120663916727858477221097952041246865275282735945207790190126754163982735358855588091472787820182495445240534228222116060531829618104853704862580049520180780721268158080201122170652265747742210456573733290428750928792490011307345171416093853660591729884698989144950920838449402833104542150785194902529813300583865288027934867158042544722423887455193124893344865153787300688215994834623763067603592461612295594034639 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((49883973734977465371129901079838600140242518833863716313588614018530531757338504850973660810583361916214523258847779376187349007126482828590766177106594745750196259436706813835713788630023456443856623232893918596607646837081662480867983207221469542925456558846919664214945569938489764820922115550499799862641978406343009178971603528204964284673330563362646842328589753806434647178081065409713107338759763537141379425455701637774628937373055351225015921964177419141999307 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((24757998478248025492647678353740742060269173602724084864897005921523085804573657005894988145456257454539681236092034990982085884770605993618396739122667700336673870465779037075279230898291318574137102606797274474718564709338889279704228606826036941555065743538643601309508543707565127864729127142456751504219058764959829832539218856020070396930494505236663932569027360254200978238865071288492459011840396567394959326356126804290946038984019415326700818211835735001778871 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((9996521013103654197145186914750873032219711390837044966612902133118377137706774946571761020483849725114785363178093866186165688360865001025303746095156162098648874287093077570810446519851304241845457998773826304414347098548897214993691011705896625931376063939654537506660828588949812154618252574688774354888467034342780541729382968635129460591644055738041739101308391668021760862448986434370129378266492104572067100454677126383987654668997166627933758759177405090531831367801 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((199570986717050738794119330787813676180599387157714959174144996068860323543186485268921613655438982087545393054105436051312683991915343507079872745970490478953540177161134053024998510836147734522269034523484434225821166818080751108139271868499630000255576995413670433716883775696229408993571506364149987485959175721814636651350326499971596573459571390088850393037649314570486251879851002969378948435090230290589838382876120496760622702629813944692446551381698633954774536997 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((495492399786640619609116494460802259817584220703592302081740162035794287049349061922018303504195792277039528976512694886382936011846653550447113718604615699075902360933132112937153940227156807634371208574580540033625139622563854328731107919111330870178479540609557991995932665262905537807810995116465690662468943214957450601635463118724709480209759463613489415374476554165462297555998449456935826464050273209383496189218967035391639258466880231218412709794007774487245529821 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((999680075843998936315274243493575533169892439789983818084755867259432843206377317311792571682674336871830547212494333840613610535976784629285907187164465510429651830566792320334157851519006086775866472109242293127638944835458038993604831745462547824023411463826691614575023136211235775926539888515805000901188540011127755836892328412717870066546995721614580286017218389399613107149946343518242727496008347444342718490711653865145120735706310445938160521735194994720216680751612159 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((499008644858770143637151285405036165172646532657128406520072321745294414316759047907982732224042110322734841099469327389655650714540305646256989626360611306911790359045792438074151150348193711724234058642043499511690812363483708852701427419623968624413246104935418162754838201235866411965141288077900887802225265061891095647659967879235286121025540476539293656847180193894925603528245230126863009985290192051696908051171506007584642355325451583980704113139894287202182795600084667 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((49580272373996141539028076120964110243105203379479969704115640315963273522953953536596911640970763850720390495004425076253607125211050719977371072494330999149304239065827508373010736693937942747453657503908189351688915503492497336644679418119945467492427776332506799045397830902404806354345147452998745484172537872169003020199118662059770431188345399212221364285709943995789875358185389855363047940535310003877750614225749736760774520524592575053893035922077374861875359783774331 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((99970580094538298184616304157425712454770138870647121927256064797310184828415251722675133099367049344396665291113766445648987011277889137724502739024457083873600352687091654985608821867836280733821904908693812033724549728123885807812906722480990435349368894802038734184704552582849030718428681608024912077872396950883297299004781628505122613449595179563955188521857385870799021720401915803594082977805431622634312049687352977784880157734816602298027303418246796519476405745237502529481 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((1996335011632409123257327903440600019376934745608787981351749642891732393820060395771796970631314183490718245488526549651418704067595223183515910444637650354205946364785190233312104982315405586986930569317983056585520462051136920865158042865910730336379563790546416584647679652795519041227248923508808933955515683874009979192011171421710546255032083786536257837628014759310554194221866529495684918656855092623230279888216470239792203474308817322907656057302459980831399157260493357621 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((24804617332691729795005152218272654619956384041101123632774083362233070565913947306450731323118730734550948486089165609251502703037320759571450507044867449616398604106120170076077414116626585495682712285388672250122976837899348476513751887397936263256055558165307351250981899584323186656993346614295297718768846922683189722717645215975151172626067504256222632566048166763428487960300544572397815310897230846561232245535439445407162904689205505716603010007491354903719029578179661409569 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((9997294574913647362759130714012711091628207200405838685308540462695847286636238133165482564684694490661372943505530848575435196570103407216007547377950048975932414832752261500821601650144356540001528553498574260809275868448544415000667089292629399444292614197100679956891245950966214015835983131992362889769067751206277136319180713775702570410211323117521755181281483347292807238386439775382708276556009686585828701777199292484119794425135999930724292795038557161134530795926295495108543279 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((4991532376990872700555564097488532477224252869004938237536497095071683328275842041075755656971044112274056635097693535924770320185263902037894286609846185200874505718563833374656718593909596095721001698687061117090295149895528620779390062848957521190950684292091942238288831146421658699362090494221006365010685609509219648079116804104640677610833034769241816347994979576864496001900713221737446330574234143528558328536225259196477743203587563507470635352254610145286201318235188768159462827 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((2481812951474225692776272430183420057347092786830677195173073595552442377671058450871127398447359614169850937857378899430558652041326110793175101010804119088054021914360694998237227507661021152110772740292899196569606609213476770303247926179673639346586012145112802606718158702379476985170643852803218301152453537770271613216991176249192265004952354653766154910317281104497180168179203615416039887010402862522767331803753629492736515365294591229205856468612338883507090994442332292192205079 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((999751211814484097831966901329894899275038305942120519662288072409047420631781822487764611165839820666729194511825111304148445241390139224176838049328908553777768935605065215354053666145624883062000564251175390449760199586659695859046344864260906943497704508951181428155762086404902074682261172834885698980273701333178039178775539258099832672352623062564183084715463927133699260834778615304418470403814094768746221586729469737547172175541081417629475241138950677980770317462586207434686531393561 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((3993740110401893369730563497018698090592527987249091080458269376162303102669409078048045390693670109851514059632890184255583181831038985625390382138059747633656296039955357055665873906138259015476348359991362092106490301625429853123008077595624614959567117485141915112107676576207255951645624477636140545381191249494515426655349427890460739120719699098725574672524478179750218828837534619151777889537754230836216201276431009057740507997407084909661243568067056233383594117758250065886391884097 : ℚ) / 4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((248307348690672186357495880912420690136257592656134687755066170071462266921047481541482163229700720917716574233870610667372385877868108039917134731165482715516272299792487816562972035350582095687280317766453323381047698005791230667465755766748933400021067421739710505013074674809038135778051351476493841733387355414963672718270189942824685519208628711487157332015815115700387419619174957702523529436992122418564551074858382156226759822769992810119184799409924092903363810754909546957332420805873 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((99977121687248143152529844279395805042433247576131460867624348850663591753878024614152345878199464068691749998112925410418186875952995812916077850178237101696849853549306192138743421085085518621498509887973837730369498193789638971502042827372568741617105408938641692951775725703708389885706055192723253992526989300897719304841019814635602512716874864210339712287349347275287850327105406684779018119864340340839133790894055307595100406090582306083788913699896765396433657623541965049486338740420475999 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((49927696584118353703770799377032496573630335638953160790435421732069175203671941766392044874866147871545719265180600090385010991960645804675514465165161555342811510478450455818466996128201396297018744663094339747481441418740298348593756438072315107215276932411109917771977940773199598283514258246776323808687076709111726490611843618014293393537940316900436243201267460821257720309195091776050136668275447186351332053571234911047803458028435675499962924965823119878185642338478123835660169578400677787 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((24842491790831355148080089717583442908335614288358466057631099573236276962084720306595344089073369264775917017678494590253505107807500703217838122469901285707306412174483240199022658221954365412902474578703315835936011983350063419716268374890513023887862002796022759619193147755519984950884129959096044662555169281923426225265442769061641737766368479472758681463624771307042909319310262186706327969645679890513041525721272449712550168366131141282419244112743016660821604237870353791971805008585311943 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_open_source_model__apps__causal__minified_sft
