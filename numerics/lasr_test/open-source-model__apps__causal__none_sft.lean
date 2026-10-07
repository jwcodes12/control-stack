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

namespace LasrTest_open_source_model__apps__causal__none_sft
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((8787 : ℚ) / 100000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((8787 : ℚ) / 100000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((8787 : ℚ) / 100000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((141 : ℚ) / 100000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((141 : ℚ) / 100000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((141 : ℚ) / 100000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((8787 : ℚ) / 100000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((8787 : ℚ) / 100000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((8787 : ℚ) / 100000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((141 : ℚ) / 100000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((141 : ℚ) / 100000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((141 : ℚ) / 100000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((8787 : ℚ) / 100000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((8787 : ℚ) / 100000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((8787 : ℚ) / 100000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((141 : ℚ) / 100000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((141 : ℚ) / 100000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((141 : ℚ) / 100000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((8787 : ℚ) / 100000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((8787 : ℚ) / 100000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((8787 : ℚ) / 100000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((141 : ℚ) / 100000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((141 : ℚ) / 100000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((141 : ℚ) / 100000)
  | _, _, _ => 0

def kernel : Fin 8 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((91213 : ℚ) / 100000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((253 : ℚ) / 12500)
  | 0, 1, 0, 1 => ((12247 : ℚ) / 12500)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((5523 : ℚ) / 20000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((253 : ℚ) / 12500)
  | 0, 2, 0, 2 => ((12247 : ℚ) / 12500)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((5523 : ℚ) / 20000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((99859 : ℚ) / 100000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((253 : ℚ) / 12500)
  | 1, 1, 0, 1 => ((12247 : ℚ) / 12500)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((36261 : ℚ) / 100000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((253 : ℚ) / 12500)
  | 1, 2, 0, 2 => ((12247 : ℚ) / 12500)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((36261 : ℚ) / 100000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((91213 : ℚ) / 100000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((253 : ℚ) / 12500)
  | 2, 1, 0, 1 => ((12247 : ℚ) / 12500)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((999 : ℚ) / 20000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((253 : ℚ) / 12500)
  | 2, 2, 0, 2 => ((12247 : ℚ) / 12500)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((999 : ℚ) / 20000)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((99859 : ℚ) / 100000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((253 : ℚ) / 12500)
  | 3, 1, 0, 1 => ((12247 : ℚ) / 12500)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((13641 : ℚ) / 100000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((253 : ℚ) / 12500)
  | 3, 2, 0, 2 => ((12247 : ℚ) / 12500)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((13641 : ℚ) / 100000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((91213 : ℚ) / 100000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((4419 : ℚ) / 50000)
  | 4, 1, 0, 1 => ((45581 : ℚ) / 50000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((5523 : ℚ) / 20000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((4419 : ℚ) / 50000)
  | 4, 2, 0, 2 => ((45581 : ℚ) / 50000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((5523 : ℚ) / 20000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((99859 : ℚ) / 100000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((4419 : ℚ) / 50000)
  | 5, 1, 0, 1 => ((45581 : ℚ) / 50000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((36261 : ℚ) / 100000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((4419 : ℚ) / 50000)
  | 5, 2, 0, 2 => ((45581 : ℚ) / 50000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((36261 : ℚ) / 100000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((91213 : ℚ) / 100000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((4419 : ℚ) / 50000)
  | 6, 1, 0, 1 => ((45581 : ℚ) / 50000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((999 : ℚ) / 20000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((4419 : ℚ) / 50000)
  | 6, 2, 0, 2 => ((45581 : ℚ) / 50000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((999 : ℚ) / 20000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((99859 : ℚ) / 100000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((4419 : ℚ) / 50000)
  | 7, 1, 0, 1 => ((45581 : ℚ) / 50000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((13641 : ℚ) / 100000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((4419 : ℚ) / 50000)
  | 7, 2, 0, 2 => ((45581 : ℚ) / 50000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((13641 : ℚ) / 100000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((8787 : ℚ) / 100000)
  | 1, 1 => ((8787 : ℚ) / 100000)
  | 1, 2 => ((8787 : ℚ) / 100000)
  | 2, 0 => ((1680188631 : ℚ) / 10000000000)
  | 2, 1 => ((224270601 : ℚ) / 2000000000)
  | 2, 2 => ((224270601 : ℚ) / 2000000000)
  | 3, 0 => ((241125045599403 : ℚ) / 1000000000000000)
  | 3, 1 => ((4753446529323 : ℚ) / 40000000000000)
  | 3, 2 => ((4753446529323 : ℚ) / 40000000000000)
  | 4, 0 => ((30780738784258345839 : ℚ) / 100000000000000000000)
  | 4, 1 => ((810275341603819179 : ℚ) / 6250000000000000000)
  | 4, 2 => ((96549285181450929 : ℚ) / 800000000000000000)
  | 5, 0 => ((3686303526728556499012707 : ℚ) / 10000000000000000000000000)
  | 5, 1 => ((29078026008717461689221 : ℚ) / 200000000000000000000000)
  | 5, 2 => ((607391328734720780575641 : ℚ) / 5000000000000000000000000)
  | 6, 0 => ((424108803583491823944446043591 : ℚ) / 1000000000000000000000000000000)
  | 6, 1 => ((82560050459781022231956272283 : ℚ) / 500000000000000000000000000000)
  | 6, 2 => ((7724474769592592369883745599 : ℚ) / 62500000000000000000000000000)
  | 7, 0 => ((47471236301261039737444756974065883 : ℚ) / 100000000000000000000000000000000000)
  | 7, 1 => ((376019044922000316748804190419659 : ℚ) / 2000000000000000000000000000000000)
  | 7, 2 => ((3181547138764171959736382832402729 : ℚ) / 25000000000000000000000000000000000)
  | 8, 0 => ((5208693876746923217571548617875471386079 : ℚ) / 10000000000000000000000000000000000000000)
  | 8, 1 => ((1066741597544757356486130571244320980927 : ℚ) / 5000000000000000000000000000000000000000)
  | 8, 2 => ((331576904251777429186312274704109409123 : ℚ) / 2500000000000000000000000000000000000000)
  | 9, 0 => ((562970594579717107444353664082275371538423827 : ℚ) / 1000000000000000000000000000000000000000000000)
  | 9, 1 => ((4810540630268792953217492339126659892734011 : ℚ) / 20000000000000000000000000000000000000000000)
  | 9, 2 => ((34941144864950816757794810580904676369187339 : ℚ) / 250000000000000000000000000000000000000000000)
  | 10, 0 => ((60137236843399736521321830761936583464134252532151 : ℚ) / 100000000000000000000000000000000000000000000000000)
  | 10, 1 => ((13451229680861862477826924757066189095363742661063 : ℚ) / 50000000000000000000000000000000000000000000000000)
  | 10, 2 => ((3716749124307591258780792988341449858817646063143 : ℚ) / 25000000000000000000000000000000000000000000000000)
  | 11, 0 => ((6363997784197020167319328149288521587514077576215089163 : ℚ) / 10000000000000000000000000000000000000000000000000000000)
  | 11, 1 => ((59679497991108501715655171393626627705582350816296019 : ℚ) / 200000000000000000000000000000000000000000000000000000)
  | 11, 2 => ((398267267629857204622491830904658741641946629227479563 : ℚ) / 2500000000000000000000000000000000000000000000000000000)
  | 12, 0 => ((668349329889962800521697878481053919561921557959306927824719 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000)
  | 12, 1 => ((164135066105002462954448029456350742767632165437173921113247 : ℚ) / 500000000000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((42899933192240754214832605348641401901337348820065794621231 : ℚ) / 250000000000000000000000000000000000000000000000000000000000)
  | 13, 0 => ((69749147427253176923985628589892371165001551066142262807676094147 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((716652663401919205734350967452304947309080593208233052423330251 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((927231313357811503905655162192092282483976386440341905332019783 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((7240728984282044026767501140569852851073286477396034217476559575430311 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((1941508735007175754655965065110909978342901980112506197472511468577143 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((100362701586190217169747820521614194466598391047610358067171069353691 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((748318612843318081813544081534797988104947679462724469078689428553724957243 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((8359544027290660348009306992232758207783539330185174607240720290490242179 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((54325850109998072547967463694682077174117496473528442197228273301748289627 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((77043385633277572196458796309033528889016592686833486998074498846670914525005759 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((22358638765551402069664662396950339902884839106004301617490692162820697024106767 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((5875973774142579991564138115301521482351785721022007012318642424825887083701599 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((7906058333768147192755596187735875270553870468744142849555369263301394126569350295667 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((95148517930346020280436854972816242015494081026587252923927107574019966135904861691 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((634468345903357522936818101999240853405001593909241212104683449399482178473932971411 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((809005298797994009892816195071952391053030187065559501736493896613510062466770148518674071 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((251785101566076539964916593879401689185989338965024046028461251291099064467343933993426023 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((68350935867596855096447473367576669014768463905366474144657999823395450112904767135082807 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((82578800319261427624353443601097993445120042452810878831890817791808093327781505556833818038123 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((1061129113774200202639923251890278976225460020614889180888806044773370955240506599880508953139 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((7343646379382356734407310995488100365237209595427459775375082849355742789073817225885368447371 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((8410960113520792597900150651186951276109734432248238690893257163244191616706934466355483044711313199 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((2783282025357907220498534954493792333800620127581334461262758940162751039956343039513322571561903487 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((786689730081459172008684806223264775394262196915787970301434150509306380417742292567961184997266127 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((855058904834572055232266441346715386747797206768658595712446665630992449934689613479682674957253010820387 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((11635903549493036821008328369966329376922441941066983157307717356299711722349123502997535673732221548331 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((84015532443742573046038750268833331777556670739018979932939471785308585097209302766689849990452826178627 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((86779487886675820873900718914557950571426826620989656490719397712199714335892843714322295830875918875959959431 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((30297311284936079478990416175882898260513607162499410299115455056298213637081163321473251417855520574539055703 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((8944500413266703686823879628679414429421127991349823212950198201829511887158313877810632858385227715647861799 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((8794117428607361649371106274353574345471555136580329537487988423522872543719793953714479569621685188432935779579803 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((125817681933142533196219663852370734192003064119436981348818085293298731569356139483429390841247426085159858268899 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((189856473048470355343179432758179861125619699999703495570151432873792753743877574089312642130323534886555692894399 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((890007833015563278124086716602612576773496958672901598102891888074791773330313565900158824983902771092533371262812571039 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((325605992926744421409415343529113966792923385429951328569183278131240047953838879171174038414903173267068718197697415407 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((20087637478357438804765396921919323871906050793091930166068280518196130490824291311016291472521915966679797144090525043 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((89967284472848573287532321681474100965240978091431373467759077786965982020777891286451186903256723459663246392994923042180307 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((1344633525651345962822218429898721296701542588917631007081622610176104403916580622028614781503330777073216938237954421390171 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((10594998921753387779808321974035201633311425452214187609942803849060928010930634229531753891845671639439495001963527098533363 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((9084885918621936915275685657532297171342525334653729868114708762182528118061213797911072111006755516926263693244245915446392342391 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((3462052466721217861927582242171114823413050519458762186043399374462453416295900568229142312710657468456966948901854588992663994183 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((1114409680451214782025670828840058286549039084585425056404948142347297453355142721851184966275015585591746884620837072059577579031 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((916529699295262731853041115880493421889665763349770662460346930324954937232717494148862620461259190965395290251887402685611784726510283 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((14230149513825200078305820291257535629285725236349380427651490871793230803603175654954963966794712350750847210249487629684273711949459 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((116890625139734703690882190026871549923045771274464789092113664388413912089373105420402303775431366166826166443002044591853793449918699 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((92386423461818799560511439302807446490822083272422631434995624555730114689807860793800206200132834585526600609745405661162707720259182443279 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((36481366990669088250521468425866387007254065108144692021051403356466338530583196083068934548341793547854800122142185214899662479924863474527 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((12228058936528334036519037703906340482730039096408456905960064327037946226919491866815864461007520049449406830829264534971945656809104921263 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((9305542843222878164312929913126975616767354681527485481080255902601810951201444406584898208132716241049637821416707686571634059288000808198807427 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((149358799315246107934077526196717507135929514774780880893373347907758229197571450326901332899772863177719253473167633447094441456429429251267211 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((1275945469503562688416202884137413375271691537819679142502157535613658003905081861053749457763489928435877187251803730001754118464819594526112419 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((936656479358888386001475276166050826932200722566166533185773381644018982291937348657828320258409446494860614604882158215258457449836417718237821838951 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((381517365403613540895258223364737139888635100985134324940936179382773794846084396700223147926965816894379414160863126274560637709269166306531067249463 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((132818154245235595575415102030317244717359757115461507805477105871721881322596778592246332820737675915629970671697125939487667367388925072723205476103 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((94222247451762286352352564364933994076966824507427747991473947459895903431794481383126494575730300843135721239955116297288369679371929169333626443396237563 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((1556758841888445815713361976150157830029645922761068209616542262335093782740272676628187438341598765751448208386863142983788959132928914749315123492074819 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((13793893815022735601062137620336554084091828689413010556476900902170387544555414479044646283293349956676922017550107549902858190583169633388153643787878683 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((9472993856817593425057134453418724401742374963796007177546313169659485039724270030399116949736087930804938541460026022824564063564551775322428068781501016833919 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((3964299350095199979692583593673660522355180937766935721500904016800075482819318256901506560882572866511654791483442104934921532925046198158711927447981090032847 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((1429461881022728674354960254060309629686504420301297878806934746475126354984992318689167051728376492396972805785441610185378443630153231975861450742777562128671 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((951930188661903149079736404899682108856127247572725202685531863144150608928369842282794654336277788432510859182193353619896961929913461082484631437767052248472253747 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((16130184688266222635762511308645423346809702384548957998441702795050149822212649607999553556162435208926499900637016166597562615256192632467772254638332204918539451 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((29566168565172936024361682716217970461953732105499801236222056041681000466344087426717920852440469459401567488915551745885377586441561616609365916001143311125811319 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((95615408298418171937009996700114704195093934632850983912555417832967409492183398424140548805974905916294612998585402363731661588513196525716670687333046136739899681025111 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((40968076917490084713817906571220047317581878526530175397015928058293045493168205422159052109684009509987205085272904124130499753067913403549175943256983615505596225109543 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((3051707489425537382990032407140383252100386500388182107272044496128356424834648191083209236573587082799196710729094400459375937519271216307718443600730176596526340632523 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((9600068237123616716890492829007562513747103059666236795615917326798456322010524320461131878239389093342980535439970305803056048473054194700194683403709137270456469605343449643 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((166290252688917640178828606970534753256140772295124493898093937002159743831766335213245623743864671367742379392975895152372593241952677485659677804260714849398991190555444979 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((1572036722653442878891048000636879479236271491950674131395083987869863110038191291738158453395300366235335311989249481997920824489466122435504952270901432391381901042469379147 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((963521024112756451597732522412266799566414511381336456838514667129267596499545954842221222009849397371093283579086011503214151349372692261188857657302521537850145962112192072286959 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((421406501930527010121498424527581648156656075519868578218277725791894542666751573239865180563394639684135900741670942628358463306274676110072849005761372855120918012021399583362367 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((161680927376341336024221808189129033952109133568511233629630574192506058537115980420117311211525821556096977075002973294852820440513432698693755364345618852650510414610206325853839 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((96672643172396854219583976566790091588851366826625842237611438332861885279513085179023524323184393082409531675099172367242672387030331379219819273495534897031925363642139375489510391267 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((1706962357381798962252256775732928207861642675293455405212161214107396952300716019765614606823268265194722328141927502268764702669579598025946184922033524595771716912738744223436646891 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((16601352033513027732367010016124764296346436032094920327290951674811619292404942209205698557574757857461109169488864946980088866348513345408732046280934812492105167111818193836365970691 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((9696501801683834263930913254586624624093899722357022948019252124655331142000227038434272724090618046225820612680820809133305876438197616092777375393348224562973008193890458856524711318636871 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((4317448970769810623717347397182775446858210929134409138096780961004379695191115168252928923664721372823199642424123116736473564897392417245805034116137272939977609611911848922711436515942423 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((1701989120510868874492859434389061006547048776110881612767311246707691516239640943959216165594430637399256583310423347109740641761484979686067235582324233006123171670182382954594958185416167 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((972317018836987574715930390690609791837476875375351134157680044046186719455266708856705317982477543850395775544455708463476228907557319156670502741753471607062456996389330423680188493506824914523 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((17457444981398333587665261163759778780014366703793867610179032844237326803580457770044582308275190837423217083604178348939619271646259312259042469678340475203920662825996396367168106999335979939 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((174235539205843621482725009905926264178508494623665143564343302939044927876487685661719757001593889513096747867617013222076653067542070809950473775915052338425961632672204855296247416062858183291 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((97474952239178147652564158726062590942871778233611902999924469857584829241673242314946662169135724207226149874736438536079057267345025752237386566583559405694987890011659995935141033058238020928386399 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((44083058891096520255638209851728528498721552748565090638821312918299178764972865867257886109839141944304281826519052441850940756587903078957297692136230451045104384080631538282837227209643324377255087 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((17812271459403097124705497080110411655763278548484189341847192835996332393701921472439371718286003863557255636418873762450056285978390756698522807197682665273740649583365490907179403563873920088935167 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((9769682818592156381833334609880347107672163508022442508332110669119885029620741451273229896433376812113718808524334768191379050526341833938828740897786204071656930411633543209232019048341064602940908611987 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((177977665143002768560846860156549868175080183187160871686915790422346283799656418239228508546822664927935971846623607223797952612658563571321687337930231575677598293900802312599095821278794342054474709531 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((1818605328021860663092067774151813714798542540632824804314425175101061724637069659537930603301767852461487159718605062673011338345724001868063034651305149494853061370571075649752146494729288153570597923507 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((978992078932246360056163949771016100732101050057251048512496810462432073206796689994985118543377599163328633681930147211040257335659217699062385943509773031988043593636330376743680153456333525628049097225170231 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((448792226119519198739919542280846230933219782034650158062385029208889070039501016461290135315975286636743000051916567384034427926155403871396375733537211508340682367203632137970565623660055409739646461912996103 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((185449781469802092625558639303022488555106718326771172110523649759471694644131587107775599139905994874007818944023217731446138441156346268838125773540122371572777452182691533867090289608286171594270941438182359 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((98083804495646987239802882350463691596077133078872039887970371572709816693411546484512577617697100952484694664029894517560614992357484223984577409065356927566725420306350602653921297837212549873111242305199452280203 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((1809558516572368234424669352297784970138773452401830803706394697526969309377673049429278822180724987643260584118930697455557336630818280429455723524203558502068338023971858275860121039288860364497439988862023119699 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((3777837165114450741432576226696239119230907374583246528083447280689407885530575747132296055350681019270413621560892777220828201915675113653504361226793114658535002695310275205616722894444873766103285055716221998063 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((9825218059461448647104140307832844701552983539523155374301441502261580510056147389491845742243005669178986454390158768630256375297903208522305259213078401434143725762403157519872123339625668311576095744384157640834156239 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((4557506669260519861278231624460965889357836487771928037451999907378644084505371387216858980183584772197402899956597109909188305699694124798538914268495932267056205405866826916726687069733919471597169186362670170576223007 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((384377387069830034630089583317102109502544177512576371601036011844066188551438032287214288573961901680707289174841881117285679895894704616969588789424191543604567844349533516899561066866470952019078608803108630617168611 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((984057614857657115448309949898357263762752287590525571156157383745785543063751371837719725687211276102822891464289551763071574760047645358945029608602520230012551657966079206860095986177276083703790421132512170893405893027907 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((18355562463515506126615973894776956525672068966376693093969491422197835052224671268625110587458711882206463372311736693284741089865478003333778857720288785330674356854147649138518126387555575805543836178465093228196631127371 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((195342678771761465351729638520261320797426940991471585936968612149350037613060205656946444708328835513423512893692880460758688876234713648945651728259924272178519440821486380483004160049560314784804111313081584405387954047843 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((98545847224011478471386695460078861099591924407994608921866583443604336739473953879433929339107602127166784399132242884965047548588225876125452985689461677740134874378059982695329935187187883422873835682759832643700231720754481191 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((46181795232531001031030216973492263518400531136683334894750228904532602290571354366910941752159563944241014706047759040071602469722568188339026791527838693104298858764997303784254500106475918053511729713515442004899492812125198583 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((19835660045348194243732277022809546798708656613724997886742212185626353956276315026499910884650174498261473323470969479754315367238197648083482722158280120059744438837630302956169415251103219653529767697339074571948999490705774791 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((9867362362843758985810594653000173157477078201026412263590216675641482367017637755204806996808021712825263905398049270266316882049377846839030943183692868011710922296645985201589129378228968410650591174131572614929829235945178492874683 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((185819956634835913574233377879023608562541037337650174100037951985291546162592048359582152230395466483393976115699647636786718778482405253278429484520902483788309942904453250844434868891949635937596631361024416980126355508518856224259 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((2012335794186586577203244366759226217751690501313401914251094808795199248884096245393164327669272320680113475100285566911439308821872602818856611309154651489714319190198576763512936869091588791933549016428849454347665550308501094035419 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((987901723202067788372741770084104794212956733950222141798854433635286531142779792565496060599850084491930796603072268088801561762369901543728529420614177569952188355443970248192549257976398895640672372766063132925594514098267565870578460479 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((467096846450029359789653597626796520277350359714707345075496661961738408861706349054155746159577435837953882464439261671925625733876526397665882454626101589421498341005272789942831650670591629190244565101830116903931885915331643037910698127 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((203977015378871103103115595383689713618626330580609248290659997704963037489084338465056484706639142457593454128474151423454643027872393938528540897467603041001850306959252127802405293000965553480452183285295946423121346022027197375831879903 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((98896479878430209180842895074681450594546422573801612219898909455175390365126373219276592175494125756762483750556030789183856853031045829508110354042480978688048956465110858248386995467801272468072649137110916543542252414445279485753073115671027 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((1877880817236300562158541885954227338686034771985527305455262577599613120390832723832874928927605429169175760936487533008819919783182579775430141913532748951058454084217183304141251764377207232803088250362650804063777629664548304648164051180411 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((20659053640431327241996703154280735496006824787968792050561766459988762452339786819621793501105810193687052671870317689393211507824903546375424379861934371347464278851921642933480244384867366195776672665839136354423063149919893897760113210740499 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((9899344619151254670012222988446919153080362842224166455413639228134912881374271880449875802103345692651576430339467236373827135135520783246923269723276817509073009466052156713410123017604557465630310545743298030686119469478797277733995058099701385751 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((4716807821105173890557569638518999146409708188447245329897549458360818332050220762507296867595967695067143433656009012161154501615406449957790404582550534941732258119254496491902741966576087966956291313525892455207465620306422503755941110940865957863 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((2090779531253180958639368367801333674528313852755912149983481887285812822155376891215798796921085078664363787862500361409613328114380952595367082244871191601145721303652774138626930827282850806183314208022041195920861116510188341463613364071681275063 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((990818920746643392215824895445208836709919135927792894897644274915869808648791461031474521537252470663828240940553825031365894477116257202301612201269248355455076412427015370300277550804764500112537515808883443272973015169569536093950891234448062498505963 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((18949553538384770263911727070904637436898557651000654813223731018888684032366205303655927928531131665341529837784767971366844351457101965288809711658465284917231589739918515588455883870872154827371590841011481679968997712560035738308225108693352114973619 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((211443217389566245973855999378120637665334647929682840529611446865245724702658393706534394782826539185702438462447161771563311960201677502862329749457238382651161094112579816023226484827058977919263141146176238262099331679435870628603425264750295065089803 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((99162566218063583734182036188243833622821854145381773322298827247901232856282215535063885532977409606659765340910736042585977332941205168193536953714371950246123884806705352971199216241554984348764884429475685511257687632661946095737542642167711124676224403119 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((47565408802435227820169751793917591799984790476177959154630234229451484028383209663595128456191994289760070573519682797957212506882684974568432597672634116073372637263276273873227308632917438785318527388566673258556611990844277229390529422332610125811524232447 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((21369038510820695610374308663466423391688605331060044448851330403441258123819401017996477135096509735975611203942880403056006774643128664131216957515489717790476307538008499197944036580438951849629742971328461671044074296855802786434346622868064473625427180111 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((9923615152448233663145946066838284796238449782162707690046842929762815152520069725599782191119468462452257176040490966652394750469566147006437086159149008697799697904874015360561994111040954787403891403465765702538347462037994089230508477020043434815092456481693347 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((190974287094608928602546613238118600177978529714311086750625597217349269399495250792084256419744070259797482266587434631982513615468260531594187690699859237504736712206224905344435089846618041215375984723614724874831423358323165623310545765376980789966976308628651 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((86329433208855900998810914382249917095889977132173046942019839491938323240201985564240868849503217732698336817528973663502584466317259207285916157205697752485745393273853946325150629583793515620330768051292854079411262777500382187744186254047451907624092727058491 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((993032708900260737116531178594520471119297719980407056532242684152455658506813119881132932998580076865657733798181302541264882374580536966898145939834458530352403844997273563082941168850378609023471146584322887025630287054871554860982369714429221819789028233064695259911 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((479092404361637223289075794569692576250199677732777687541330266244821732583905839435125062095974654461167976420589022479656680057657951968151178940226793664670747068995235144403558243491624826037440434096269357365501512839532306494115516286533980007822130921372729961943 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((8713879164856798502348254060813913036482009218130699997679427121867547844699662921257546415177261381426290855095626170750953332785168227143713404128388496482638953072870381311610440356149989595111339953585612632809169597142919909888544809028674688913691609491936165311 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((99364492476919482614610158393141995732204502932572868847475451949597937979381945103717778217599484551147238872933511148696393716032614518361680585610120465929033811913736313509484312834349584064857873693395843494268815373135999133534784888762232609848416632222530048742262043 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((1922529332281832989871867154510860023919875185842755933378349206107205613630225252453583893668558672386333463684315985728812471305179424407092827258283337452173676675791463124375227744733333018579994553993609199756804366078916861021889591499242936667789152592643747885767779 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((21976475645540961516491214353501420000243955484481916430956436828628102151751046685155828806911849549403489461108269714787563062258828137819140093415666004112938337298615186631345097971673123892997948599490704761001889155606464883028984513486994707423314859154143211253860667 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((9942033452297256767726436377513660856721569325988769086184778398678676716913365358745409704561901784363793099316884352406044160020482868063323971255255918058784961086087630364140592626559528611307881233195715072642741456629853888967108334058669523042103626274913633335927947728159 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((4820632166992418669241441128427270016655203240753972417402920780343900241674853677017669234808900764533592928989233533041339426559217290751625174470801762559316818242809334803005773970049493427977343532130251279106918885646043452283027687929789920715645021314056093904451112697967 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((2215810900782640633322466606788483711204787681032318927418823822716088588523728052676985346348732047954601095654076892262854381649078987611242029287317795971972571635574419532352035106393080285561103888579215603765587181545964891888081538839380274946498235822882321472004641510079 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((994712697284389681554631441302153547724144502931413594658172192078678139379818794467245055382204747457174659967990972436012505967948303844659969390105658053895952655545311028404355875246374283223225770923480758920962376483578862774356852474493423205239398063413697237469995896128566867 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((19335692617322577935278855140076786263366970107406320164285423996858868249744126896983229130724322219260600011935912771695875757884875218138859311363368247213368421107616232715629985818976739072585604729821993280478128558004477501294840872610430774984107494301632999129161517471312091 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((223300126883086583514320629154571858284450197699160062173858324254783763074961275136880418492463643434111292235220380634976010065858519876447477519876937905146584595257209683902758739542654696450553233759142033272851933199763117489939988596637326284315107523272412068994656596354137971 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((99517729257401036023642597655493331548562392545883028209555860156072469127251411699740823236577041629811272259660360568806008706854468638582969787979707388070011529570254454833846512448847537495640092243243450463457741246196678810237411584755968610819501215558153566121350735673574969639671 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((48462645668808739246187191146106216260919487781738290645209158476836882382498771657320384250111229332819125279601094109528224909879888420588919718297561306751793514910167504605075367793452665140939657141211675259545411631801039443925890021807588694871483084930361814757695468257985957978823 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((22492596808814650923732428716589062707372514945266542808042704771767580879330102182972514948826740159913268409065780302898784903976125978700595428089889520419869821194701652513202514897538942686869228578477990744880549186802349968573456785848289278597103107469532534612485003279479128965527 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((9956010638755320698824512259950513250539021511287628652078218672415838126503983015368459709877901698179975576620400468562502472178316647931068423270993049988029961646691619588759641939996730437589819733782964847123370952289337664318185022880346164898679164374705861226626764652993793705743310923 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((194308822001935898613975734332038396755641582312763326138263386043803524513067080405031822675642953416023724434177362982654631668402411404465009714100984431759535254216465779628745936691927565110862983677201261904347942949807579257984444318442401035723420674398924974625251327131041747684126739 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((2264626541495627026238196864336335504186496423947890081827968323713018391369752847157839185766184808879741089317811898842864255293030823400886116650687431875052348182139422249258395713368712420478184960578224985256731798968204621137801975517869481658106197235444793779757614143195916303063791211 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((995987598392789066901880236766866165121415769109078472242010559767065843032807802780803315517093047596090112270276587938991537994800796407736544091817089068558176891679682697549533220272921773403880227377545572600664034671167356375454610491985014738903222620110045720064307084293522905281964619219599 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((486835131796171771904286917006153426180076884228283289448942818276536011222526630542000998926874520587046181244797468776196736728428496978553371751356366857098673221638766602025622284750583069069621696353112457602542355617925546646531507440054403783152725115360695164180142710099580269445188735486687 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((227914151886488219365305471796960959114228890805940084094725895899515376964630494760348826462908594825730178141256112497821961674590032322779852114275273919692156822189758068091379577378159259431254885497970955514857023254919461990690135178239941941337822051381839527121988260886827959095305235868207 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((99634016812201469159321202036216163519219696547746374688610509188033376740551498115045412818260608150382167410508738415679235155119765042738873396246912145210396988820778897891585573620754013717488127179788064313624368594461188077074341386805429149379579644848097600264225642079665104759483838812877283587 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((1951285339284013838279120507775509608843988208148471160063278794533449592617198014958330596617670768923337047230423163627122020801440934435386810557555553280831513276614630352573246640912747802367863992308952469811412023682128689248569568200572853512439282708991119383758173709743640569664131886270750731 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((22928434361683322113825021306204746945061093895055893802318280435955633428441990343708022132269531827977371574633949742048459049781902054757484228210806306208495437190884434617697569909260580990490716147950432196791030623440580984626316834496309997573990426132850166902006744474895055617724504934333156387 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((9966617575491332606429164801329384923078586181209590074472230374568088392635923797567637239392004851220808636014733557109350076203939128843340859091869597501075940541309705613385194926669835853213244544450008710238619532606588348074181900914683609002359598145529526412900813491012493200426799389638975667821031 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((4887359572788350030345069985043814400627323164825264427091185376783377785870722206161169025465396193331270095277534026123278981657998203348831392139212088474363804626667595254814974406802309865604060465679201582525604657391679379344543988995808753208633109708509953927121678905541284138225198859119459169656503 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((2305770181137176439324402430412736565042699038956287742214929805928670298348013674415632286283292238698878807779561125386327929144256942347551135108499474235278722474429408116819075290722848897721704440029788824026279677010373410665240018313310897990626844984398680829041423080404311752156646288959440389558919 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((996955088913290921030223409023657186988767081346670339462835549155479046557500517347536895516662938494403618116811891944615148500789899759187649780346701596865639764594482178113703784846335737679139674632918644486995203427644742992890353728131036027932226025648184692699921900955722542290529652727139887588959700603 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((19583358257625110570165109969345550414602892267462637369663177093741706732904197000780635186413988688560399911529586579132663060506065568961795625060872966434288309545132756308999674930154647064141867512566878526269745259669151579597885157799116177127473544458091175884915007488149550082462864195914510812013090499 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((46359172640995799469157207725038901315758934170939189331822675829615037634752868803220815281137814568519614485166354834781439299319089087777188500124841457840938510171835561235297582711307151702042072671966400113812870979326698408077630087370105392610094830853931605628204981987880960511384268550513878972736452127 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((99722264525048004779929767807274842996806411790873841673423618945118710273649294688820882850761376608890037219288763099944181540202549126734783099414763692754905599847956502912285263327188821640927367142292408319592293490245759942610507834604016189215782132477447870375237976351874320249946081214200610566651781171101439 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((49036997174948340824967351120112517781704083354631659927417134047210098636362904960787872162884934445870349006829696043675550089271339301978230543674334608508614033988577825011110166174804906016336641376718411995283094737995742026768142642006686771689801088304552022557556502696190570029818841181100197029374046818710607 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((4658889197000685889255107475402686258157866861540745350550326671865589071122859258571464097102902531769127131741981454914281759726408318166154932384100785173061236663684581683979546052709949490343773991611966148213338965729770384428388186586405019734752992935107637563455619658429868431210829674010677351304029683376979 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((9974666914123203659991733911004960254267703238680975720557988554841112920190373116451419187466497444626686964882985948635208630826495113496859770846918840707253204478931656500138275723862873988333907939149917440054971866125786501645332251117736128666939135649665452600536581536983512372958331905790880291616008915959675555507 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((196439336935953111176327332270081795088743807219152115546322389845209863703494855010609739337217236687564713225305831794888153418572355921519218373550141293565848016487794058801288541898816489803701557463447761067131033097542553913225330146069149080837207522217496544783205700651562294649714277305480346387433243083295744571 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((2340262775400979353286901262963075639408287638503004443453600715657675580382598155671180657188262528321986910180492993781481024745384223878756880502493863524732607699869594586098812710612184956879787241360368952624278029616489822942592041662976820889394992718969227665480548181923384458591977732890088614170693682871942970323 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((997689293237919775438826025224495439672520015509807838399255810052722432789324503070883298346381631416733998127871797332863284843577098787389070278260008217430686540136793184347112543600704325097900744853681419459734148824931364174575690621202065504097519380012934928052743211732877114074648328122903564039171021251429886444459991 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((491773123937394374999912278762860834460610554454539860644991794000568417867771208113528947825899395480599689373951170859158832988219609669480997961611983872186597832568906039785187691838247761241573573720174105027647901657364208046706911887088170165261241843945657135429936105881873188797534192384744883442930876048610972944322983 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((235044670879103499761545254966777187752167289803746721039097114458934580951482007174593282023875462829947682399439764066647641926755497637665070390186297446048361042757001030304012315991099756750139094057668345863025734617349458882656144049967282190624516827263650663225462383139980918515589058871049199512180465047599162442066551 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((99789233504110376477101638238801902538849568174696102363911320202338971262012655898604478292068507746414558171237570250122458800437197911694119267290930129536505211385497316723853176439451043605154820640338843313180730916768464520455572468631704000825247035209119833592474866571790920206090897953074402786704906361406674232258529159083 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((1969592420447964540056247014481878589560441812548904144560202133972111941606311354124630369483892044801319056817408084411062415543833730249227961509444106002764033417340444059221086827741194192916478140759477198204920128581840305289653819132232947842726090684722046209085156301482036304170267320326128956556542450610141687349937619059 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((23600287721360178988386600893134424017344512513223770227556389885993906107256683706703957196303184371132460650241217995870355216301827130774259676902526604507853265201935723714385115160613852881782693714754611115682328096610703806019097247512160003022001630715404780642424489423698938115014433380950774765863707095928046735984634184139 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((9980775355610419769605871728675837936276085661918555584919443249615944585721960382479410278454444797073711094473092495224419834564278133119355700727407609905413249846105366750332819782571648040356986655067226915125154009111201954304314131581303617027273257822529447381470410004612765204758169074993775501383714623942986976746997220187437679 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((4929768228676597338667501897732191006856901154653562067006052797403277634524697818033672033144914900435852128998412717712322943584306240496279298720257210028021186888902251675770525121449502787057478659107543857169868868965642992486278711232198999760611663623604879957460671904273378915409963414443899984354637053274099505987225771070401727 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((2369040151903625519502013199544805899450850258971845526854783945537545535298691046917464685998123867290603100599193073064845442585712196244926519713543967930800275954119550002693225435566588484871521847024863101999520945148303788091187448946336965108416877527672398667873383947249470557144156058087263625681251293510147999455815579960022543 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((998246462511293218445060377987709205681550601480577210567257177127219153497457172367094449728665273275484410060174185766905006370111501356215791530449030322302458758212808817398107490827707732705081823768646968609310672633060063857959404883925446819908675665766378484006060507750744152621606875837407244807712761993711671110023857444956753014627 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((19740503102362336461979806206803220976299713824021844891286592193477218193713833816710484956241876948472075244409195836339499817278882822655049850858020080349859543609441867317452533669630547430562855742012159553810305655956333916684196160832300235992816040222913027786429900557910143125057177357197292172574082318951100744602098258333129973611 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((237751084130360193248414218182982147465039057510805472693235561354818809955863912876980712419428346934971990414867624726308195324697744510833049611170911815621440381391505467500749767668806692273864672813076806409313978933568846313765695845781057793155642330730381171892692136544140296357572182895778720675217371557390357643348610582675680296579 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((99840054585042588334029292257392919777831275012847889107471228897305040647963561063119786043100745571276759494818668006356706346036980373204510992866847402788174170712864930661333578560867705423228628391409595947761054382879307604676051197677491780784330033501548680661644797093468626393074627965757427020645904159732422656958606109126840312723172551 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((49400844713276287645983799145942567745942634898579656292983417404269435563688776204664221112874021502019648693826687497713490281718960621465108945371024929115601958115640889873922433861739139592448032958066463185395920967572775235007439870526920402336603834237051562497485846250255650099596440840245991340710245004255718026620607461703383757929786263 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((23854696411725375057549156048693604364564601445508861816025626516802388033147001816592406531120748319168369102826268315319313944503980364929379100927102431312332481128665511720198918977376190408461482791084501152593074464883779157101194935561041159110961018197669325136787443815772040758289687005681350586959287770100942638242862843027232901031410023 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((9985410898865489609711813834673580391695324087746894509159773201409884672622700295250345044349348305792867063800895164863814255941071090781103061192363752150517730633232548920412219701272426014768952881465643475183129053425570284545316657893757057800681095345776759809190606877286553819191516040640632190834174856121673467809165339031786485444418737894363 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((197786920278519845289250021609113426934154355476243737957874786316208050379213887708301042384651349713863488577369287183465899456208052177727719830215678930438297894644728197251157999974573513351679795575395756856008761862552519851152468148780478155883817326190457526409584522968873737376416300834367485304242464222392693698555515912801415099292754992419 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((2392944167073676556103898572136926567951758700592302362031221886034205933633687681652608157287819959289451691729868404213535211363787945013946374028311071005056698697564422471789637087050593527875193551842540994888954429123439169283157009503474095404798880684429461872796206907713290497397321118884970317942981164371748150747132326869315858550117126012923 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((998669284318217903770643675302081288267705596015657488863990393020199810643934362030669722530237107016284783490471050672723089727152917403416753520539074924905173764249040484677559795612161794085120499177125738301878750350106542364231968316463262513173524749774335592475702825097938433509915752614953984022557591151426202019277398069106340696841766339558532319 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((494891811422847251991781767083672507405186120991886817828871569530984237585067123386314765397719428728679263197189629689011153352674554465812054306462098487168540668458322431624553238701974616163409840889302378179521016009937915454174786845710661179588223637587349727160576898862940972494728879800156171033930006775245743627941650174251529561222039668227712047 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((239996086176539982115873497770413305628168929084633494878386466592933365687557890679389622492116600988384064022063135466507692180770221207695849197411970984803149726578244228964608576176897216075685219989261568414734431634516451180747228219092228809563540280064849398477946664295945314460394178674468412063304235141426137754757997802527308630240144549377575551 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((99878621430517609656631721555328740546762230529376166531751155718551485328265184963903477401150517242276383956516335945011091183282799055117852338868930641125375614558447729728894261637172113723886096091443169967729266455684268048668690526049563563614096713001166472396486281785658258335739945543267797744649545561695038164784349310077396653981028033130152408412947 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((1981137875213272244113491354081666013317062727626223061208222542733593921198617401918270245881920653506752857993063703785295923817632259048722285139718399775216578691288563976541906363334382117070036616040572081486299882371803242373640919456765058059973417964759630592422505681530048594889791674045892740767632370917724194693344141410099954295978693827579353597851 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((4813090024540659971239788686497833315579730676375301301617850106660482165739512809671728342783771146971020341689540105798702904249768752384078494502945222426284503317648645445244109556652465968143544822310178061799864725282740874186255440396016234898006363853154059861673832625324460582858532207231755900062775476780500102218224549558802403696198450140851360383191 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((9988928696541802729610349218226200411491823333275988277860618166556236631247052316112527884191142129219755809825724550552296660100773950214464665385251770568968885930719692771761632286711380009096822482788805862266489581222329141523217268952558841327932603482975397446700703220515246717577847652838085635682718999318889516124474853620089580999571509985900591628570134711 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((4956475902606265425019508048072818632126394106105856947550407943137276239773312842197323270512875401068184441712937522652882687115501489009556313433137023510840378507114982248409815439531887134454319608415353170398747375387126960038713280922553426959193111587337590743180584452701881093769214534089992249080078896777169699566048005081920316652192405046146869309959134343 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((482544154170012894531849207706949891279119908886626615795482128505081632882028918250678280267615182139403860786458597659957467593968003768518882606039570409858358197627506637141036936501425275464564292122856892610239063987230216212813014572778855963607168811512594443049485192823234899358639460113705331468783575249691066400167225191335703215922492351860657532996975787 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((998990153197667452375948783242066418133403681698102718788500564826094011845937382909572005900726647032521586681633813429526635257771894320911965523784969748907358992398735336790693765767805104769748469122615349114913314172032307985757216752969749594044716561492634927305911242852857198850428217958320305087527848084873869434261724823249230951713916140343950664216767697394443 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((19839333285736423797511061034950234870411548272422748930098254423611695449747818780211745788269416175247997239962187489158907618552346673083475680061162596457580163695738653363518009926943339328452941707752166353009849027778509616297611089078526921131283864532645509145871953896346630380606625765384134953388803505839620676943764904697007830603370821257781424577645841210579 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((241851117925850664369723393429338615479302181224495059596963961694624882787515870677511638461178072568281980833005164311988301898369956877661821229719929095411941882683534906830979020454006064056656688342106845880665132407855118888373374160815093930504457976080000486580500848437248312030027611340571702885471110079419997878242589048919732762135669476800529325596060948134187 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((99907888843618841333567416365858604197202150018729043288855502019482513102503486507330791374222979655777391485991865024347412981767147796693343111320998445707086935773665846274689550456978807021363067114081113838818588125573582908304873011688629769721600731723427709624354082194337663678744109044632269987948677607365600252707314706303032102798681432909192771935204031982439329359 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((49629370011838089127766901324850024283142949959688981863466810740098743953094963686118977932830723987435661001281963218712686609265819686295005224292998396777069691458183189401403796274928148254488195284105411954565898362084823110012131693395790103060336093948361701362664298309635563930641572745756530193702538190670845132818689968043654047912236065611726673668857650865756113567 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((24239381957098129684302758459641494061632861240183321811031033333453895619486412082447208601356979203430244431783239451874307896818772507590303922698485114039594614493483136906860361609307166223843775757807064862021957871908719197962372120314175854504625982949649016980541822451935324612578894086460009887420945404367717940861713330724022618147719292322543257260203532461547470319 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((9991598265093005374558684748979060864639399709658332225506376905703058467618650514793163473617000643342423209611775984465800580305926851979789905212922231228280520672723382836253257965832407924839589440676680636580159878697943217815212382015154987185616367542689011677966208899192121317129286418288043242410762730600638495850192296306018467192576129539946200306525765369214238548822467 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((198632223592765421636740826859868283425892556206317224277232554564518996866080239457194921335816232289659600847018575299475086185612787214224525978637032479142833775275789011475945039979375567976122250082669680266235030696451452289069007330879962893103444505200255058738128938068791016593660690900675472263802239715395366860589241542157947567121705498612877995367282711422178328857291 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((2429022724055292214136010003652350138953783592249457593791870897404820381992346942789012194002083907443586128854888670375257018616138596530684914287190059881435395213008621240668007660766567374434629620593669462378872428380995492847789377185196895713774339056813714044301767152593607619341422252673365528283039741217544367566761301624248257153306557300645908589297356385435366755073251 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((999233652553928299229621312008627078646353565717065457285113156699893072006899969405828819919027479681192448218318922871079068331444505949632576624186275477025151132121117918643168418837471424048393471652442070904386123015675494726578967000748331846161625732671292822182331812322010961699313602071307288270012900946276039121983589922960862448036446503727112768559134636622138340753743682471 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((496845641912538024931389009360721281302621937538987440093539533026568835176046986359791074860305510042678881473672122111623067935692713459477097522748632211388246936395051575357655690316009298815847559789258586543810673212713893418928144673566949319900643927747784034222065433431208150468176714279599298151031654929896032356787910694031366009372716833050701854496343020633273240529455535223 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((243378464471739308780385886800299491978780299983537948517281801214733471841966546452565538564192271432572343082243738074958690477439999404421752663738746402044718059731884720584581942662523330860371811050443028456795083332258785310625073787835883307674699328809249977320732491597888145352587400225461471087682021321432082790044690238039618876087502791600740015355726160353424055006496930887 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((99930099150401461957631448732242901724569847789750691555347026362067346776965366909413864151274253504160606779337523911839735059716047721183836211621902745085895110214163528713199320987422281001726113729834198613401771438628808900495447317039257592683940367954146632189717031597327585849479491585730151684972686734012676356433489187643029146472748394944461136958584347610215104475171222509227323 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((1988362236746664023323639257964327860265914299073315410782006637968995825500691453413425260865494133568875264863185972644283220884410896647371100818843598439501980402739556471809550771337233036860805839869621311113334034760947758522123199196320684493158829034160717244359026132844270554109167697388397524996381389440031036743581799942354057572172346761381527751354337536248147379237480753393539 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((24382428469784204399209346244853929629845856049084071960505794758781940442700305940432696386396585897214757917295660758000646478512211326483325110284777805245325250973207807809437139552507396979360445405689221054115452751662358081505446447959187143138881885729626304079739922549379187923551445479755067925824677310839602098290699828837092342377306965173157712774878048038317278152401937223671131 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((9993624133805568549541437333214071795003189526446529828837868315563248901567342011908366790830178484875001426163713568570637754001879860792341252370668615087519750687964497944517049665225748517010444011639366758124215778231649546240891236129101802801480252782201576761920659603087041088088572866009204325641413675069498248499367849272483617537218799348069133685403354098570550324493792718734151812799 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((4973168063803108702746513422811382792659906140685947792925810737757215541514760813274566706459985331345030893744336509121373463785501868884102479540342691254081558928899974810461184484859540012404247245926997772765466359909238695591134258822371135296203961796293356603402798070687325408211348514050368919638897308280904751109539689878816560708122462043786144585944087194075880831326962143289820598287 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((2442415262267055349417401469396983053278884811336726688069771445129704068459634178457573623670801027967913256142267496348732123101335502751991206066742660819378321814212222676747068637349160143179654449233037184080518481237259591048931069520068945962208472104433098370087814231472476318952007174194414718828004467009147235268623977145078576626085797567579027690314303054586093792650526087415458865247 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((999418438116807324109323123474455130637625926275767325277788482667470622058661966932197860091993070140903505084670805730033581455773467742451822652485796387977939019501305751013233651114236199482073629633661560108784093779843450061270412321043762738931418297022952421185069124376378278767822996827297554154730265544114143740372839635691048206422338344935429890846696137392915606748052315253898189300835187 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((19901030883188232119208050729032170456263258324583183520493491942475891203663788384414364917719349660029533505509546204161451837621929139042156249363308201207053314134659784803523333699175918772298605580825253306599854153042067092492699187008779932098091472092729749695613330900241583737265054269310176214685222537905438067230662549386711216526833190366190000579985291941917148409174663717226913689671931 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((244631889812735237121025995568571269663773822406769881634755662131063217766870899010409636956924238490824599775897612535950467142632079860475871184545168798267952982134023632345044245356618444287358027480733538932998821630989984635019876449324583298680774041162150456444382285643861177167188827097499814853682830426781198356711354894074143584156426637627130295229719416372798799719241104892165778297477267 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((99946953995948346453983690061475475830849773613391565040562920869547997849836733989786563412570963906762231409288078203053553065325465313192258099601186945936631751785772601467170081019082826463358381979775171882202523545940860610438658119039364730706151457126354559193553710041742591941249439009608291807115411711075283392990627821690287580052400747456595366633799694780020011238310095831253815540697079911831 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((49771874512368311976520206896634385300634447852853920212783240116407232526587184149372940709474801219642960924700691567115175206985320558287920804412782290199409368105772652670197333171380687443518420418330943982527114517903651212966240034199052291791493306927480162793004382248814797030288931755451184993888109468452829028310749061529902940049659495650334985509467029831365571148149160525852973742967205036903 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((24499698725928789629796481212311923116244632661654283149014114193537009138788241917355140288552172582992314878791545270907052877417908285876383580573918151516052344636328402098008163785616510244493820952740300735256657465081631341340812919558122625672873378519868279008005660655069861596289624726264319839008784147241330875071827979997083999064670061845069292287805556562660381150509028578340259971021129191479 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((9995161514832436525107214321577362576959300400598284822044865701274081527877158017410401808550835330827503413535393477135123735747531667612205438038923064899717991975635676297624984599993601850202308095521232752891338780195903718859941323011937575181900192858866178407721614554037467038737185080383401120602418048402309824124854135499836201039319629377758433176768771559969965285079978771056154276913602749997841003 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((199158768560184631975347561099705758418918507390377856014079731312577949363486776357040113787091716731562956176608338488825890128594760958145600996560628170130101301055991027544158154983709329554704277285780479995303590609225812596558272169027558310771463845406572295904487173569636601626543234706955998716338833588573539087699603611649535705482344713819461314966751768988794265066786643413444776129228669668181299 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((490676689744655178171149922910601376753319365552697846770142763237124877529040495285201664796032460720069530661329441204302142730167897340827440401395922293779510767879275828841644448461740712944290721104463147417250945377277582209881800416776637375803418371188153378062019680358998262183560311744609342330342067234381451341880636483078962522962579497839807424901452990438010025069275040724479814089680051682336591 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((999558667252411032764604339914035972732188667439771353473178335210312798402259214242054980163347343030769068858803845229926041308739605997912094619844289518697977202073656942135267720319216405562503128316778203089477684158008965908371827895887862045066662291235760731103511628317419481004334862737011166413508357448919885987900320261346559405399461354433479965352609960299540443548000103644345000060120447635553071406639 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((498061410221133322507864639211334773952219372738284473377504673181860941768543698935448836918457518343995292858712137608418756685842232400840067781905500654926861176711990404883718450062994474097692782622266330468323474247641786731828210893212008912892521629117178233364843307638171863781152979929102318426414104045928331370629512035903650521972291162250557826083116820637418846395228525860708462786999810159509048878207 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((49131481381839534795933673634874241439852104423305439835890846245574187876488629954798355480261702665346862070870275757977199977958867100754738175891062147564552348868242664862450165645034264509938621723954389150347663516994223278738199713168855717329486719218512653128899482200908120290116197910112269657156150061360214213371245324869840872930947078633913522223056637850117279192015902148745091140618720327783634110147 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((99959744716094167531557855656578963180821124923183864464349015489538261280665269708660560905639401199865539077818075134957244005894065681887555886559857179868998594532744470662984174573476686000572597843158290238400528005104471807400319537867619560716665467570487443566144606153716783120848395834830999522075337807988329560614351911998203723044701068521941008079707612308801982477343733453711640490483766390181702302213763107 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((1992852961166694412009949712714553025061430567159353550921522243195967177185742566003561113140090247845130696114918803229188554941522796361206232210366446643502755193895278372692211576029332781754982830937715443904228257826310487295840738756756864755770305496742041151230090539857828005303024948589267115870802239384067820823594363658077561395859929066333076020331291160700481843804817413300730617594165958074506917455241771 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((24595553900423466507496781620186916356793845125317331619452599777985814077657477025292386821800750465453868399666029329335190007748168038174329467481145444875520405677523974670134561833491440687312827574403445032959489940381465968249607675196599991902025394566059063035922915558449011775486779187714976777554668685247556536923559145215580399947250542558109337597952739328858710910733283214197970689861171073701928750738900803 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((9996328194789097303055986688003536968612237267618369829386666749847253426193321245936055741886086701643335415905020087284855097509615413042009635080784252947390968803115221402582775515370528960170228367067997127515227360929594186968405346007519182991649207293506871189998747961098968938801944729282439959407057787480039504212316880949092156190076318563091805169974370441522755227705953959513399864058495783747643612091823974278791 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((4983533653047375026013230056908524510062301885120074207295653567804038571764426421892986973543943193253650930165583772520858237401523405295268172981743659100716059013887231991143911859789844351695223930717516866993423344253609576988487847701423743460445259443543932898829730859456257380096888070276487407313402761441760195376367555594061728551369105360424854218840257058587029106690751083914981853355431690427917932699851377367383 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((2462340315555294618923220800571619914361702051221108168630593070777817256847005830558947981423151484062396364703650220507599197093503225624052481417956414238683158102420021457101978999726587255001193715585610969759972638728416851681578740500425163095666163519183653300662949080530122360362777445505871997621265584080492641524512086121268859015198879624285510007450667013675803535738604768107113619007839561639096380480727509654311 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((999665083631297932303645713772866617518027997891274367247846034253817526763371410805565452384655626316993553290944597221513488009144550669800824844623574064090372437438548689793782703083492058044007040045373221992046433272471074575949156825383847238217299144862642241853355797775720253814941784592039196017395961969416843297718059662009542842565431245095292824968872251082615072584743178509095741800367575922973816789731540165891363483 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((19939306766875112924144899344887301650023881637476871246461842036629071086781477122335996352224302660718049011945569265450330132555706687350395110511348042588559922518598160246186983118583366330569289725045750077413769944671817318785516495846576742839248343536894354988468815673993907160998332160849769888244968436057121500000585895999195741456154305383894129893761290278239992111014994434357891588594494265246827668104704856236133859 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((246494103059468118290231118243188784443006794423764270790741618634373423217313745883759925318588020561084060859515876092683430556515272982339662367430067864392898323715181674241195556081486469530560016050056174260502563450016637753708208940492350240478826400216840841674964344747224215978039665869758100900067739978757008490025739023157270504012060340896833094092272802242609683547469116910000996545970322758144273581984724471692764859 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((99969451273261578299212436490364482783671887771656808859777780322393458068667396493808041608361593643251932976326929546365909781778101900244542636552650061107875141136082341642160301696354561090368014143658627697560531318081904125296050441513736858139514506900356186806170142382516771511222284997993671186334737879116418527714757375950876431298920680158876944443885744637998568615672179541350149896836927702662210750841782973151448937374879 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((49860197091613431672622243261127702408299093168573204843117092718947104111096663700009646220624590191604264112667233809546442992113493095215767821599279330250672847217052083769271169641333372440180406857826020981912705581035354938929250693870511946713471182258907095803219833632186721916881476657296889271005568070138835785108951391923387224386945110357240015727914115086156930026360703171455046908002106473214403893387851278598034806585327 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((24673690338177760699868956956412000617179773717159455804778459436943346635648939387345391508905100966832371620669873060961832117787137011901083200573401021658756554426765523540373376243525966930714554465529650197738220923868035749196377678311814198287696733048806048676124192007430930870601342765488766322655838199916856905680291147689574243224116091684122802523653051741529347100018761145885198920373723317231091554914758721281142718149183 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((9997213558988008341406063969595615568147063899316132506526910676546474490817359236389712899223486040981938562569708224712673728925326008627005467507876870023832615248445478628206367598629588580735737674085534408177588743116204720980628648921792480041479536717902188867151197197136502279853118281521996729919150446167845883168446164532607291928068451999331642733560150425665763439141306512505171222540186686542928229216531550330063111924774838227 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((199484811697688262905752347880873770254656320139856877530383936707572503847249411253056684185277150934262328674454362808450551654909107593729618402542386516973901533867249997131640189601576948154002500178958528021945842162917958450894063946226912530496478980923166506284383693310629902267793618097545322107832912123912480052642949585393869963978904825440351661251425506601582149191029991356376451944856416553169431881479725488716412075687646811 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((2469635169556800775482771547031354117205616224315615302276948351915656619065964769319523207383746878395071904797383474187788271103860510266685024734319599296833288326504951815163927023757366370150957432091347158045283941824253108443368540726475398236829838732597367465767262036602051644176458854536081869194525127282764024570023157806586415305362781592776646553162911977427025814118398250895846356265570673550555219134020149349556248282216380659 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((999745840355973204844671312858724882817398139448322394317839103539833577730923788028814882676871832256085562107670796300717108836465761224895049707795972945483844334656457442114587407773800663214648840466363849973102402025858381214806080954103457482023472982650012353139462149942411782452242477812465887726115469646307726541443480005512708918634907712215037128656222000776251280574395990925134182721558048239640112571527492300256046627994487319199351 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((498813546816784444436028285119548391294516361785818806281963929233051985667995681181884977394124475651829746673510756203604534957241617293612223981231533880144686617543036676020908512529818095628650622814639409838152436237228681869523514436233845971931298494229352398751365796653737282338085975011256369899369324197618448621697277853661490964436257531804879982814663605551352805751382335279510104437330101113333993574394221295967687832691511474734663 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((247174965899439183139073410402611833801581543208510810731340331065104161069816359008887811816885626177714175745449418005170729064446215498348819817850913461560608002374828860807091865286003246383015007631581833004948641617530923331776884624166368415872480273958528032696042430299208070439448842056544614819374140620240565241668180967410418576338051406151227502856188614528012315198540459643262834058489966360927107873802017528370192329965002475080983 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((99976817336389383933497004459782872736423336493499830552913058151178840125570751477472291893605510435574332376526976342977309648300551478606352168997194080276417893297019452667597861225271679893797764685458445847596589395984620525746107062066638667307807041166455576766909761082697205912816393128708451017162170332848666661024684141742830718595445837154270181616119977356804208055032381520254264208581474254082293587986737155183254781079261171846130402763 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((1995628696937789964635432522383639028174431318053638027150677068611440387898350980288093251030090883044469818608175392235434620788816100582923551489431179841113721181732207795844896942967828094577783252121960789307871676272420371327109227790885321804250510417650665118539811679805740631966442126537177598025120423714813074273512239273593980000455430651786988722595288345228107155470630893305954723766498067714588927187300239610313513130117248340932131219 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((24737221304708045273287019231066184334150244444705795832850445863837882256113471835110980415955563511518215339856903875851102442949096604080947530007987121199147516875416827680232503340071894111351421227928154612471923682869667577952868766401971842877731454780606840766718905486349271168053037263133462074749098450851646333020234984186398706827973264320603966259433864950534086726744703921599281629948624030214659925596787585828164685716933344840185048043 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((9997885439704084876726062267790175170907381791581600044222858773143475544373684954514680160491439423360041579060155093171989344950438202018121200390741063644252905301301035336169603715940705738152975510254721221096827708575945192014879663452284312761147003645915912523640140037636060242925721666448883942628413042570125432152044514620788818335246401144352446075751151494646182229323668615606952201257342011137608245041034256135730218346582649267601092427221519 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((4989935137565574906504505752846213041783192419374919496991073377188962510554633952404528981637971377617301914870834836133784003844591471017473390256786731057631716929706317138458427326625304172398189242893595609072634272349515685376320332704089668928810325082261315532141132043085712140211855569720317249823990332368102994898116148138845929065511224381339856580792426083131835408070529431326939706737758955953723549871530002572639814976782969949789423904471647 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((2475561648873997169546490655052788017907374883930245420763783394994037899084886643979714298586890371141361350022773247587547840635770003333125818081383031535703724280948614501231320459262004819727498866758560048980952630213960276263701814422934613066744330019099638046946314557273111454538543676910967364800102491786431757391156926262150773852402012423251066351271224476559663552184118646838809060057480337873198039868271343870216534442376780592785426546114991 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((999807124611728693860814317631945247863975015355532484833699617274735834828956925756147521478905664122939472550813926513496664120964319720678889051240664638183240251247571336118038063742099592494147355216863886739904945782337688799253218742473209019882501643554928129018788093252897962937983850361802051058965438851948851042884436312106010486812829987579819663907489781281162219683299785435356931133285936861894660854927857604908360406046843187645698443564156412547 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((19962924910752211627880648904093250295811164298882220071204841765192848752710754167324081706131696701527060036052874827534201530952665363824519471484635069476791046690893462325067225230822318304842469061619263039612254687204946028551594696110634671079188618570416338559320626325523737613579277659635247170837182556578335580223277960269709534947743523348343898593077739401812234349676275825239743972919351051594817483528989938895631305911481513347049307576613447051 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((49545534881510721096408118403549935344022407294013360460974315021648901658103472734830865691527259106335928110518054787490245552205462950856126147895956097080299494002441962119219485212720020502765169991158130036338714905015511303685908871328587488677391887947934791394450318033705429673247781687430337767375831326993867800349484594107149801294633271413910907389021819318698325882494458728030651619406835877511196815470728666253035011043671203321524903806159003527 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((99982407257209609353126456354162621893416753075624184539136243190480479702253648068995483876655422341645678109777390679075571224465518494682283507030814743642607893037044724281334605908108130130168662711395805701206949819644367608446283841157208814330542622413575659432190718349876581893462320943051050483241414574002810550174618089336125534533658661657118091003993865419998649543972823328915211759460410158983997700560534675716506277716750707674727092132817398857649511 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((49914651701509057008692331354489288136979339588223621703759513233699819603974604939956364309774727497374515704368351116954963757868213326269951112204490052127212373631143763046250069865981942631882866277586702945931949000286582493174411865793931057781885595915776583795753698011269430306450803384940513328326049179856617676866367959415877975963880772602158385183361019327181628543410218171351480780159837569129881292154670722996178572371882943039799065854590883688626743 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((4957750876771350472508779827440359571117718368920648618816611484805493166147172894779676963467987833272036269907635179851553947856553554739648929616944161582123960648885905200784647052437001632018572780650435067232942695484817323967462309338621165700303071816422980453569069131251101362444648414079165237789163084019013301060493041100155222360291751437016604578812059744814218102056057160923402406010019033750663216390515599372858151380877338274599907731682341192120219 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((9998395313151860097926723463432235230764222298286908744368234150133295995081662001317285070841371038048527237427125136010520078097173338455455125526801705211873193747587960435873373408696266873563074231894545625424189513899221702669210888003472487581531784218209476623788411992847292664248378680178515467727899147538518358713077439782616018381418607505730712434747292446554336820854393134300343210215662391831407382261228049376129687109377982299134882254710673402002784846843 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((199685669443303116750315044862679884451612767495313002929462712162771047781671672254127725058344960777735514088349356557387334213427807579096891764334195699367104747371721134536858659705223027250116847044760683174027273840685355748179594512143201953601556901732784630840773976099657936839355125377011586724892124253464296019188538930121864271276941464712830702169288245407820226144367128609088800465839466598782740967767243807270754890231836569224351258462845368974981773379 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((2480365273010117781795638345401078460388478911378081031251712969868911342891506656399191730603238055094624837084202934913960789818515310474666292573530959831098073982444708738471029031709083918380676045228930448313520892661200992474946721254580294882193295612995575444334752992227364124540101293779476435434551236652492846270455813076520516679828972356635476437193597296690584369631501168619698244250953097991874746092992405275062587092229050284238256015189565053800358599707 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((999853631698520615112190227270044472103697008493643807300059741536108327599383636126153523166653976493520314907440365030927567883477471720537428364676163937490589621298740635237318008727412590338308689913797190131816598131289709165566732727460736009774258633895540991285612423103580105784087364555122931357864864944430875053295932514891754884624335446420215473310604785927560724440591760958937205233401213746118161558193394067744917150307693899450990015098924653016880014235090559 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((499276533833578038002543693979197638144195176096322949067755220864002391449084689034590874522269101477634565245243067038144092264224053845775427375208785443973867717668112248832352165494217343568654025288103832106516351908534620721983947786987309334978417211354370490118186922826317607237045883878187116577254982112830516469684728855093614952681202271721600830028064661018016300805675467717017047347614448461458795024802303749153531019919208436870634780283314203925882516857609167 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((248175333349897269047045037424657674840726435008093326969601050885371827344355707802937876971073047120456520317180503118303859268663929775792257681253049630010143517353515430354455409019598022102875848312429694002807854694330119552281233706739069077874637213390832030748579257287040678893652471619549985850517017262616020954427146669986976296935888886289753274789594835672335991787645868066798016573869001391635808911743459909293492211000146826996788100135393971572059402080534559 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((99986649308117160866228207199982566433994515235730732595260349204733048885322579601974841308600009157903468483652358015565996249355630628045380453427206941230329151127522029561901487530053484602528150533107183103493387365349328242118838392269876113659539452773513980438134565948546852188883960783166427937944927926176373406236281892480821638291239509074327113967080194338810596358399696292347539300954224909424675870207494053101217128031015683650623152247218214375628676738425315158067 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((1997336023032496147942746273793517664429094308953056186694946617690089948357725388392513828882901590041159540338513098016118426458731205768865376252891490683332665776583183347806743855654011108444424974161727653027469648793120092762405601603199443440899796748986860730425811102255499447936138357202895286203444940702371823170796559106854031646059147993296620281743119727069531714213998479187850063209185132567504113119067368910627959349003383154546989308676385499998915791387129282491 : ℚ) / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((24830462741853916190799960285400717316789501751377454985133181321810293092179660275575279814950868281024724448973538138512375162365547260165255408309438133247905224773356561689563028216363541332172250221605846598762665408728336847595508892444443935228477303304109992782934250264770699875683652378639124678259722093651199754527024361540011417657167735490684242104263062146600107716605652516546939119136154152615490027226958672518522790516218367125212531878614750703600554054459466376531 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((9998782243341290594091273463332009832143941718196707312211482232011315587976928453234931200281332635319849070799382531673821215892475136475903287298455826730442012861794666882429720382078768491050400194576305492418942341755608276948385606274112209955227572105830530697703568163864804028704672714914959391503770710930325547503029980258853184093458829341196599046279285766225930925638711497913896102257937716663352960149236155065521317899093033552824289585925514987844218491341988271512765271 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((4993869666584780079836778342905839394188949147646156809625573572182314839828914525677085465458280309252080077637748046104420837246673886252865171972847179315146136456954423857453002257623580365158838634569086049766591981849439028912083633189212274120244186622584663227233061439522024556641534345684070947079739828613513897679562027715348431642560088624722113969727184392761020278587181491908953462727810096252717891674457403336420929243115218684422419693719373663098432156867938458944611623 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((2484250341617401719729680874135039056010968752440660433579835303248182625914101902324656623736389607394573030436222918286395827714596349288500415973843186536386712352456758057092894805713510032128884523722549050104611813440912585948428540490133856537431852969653598601271643604158702843577818003153489740662838365325525199186986344714040220002561109477361201004334400423256365535788995976701729799711724812381128318758892974084535198438120647537867203474994301591754013930766126981300512247 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((999888924761889138958847326410902612819345355941876264068745928828448128726139575004917779571261193665429393294824078861564254565200334623376566544354051323563807319162876950347062085210550710374180152947888552880008987818554297765293096305080597006646172534489120196529635562930600369870239312345538190977233437856087784164393873589350775480716660200698565388808272492594765837520283791859220205175253272950014413554092277411991395969529972869453761926001023998586234701250776776209493858663723 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((19977430611141075390934788989217851292051882426017207867669963118821687560470142112984785047046038338700661483258994351457513132724405297866828457358422834361967013861005992825863501047115476448422470642576788657592854578303063749180731366516810847565674047280949127370966896586633014865416060109938419249149536201106650501387204922134018637836322294642626604995751109896553300775878484210987420897802818030581025006869054414887573738218278467239169886391962015704266514951905410078644943780339 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((248537139699163718746795891345199334706992899693443853387740355530184473820785330908687387804916890075889008463708162292559852125911084297189686115955504256423716248477944577026787293254893603182570278877755807759555192104693144228993140183224711669002721641104762982490268472743563495142039985077056341253451041362448646122130033757295459255301948893807848827589357039216507743584673206240828757353114450161629180158007628568838041846341280622213512675813976433924711389657701087919393536223051 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((99989868494306194031853341183917660023090947951526359674502522406229239165497369054923565428033447257804811250600788705199860351655618122002046764210166083376225557002803495272006573978309961945360094290835758573844259805893793162065679193275316494767217335388356120486057648601588851536974138396973575013606393567167335056986858391705452283922608726886318244809368958867046376337737645506855052574650376785589664703509418899579971200568737415341485986556331401983046225805187102088396563330294165999 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((49948072392843855974769077181286722633199529770921668801733017705443479315530288164544706029395676890623275042391238681178497746059176172804096443302214113451469387483306461193367879415973950188920733813841349705263754943851788879395176013432288920316918873885554530883266565218356295563483059314810087655702645041018163743408965905180876253410157247032165124568710323154516070369267993517276775683806956645761798735400452238133114906875720490871546303532599556940561172045967207413805512484016589887 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((24864149376020973232208927860394903872048318432867979601714025466394502935693371286229753775144244618566149366931600891891610002840034941982244039529407441650237126500041020588353253505882692913968944207292645673924141032186067381894213943099075843554443950619755257856085422412657017661395488360240057047896898844500800691926369601155324365646803970557955289007606570274877004823881154370535266501509385827562878059198150222077118279525828137750475535751705723354373382943287096755346053713298726287 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_open_source_model__apps__causal__none_sft
