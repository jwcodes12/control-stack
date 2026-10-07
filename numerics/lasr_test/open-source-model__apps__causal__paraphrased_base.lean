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

namespace LasrTest_open_source_model__apps__causal__paraphrased_base
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((297 : ℚ) / 3125)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((297 : ℚ) / 3125)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((297 : ℚ) / 3125)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((237 : ℚ) / 100000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((237 : ℚ) / 100000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((237 : ℚ) / 100000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((297 : ℚ) / 3125)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((297 : ℚ) / 3125)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((297 : ℚ) / 3125)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((237 : ℚ) / 100000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((237 : ℚ) / 100000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((237 : ℚ) / 100000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((297 : ℚ) / 3125)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((297 : ℚ) / 3125)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((297 : ℚ) / 3125)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((237 : ℚ) / 100000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((237 : ℚ) / 100000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((237 : ℚ) / 100000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((297 : ℚ) / 3125)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((297 : ℚ) / 3125)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((297 : ℚ) / 3125)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((237 : ℚ) / 100000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((237 : ℚ) / 100000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((237 : ℚ) / 100000)
  | _, _, _ => 0

def kernel : Fin 8 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((2828 : ℚ) / 3125)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((341 : ℚ) / 12500)
  | 0, 1, 0, 1 => ((12159 : ℚ) / 12500)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((21617 : ℚ) / 100000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((341 : ℚ) / 12500)
  | 0, 2, 0, 2 => ((12159 : ℚ) / 12500)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((21617 : ℚ) / 100000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((99763 : ℚ) / 100000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((341 : ℚ) / 12500)
  | 1, 1, 0, 1 => ((12159 : ℚ) / 12500)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((7721 : ℚ) / 25000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((341 : ℚ) / 12500)
  | 1, 2, 0, 2 => ((12159 : ℚ) / 12500)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((7721 : ℚ) / 25000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((2828 : ℚ) / 3125)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((341 : ℚ) / 12500)
  | 2, 1, 0, 1 => ((12159 : ℚ) / 12500)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((163 : ℚ) / 25000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((341 : ℚ) / 12500)
  | 2, 2, 0, 2 => ((12159 : ℚ) / 12500)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((163 : ℚ) / 25000)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((99763 : ℚ) / 100000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((341 : ℚ) / 12500)
  | 3, 1, 0, 1 => ((12159 : ℚ) / 12500)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((9919 : ℚ) / 100000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((341 : ℚ) / 12500)
  | 3, 2, 0, 2 => ((12159 : ℚ) / 12500)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((9919 : ℚ) / 100000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((2828 : ℚ) / 3125)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((5097 : ℚ) / 50000)
  | 4, 1, 0, 1 => ((44903 : ℚ) / 50000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((21617 : ℚ) / 100000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((5097 : ℚ) / 50000)
  | 4, 2, 0, 2 => ((44903 : ℚ) / 50000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((21617 : ℚ) / 100000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((99763 : ℚ) / 100000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((5097 : ℚ) / 50000)
  | 5, 1, 0, 1 => ((44903 : ℚ) / 50000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((7721 : ℚ) / 25000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((5097 : ℚ) / 50000)
  | 5, 2, 0, 2 => ((44903 : ℚ) / 50000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((7721 : ℚ) / 25000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((2828 : ℚ) / 3125)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((5097 : ℚ) / 50000)
  | 6, 1, 0, 1 => ((44903 : ℚ) / 50000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((163 : ℚ) / 25000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((5097 : ℚ) / 50000)
  | 6, 2, 0, 2 => ((44903 : ℚ) / 50000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((163 : ℚ) / 25000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((99763 : ℚ) / 100000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((5097 : ℚ) / 50000)
  | 7, 1, 0, 1 => ((44903 : ℚ) / 50000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((9919 : ℚ) / 100000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((5097 : ℚ) / 50000)
  | 7, 2, 0, 2 => ((44903 : ℚ) / 50000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((9919 : ℚ) / 100000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((297 : ℚ) / 3125)
  | 1, 1 => ((297 : ℚ) / 3125)
  | 1, 2 => ((297 : ℚ) / 3125)
  | 2, 0 => ((1768041 : ℚ) / 9765625)
  | 2, 1 => ((36120249 : ℚ) / 312500000)
  | 2, 2 => ((36120249 : ℚ) / 312500000)
  | 3, 0 => ((7900410573 : ℚ) / 30517578125)
  | 3, 1 => ((1910282100111 : ℚ) / 15625000000000)
  | 3, 2 => ((3750811422633 : ℚ) / 31250000000000)
  | 4, 0 => ((31406081803569 : ℚ) / 95367431640625)
  | 4, 1 => ((21278962839772341 : ℚ) / 156250000000000000)
  | 4, 2 => ((378081290523057561 : ℚ) / 3125000000000000000)
  | 5, 0 => ((117140526537758757 : ℚ) / 298023223876953125)
  | 5, 1 => ((6088795478992752592671 : ℚ) / 39062500000000000000000)
  | 5, 2 => ((19146161660243246103123 : ℚ) / 156250000000000000000000)
  | 6, 0 => ((419786306540236842921 : ℚ) / 931322574615478515625)
  | 6, 1 => ((351663721645149788888583801 : ℚ) / 1953125000000000000000000000)
  | 6, 2 => ((983858459255606719627908417 : ℚ) / 7812500000000000000000000000)
  | 7, 0 => ((1463758479556586910921213 : ℚ) / 2910383045673370361328125)
  | 7, 1 => ((20277929056855861513725113092527 : ℚ) / 97656250000000000000000000000000)
  | 7, 2 => ((51347916352855822427312418183339 : ℚ) / 390625000000000000000000000000000)
  | 8, 0 => ((5003892744751018781399643489 : ℚ) / 9094947017729282379150390625)
  | 8, 1 => ((1160881981957093551732274050223523433 : ℚ) / 4882812500000000000000000000000000000)
  | 8, 2 => ((2719101905603462298995437119416911593 : ℚ) / 19531250000000000000000000000000000000)
  | 9, 0 => ((16852207946421477980405857802517 : ℚ) / 28421709430404007434844970703125)
  | 9, 1 => ((13163978211140175472508339183438103774579 : ℚ) / 48828125000000000000000000000000000000000)
  | 9, 2 => ((145763894715453490944509716309134777012483 : ℚ) / 976562500000000000000000000000000000000000)
  | 10, 0 => ((56099291773309929936736722164346201 : ℚ) / 88817841970012523233890533447265625)
  | 10, 1 => ((3693349046333934862011101146341290850437826393 : ℚ) / 12207031250000000000000000000000000000000000000)
  | 10, 2 => ((7887172103251637591548819887788759190972107409 : ℚ) / 48828125000000000000000000000000000000000000000)
  | 11, 0 => ((185027696200014201261556938714608947053 : ℚ) / 277555756156289135105907917022705078125)
  | 11, 1 => ((205141484098082033564643207690782585099588796992463 : ℚ) / 610351562500000000000000000000000000000000000000000)
  | 11, 2 => ((429457689308964546739998989592984891810946943486811 : ℚ) / 2441406250000000000000000000000000000000000000000000)
  | 12, 0 => ((605692384432058034294137674040657510469009 : ℚ) / 867361737988403547205962240695953369140625)
  | 12, 1 => ((11285336474847294834063345101950414171940404293853806921 : ℚ) / 30517578125000000000000000000000000000000000000000000000)
  | 12, 2 => ((23466363200832131542582120348093475941997366996470609977 : ℚ) / 122070312500000000000000000000000000000000000000000000000)
  | 13, 0 => ((1970504499356415974503992127673677590241123077 : ℚ) / 2710505431213761085018632002174854278564453125)
  | 13, 1 => ((615367152760062354660569809172842394988047523418013637339999 : ℚ) / 1525878906250000000000000000000000000000000000000000000000000)
  | 13, 2 => ((1283795546856151849733448429929006394361028732985611215302579 : ℚ) / 6103515625000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((6377606837250431418147823441707091945935538639881 : ℚ) / 8470329472543003390683225006796419620513916015625)
  | 14, 1 => ((1331436399855820434166152913326133820290125549591693789358573857 : ℚ) / 3051757812500000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((70192376950953937795400732118518084875009586104699362438819604449 : ℚ) / 305175781250000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((20551559989089492057554962520166192650398336330224093 : ℚ) / 26469779601696885595885078146238811314105987548828125)
  | 15, 1 => ((1787431198754210103185252561470601398796291525159139995568456377371119 : ℚ) / 3814697265625000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((3830481435235196344121367214240147973344432437486201796026381793486347 : ℚ) / 15258789062500000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((65981336190849058560743302216462919775615973443875688129 : ℚ) / 82718061255302767487140869206996285356581211090087890625)
  | 16, 1 => ((95357276600568376326747344730211459404854608740310767116391741878118473769 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((208442255166566857023822681244287985765743841355387465476622310294759813513 : ℚ) / 762939453125000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((211162482940546059553462896822635033876346592593036549544437 : ℚ) / 258493941422821148397315216271863391739316284656524658203125)
  | 17, 1 => ((5057298637637602858909561871075751444526986136775970347285553491580119839782783 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((11303826739076739637490434720271814659185371471378419282265766432576679349376611 : ℚ) / 38146972656250000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((673940202358442137491195691447155303148885100396095185597995961 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625)
  | 18, 1 => ((266796164028044426927613207187354906280933200633438644620704525549930279282777302297 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((610683936688918287029681137671857714092416928535893644472037574708326116118549343537 : ℚ) / 1907348632812500000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((2145817581652730243181359600514878407763099990616994133265907968333 : ℚ) / 2524354896707237777317531408904915934954260592348873615264892578125)
  | 19, 1 => ((2801531495665701493281495781545049269635290142742580172436151365540305693822612561703939 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((32860981001346267618693950193015218765147463436561779404254827084039946126088484812073147 : ℚ) / 95367431640625000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((6818105525235970747580191778700836169835462169392474872609660830148849 : ℚ) / 7888609052210118054117285652827862296732064351090230047702789306640625)
  | 20, 1 => ((732285081391911640081444925376419020737012030039988692679368052952466530346459642821109965577 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((1761144750571613065107330125487664690758038027843112203367395770757824463328028358056620061401 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((21624519313873730336229616189055839790424110127315717263907849251733210597 : ℚ) / 24651903288156618919116517665087069677287701097156968899071216583251953125)
  | 21, 1 => ((38133353219887906670348569758600538472995351574965086304006299143264230329330960794768532553990047 : ℚ) / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((94010510974335435980494943763347038603894382832694556734153128157933479497522076559653200595272979 : ℚ) / 238418579101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((68475755896217425209834960329180774621473830665904468185355549009127349646441 : ℚ) / 77037197775489434122239117703397092741524065928615527809597551822662353515625)
  | 22, 1 => ((1978797990294246105430728319391540714776609431820973311517986355793738718929084491056628560386567932409 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((4998816779727658723027231100043919852818098700246871860599758340608558157831633432441848508040291654273 : ℚ) / 11920928955078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((216529485413823240427718285768832167173760640703976647787635965489142863794275773 : ℚ) / 240741243048404481631997242823115914817262706026923524404992349445819854736328125)
  | 23, 1 => ((102356059316804117847137578333985118805640032911013864839725638568904982752517698850832269698694396914809391 : ℚ) / 149011611938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((264805603286230149237613447061026865243956599033151291031739654590268831962640010620598866645694563157775211 : ℚ) / 596046447753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((683845533935668254974290493272722795468122115600842246691717238188704515666901339169 : ℚ) / 752316384526264005099991383822237233803945956334136013765601092018187046051025390625)
  | 24, 1 => ((1055844176181199245190097084057881652354229622510121669004880166307037742774865280730298835602604088663243856789 : ℚ) / 1490116119384765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((13977401341712594745883997560454577932258772157375343097550532029209676149976755241067519223608604333772714163241 : ℚ) / 29802322387695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((2157353136174370234581990955970464524023621291950420269732559873927057922983151528185557 : ℚ) / 2350988701644575015937473074444491355637331113544175043017503412556834518909454345703125)
  | 25, 1 => ((271572176280444940449921245894995552089243371302748184749796989987581911891097796244722655850672895598287520734790591 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((735260007766832092929107639205952368533205813901306834047669023860941515660876007307301478999026621197727262833081283 : ℚ) / 1490116119384765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((6799238313489557803131299926594487606563088354358408510579877836995099658312460462382583321 : ℚ) / 7346839692639296924804603357639035486366659729825547009429698164240107871592044830322265625)
  | 26, 1 => ((13936795766481082912522245179040096239177214453713283838434443863847861596487771374746870774521993620673324936710169875161 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((38552193658759772914688714684572048520242034515730810759921343210294676897356017225957163818976811367099433255734759419857 : ℚ) / 74505805969238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((21410257339262340653922283389628004490811311805883766729720514877801453871570475502223658522413 : ℚ) / 22958874039497802890014385492621985894895811655704834404467806763250337098725140094757080078125)
  | 27, 1 => ((713666622948861010912895150637912478313901883459179062195322114614320721384668482532345341698023454772374835582613471697251407 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((2015252543946306401608770890191608176828773124142167026450749515667992078951169924285493728314470166755153600291904845644621339 : ℚ) / 3725290298461914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((67366993345164746827626489917176726510798445848783628129776554683107861667122671328431359084587089 : ℚ) / 71746481373430634031294954664443705921549411424077607513961896135157303433516062796115875244140625)
  | 28, 1 => ((36472533273178242140693944216740702482752629901816968626214590463230450125271942038247837504821950343746944480329824985322684470473 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((105041120089502374641930745613479541572006231193321468708756232774796619188735004132060981709043956093705840261765726744943993671033 : ℚ) / 186264514923095703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((211822562148034802335822315021115563231238180053311149782654779795970751914377185167250298438722053317 : ℚ) / 224207754291970731347796733326386581004841910700242523481130925422366573229737696237862110137939453125)
  | 29, 1 => ((372117150165177926803713746619755486253883276039893461992049443931334740247380395361657998692281593560424293406536537774876710858378643 : ℚ) / 465661287307739257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((5460263423752483129311084404972981297426156417711958265780544190651035008585812244817731172729510684083986049339030899828979038794398323 : ℚ) / 9313225746154785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((665623908779357728216001136677651627376379620668735961059243602113448158663090775435628890695673984358601 : ℚ) / 700649232162408535461864791644958065640130970938257885878534141944895541342930300743319094181060791015625)
  | 30, 1 => ((94757708260472875814957486501257286519763701517264887799323845487217661899639258179480058287408691103493198490548059142930695031781397888953 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((283115830804595987813826202366919653467047562784026801523813296107163688411346684732217999235764403894972878043332839155791577683887986765089 : ℚ) / 465661287307739257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((2090477235980258990427025057642951347715520465619847889981465546934465368478071012252724273859141082697764253 : ℚ) / 2189528850507526673318327473890493955125409284182055893370419193577798566696657189822872169315814971923828125)
  | 31, 1 => ((4818611869855666982894901082197858570267060218356012295341771898562944156052304467083061267627342217360577398845739494167580516288409672099256943 : ℚ) / 5820766091346740722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((14644670306633294632919591199669426757195779058225152001276402996893364791544545380294024248047217422313986473605068306418580223047581409872765131 : ℚ) / 23283064365386962890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((6562159691952907846903170122759743116011738434175000433198599067223274236364892008028097280760448028530654260609 : ℚ) / 6842277657836020854119773355907793609766904013068924666782559979930620520927053718196475529111921787261962890625)
  | 32, 1 => ((244696409306412827226526817042692373749006975256345351055269786320073609760968411161223136882089148600124635488622055936501421952617819558942468686761 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((755831489581372167349249646902606210208966890783326378990742369237404064688319104686232023934450457041712386631955318970202139321593644442276423231177 : ℚ) / 1164153218269348144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((20589944073220121584715737793869168234181966783728371851120058476146813835155249553007812342136787795501493227517877 : ℚ) / 21382117680737565169124291737211855030521575040840389583695499937283189127897042869363986028474755585193634033203125)
  | 33, 1 => ((12410294857331777429338590621151995483756732554380748513601467813565050702199389274134658694920177098272082483896894322288592130675139555318384753802526719 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((38927971769611499151977785640734138773007994508370073413136145009360815472506216724480893885480662434203352365276716164152377652727491521559257283935224099 : ℚ) / 58207660913467407226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((64578850790245560696806021127013928710331509851513431301325088851916296696804467468107197154019838294480732155281884281 : ℚ) / 66819117752304891153513411678787046970379922002626217449048437304009966024678258966762456338983611203730106353759765625)
  | 34, 1 => ((125736531926039341277170563661665434468506495066161884669221806986897728320089347870659029397637079888578999768283076839862514206896375107002700138932149794437 : ℚ) / 145519152283668518066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((2001003807922145424650613694209931917247210240728056107165359045138292950878387798100422999611770755962604348939710267361754030100627297046406558181069282464369 : ℚ) / 2910383045673370361328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((202474268007248998323160911015795143343020346694859970302514737152510246967892476912935603084246235224299352122203819137293 : ℚ) / 208809742975952784854729411496209521782437256258206929528276366575031143827119559271132676059323785011656582355499267578125)
  | 35, 1 => ((31813955074561553257650797267596466682335492015178095581168424509026406458306357977706860516436125717572977243399380525087694517556775909716027289335793879143597199 : ℚ) / 36379788070917129516601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((102668656051668546452881273970778747269871033546456445903226588208089122798242155420038275408362466178830566316818586988400425911859483997682648934167297340542468987 : ℚ) / 145519152283668518066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((634613723588358144359753691567042893343445405561751454085409757540083228141854433813308290311867517362780572761175682990967729 : ℚ) / 652530446799852452671029410925654755570116425806896654775863645546972324459748622722289612685386828161426819860935211181640625)
  | 36, 1 => ((1608343759285474171144449085884218685867989041906785120381895045277464603120959135610684752110428963691813625580796112266420761850464608230144690801775628299711083894409 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((5258753578748233689190712299801634851378475030541984803101445329197856255881417531275466152870799549957906779362531581685632240544173957195234349465892318090358144616473 : ℚ) / 7275957614183425903320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((1988489153007433010692679174796516764779588185393281418621970297050806149549709679772555859969521227065887225267302589219404003237 : ℚ) / 2039157646249538914596966909142671111156613830646552046174573892334288513936714446007155039641833838004458812065422534942626953125)
  | 37, 1 => ((81236281518726816377102147470436105027451749380555723800475421739111393065236781444871442140751526840884764797022273178457457328861279732875582482887327604030245531596879903 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((268924724510844184747023582361000260298924224882822278648010275800088287786273406263692897388384937903508584312057026749317730989762315632533797950133564268985861346152697811 : ℚ) / 363797880709171295166015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((6229077145641133611874195878339922730810189695994225809576780446082963479565783164860913018767430680029653340239362215190434726232361 : ℚ) / 6372367644529809108115521591070847222364418220770475144295543413544651606052232643772359498880730743763933787704445421695709228515625)
  | 38, 1 => ((4099803537594662192151478492801619230241359103349874692293183208550314197614504594891460405149078648427544536097998284020042544848055565296115388727863685644233561067583749883257 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((13731772212314238759991958501383245997502280736284138874975698312668367468281082261556641133796290995913204546045986777687004714654121030041532505015954271561240777924491777269697 : ℚ) / 18189894035458564758300781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((19508423358298479159490535856493343107773448671840501707338911495345382247209547885427052788241870994021747981145136634802175046654257533 : ℚ) / 19913648889155653462861004972096397569888806939907734825923573167327036268913227011788623434002283574262293086576391942799091339111328125)
  | 39, 1 => ((1654006034826695467621474649945488784177439822181691481553820353266775187358672117714335304221107829403566328855253847502963735357574851992779266827198317382684076764154945022020507 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((700184562174026235813503256098851307892005741300463933129507200589671510289189956471324951571034270073631401733068933293080200106476153477212134618115079478829028494189351767361048107 : ℚ) / 909494701772928237915039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((61084174977347328141508953878875804387040288505117536071653742939532870766975829842488926445046689392649404337391634810231881159654304756449 : ℚ) / 62230152778611417071440640537801242405902521687211671331011166147896988340353834411839448231257136169569665895551224821247160434722900390625)
  | 40, 1 => ((10419069653114125574017020487042351814641507642931540128352576961017910490662631711653170166446270504824237236368876650746178507011495117783988457578805879111090355018900272785656376135017 : ℚ) / 11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((35655621775056133465967064853992798444750939188444772730054172998378396391499072507426887823201645132351259621107608742020483304939878229890854442266336325687630236108033339798432405238121 : ℚ) / 45474735088646411895751953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((191228402211185834854405191809187743801102984833574258395947101378924364066092735614875000111275407044774706237122257015246166568615075267253397 : ℚ) / 194469227433160678348252001680628882518445380272536472909409894212178088563605732536998275722678550529905205923597577566397376358509063720703125)
  | 41, 1 => ((524726578012684742683622500376034396495545409140760343986942644867319485361788647037878173251566802371275446477783905303827654662440042040340666921046352534765452107699433740692369678104341567 : ℚ) / 568434188608080148696899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((1813468376653036353225378126828658097361562480202823870034474869227418292251112588138174377278730034430325159541683612498358849242665714618168993694201994295668570650084359818522972489048073859 : ℚ) / 2273736754432320594787597656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((598551282000882262437688726935529717577497519050291335197833141280614993882301158882354988204322380630004715397890223376336179834520624780841434841 : ℚ) / 607716335728627119838287505251965257870141813351676477841905919413056526761267914178119611633370470405953768511242429894991801120340824127197265625)
  | 42, 1 => ((26410823002711337724998133918007310464055625174186455556810069920513707726329489900801857847128822651706755731601553202139245485890376175667386047059255351967350341475165506077587253851321935060569 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((92128295989373907902712849566653823821577419850109222129363811696473673244507855480976704259199758702770454441689277513348245630801246160618107841037045185337203865472514064036373066672916976358673 : ℚ) / 113686837721616029739379882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((1873194777209897292765755108833511722896595102439671809858518181607256991147244247830201431296934722132221604393072553387091281504765551645997165620973 : ℚ) / 1899113549151959749494648453912391430844193166723988993255955998165801646128962231806623786354282720018605526597632593421849378501065075397491455078125)
  | 43, 1 => ((1328605902416669430858705263595261909900854077353294281921869432168300799713214343126555746952179059341067983585423142418890599071691497052887876616675008077891405186880377378808581367471489571563326671 : ℚ) / 1421085471520200371742248535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((4675300734190135340092777038411789696801456969580767857167066942146190822822541874759845229138109201253499051651066094867091210526201345819741563113530538073106803933307973355335108744334742601448374491 : ℚ) / 5684341886080801486968994140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((5861431554047721589541466038593151407312296320216416609276908349040565859864708515710376912254953362035448538623106061224983409510293307447934946534314769 : ℚ) / 5934729841099874217170776418476223221388103646012465603924862494268130144153006974395699332357133500058142270617601854443279307815828360617160797119140625)
  | 44, 1 => ((13360561711445504802755166190726071181803304059761970714172881957659268896576284979282294013694231737997960296847196666165745755319366373572812037204771396565246481704946705647495045371810850544017297682037 : ℚ) / 14210854715202003717422485351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((237022646005810703532533250269984792574534435234164182910195880886237723221753611830005548892849544125731561965627427885453338160131665273258133436947631815788764785967445061573761744866871676417869463937721 : ℚ) / 284217094304040074348449707031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((18338743197653619297722986553428870476631440776437728455400780971884354904510838753824468609567076757353516721599571691913907036516410496566056785543426932357 : ℚ) / 18546030753437106928658676307738197566837823893788955012265195294587906700478146794986560413616042187681694595680005795135247836924463626928627490997314453125)
  | 45, 1 => ((3357337157310434554566918796472117653447247086307655364576798616383371268766970900627808356689089456806836878627826450545664932030364833075893670830619423555142632014878811542118472216282240677067141230548540511 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((12005003534463672780314202178355742837247348561171809599819309226198518357143388922790776213691613063249236399603171622489447365701648373887122424791913907590224131529298452773552268554959536990648715864902337843 : ℚ) / 14210854715202003717422485351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((57370136896735256131772232836495090385264548212221215710516171590981563959998661593926605670699657599537208583600550465887697706834974581486610954343013757283721 : ℚ) / 57956346104490959152058363461681867396368199668090484413328735295587208438994208734333001292550131836505295611500018109797649490388948834151960909366607666015625)
  | 46, 1 => ((168660298245768759444147716569920988248604298518613380505786019294007599268878009160650516410432712892258769133178437372296088718723309875045445491220664144401817410141648251318016690918025465281975156756374838942521 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((607510063671267438552958960837181455339400166037938244033678212374816243218430595522073981099571657224458252332845341038368671696336195149404778401325978999966082159579437634611528926468910412415144163890133320102497 : ℚ) / 710542735760100185871124267578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((179455781937001119208813208409727630226249497645584471900098367642085263785257494981721342220626020846933298671037862096140311013574825920187268168963925382405003613 : ℚ) / 181113581576534247350182385817755835613650623962782763791652297798710026371856902294790629039219161989079048785937556593117654657465465106724877841770648956298828125)
  | 47, 1 => ((8469604540781662236848583142725702563426348049002960451464249140066942973043475221052712327395639499793146105581496935456529740022594914982211049251881202980600259838164786532042378648237373409755437667371018313650498287 : ℚ) / 8881784197001252323389053344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((30717670549665655260890799863899507997517630093799030573596218131632600703131073881495030701889968274797220689588996329792241121977915012526149307229747335611541240569563412654833207679670187434846127887107626688922540939 : ℚ) / 35527136788005009293556213378906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((561291685046069836585527921970583221457087814658659367379598916138034003817149695789860772624578478065883846131118528316040742979656850838986883100835863721462102170689 : ℚ) / 565979942426669522969319955680486986292658199883696136848913430620968832412052819671220715747559881215872027456054864353492670804579578458515243255533277988433837890625)
  | 48, 1 => ((425166729526993541941685220554664698808669040682044977978681466343186942453140352159947521645731932024266344910281514807986708969228744400935701472508389828925861149951261829353796461202974624050864570723716987457812217161513 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((1551993858069093447864648499402571231475670528124930227530644094232383502707104983307594062537907543565002263425210261716748731439754982934119001214684698577333514422875609586255255540320493995464989543677154082591395214859273 : ℚ) / 1776356839400250464677810668945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((1755428928211006346185760990169913985209563825220146443593633023732787906021279027136078817559333220691433509013251492790750544375429708974833932656057206166859674792224117 : ℚ) / 1768687320083342259279124861501521832164556874636550427652854470690527601287665061472564736711124628799600085800171451104664596264311182682860135173541493713855743408203125)
  | 49, 1 => ((4267206923622600543837708622508184919513870327306346718897985842947929020311669536930510204938260775188245398467909428793837859887031656949149547340475737182349100982244569923661574971954934644798037503349247651788453639735837107 : ℚ) / 4440892098500626161694526672363281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((78357479490472847422573389845342159886263178125819275017837869499121611804791760565297906261452845058810038874613035905772401310303953639537022593164488072050147255255589823428484941778017388513513452347650391710891294816314862563 : ℚ) / 88817841970012523233890533447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((5489653143045478598019232164066468734325519889489629619495691968911410895810613611998182622860998362868855188972126142590327924584215638237639821697871602672894316104646131001 : ℚ) / 5527147875260444560247265192192255725514240233239220086415170220907898754023953317101764802222264464998750268125535784702076863325972445883937922417317167855799198150634765625)
  | 50, 1 => ((1070379709331835580967538784185259332974759447214839386518656753890592583514095953046603112382336534620090092080610245928793250111515801564690059547355579662993073598602250314922743280521319438300069181946708898485909131742146986687513 : ℚ) / 1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((3953484975354790167254628941203883376068119428549271890650434530949169619201136017258268095149423405098436911506567838448141967473462437385527230356753104547636429556871761299427320293299400834113006493857967844617466775171657508353969 : ℚ) / 4440892098500626161694526672363281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((17166302007484965509591826322061073531150299596748720929599122443691115943297529429910084603710915916297751304046456859301964199131975641363574978719524091212117487794677783861453 : ℚ) / 17272337110188889250772703725600799142232000728872562770047406940337183606324854115943015006944576453121094587892299327193990197893663893387306007554116149549372494220733642578125)
  | 51, 1 => ((53683678972853305177501006157522428432833737245840960282810108340866064554161084316777589276934803147923776236415091811491856640975190811871084879267997472478101912786359582777240798895799213238591470084041233591583145436154704649267889423 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((199346237362213606705000784078847042516276162309964101118218835641531965003673998873662156531745636426969509434718897343833155548734467988223230158760770211671621380920515377048829853133291656362238141075233831149188825983491829862203285051 : ℚ) / 222044604925031308084726333618164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((53676186198893582568605177845292153291335951476080533931610398132038619418723894900220794716357009417867005780447392898282569843919645290112219924062386626364031886266906664605892209 : ℚ) / 53976053469340278908664699142502497319475002277726758656398146688553698769765169112321921896701801416003420587163435397481219368417699666835331273606612967341789044439792633056640625)
  | 52, 1 => ((2691761600321065665018523016115562165508581916209196019300221970573151619496342340413739969266551448717727223737388538430985949480651861464983173596942381345826726528709531544076155859120736865391778302477228753144896376916820431107305778350601 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((10045746943174010767833540721032036020996962751172523530757312865665287148690209758474513304923121079060081832055213539282836156801026006347615382337350797283574356665362201149285992303131749605141982140774657390557223022289055754691787838201177 : ℚ) / 11102230246251565404236316680908203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((167827142450865114339888858591809451211782146450840597279544455483905664250771430004184018261178057654280908261492767429395029671024813681487451333509593430657993520561430459523285432677 : ℚ) / 168675167091688371589577184820320304123359382117896120801244208401730308655516153476006005927193129425010689334885735617128810526305311458860410230020665522943090763874351978302001953125)
  | 53, 1 => ((134936593411825107410915287529687604949769375409144982388262710072676473892441952920276274366106777235040564463243455862410334715883413446514257551483487367061178080619545498407248847167761424035703917343624432815470155418122942689470514622228705439 : ℚ) / 138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((505963810496688492286427126249065594881215586523572912543088545143013804055927916421136401424369356749491877142333131075948133486848000914575050456388524121303054637812088847327013578043278535731298000098110180627309132702425605502341099507759504019 : ℚ) / 555111512312578270211815834045410156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((524711683477277989715310115989272258351557646651992356984521250003799120171869901634206187402987906485534583295962609768616400635970850594528054209481267882214903633018407877087545783688681 : ℚ) / 527109897161526161217428702563500950385498069118425377503888151255407214548487979612518768522478529453158404171517923803527532894704098308938781968814579759197158637107349932193756103515625)
  | 54, 1 => ((1352570489845910862558567619484732036795683148502428441933923472640180862175664443237246520490331969986071539203689534125889896708913052662528149392122474393462781305253327643961300404648797917454017904196441928093260180117746669921815747426496933458789 : ℚ) / 1387778780781445675529539585113525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((25470380249213093659031178132117063296667121507509642392854205075518476793242437767196880514934642200390440787598792162826120942147366818414696173602859239058514361109347519133051880190933656003182405565207256376949867514401707519424547243314923855455489 : ℚ) / 27755575615628913510590791702270507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((1640436280330715424796473332679021728882697951260006722670880875933599854566949011766453172226825922788679847599923083795294858268252682679080155549150955759385303589396940406265125039015730493 : ℚ) / 1647218428629769253804464695510940469954681465995079304699650472673147545464024936289121151632745404541120013035993511886023540295950307215433693652545561747491120740960468538105487823486328125)
  | 55, 1 => ((338878992587375038800014712536297369324836786145883245244061773945564536562953484961371772633991818743435599115982066335523720509979688320731309404409432217039351692636981640003929477244514550402179402560313395054725117011268534224364650877059205007521471279 : ℚ) / 346944695195361418882384896278381347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((1281577520065307697900697374796726077041195697210043027737076529306946200537152416404046436060894679744512095391972675596174524735749808835693221832322153451114066283150555871656843539463392415216162142248286723244006843760382968276550342159227123278306773227 : ℚ) / 1387778780781445675529539585113525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((5128377674078304689704352599383022768856810201563837565209047307524145209718147211353398553092389094795099252884272554003242850650515827859422486907804934726546501410879806624735103493911925287329 : ℚ) / 5147557589468028918138952173471688968608379581234622827186407727103586079575077925903503598852329389191000040737479724643823563424844710048230292664204880460909752315501464181579649448394775390625)
  | 56, 1 => ((16977779516509081843787966155402199782710852929049164333194728584817096322319901424435752780240210803879561505607832797044401276313525050691915616531886193988206081435716003496431510189965880567252955151204280989162407242705648715361177704503768165099723599139049 : ℚ) / 17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((64455740284363913849889714179687421803175582787764829678513878842671975014165250605183344818904179005108991614162391420743682297966839551632202676073861160456373220621792191981407359634585872274050962332774488232201374990998219300288286516057258588259156794648233 : ℚ) / 69388939039072283776476979255676269531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((16031876666365450251171177946576280014003747985649215614085548880628047718716718457700751677004418188670267699255754260940386379976837640070771189896541204903563702427672027996680028566956173003582037 : ℚ) / 16086117467087590369184225542099028026901186191358196334957524147198706498672118518448448746413529341221875127304624139511948635702639718900719664575640251440342975985942075567436404526233673095703125)
  | 57, 1 => ((850442638555214170221097204331106655305552385273163890898527075806151787488026915746251418871916320123919308272967286080752169105987004084688857467013042416112709973814195395185345117445100252126049535438893171847796392686661408919991856726006194949883755385181689023 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((3240399074771379984232746889786844350397902063436458509479482828059750653880520398165943860086791767735905550427066357031794819447085145120447572353596683411004072313891712675826380299424833795726863611251325725897581500085075807249628620469941907738654082289336537411 : ℚ) / 3469446951953614188823848962783813476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((50115724100206507649959806218921131203592251602249366068116316906134134778636498998356915020253312851902413966304746419374461427378180842633654665406383682145060014333281291618139732931643458163553828761 : ℚ) / 50269117084648719903700704819059462584066206847994363546742262959995957808350370370151402332542279191318359772826950435974839486570749121564748951798875785751071799956068986148238764144480228424072265625)
  | 58, 1 => ((42593461594780787756601336894212242081867156675061612288726930178402773931694280094327537569062850523734074017561386071620825205983498773026823944139360368394992321904137949331502097592780636341496699494999673613058934664270719671004418550074810384565157160567691273120217 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((162842464169322981934470763394001274354286598385436561858796387449902806254502900197079951077437840681331833787895817658413058001365327310622093767431013783984021790056803389999670770839544015869869254664546433057611974952415811777990867919891615785827014261831162815167057 : ℚ) / 173472347597680709441192448139190673828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((156657195529524673445485441318369619431226550965015533214015396309666132623064079167288322170041425665001579549239427153475504244137007912072705832453519161474298045121471981582126077681598327528479690626733 : ℚ) / 157090990889527249699064702559560820575206896399982386083569571749987368151094907406723132289194622472869874290084220112421373395533591004889840474371486830472099374862715581713246137951500713825225830078125)
  | 59, 1 => ((426589366751892860251869746937713117177625533879114302592681623498592778888867041896110425921170440147593755361516552644256223658019909309252213901214587704215918251617051442301612779169908987877097456912854828362104903565979380410195492299056774983152026562624450409057107011 : ℚ) / 433680868994201773602981120347976684570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((8180510663589500558585128745280038413895638717592414088488098838140261464165326710112630879188244756591733633647927439543926927734898865213334763012068091133071633897902207132125881388729656558335173851506181829208996071223478628919562027605818457751504845588658793565821344667 : ℚ) / 8673617379884035472059622406959533691406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((489682573251685369664455044708538847462345134359858696596055703573482071398900403384888145386767954655066819629404113363417873900892934903793894715066883777299528385937749291683086650655155782256632636625604049 : ℚ) / 490909346529772655309577195498627564297521551249944956511154911718710525472171585646009788403733195227718357156513187851316791861042471890280751482410896345225310546445986192853894181098439730703830718994140625)
  | 60, 1 => ((106797548341771949357851855682593801281397159635894334207135489713312695644634184483228984984206888744790549226353823730476218456150676470196429854736149997363764916759721784055173282510668284746057608684914068021863953396423392439281652225604727841861739339600806470246511151168457 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((410815990373847301756223638052140040064243012259689081821679066828458708405346771515076961186593868973884322773245883194396430275778713299659541548620708566716086283487345030882074858706708290663115626211878503880204524455663798913390422210549913850198339669261482282185357328283641 : ℚ) / 433680868994201773602981120347976684570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((1530622393075108704038023293498840247219875940690914046057458538486264323981325301709328582309688534747161317987439249383586834574454834059342517444485183536734983507726412896157375619839017152240794819918468016197 : ℚ) / 1534091707905539547842428735933211138429754847656077989097359099120970392100536205143780588761666235086619866114103712035364974565757724657127348382534051078829095457643706852668419315932624158449470996856689453125)
  | 61, 1 => ((5346767178838704641671387693883149351824817120720149880794299584808910659886333061328837075300742553413752485008155825937930751442788412924409554973515230380512925981231647877249379946336708934676165200494536244457897993914570791690890216725495249586105777681069530473737504480745125087 : ℚ) / 5421010862427522170037264004349708557128906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((20624258831348911894267593653111966639529829270153432526853933502073300622328087834585573334019634546263117463113961651294932050557291555168977206036076302917504861510329461655014680264334827365048503489660008478562586043478951687660044454095951972855333187824629581232354969461942833139 : ℚ) / 21684043449710088680149056017398834228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((4784225364864352660728731208586883927251446350027760085012408399278083714673047206161684065634014048085698307504366999731286965622588314942987461802616712212298774710770476605575578789736729881596460636795864317383241 : ℚ) / 4794036587204811087007589799791284807592983898925243715929247184753032475314175641074314339880206984645687081606574100110515545517992889553522963695418909621340923305136583914588810362289450495154596865177154541015625)
  | 62, 1 => ((267654292338685408342579034346135826165877172358952504207203736399388479902329726269695684185913386496497130992062877745251127231115335675458857639030321182964246633815032937414765283251921456200632701113652482430461224817569309161683698703723503387314513108223432096523847892127591189804729 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((1035100983546223701022694010108576286999812295174941996522956355978681488378160686490768329708715189209852349110552501007318866026589632864455445489437962746902618331303674653616484546255339574932950608303885965664903425410265636931992845860869928585684550728250987673374995435103050646714273 : ℚ) / 1084202172485504434007452800869941711425781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((14953618198236218217382106028421719334122206495859302904046077367030071390263687664424313896557413202426123876859502382972902655799523642856164862195339478293919189103684473263200613494975438902215705949816319188241446173 : ℚ) / 14981364335015034646898718124347765023728074684141386612278897452353226485356798878357232312125646827017772130020544062845361079743727779854759261548184092566690385328551824733090032382154532797358115203678607940673828125)
  | 63, 1 => ((13397197910849745212485216462110111527808436200401486323660702502895262380626009296224834426138288924395282547018093881447125122746735050758602072865063550336817571459969882850643936233460766743883012134388151771344071703177177037446319750002653481750712926016529856073458994636146720730674051951 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((51936075176377200952310530488154418239022475280294744125646779030221467200893247764681525918092840264980583538777316904201819023179933748263898058356783029502443331300749794499353240175443687582232780674974538328043401962777760970345682006862157190343561674601113433081485630847129612367149815371 : ℚ) / 54210108624275221700372640043497085571289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((46738297472111490408885515131307908488944838151480100436489139337309950157816677981864057696165681644085356646374774325712440951284940012614097730968230720107510511227799582334059074581290437456281376641573097222726936730369 : ℚ) / 46816763546921983271558494138586765699150233387941833163371554538603832766739996494866350975392646334430537906314200196391753374199149312046122692338075289270907454151724452290906351194232914991744110011495649814605712890625)
  | 64, 1 => ((26820946987060199870019560869430414257244846831348790289604067369359924241677354732868953979986150881557371534687717275300572105972543992909392586097763888475199071330102124649044436651661509433967330815530828592910311640405466561678449385512533409643092602820827450448169771005711076017414361657617 : ℚ) / 27105054312137610850186320021748542785644531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((2605227654651270059753748343739098796015784604764860398640711721423063151137912581908926482580230241008994163210322759004318266600408999313160193575967544038015249552323433993963387115525746015879285402044287332858295812218986086290887726217185543503930485010238807191283631264570420326379110730781001 : ℚ) / 2710505431213761085018632002174854278564453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((146080484024567123907981109550499034619383621608604448483912637743877877378027344291686861404448163650799258354123179251443133762370957701350366822802564837377499239635279381171118249220576532878911733815782926940809673801999157 : ℚ) / 146302386084131197723620294183083642809844479337318228635536107933136977396062489046457346798102019795095430957231875613724229294372341600144133413556485278971585794224138913409082347481977859349200343785923905670642852783203125)
  | 65, 1 => ((33556597350785209085870844584641155480267726094925868788125211875368493277574185944328219278004597640618617180889133011552097401409020590621673426027080853460364431865990448889877883885664031990356727218923723225107420904186849611419414836044774718196828256556903361855267910771221721049682064656107442431 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((130653174056110563366871532054065435384414474537695004890775071565222558061528636372799831690899019616356657181863452342791604727572370969344749573275700883894807717304932209564555921009804444709520700924670697441142442699183798539207237222126020738852074868072528910803641026954616519361477309281146672803 : ℚ) / 135525271560688054250931600108742713928222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((456567417488462792135685805181187111818140692272316894217259163595828319511691888903688276050815706683603645619758217980357278380413653834661644998711929487958128830573139347234419865997937859208274885335453517372790684788664944121 : ℚ) / 457194956512909992886313419322136383780763997929119464486050337291053054362695278270179208744068811859673221741349611292888216544913567500450416917364016496786205606950434104403382335881180810466251074331012205220758914947509765625)
  | 66, 1 => ((1679223038364087022249288379166603725680097747924850986119103742144244788659558357841532734726167009810702633644556428283369351047127021601258334001705990720896165453543781722506514016334135543184731580607408535683669712209328595849525233572796987381610140139044153678159479456222973816570944360206394620585881 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((6550871381429341469705367183215364122998061549789467417462769858208201365580002862080794577056396414530195344521182244387895588902109285438081967898638921229878460967027184278044084817764167265011000988159905196313109201916011595683641602662405576191271652295742911423321095198146814017649333552860047585156337 : ℚ) / 6776263578034402712546580005437135696411132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((1426959558741707044046954542591071658204588785131060657798765864824445244724785159465873669668695255623554056669857075002438183573649142592056905880814449491491091398125117002986743934798878966549477944804973172080817454321754862364813 : ℚ) / 1428734239102843727769729435381676199314887493528498326518907304034540794883422744594310027325215037061478817941717535290275676702854898438907552866762551552456892521720106576260569799628690032707034607284413141314871609210968017578125)
  | 67, 1 => ((84024954157992100228028607764950906898508036096692900211954023735828358008013287711632740039988282316824792552100674027951262523808795428852205104929040534280019903486038370229713804899440655009753450164995339099347279153478133257050891670462924053981432019044475765006303958017404388327270005610758227766979233167 : ℚ) / 84703294725430033906832250067964196205139160156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((328389776946488726223798594102368211974147790654888317351327042037959728669829944315687088289160461197669966849779862779591009957620238960432649518179365218802863554069272277395476348337084758155239284836768068255566200586158460093162679346432182566452938540190576156831702604835860380006756438139962690240779942139 : ℚ) / 338813178901720135627329000271856784820556640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((4459775701135092107712397088755908480599098669928603543231025335021789768162068986114000815938659048910670081191045916088107059127027680086692473032371740973016503552848702537595901078100950657115912906271934833615068628757580251988394289 : ℚ) / 4464794497196386649280404485567738122859023417276557270371585325107939984010696076857218835391296990817121306067867297782111489696421557621586102708632973601427789130375333050814280623839656352209483147763791066608973778784275054931640625)
  | 68, 1 => ((4204168939616799247306931068076331962614222481046444367881324887198317484358494521156622380503497712119323322101141289539264621906198059539758105551944454828427631709643007578911923196373036497783888435907168281205589266405451304461010569215880838617789955278600503314728150361908264826310087810107442558316647576796553 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((16458786919601326213076275526090458912121940083715824963547956804556574259528748899472065629383453289034398392007893720473845460462435311243746018994101314832806027960645883364132479523669912969783562948989321542437181432301385514408037370070242389394009735274456213067162467161003479312659765216190883427594914347676313 : ℚ) / 16940658945086006781366450013592839241027832031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((13938289648477367315446939099215327405623380993489228329557700488998679639613507827556988301585742996592060017510434438138453875651071481898777386240011276631314725419177604692413049594149866394930018193822877656246279294425366643937876314917 : ℚ) / 13952482803738708279001264017399181633934448178989241469911204140962312450033425240178808860597803096303504081462085305569098405301317367567456570964478042504461841032422915783794626949498926100654634836761847083153043058700859546661376953125)
  | 69, 1 => ((42068433480882774109259665641367905105817334861481151913425938603094625992098304487676602442483446426695100192910846548089485177094968500317360674218009761577839805322281941188928334769171449722114045947295518368296829361244810571485695800008536272014844233303058694254815424908886779971048153185268102617784337419134869971 : ℚ) / 42351647362715016953416125033982098102569580078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((824763505391765653999857710563980132584790243522666596110558356195203150846720398130335380049910514392200354887328520341563609822568298818674515746885174884979471628813083739218497018179003570199009244529742852137276311818103454948815185513437472548698720751249014396935473792509124934855171507775089777428254249749437605203 : ℚ) / 847032947254300339068322500679641962051391601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((43561370518604391126947319185748502848381452558747342432552804612754072818486927432664269148482028713964486441713747926809569786715721408977277049863201868937183210272063872057931108456257003216756517998649366595560931633069092154414743173663401 : ℚ) / 43601508761683463371878950054372442606045150559341379593472512940507226406354453875558777689368134675948450254569016579903432516566616773648301784263993882826443253226321611824358209217184144064545733864880772134853259558440186083316802978515625)
  | 70, 1 => ((10523228126402618450018822049560920659749105662862758374562586209004299108661507591673448308074507152210432100668876734459506885085283415478489379058213164057699414133659488989010358853327535078242691865559400587029699756847033305539255954923120216022072359752400294110188983690616963638295767142360632287342588915338893329022073 : ℚ) / 10587911840678754238354031258495524525642395019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((41322811791647643154253541092935444139941855420677686791207042049432673256104787196720202423367894356490271049171044246009472890815845410777293527712168922955478204303147320226927526053661134897318417950986348431984297014653595427223900104962753017423411879036248296757929464120249155300050414949331086656717835933005605431274049 : ℚ) / 42351647362715016953416125033982098102569580078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((136141203928833206728455066823445381509218157552261874138520667788199164173368303580615510125649513201848257382773477061248782814252345326361285126939541068553807764857614148891663562851798495884157515858049998056297732747176127879429984179739238653 : ℚ) / 136254714880260823037121718919913883143891095497941811229601602939085082519857668361121180279275420862338907045528176812198226614270677417650943075824980883832635166332255036951119403803700450201705418327752412921416436120125581510365009307861328125)
  | 71, 1 => ((526441419188450796929039189449259780832021313173241090168447581579468521078481027648322403864838406025224011711774642494004431723622128551100955028254964177554547329861391572430365835574793122339915950322065574310695519462000470578026105401873315847356641054483079907760078506628359854301517709317509462592098961174265680383189289903 : ℚ) / 529395592033937711917701562924776226282119750976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((2070065792921450705514430499642528298626773900209136087726151816774854977446264076273365513521511612108748930589364458640723787589422664754908252735098371136278213463181273781657669898689187725469500923008165062809752407491587710501969136822115073705621474874996594465639839726875846475095737882968262355220941689705680057872600646571 : ℚ) / 2117582368135750847670806251699104905128479003906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((425474975030177773070096079495917962201804604920685297998928124577935505790683290029233653178281623330941527271005261642434431103144023775992044432505041464368461003418012559040107018674585180070303964089907861140870669736691387351606403024737381363809 : ℚ) / 425795984000815071991005371624730884824659673431068160092505009184640882874555213628503688372735690194809084517275552538119458169595866930159197111953065261976984894788296990472248136886563906880329432274226290379426362875392442219890654087066650390625)
  | 72, 1 => ((26334880456719645410080188717922081571206221201884390507146786558020620543682593267526384422187302922598628564004289081284563890632032705436027619369133684279981187211742029528410728009699131284951494924695789170900024544013137100284696927492511888222398664492262184934342526039567837071342257654644551311249382316899185973202417817998441 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((103685251953966035877503723719939956604841278974066877093521704321883517260017667008596928823652761340561420381033893697512182588109053872389491543680184368784282730098442787996484650116539478615023206341001908744392772604386028558814716387656826318099428284130773114450038203849045134980723261216489267459813658313275080330305850075519977 : ℚ) / 105879118406787542383540312584955245256423950195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((1329704636633584818623560308187001069899627345724725266288442724034239952589795242650338366634882930767760937224033719028626050236061271716762783197374317644041172231418263723135680345467036369582277451831704639549071883789354798769650432017816109662867477 : ℚ) / 1330612450002547099971891786327284015077061479472088000289078153702002758982985042589074026164799031858778389116486101681623306779987084156747490974853328943678077796213428095225775427770512209001029475856957157435707383985601381937158294022083282470703125)
  | 73, 1 => ((1317329889817015215209919620313389671912813549366661268923654093151883194543620170029648971527795569157864285586451243671578820721081101202203586276687635531808397768440596759745266772791240179688383699689729813598664127793449254493005386881369792927543499502705685537798785432066667121472678772931107148720761471964321384731216383433469476159 : ℚ) / 1323488980084844279794253907311940565705299377441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((5192694411240537039628264593777459270500940387636543935790113773510459987171174013225355820568034674461170298532484374488619223356066728830335069889569216266620903874483373007431388166844718096887978112854706457965778368658085679577061610912671804538696892213992346584591440888328382758249942547466910688881765105917931535693374480414425742339 : ℚ) / 5293955920339377119177015629247762262821197509765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((4155596610050534355759080412092042378154033393112733189149572235218325405341887503864111886614394240673285112037163729612396592181237440409559155701706008993620824175926237953309759319028620979251986388109576996403180380400018981355907435070942693020388053081 : ℚ) / 4158163906257959687412161832272762547115817123350275000903369230318758621821828258090856331764996974558682465989019067755072833687459637989835909296416652948993993113166962797580548211782850653128217112052991116986585574955004318553619668819010257720947265625)
  | 74, 1 => ((13178657004128471227839582130395473795940582910682656131283214976035870979559625237762551561965581470257689743862361444301214231625684901583444747722793920131264706035849281453676121033181889662456329414673691989829729917458900525430413457523401554029225721433727487347709322667096956397880841975288770912442354425926474183459770605950718816822341 : ℚ) / 13234889800848442797942539073119405657052993774414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((260025278941523140898127806273338642254262168870531222299598938423120779374302554742422635642475157051320466969540713823638617983218865815979062360260434031242588060378893784890378121819496181488047648070789095521686910325306864670652191342549069377407863418946061855432551107597584580266282145031426103210976783441441464139139633919490534788177809 : ℚ) / 264697796016968855958850781462388113141059875488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((12987001893381525185248091469581306321913004121357841134183290942602095556987940853580692745879711014067978989239837690467114194293714993961214557385460339359810906724129988882841422173112446773303697987853622107573210031532889961884931268019871982404778752003693 : ℚ) / 12994262207056124023163005725852382959736928510469609377823028844746120693193213306533926036765615545495882706215684586734602605273311368718237216551302040465606228478646758742439213161821408291025678475165597240583079921734388495480061465059407055377960205078125)
  | 75, 1 => ((3295889096574248185785026253468938184320326355736311860029815025750383369835772072009078530444137349839113735944809095861416094429557888123084921890216891031177932208077198175180798065826011099984305789958425182395398056878353677523036221744914947296964060479183972300116129779443748452798471703884292714116423540966709076390678201848430021505997393359 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((13019347395312069952714599887464239651901317190708453440941902066670489043900615812336518114480833352153511820822615798454910642072399050602324194745635881523067055808487943374320392582183398869548601761854478917653550002123014463868671695714416416671484561143889195554713330737138204142896840189307063619296864117049990842501675997457499759780417599067 : ℚ) / 13234889800848442797942539073119405657052993774414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((40586537229978622058761015376554092017411843422809448712683786352568324081040281085966775118267210564796521745316319310901175915228799479431631221601818545727830294073997695907179988214622957737337484416774225700670212705930126195368163881082841861687968491574646929 : ℚ) / 40607069397050387572384392893288696749177901595217529305696965139831627166228791582918518864892548579674633456924014333545633141479098027244491301722818876455019463995771121070122541130691900909455245234892491376822124755419964048375192078310647048056125640869140625)
  | 76, 1 => ((164850443659176075204864415218821716964798252590456569035249426270346116384054365695615219423552006428674071338428743212217115030237310836500515644062028676238920288008667530586438002923049610258721462402409315487419586457337900373600002642012700026163472278126486634791752081981992462567989033078636418723445979653953737314097594024458094929118716739407689 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((651804342992653649098528794002531464791247659555133611060902097244703785682481072825467765973227932300268992138840685044443403894206760792249618704161029962373935688826812037732694699083841873745820891358224039458074731328965593248434627641599766303290174514093659375248060344033015924084152056119248037552692732601125003450305904493119902991884366306708793 : ℚ) / 661744490042422139897126953655970282852649688720703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((126839026897303508291174316174201715159746529973484727163261746451593213769551866011240840137332758405407929632460983268291578531286337041924267011301620053625444852448009506983331401386769219051298613765400580220411532584730126202868599502960538958126244209511236280837 : ℚ) / 126897091865782461163701227791527177341180942485054779080303016061973834894464973696620371452789214311483229552887544792330103567122181335139035317883808988921935824986784753344132941033412190342047641359039035552569139860687387651172475244720772025175392627716064453125)
  | 77, 1 => ((8245081026430545274645044112843588054092562732910411902321847884683732010445757374110686183882019249003121841826738120726449265734987837366871345886783710136453382129896373188635804944639156702064407196991106946917493047435970712033562952179227750389400271851516184863234441631151665904125889025513873909804730528049830199891555835929114506241800807207787810143 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((32628941258722408626748014134577007528999700430818393066958352175378750709338548020884182189103232151146785520458248497161324706298044473188957141624079369051635941067311054543907488076556887110763408660118655167943440189556747146451416938856109234450059579012790396436897895075563376365986840182329833935162178405173124826288907776425214643459456097153188895411 : ℚ) / 33087224502121106994856347682798514142632484436035156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((396389204349711712413060230794726022142093926683076077804554214735511837503948774267685346229855437421004144177807261486050624845913049011098120597372472781362572982744045957492068686608706772008660629212187434422436848688240951034110624542054473465058110234929447344785161 : ℚ) / 396553412080570191136566336848522429191190445265796184625946925193668234045203042801938660789966294723385092352773577476031573647256816672309485368386903090381049453083702354200415440729413094818898879246996986101778562064648086409913985139752412578673101961612701416015625)
  | 78, 1 => ((412370977140423614542025124942156903090889209589874550254279512563363596381331467896751119134190521382199250570919557248590167617333038944162736376416762254434387409284165630526950436767725349853613783317541599569290602418885154091490503655544923333207841138839153280231226776467435616250205279619272904140291148819701864155431557045643619229627436372894316591813177 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((1633238061307278271626329238057566442321512717443615781750168722403963971330396923125131102754289041731619758336300269073405810916706023007839515530285782190787620216609795538754984728312937028776298472997562661439918143082791187994048256274485968329450118018920039148197649978553942453415225710159333394463686142933368762190239866267744199688517791987822018843835617 : ℚ) / 1654361225106055349742817384139925707131624221801757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((1238765033288914069471694534731496352087625186903680614865185556054546941972592437341189941392651166559445092163612687992932544437477377155061402203780263243536528082766021566985093631626058440401705226548424169418879641023545891188209299791436517495050247026979449411609075933 : ℚ) / 1239229412751781847301769802651632591222470141455613076956084141230213231391259508756058314968644671010578413602417429612598667647677552100967141776209072157440779540886569856876298252279415921309058997646865581568058006452025270030981203561726289308353443630039691925048828125)
  | 79, 1 => ((4124778170540875430982582493580785137823792248207738579430976133722304449813403768313636022550536371790680142940727721905697682091941540339961635662281295626350040462464906196396849868095568172547161764085735484325520871912499306671435207203682791962470385714775368123054594551815573639874757024549901580466091831320704154240587040165482363947829099626453298380522766947 : ℚ) / 4135903062765138374357043460349814267829060554504394531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((81744708148819672884119870023819600899779934756489041778512076844247051207671399006566723723883717190815200329214798915387397464975036549114607635098807426556344801086915217951898544760256195835957608147287594318655341180962803236114057240022493332814740114542219174948873328505625755329813065304162283381215154818273139135029279300067099907467158586399741438818637762827 : ℚ) / 82718061255302767487140869206996285356581211090087890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((3871278649728328197114577775608206563296877660575925862694701742467632081621695486901434473804104966320252509478614658238955039960546255568500886539824678883481212941705620238926105371165479798084812902980062628842304852730839285479457317268015179400583071350419671437769968691649 : ℚ) / 3872591914849318272818030633286351847570219192048790865487762941344416348097685964862682234277014596908057542507554467539370836398992350315522318050653350492002436065270530802738432038373174754090809367646454942400181270162578968846816261130394654088604511343874037265777587890625)
  | 80, 1 => ((1031438562406617687186366754684432635589819855399371924329227971875272228240707995080725289488436283961944871702677956508572671162366129717969120905816181026939688996035365225168764755940644188811688762627972750720982599931971652022629653843834077175924016774002309533971377601302310248753844781435156817864252367554713858711074873903774815631547016634466534877529418510265897 : ℚ) / 1033975765691284593589260865087453566957265138626098632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((4091062516711386612949998983075196776152575792152924313767721493608877055992047209733757651512352230759516874154109899668707130082226586787148915778254705150809673727949426569354795230923446181131462148868554722962724382731532933033315617271073441936034506483053468639193444438500192868423428802435415977779417498089751348063505171285382259325839520421028239064183782326797961 : ℚ) / 4135903062765138374357043460349814267829060554504394531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((12098135820141959668466981047506054659731925124147209226750482121277755182211167568521473315498282180035367186930265930358957991418925538791430635595668236978609593710528841684096340305052809770948821271818614232258891960761099453083409722789674139609164465648117419893949415063498997 : ℚ) / 12101849733904119602556345729019849523656934975152471454649259191701301087805268640195881982115670615337679820336107711060533863746851094736007243908291720287507612703970408758557600119916171106533779273895171695000566469258059277646300816032483294026889097949606366455554962158203125)
  | 81, 1 => ((51583073035130168301156471827147253091328210761420481180502326582255482918864166473523697824622476576355866306744433959287790585345689169157944551713547869718178437757281615266565926237170974124800044929988471040635498640380367392916248879800174958976005695414315884600422953454606646394458605283458898741026798386859229845631515288743263309931433614120247258631612541051989940607 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((204729949598237514487649449731531773413984358006925155254336298118112456634582450462380747027949391175210718244416195002120735881740541079193302202218751324164053158657282127454479146098273357592838755363103821166894606205207061333432344544891099928716496298596908989084311682157325661722410610919657460852845561186429610933496967235377680531604152560608934731782114162407509950819 : ℚ) / 206795153138256918717852173017490713391453027725219726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((37807777470330985464383857083866017886247993938708591715281193418908778078371346669916903484917496177895309311278616041240111757265536198838759988905312415100897691986454775683916057618304448850883799001049907042243314706402032858780834038410846005140703170943909154297388769560561491641 : ℚ) / 37818280418450373757988580403187029761427921797351473295778934974066565899391464500612131194111470672930249438550336597064168324208909671050022637213411625898461289699907527370492500374738034707918060230922411546876770216431435242644690050101510293834028431092519895173609256744384765625)
  | 82, 1 => ((2579662584689288997805204253008420663267465413273907379125801285508686735188916729361122304958947420085844911364008586840339968879337015638053284735867776787383362999715508636970271088715748236854809735004562536245683340257574121627534991610185581163549895814109484212595503738907793255615363689703120937782218804692870481450243514989340408334494433578760636108371631154003929896964889 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((10244664619849892984362901388906849417634139188588801016693544228756628426012458399174483835044414564379230283590925923742186877751823426859809022306564404676752700972183396941143223201374210396447661948102055829433545048712487605461889049260611027162759637414004076592086270638942914495011625706644538992207378599465534797839549653477061641273503330953706597370193588721552390230721073 : ℚ) / 10339757656912845935892608650874535669572651386260986328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((118152423970375787899400156212919646421453419632481284939661558675971794477753433339206806019997785980948218815545376133955094041836982542617869971876606762797181675978566641263150883555862177658551047463553093344886494743985085191697671605506021059806615011463853497219577389570350173751373 : ℚ) / 118182126307657417993714313759959468004462255616723354049309171793958018435598326564412909981598345852907029495469801865825526013152842722031320741291911330932691530312211023032789063671056358462243938221632536083989906926348235133264656406567219668231338847164124672417528927326202392578125)
  | 83, 1 => ((129006366133225011500486819877743490371244045945284522902718071465668101684779509144950142378850113190998558038384805960035676689178987847235528985288523972312905139344795508807511445329682181313753391321751227489735949375084229061871641129199296319711346292416463055280900850626542262693437295164729381381748377774100312154649185025443694482903054232124423603622447359389167929435693385231 : ℚ) / 129246970711410574198657608135931695869658142328262329101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((512610336201764968764099865376419939882722836831031355698207053112809991370269053776346409198502367185030783476972753822296268657202050411114634897826533696341398536592150862938704038368042844484685225332899633898031465263508252139797387387897680581451851274659089215340846940729305778464993064011126964046591798241879152403196862873683171123227792581618059190691283530331699101269388497851 : ℚ) / 516987882845642296794630432543726783478632569313049316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((369235146501596981323636792956844722077195560638823909962007711958453766258459412472907481689088447472434950570516854860975187176221380918966638540630741590477439164170113135332929050606281976881668811878753011196284009493115246756700618253121491798597814890027522717844970949120832401964585969 : ℚ) / 369319144711429431230357230499873337513944548802260481404091161856118807611244770513790343692494830790334467173343130830704768791102633506347877316537222909164661032225659446977465823972051120194512306942601675262468459144838234791452051270522561463222933897387889601304777897894382476806640625)
  | 84, 1 => ((1290275820235229134318872828317481325874331616417601105551502400117409413365898833474992060629964014665505865823756117598894554671054748611811977780530172225099505697049201839945744663612054956951069922963317008170451863190602751581528546628317384852488637879660337127730045852615438978431520962332817070688410807497506430577576584749800837989814403801037023262844107312740500796018203822714933 : ℚ) / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((25647923719192043926886301538664818842242827150956261817857207346966548299648475954166526315060347901447515871753096988795776727853324873839718415769167269314333328469559041032104170782221788158520624815391056286984043420586528307946761105220884804515207405995803931807517056722141961022207383127110136694195197442513456744569736317915741476063725039976948460270265161125710640489634268457093081 : ℚ) / 25849394142282114839731521627186339173931628465652465820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((1153884780285810804258660947940419255275950576480865380349572884489774536839462915315978090293413094196775376963904575403557145665311547390222973355915292421892102282844100802473830704834264613319129555155066213216044311212546873561010607647172779561011831876522037457653096879788345628367421385957 : ℚ) / 1154122327223216972594866345312104179731076715007064004387784880800371273785139907855594824039046346219795209916697283845952402472195729707337116614178821591139565725705185771804580699912659750607850959195630235195213934827619483723287660220383004572571668429337155004077430930919945240020751953125)
  | 85, 1 => ((322617374689389212737822090047519785016530943238162550376700863762262937570973274955728062675248729317968103981099303347611201890299296487175049527683851317731906552124386262947946292278159075372655635056334058807892469419929049128580721331544722561547868103392398079040756711847779432194359155574680107983623687652986101137849284810920077569723261227649808150255433900777907448945101327502525096351 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((1283199435877659606401441494109350406832859032536999281107162336168807633897635242854380221785773333473699473151403012715928073313965167883512989038230163650648153059025805255028642791642717835993643684032385136267340364648246925107954433951024064589009049896882158716753739272209958325241487371456833840165423548477477553734493026932765236924371125793562630862930044829488551541052143254216410886163 : ℚ) / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((3605960489833568395304168465333200595300518014644985304931764226934792658496187677146697702089368995215759943399181232543507471475743187742629692284939556981679316276417557243621953701145360272397030116859629430827951850752885545096354433511658372956595246070317456966453954962524665173309231009564521 : ℚ) / 3606632272572553039358957329100325561659614734397075013711827752501160230578562212048733825122019831936860030989679012018601257725611655335428489419308817472311142892828705536889314687227061720649534247486344484985043546336310886635273938188696889289286463841678609387741971659124828875064849853515625)
  | 86, 1 => ((16133078521113133700004280562932878612829170253798259171324786989757692911816219259043923481143112092929319055788731772692092448110029297301798331741952815933484091660430371807054793475318182055598504660017642360281640535769374685441681868030266132879341154718769871396771639134130386980842637309239305505372123284559295413174884660842261650915340354955706949885183961390808781783056542665370499639605241 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((64197027304381816575542644181880994694932902008748536796635087591372985956102518439687618840669551086304261146884102076634415460156399990253908656554067399070972127594147720495533876280100066218320285431634728564787696060333745131755981694210367375825111302411663784893876102381196285741897101904382787966518133341153255225338411607086995975106554511417667102205555589347584406916957114409200979685781377 : ℚ) / 64623485355705287099328804067965847934829071164131164550781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((11268826050203379674609798746705087975322770521531949721419442076264438226709051727949335047569975408555416549136819192202563702877908396570779031139343785933465515868878977429419011528945516181371712841982476342422005767191044654863166697613012854840169435647836315289291150216779827286012765701542606013 : ℚ) / 11270725851789228247996741653438517380186296044990859417849461726566125720558006912652293203506311974802687596842746912558128930392536422923214029435340054600972321540089704802779108397584567877029794523394826515578261082300971520735231056839677779029020199505245654336693661434765090234577655792236328125)
  | 87, 1 => ((806754762932834877838028111633645526347158450313147099475980091404277413448354544566497581639551422088502511410841668319646454479939265114770887132759815583835724632949908965887415625470114255342193102179923132578286978696324520706254232524802964208111274361434760428813935160675689715456627503068221965118893249822836325665401511529582782579278992056351287632235842525629671134636510049470357335613289856047 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((3211560321937111279567278623816077833944933222033274455764275095262601031472980463750680660736130621778963195187957498928761538239470106075760324792802222431735735106132869513813190775980120369150778089745133909186084003440432168738023855940529192193818980274597219071127098803889507148433825256273271288704090590943399534267180244858279410809071576383024459184595193233310392066785082100177925337482912824939 : ℚ) / 3231174267785264354966440203398292396741453558206558227539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((35215645647956558509451543126753228456128124960254639059275472324465970644138926339698450595969265111911116217221220508578614444065308263110357666804360222836329258374596390496822359797940536420397052890574706571496175851059662825611399044730984653859618163265139058976113390259178583364513665174256679257889 : ℚ) / 35221018286841338274989817666995366813082175140596435680779567895519142876743771602038416260957224921258398740133584101744152907476676321635043841985437670628038504812780327508684713742451774615718107885608832861182065882190536002297597052623993059465688123453892669802167691983640906983055174350738525390625)
  | 88, 1 => ((40342338911661180943354353718723084907082850342443724479089675480533107041079661988755670533641293196551771602941727022319041423189219448115178796524457497465741197263172099211025702452684006777886816056549806050061332519223543695259976290387974784953951078936699971291427756874094664562978470907860514708879029367625097329460406221452815642729320875802473143578112530679377370971765222573206088000361293518575593 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((160656809242616745275771229185200107968795202953944565951299526706126982021616294218418566403501647703281173556169095508099131265503927910279814711033905313975472467287266983775266335185920034373894021531070020751188844928146390001002596496013265151354026332951170823573478627646906501404853777014993610101523775382519456294865400551936454154786081084371837343011902319167874270067819708432891026787478988163322153 : ℚ) / 161558713389263217748322010169914619837072677910327911376953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((110050488323613024932400939809555754017415743404357260656822567398558950416017783854472627914905377538098381088121286076478335061337264635601699502792405698357666578612754349595092993490084014057751143616571093543962258873807315663511422823128550539776309538379619381715692472172098383128812031894967230982325717 : ℚ) / 110065682146379182109343180209360521290881797314363861502436149673497321489824286256370050815491327878932496062917450317950477835864613505109512006204492720712620327539938523464639730445161795674119087142527602691193955881845425007179990789449978310830275385793414593131774037448877834322047419846057891845703125)
  | 89, 1 => ((80693073268527678714998114165425605467598327087572186976669203250564605076021239987509983682271510494761582504848923380509637311078883708885086799681260160799928531842381514865521594349206056426752385282705227371722235973271301076227536553354075713410847494033885548841134794727826813359706747113969960921960182643719926207740032962028219556817702949790695979941883206173704330193825338404769096620969288889074839447 : ℚ) / 80779356694631608874161005084957309918536338955163955688476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((8036472311152167870191064067720366703208416151022715499590882951382328860070168607916399498056313172511732055633436826131215907750904681063466785273096089771772171728401702131175176270458688833678519654570574587539283151210486959073979987068913675006890999025867862505609539924378084653692154214173718248273347736748411630361379843026582606236324792947409434664534008113086204188227657725584631497989535057754373826243 : ℚ) / 8077935669463160887416100508495730991853633895516395568847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((343912288576652251595304782303603747184643616149888400003717757056153416258976105758590496835553332057785173047893479768712023470713574600499131259739657653007129321596231042123920985532170645070533603028993750541609872992035179923542761008274184484803995164118207745652115200425010944281928509893246523096190955801 : ℚ) / 343955256707434944091697438154251629034005616607387067195112967729679129655700894551156408798410399621664050196617032243595243237076917203467225019389039752226938523562307885826999157641130611481622147320398758409981112130766953147437471217031182221344610580604420603536793867027743232256398187018930912017822265625)
  | 90, 1 => ((100875915329490547532046467347155414389444301119214418692361231477117338289102298534755287368022119529992515075284576402780639969208547242272350657808351190193012326829978006217593584623828980038394362556158416998353257550178809062331105842596388335918446630685182985923871499295826070515286958688647353686505779957786509649679644229810490241780699453356428215731168588797472954431047078449275428213883921392677232149692633 : ℚ) / 100974195868289511092701256356196637398170423693954944610595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((401990975632634351716223888622965057181002377745908537780137710062733492010978807022903925344076419284474283096829710050815750043195779920211577800915372022981609399800483488923115296712196831659382258827777365095643255014380878081852098740600003139959935496967616094333711576097122461974181329683032959584141238516717973826202133892168422275939675371225843585717948436488646923763779289836837516701932139245106093585925329 : ℚ) / 403896783473158044370805025424786549592681694775819778442382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((1074738663336880745906756063486404130861271814604278354167462368370516562688127592766987378464072711747050692287838019362265389616589833379641309033302296649115562462972146829217067296904394375869510807120152757779437111124313273908567857082857654842765047666565804423954609565309170690409444087522723648185321235895853 : ℚ) / 1074860177210734200286554494232036340731267551898084584984728024155247280174065295472363777495032498817700156864428225761235135115865366260835078185590749225709182886132212143209372367628533160880069210376246120031190975408646728585742097553222444441701908064388814386052480834461697600801244334434159100055694580078125)
  | 91, 1 => ((5044232408513878601218284362189405554204135659904817351530491858931042259393489651869881217625727524192164038031710306432034048848410612146402834289322346746638689569201108496860508177341020006523791161297894783549076364176065061884335575270839085409278105383068381125100175835132943391814554884067247004940828803463330377860511935015365710696902687464339685736792451775048637441543419899736200090319499840442137709779949858383 : ℚ) / 5048709793414475554635062817809831869908521184697747230529785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((20107258940569833578196964647110804551170540179143074640241384382302390284807199034276045758584298428108236131251846414111671311881843966932709163205899614013598342198650701693878944171578399577024025831938644830652095294843790127672211375668017106386326273526746376200882543029132391835692334760501371231167173874895538537455623004717414940505944143649184912991820103832052591412705169286967342442891524237876902329356738449691 : ℚ) / 20194839173657902218540251271239327479634084738790988922119140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((3358594412548286806909412832326465675272863154614630307326047800925929281493722225100332348212422280969516304378741101807573356965128062577093640167299347443734437962466498239559049908831301643740357118017537096649511869955926017003395302803628513894525021496171572783601222658529458899915877446841207729784629745396675409 : ℚ) / 3358938053783544375895482794475113564785211099681514328077275075485147750543954048351136804671976558805312990201338205503859797237079269565109619329971091330341196519163162947529288648839166127750216282425769125097471798152021026830444054853820138880318462701215044956414002607692805002503888545106747187674045562744140625)
  | 92, 1 => ((252231532487642460604130328260875050915713994090420208904771687039258431912165763599192094625459384823114051525151540968636556442570084132310071312902404212774244305866068190908513685855969402940960626727162272713442938768634515136566510687865435048472219060548144024685622843454094109164818786867824348859686928854734520033108291399184021485390914208271412884513224266088220264553743341891791781444266061241277542022284109422830281 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((1005718058553188194083416685125534057200324683498200896733762550938410320543212125258420420962664085080573967408992169260392687105351835207620300540925214373523075962682884658194238270856013592100116886128082447677769603937192322584563141110242839401389570672721490684926771214563822240470408052727156104329833226149444746691189957111919359183226861874302307660873422629160349132362887461408516225154592075600320848922099244319187577 : ℚ) / 1009741958682895110927012563561966373981704236939549446105957031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((10495709600660267769580777879778353658412864697855584264557013878437616889975800804944027511732307248546970066872877282946463813276794704028858371334123968695992325924046716416889191870880153388439544165634048339478768692286509021054243800620246018541171344213434076184079216452806072854705756317563639374570124452116807822277 : ℚ) / 10496681418073576174673383732734729889953784686504732275241484610891086720449856401097302514599926746266603094379181892199561866365872717390967560406159660407316239122384884211029027027622394149219425882580528515929599369225065708845137671418187934000995195941297015488793758149040015632824651703458584961481392383575439453125)
  | 93, 1 => ((12612484560070362284422464851366794425808821979553976345104202085873110833041852416796866595876495150673858894089396618629611108585258312271570486101172608616097479285193223942080721557805614015952812133831326097805411818161078681086452594440941050820713417994787405634337018609115989274631958405180111867339835921028090484295216543398402476401599435604317733325645545537054099329266096948211516280500694234539440178873327992538078438879 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((50302254467571863965724668544774576308535756174635202085186624980143839533177089648739180587710371350146662141060764993567974941842732331617312089116619118104347972860346968083138658103479082513231853795522670564156563161206667355618956745177434707408847494123668656600557286379901380761495058218268693377273798459278844855109514489243078815448585737620034086785654912654193791844212454934116454898202344427268373605899350790577143539059 : ℚ) / 50487097934144755546350628178098318699085211846977472305297851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((32799381131835089376252434812635398923307855417427497785913956177656233320825172027507608650015143142532012468147113978155869538257439620058728839573532002613239220732552424637638255638052924844825200387539505673277048874446092027068407356565257556832728134630156781048747770298800458676056800421997171884844285488508238038977481 : ℚ) / 32802129431479925545854324164796030906105577145327288360129639409034646001405801253429070358124771082083134669934943413123630832393352241846773626269248938772863247257452763159465709461319981716310705883064151612279998028828330340141055223181837293753109987316553173402480494215750048852577036573308078004629351198673248291015625)
  | 94, 1 => ((126133124512969283769348436262654522166909260581707184382840919278679654088683055726848592150070994718536268734826281685835340074767944097186259280076754930418380128564665645158391212001846301460738003568949951554215655925391331553724151900474966471826609813444676732571529867351545308050940552800403596888744422626591718122528544426712436297398322149840445362491814985623438726888075811497803174113391989460522557648998707563415426832845093 : ℚ) / 126217744835361888865876570445245796747713029617443680763244628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((2515865467568093953907740005055679004735571322028790948955119493610179810222308143570989942086688787867574205252746148766803290095400456357204943808234255404704532433014679357568316915941062100648895864764907552824378891776331056419348610224164256810912184194712819313407686965719368489664608967139731259471049946974918679322793403997288597738963654669453220545979523925320722812305749048486767568220828025871421886392567959661151819546231329 : ℚ) / 2524354896707237777317531408904915934954260592348873615264892578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((102498882281979170643160619927077329334227971532647168381523170974895117693711109466059951158605881818459222256890716523922517411412864861354576925315915438205780900667121727533602302654425706030909946343231775072874653631495562363571349405651554046967628830967099669306395401187085461645104011455680501257714556667507251916659956893 : ℚ) / 102506654473374767330794763014987596581579928579147776125405123153233268754393128916965844869139909631509795843546698166011346351229225755771167582091402933665197647679539884873330342066624942863470955884575473788374993840088532312940797572443241542978468710364228666882751544424218902664303239291587743764466722495853900909423828125)
  | 95, 1 => ((31535168171990243773405088474071142889491829498424535160333466660583974267278259907771586054859198164657767292199811213075215766958867855919336750882679318145866025767868381052165881802188366657242882630112907650310540088555878478569633356480073560933850630426519466365292102244456644796488859496084392936855331022976997048526444751997775055663365292263678097855010954379477728965141867788029038202577741891712289695613421955926604136331857763439 : ℚ) / 31554436208840472216469142611311449186928257404360920190811157226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((125827917803062211599766629039630156339336089096758030356918533932846507956212653271563106853296823843225271773292251473129822702375610913074740862832167168044297290145540163060336534627969723476345003099357401905909829342466985764984650689630065705718394411277740071748287122499513331994122816403948495410867162211569533203041952038549315660429469945577192962428534182453129760259935497748287379684939020251310126491424407341679268764424654146507 : ℚ) / 126217744835361888865876570445245796747713029617443680763244628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((320311315472029400476104277769226003541925942282333081692192849093513673657869776858356397802671986943161089908020315684958249105790661877374780316674555530544512088447443591272406423500503504685864202156378375621236893640375744461123192998198237583089059540953133778862663403251070699623652206466266017454863382836979116990413235046529 : ℚ) / 320333295229296147908733634421836239317437276809836800391891009853853964857478527865518265216062217598468112011083431768785457347591330486784898694035634167703742648998562140229157318958202946448346737139298355588671855750276663477939992413885129821807714719888214584008598576325684070825947622786211699263958507799543440341949462890625)
  | 96, 1 => ((1576844423213484704430750477592832317932235848532456517588290720170147377362617249690797403342507900710565134031126780585745874945747414282587358622272879423003935545175742005694638698697606494208141949747504676792830447427843304319895482607898028207590066058670382728738984378874791033061115737175714809492246354378573187759748878953314091480583775770875688582075006920196894090658784653606317778027771981938534789910242979144236781292790285179900329 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((6292990001801439577516503887575875371336167828525605259965591647462592814119085932852645283520056613213386937989511718910125927861529454676278526640748868285050997752760490494789849412582740912666187565233187378955600358290272312226183454788374580144192410902740241321968912042155629220642911692392667892630774673682561765241549927990710558935129180544924564650996433732581677563093196055853684240866971828032808772158596609700855810460494161221598153 : ℚ) / 6310887241768094443293828522262289837385651480872184038162231445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((1000979388838000100475316786954656501093845435986959484741913007163051296667126851731490817755126857702004591527173231992391209303410616943790993647684226388187891752881943431766425089390010186346782944628609657866693476372814774389004567545828499442052751653622262058074165881562756107570994883854105172043749323479441344630447619190099637 : ℚ) / 1001041547591550462214792607568238247866991490030740001224659405793293640179620399579744578800194429995212850034635724277454554211222907771202808418861356774074195778120506688216116621744384207651083553560307361214599549219614573368562476293391030693149108499650670575026870551017762721331086321206911560199870336873573251068592071533203125)
  | 97, 1 => ((78846141423481385021343862583020969159482726735357034405360184156051492853317649233384648373671920914868378109834976131573960090396372192197046148961728161384725248461228052117266586412463244070353708833021588914294189737192480914590189918155207564854440828318509094567162397326977090456257786878285114449554012789596292466159332723789853350321299723440805055571643966952737799560497659497656203158718230067028225233940359826368767189537053653957008843263 : ℚ) / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((314722834151366567503157714800982197097110368484164976468825032948841769862058356129578308625248153182807715629169657516803571437160155385722325749340445898279849189987247332699650901962249616405365418313117938227695550050466966924366344769772208771311018093569916819153900470945413458476578691373046439918727593845438421096687076560667043924970247614425361265335038104983089344335925084013723590326079851161920059592927497424190227954104977655581229771811 : ℚ) / 315544362088404722164691426113114491869282574043609201908111572265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((3128079051268554771421989277955535344709891365510251203213853827777717278107981995371840172515156499289847201299132710184886342510778428325088164136052815187695394023251926511435636789453030916661073982817119398727745217300545710262567972478740132537990466900840006261016721666711749800446106168937862159919084576851311378182277712314963101561 : ℚ) / 3128254836223595194421226898650744524584348406346062503827060643104042625561313748686701808750607593735040156358236638367045481910071586785008776308941739918981861806626583400675364442951200648909636104875960503795623591311295541776757738416846970916090964061408345546958970471930508504159644753771598625624594802729916409589350223541259765625)
  | 98, 1 => ((3942485724792967878732776424280513043323412082646172375484817239673646235946270316323904287232941309642135961835823948863142306826696176796264306984606847826119484435691298145613050587078206398908650103281241123400751488395227784629106888632025558552118798632694830482712955060356623846676777413849523380384902270878583183049015779388462365808807435598835591067786716975701289195732604023822783094734138420812653752992181325701712453617180865843883002950762137 : ℚ) / 3944304526105059027058642826413931148366032175545115023851394653320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((15739514553240751458409449538051135115475080708724919155836133889075419828409446597856701003241940945979951347799920624847560666565803693539602970007665755924771846543624884506779255614588195145556494794201578935022843224277998516691486771248429862290430985063327738350502899803564309446195996737598381205068132359196010633304596274376259803469289687392053130370333893226288079086155470329306445046411910831330267891970799472978420231283457261565439456740075377 : ℚ) / 15777218104420236108234571305655724593464128702180460095405578613281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((9775299243345880666324490066957525078641124258347770966325415635957285122281083266271514445071793035330994811712343585997871084747772656578496934740513058106740187254324543444340564080129678025043679146554973929229363681145398044530239274479680645179516056721813816333602103103624189461397002737626438980061675839746293751147518386818469801605133 : ℚ) / 9775796363198734982566334058283576639326088769831445324459564509700133204879105464645943152345648730422000488619489494897017130968973708703152425965442937246818318145708073127110513884222502027842612827737376574361323722847798568052367932552646784112784262691901079834246782724782839075498889855536245705076858758530988779966719448566436767578125)
  | 99, 1 => ((39426485393196262656123377009738641886196080709673242772167576967092742186419552314428298411410685700410546173498603934979129800810104914248896330176351378408894015223060470455116438500155873259577751610267551286985141290853500230911944314783249463294362670238246501421149359245574935331814777256580844435752185535493804002436637205004933828165185856853672790894653759941795607977394974120860841818826518528277285605558102593842826640248109162242603081224268772483 : ℚ) / 39443045261050590270586428264139311483660321755451150238513946533203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((787130820941248491848563358345341220017455274604865207245894373903619876013541939792771205756678081718321623360168614486951761962386964903531028853056379851768954274023262375600667790231204198681872844049731442943225250645156871468016061734797983194187820588821987639034183437649999034048584979421944193930461734823651019403279620218489164669291480829954421743709138393240611499328235415034546203654473646182751403869169401603556517149668164908898014590159743102587 : ℚ) / 788860905221011805411728565282786229673206435109023004770278930664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((30547957780052174814187859124666103184276947767247435554132766077868141887659997800015687966909688376851387472642496041186393515564486264288825601957907480688166290044505106579346937842220812557092780636295467114445953635964981844643069944196672959449168334428784093302198042046309711002253894029101834410022246326086222395895297674146864318910019249 : ℚ) / 30549363634996046820519793932136176997894027405723266638936139092812916265247204577018572351080152282568751526935904671553178534278042839697351331142009178896307244205337728522220355888195318837008165086679301794879136633899370525163649789227021200352450820912190874482021196014946372110934030798550767828365183620409339937395998276770114898681640625)
  | 100, 1 => ((9856992259686785994837403997337952563739221852655819280909149869302661242633944929613530026998503320300356855079843219112043281816544705091724438633020816898161889083172806234098332986110119034183500836976725305581422020672492495513804266617330174095684760725144516754308503042728775365876782613275173741122772420800786959912302814983007024026764343965211884695124669622182645862620037910788014256949925510932433110271275457947483547922700663012301026346420497928627337 : ℚ) / 9860761315262647567646607066034827870915080438862787559628486633300781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((39363671173707308044641257532153613956322622663126352769157157867419677431119682885447626192151321203697646930668098981439367459291643980021786280486967883998984009678305334809791355525457651853493492315515765160674908732909084813067488823526638289656843038503960559310423904582291815533608809724519411421840101072274640104273855583349021915588354409955106803861572445560149822431551398503176782397708005433316672782567906618620836037278441856903258507241944903202381081 : ℚ) / 39443045261050590270586428264139311483660321755451150238513946533203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_open_source_model__apps__causal__paraphrased_base
