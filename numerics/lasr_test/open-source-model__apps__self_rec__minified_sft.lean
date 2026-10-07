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

namespace LasrTest_open_source_model__apps__self_rec__minified_sft
open PL_TMCERTF1

def cat : Fin 10 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((20353 : ℚ) / 50000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((20353 : ℚ) / 50000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((20353 : ℚ) / 50000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((6677 : ℚ) / 100000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((6677 : ℚ) / 100000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((6677 : ℚ) / 100000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((20353 : ℚ) / 50000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((20353 : ℚ) / 50000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((20353 : ℚ) / 50000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((26239 : ℚ) / 100000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((26239 : ℚ) / 100000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((26239 : ℚ) / 100000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((6677 : ℚ) / 100000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((6677 : ℚ) / 100000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((6677 : ℚ) / 100000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((20353 : ℚ) / 50000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((20353 : ℚ) / 50000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((20353 : ℚ) / 50000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((6677 : ℚ) / 100000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((6677 : ℚ) / 100000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((6677 : ℚ) / 100000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((20353 : ℚ) / 50000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((20353 : ℚ) / 50000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((20353 : ℚ) / 50000)
  | 8, 0, 0 => ((0 : ℚ) / 1)
  | 8, 0, 1 => ((26239 : ℚ) / 100000)
  | 8, 1, 0 => ((0 : ℚ) / 1)
  | 8, 1, 1 => ((26239 : ℚ) / 100000)
  | 8, 2, 0 => ((0 : ℚ) / 1)
  | 8, 2, 1 => ((26239 : ℚ) / 100000)
  | 9, 0, 0 => ((0 : ℚ) / 1)
  | 9, 0, 1 => ((6677 : ℚ) / 100000)
  | 9, 1, 0 => ((0 : ℚ) / 1)
  | 9, 1, 1 => ((6677 : ℚ) / 100000)
  | 9, 2, 0 => ((0 : ℚ) / 1)
  | 9, 2, 1 => ((6677 : ℚ) / 100000)
  | _, _, _ => 0

def kernel : Fin 10 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((29647 : ℚ) / 50000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((347 : ℚ) / 20000)
  | 0, 1, 0, 1 => ((19653 : ℚ) / 20000)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((13603 : ℚ) / 50000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((347 : ℚ) / 20000)
  | 0, 2, 0, 2 => ((19653 : ℚ) / 20000)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((13603 : ℚ) / 50000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((93323 : ℚ) / 100000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((347 : ℚ) / 20000)
  | 1, 1, 0, 1 => ((19653 : ℚ) / 20000)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((12247 : ℚ) / 20000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((347 : ℚ) / 20000)
  | 1, 2, 0, 2 => ((19653 : ℚ) / 20000)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((12247 : ℚ) / 20000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((29647 : ℚ) / 50000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((347 : ℚ) / 20000)
  | 2, 1, 0, 1 => ((19653 : ℚ) / 20000)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((0 : ℚ) / 1)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((347 : ℚ) / 20000)
  | 2, 2, 0, 2 => ((19653 : ℚ) / 20000)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((0 : ℚ) / 1)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((73761 : ℚ) / 100000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((347 : ℚ) / 20000)
  | 3, 1, 0, 1 => ((19653 : ℚ) / 20000)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((0 : ℚ) / 1)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((347 : ℚ) / 20000)
  | 3, 2, 0, 2 => ((19653 : ℚ) / 20000)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((0 : ℚ) / 1)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((93323 : ℚ) / 100000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((347 : ℚ) / 20000)
  | 4, 1, 0, 1 => ((19653 : ℚ) / 20000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((9781 : ℚ) / 50000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((347 : ℚ) / 20000)
  | 4, 2, 0, 2 => ((19653 : ℚ) / 20000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((9781 : ℚ) / 50000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((29647 : ℚ) / 50000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((2061 : ℚ) / 25000)
  | 5, 1, 0, 1 => ((22939 : ℚ) / 25000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((13603 : ℚ) / 50000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((2061 : ℚ) / 25000)
  | 5, 2, 0, 2 => ((22939 : ℚ) / 25000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((13603 : ℚ) / 50000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((93323 : ℚ) / 100000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((2061 : ℚ) / 25000)
  | 6, 1, 0, 1 => ((22939 : ℚ) / 25000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((12247 : ℚ) / 20000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((2061 : ℚ) / 25000)
  | 6, 2, 0, 2 => ((22939 : ℚ) / 25000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((12247 : ℚ) / 20000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((29647 : ℚ) / 50000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((2061 : ℚ) / 25000)
  | 7, 1, 0, 1 => ((22939 : ℚ) / 25000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((0 : ℚ) / 1)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((2061 : ℚ) / 25000)
  | 7, 2, 0, 2 => ((22939 : ℚ) / 25000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((0 : ℚ) / 1)
  | 8, 0, 0, 0 => ((1 : ℚ) / 1)
  | 8, 0, 0, 1 => ((0 : ℚ) / 1)
  | 8, 0, 0, 2 => ((0 : ℚ) / 1)
  | 8, 0, 1, 0 => ((73761 : ℚ) / 100000)
  | 8, 0, 1, 1 => ((0 : ℚ) / 1)
  | 8, 0, 1, 2 => ((0 : ℚ) / 1)
  | 8, 1, 0, 0 => ((2061 : ℚ) / 25000)
  | 8, 1, 0, 1 => ((22939 : ℚ) / 25000)
  | 8, 1, 0, 2 => ((0 : ℚ) / 1)
  | 8, 1, 1, 0 => ((0 : ℚ) / 1)
  | 8, 1, 1, 1 => ((0 : ℚ) / 1)
  | 8, 1, 1, 2 => ((0 : ℚ) / 1)
  | 8, 2, 0, 0 => ((0 : ℚ) / 1)
  | 8, 2, 0, 1 => ((2061 : ℚ) / 25000)
  | 8, 2, 0, 2 => ((22939 : ℚ) / 25000)
  | 8, 2, 1, 0 => ((0 : ℚ) / 1)
  | 8, 2, 1, 1 => ((0 : ℚ) / 1)
  | 8, 2, 1, 2 => ((0 : ℚ) / 1)
  | 9, 0, 0, 0 => ((1 : ℚ) / 1)
  | 9, 0, 0, 1 => ((0 : ℚ) / 1)
  | 9, 0, 0, 2 => ((0 : ℚ) / 1)
  | 9, 0, 1, 0 => ((93323 : ℚ) / 100000)
  | 9, 0, 1, 1 => ((0 : ℚ) / 1)
  | 9, 0, 1, 2 => ((0 : ℚ) / 1)
  | 9, 1, 0, 0 => ((2061 : ℚ) / 25000)
  | 9, 1, 0, 1 => ((22939 : ℚ) / 25000)
  | 9, 1, 0, 2 => ((0 : ℚ) / 1)
  | 9, 1, 1, 0 => ((0 : ℚ) / 1)
  | 9, 1, 1, 1 => ((9781 : ℚ) / 50000)
  | 9, 1, 1, 2 => ((0 : ℚ) / 1)
  | 9, 2, 0, 0 => ((0 : ℚ) / 1)
  | 9, 2, 0, 1 => ((2061 : ℚ) / 25000)
  | 9, 2, 0, 2 => ((22939 : ℚ) / 25000)
  | 9, 2, 1, 0 => ((0 : ℚ) / 1)
  | 9, 2, 1, 1 => ((0 : ℚ) / 1)
  | 9, 2, 1, 2 => ((9781 : ℚ) / 50000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((20353 : ℚ) / 50000)
  | 1, 1 => ((20353 : ℚ) / 50000)
  | 1, 2 => ((20353 : ℚ) / 50000)
  | 2, 0 => ((1621055391 : ℚ) / 2500000000)
  | 2, 1 => ((1294511859 : ℚ) / 2500000000)
  | 2, 2 => ((1294511859 : ℚ) / 2500000000)
  | 3, 0 => ((98941929176977 : ℚ) / 125000000000000)
  | 3, 1 => ((68491744817977 : ℚ) / 125000000000000)
  | 3, 2 => ((68491744817977 : ℚ) / 125000000000000)
  | 4, 0 => ((5477456374309837119 : ℚ) / 6250000000000000000)
  | 4, 1 => ((443762862603331 : ℚ) / 781250000000000)
  | 4, 2 => ((3475818204758941131 : ℚ) / 6250000000000000000)
  | 5, 0 => ((289596399129163741066993 : ℚ) / 312500000000000000000000)
  | 5, 1 => ((92724848029515052774259 : ℚ) / 156250000000000000000000)
  | 5, 2 => ((174487805039335876204993 : ℚ) / 312500000000000000000000)
  | 6, 0 => ((14945976944982317431413141471 : ℚ) / 15625000000000000000000000000)
  | 6, 1 => ((194035550260131922460661079 : ℚ) / 312500000000000000000000000)
  | 6, 2 => ((175391503334999468472073201 : ℚ) / 312500000000000000000000000)
  | 7, 0 => ((761119003487890764889105405190737 : ℚ) / 781250000000000000000000000000000)
  | 7, 1 => ((253352732854466864692397709130781 : ℚ) / 390625000000000000000000000000000)
  | 7, 2 => ((2211606482043842349736154820779 : ℚ) / 3906250000000000000000000000000)
  | 8, 0 => ((38465676346405497506667307947689779839 : ℚ) / 39062500000000000000000000000000000000)
  | 8, 1 => ((527679317763430947391770733584003187 : ℚ) / 781250000000000000000000000000000000)
  | 8, 2 => ((5595364091573426174190797221903487741 : ℚ) / 9765625000000000000000000000000000000)
  | 9, 0 => ((1935430969141883784580165678725158902886833 : ℚ) / 1953125000000000000000000000000000000000000)
  | 9, 1 => ((684499552458708855472232764564361091577829 : ℚ) / 976562500000000000000000000000000000000000)
  | 9, 2 => ((283892790640966425583886381994403974791773 : ℚ) / 488281250000000000000000000000000000000000)
  | 10, 0 => ((97131675067149428561448171877164785993885937951 : ℚ) / 97656250000000000000000000000000000000000000000)
  | 10, 1 => ((1415695747804082694054992649461452426330296067 : ℚ) / 1953125000000000000000000000000000000000000000)
  | 10, 2 => ((14435187026643656624065811160906413765238867263 : ℚ) / 24414062500000000000000000000000000000000000000)
  | 11, 0 => ((4867260426965779108561253951642304410360736402433297 : ℚ) / 4882812500000000000000000000000000000000000000000000)
  | 11, 1 => ((1823920620257287618211518501538649484312931992162661 : ℚ) / 2441406250000000000000000000000000000000000000000000)
  | 11, 2 => ((735201233813963039410074780703565786988297257144089 : ℚ) / 1220703125000000000000000000000000000000000000000000)
  | 12, 0 => ((243679552690754453231515495904339398853964752122939956159 : ℚ) / 244140625000000000000000000000000000000000000000000000000)
  | 12, 1 => ((3748370158245612483642111608316998017242486866474143459 : ℚ) / 4882812500000000000000000000000000000000000000000000000)
  | 12, 2 => ((37488662603267266103189350420789347762618054399103759463 : ℚ) / 61035156250000000000000000000000000000000000000000000000)
  | 13, 0 => ((12193361839247797274954739907075950157823493006188800880245873 : ℚ) / 12207031250000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((4801416711095450166223473346218024376914291665627898089943749 : ℚ) / 6103515625000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((1913039635316300817501780819223507019491810235517162518368489 : ℚ) / 3051757812500000000000000000000000000000000000000000000000000)
  | 14, 0 => ((609946305479429445810583174025080694328993097154479379696649396831 : ℚ) / 610351562500000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((1963279316978614183277457833010192445114784736971454617477008487 : ℚ) / 2441406250000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((97662152230608971697933278990891403281065625107915479981083605031 : ℚ) / 152587890625000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((30505563470111144779946359360321567344771658351338850169866564667848657 : ℚ) / 30517578125000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((12516015398636211775366013229520892435634066543582431369131068827691941 : ℚ) / 15258789062500000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((4986334054072493882524638047773366628401425166563217386399667943075593 : ℚ) / 7629394531250000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((1525522707776510109291069715955453507070445355142142890986034042707709134079 : ℚ) / 1525878906250000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((25483268830821247728868456063423290138383763709943366262123606618291478051 : ℚ) / 30517578125000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((50911708293865421362298939524357814697528478987582135661004619749259029211 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((76283385096356445210152343868931330124117493443899110289062951264155452698040113 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((32372137486237817417874570366527532302291445664067500432664886772869999275931269 : ℚ) / 38146972656250000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((2598332438407570759105540187232064827569256244023259609186753711057999423457813 : ℚ) / 3814697265625000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((3814384186896992031145386538682207144189711328131276922739849316128416706138795230111 : ℚ) / 3814697265625000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((65695559211088368843014940799576703934013323926558594046222336716846168591673417283 : ℚ) / 76293945312500000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((662750453405448798129459353074576594871134359330138640143071765418479556254682069479 : ℚ) / 953674316406250000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((190725581436200747747367274712311395203792371745107966928468312675259170086896862187100817 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((83210967446352505220686628006298529501291576924844941179081538537927379897571882921995621 : ℚ) / 95367431640625000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((33790628989686508165219681025053614689697938652664032090715452353204503918538276809064137 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((9536467985202324818466197593395895933606832445127215895528300065883408615566231273260977921599 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((168425527513750799024879402914201508879010841772988149250139040698669659379595891106517195363 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((1721744280695770134863783666388391004036123969549025888027930573986984560743594714148477452167 : ℚ) / 2384185791015625000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((476828999975457386393067360051408126743641761500686569654727512053245415225692058558368212441645553 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((212830319299398470392444264412432362127945166640935949743130799165124870982109509958810772718008389 : ℚ) / 238418579101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((87668309414906552167037578281720835228160329097323424081058812945373831877328316584967147041596201 : ℚ) / 119209289550781250000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((23841616043180588259395268023444096733568747303210854730553706549842566825196092460079942394257465709791 : ℚ) / 23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((429878958310688827920826791671180962356980561024230980894949928257573505267894857223164700663960814211 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((4460689987413143047798177645362811576943234566773973042411408797387183017962196208310231774546165799207 : ℚ) / 5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((1192085724877585056376291511091047135860112651298292210196725738083182578666588553163990052162551085898173777 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((542187241899439743586405936103579288143224042658659295137134009414249462093741153052333514701094492687185701 : ℚ) / 596046447753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((226797048569498418605505394454812668612445138861229836530362907860000657356997920163280374554339575488240521 : ℚ) / 298023223876953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((59604432187716271978887914429316274436844759773040469155702327956952113909728350835652813076463152043623157966719 : ℚ) / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((218650839702681594859589346727349269827540198427358011100135086640771008932547965022447523879710647388310733959 : ℚ) / 238418579101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((11522442899826193760314959121107372523464942832594999247617622680203878299599551097691836397602946793677788352199 : ℚ) / 14901161193847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((2980225936182749705983089999085939588229136592991330789059106916939759321081716417224598949277903068637295764239318193 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((1376752637723836512669517997783487066757823202823527761086402186032439850243879573484761385319761191472022310140783109 : ℚ) / 1490116119384765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((584956557936629463211431400008797392270844690893641483091873595018222159805275874748814113588738448533763126858373097 : ℚ) / 745058059692382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((149011425085686250064530669202900850972229212572413983903235342766513044592109646621457685049241992275889907522403066467871 : ℚ) / 149011611938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((2772196126718672746891331807617077645602226536691717575174911153864364776409524984329351250806470486672596244589443290819 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((5934824830273102713165185272607074721437937269967554935377610339531770955779816476535637423673634071491164543041718986363 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((7450575057299153732225640749858401528773679465134357380779218206998812233022274693386355988654877345003308088316683711572971537 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((3486682894641581068430010725973585859477238133370310693671432389366516565207242662463373705998969070769743362135534702395134181 : ℚ) / 3725290298461914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((300845374649105328931307544214161359208060630532179634937431466597610866930166575274015938362859662297032751206162196768251509 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((372528865612938684527418571311052030123553275102838293267961482182893786272411377834825295995651148647313074894324721997003887157439 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((7012706921338400483981963106866973504475971378416200982641757755359263959633471480462557543057536209473044157522989848241434411747 : ℚ) / 7450580596923828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((76196973936614569985586889673518034645119615830652896797954226277310347406003037829443529309120253189172783868542883338305585196551 : ℚ) / 93132257461547851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((18626446623286326871590628383658759537072983946973846880515254062276252081618180118669065550383069603946890731392045033045174242556594033 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((8811006195457345063914122260893153495043358672461411439466232672288251892009049964234105309056878172817220243828196458476338209984703429 : ℚ) / 9313225746154785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((3857094494385964326735925973522981203266922160351588354927160561495330193812721987570043515049858529005967578537382453725423545712630953 : ℚ) / 4656612873077392578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((931322430263546417332359859690331243995602755075933638466635737184304045463734185978181786372206864548213469513579959094690280769075343296351 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((17704817949031407860984015447359071978060265163595909297622950446463671033672250539348369098730038530649718885749960077403341940463494568707 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((195115264982276859558717817792988120996764217096553139524088177777868845781170711322024947425423635507912071490667945112934714480982556628903 : ℚ) / 232830643653869628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((46566124451172194863168097760239250390737634879736204579620349700303062035863327411695155420576816913260884730669105047280282753960776702706918097 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((22225996475414742412277610188170260299111158407597827397788379268908358129771143913406644599501536040562563036678405006471919707279669378112273061 : ℚ) / 23283064365386962890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((9863738871680741052872057440631885198759103914509944161646139941847107556758512603071785255795650785123716781437130678879426024440899290673440009 : ℚ) / 11641532182693481445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((2328306309661343772534125844297813056334198661279539257172004507564884880177240067774526272753840891027445449610146957336718542806675146905152000821759 : ℚ) / 2328306436538696289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((44626281951717737840138465987869131882317279636436377719773312193252090605342194330190950250309611605086398017065635615574535803459593300532552867619 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((498336390690798822135368405859128535625138266867946340514843457925281726594425368809258458484965532499505320917366874003968933666002976245805475511623 : ℚ) / 582076609134674072265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((116415318065401944395608291405897263681139987710954500357378417635776142042614636289311380408333120896290675244592026844161694638589498080297041368362689073 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((55982753388734688930939646929884293521528587319907833834725501710141713057842521566695809037738275106861409277319943648354190756502538013817329785209257349 : ℚ) / 58207660913467407226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((25162046109674724804139566184030055977646491240635026572151308073453389021139303633094248270020451437964381770876264320646564696002140089015003392026308969 : ℚ) / 29103830456733703613281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((5820765979828575724061052140310636176354757215666668072095197947647855283137396122069214494965852035212329648976419819848861760950262849586566385447848642947231 : ℚ) / 5820766091346740722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((4493293968801861545876796496698857405804028869976014121449749577928345824668044751726625731287889836031748506406381667240017305883130231266245853033641297339 : ℚ) / 4656612873077392578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((1269764806153839218450981629713422437090336143604183794610526970818496652124042409028057984558776856066171271404817658361881082272337913850307842306699282276071 : ℚ) / 1455191522836685180664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((291038301261157998419460669053789430720389487172869708333406333553915965579174382830986002132252615287939937103203918399059204626892442701692933629372368717456557457 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((140836186622359072068374622008399083699140427431963737811507959930225135828621521607405985636640752230487960142110387579731950313884897201768430348831388202688394341 : ℚ) / 145519152283668518066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((64042194070288733567876683695302610264681756284410597319334215042279939871547342787207103985702777697642201634324944915439927584631025940774256128785708868396384713 : ℚ) / 72759576141834259033203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((14551915130348561875552883267937695252567387126214068242960497570872946631525782927790242005214893285441555315298686568776908239573480248777090403310002615366434558927679 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((282444500350393445723815973896847727146555490511476673287660505565339583464167062852769358377295082837550833830777745488136137489457465529236847350152915195584644819811 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((645678232037077713231993318106480733045399607150693329489186604625182617273927589684870250610637725111892922486489866326476109464923796248737211525074448510006023719963 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((727595758512394348745072970869548851152865326130868481199049871483670248784844886460197304728605941233485790432660160704528998578634968935494399186931647537768685368528899313 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((353941216760532148598445223676209090566283204709265365076023802351735378261801051353159504363586490321823974367041128205866950775294182881487785389479801473846030002032172869 : ℚ) / 363797880709171295166015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((32533016505507855785841313059096138898902097506580275688534244556844952522891491542260265595592863381324384840461346754581313846860633106578351502290691339832556121092614869 : ℚ) / 36379788070917129516601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((36379787984764481998273010398619514790128998323801857862108231539876371865724296348885469493288980339749153228957075784407171220860790924030602452694962554552228215120776277932511 : ℚ) / 36379788070917129516601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((709507600033349546646522614591170433569039852112295854348362471576830402665618957798988735449531113914674180403713018841631929349580527728518022992912818303697976999110803534723 : ℚ) / 727595761418342590332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((8192221503941903796975534408622730237676261831940245357614555415541590273823651211717944063466398687595279849723900097265699368879241939236754376798179557281786716451623233082919 : ℚ) / 9094947017729282379150390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((1818989400991688934854191540850372754982954413305753680037922740462714796703128213855407514067538400132543145778890425780319405184859868524735270915047554854809909893685654311865153617 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((888748484894849859924669787236897748764466123925553359198659401978730832752589438422603082749508299584658556018919180152072921253695476372650818126725674778358537070494056022969450021 : ℚ) / 909494701772928237915039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((412400117249564997788605645315603674433756318705840620411939949702213265079827487091788732337748529633949836090934401958170840805178998379515708433456714692071849242246754839504760457 : ℚ) / 454747350886464118957519531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((90949470101569418704191796689716001066979649491275679352084295486498105577857642156171266569560310948729506642906764453109129405515540522152826576818414858780549398618098593383866209283199 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((1780917605817991710734339570581880526633441835171187813914970192482954733641137820188327164675005536440725466259450692582001591014521490162158145094953340721491847520440497430341860386723 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((20751803206543828529850394227284511635875437070997121456567418039916304421635412285386068415737963647990331864134880923330384125163868464459455007669308772361069244438084867990139436739527 : ℚ) / 22737367544323205947875976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((4547473506619669398951653200366260283632745668467850065751243108288209336066745517004009539987754538696983683442256845741326359485319229860264849522935545318266948020830768998051481506619000753 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((2230070305872280164576090063456392548221271170451113038314420795265997527345667623348870821923861400886021586717307813394784640518872952157644260091479487164461786824121129728694745027884617989 : ℚ) / 2273736754432320594787597656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((1043813007149589788188063232733590218965481392500401390296368844002964456906649071014145603937105956507608824911798263935838994871291177193076075267870018739056002239821154203749981435161922281 : ℚ) / 1136868377216160297393798828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((227373675376675380802143612626571018628860010833066350899327104431420542186370804342617870832016958808749475263012588705693102579661259207667271993806470112050660207973569808485232272226733515324191 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((4467340335598064320866448687088289590874502703226736118292092371655817360047924069381790369205507018164135269079645568879952134584963849273216368773746642841285041431518456183921664630977290586051 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((52484228042411649721683286612135277107582395207433158955982831084211224257822667051708994781411625419882168159527852156255072550814493781660849001187879942756367013403028560930481517784828868083047 : ℚ) / 56843418860808014869689941406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((11368683770188397121212349193305575989289812741167918105112350665078324814199335236345592016556806777802995693122534217357683412179217351729711612800380419411965923185792424112161681174705968528816290577 : ℚ) / 11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((5592433142865527832650991307279276615647591357792854740078628507903797458553076739127579895745043226588187615387968430549294585178906142150917761744283846907748288958513620695437016961558701212754352101 : ℚ) / 5684341886080801486968994140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((2638051124921451930064029591793766364311473879110376045077580383931008535976857606673202011354916300124261180562147539161209752220757608048838903877564851786173817600663132773245194843043483707360308041 : ℚ) / 2842170943040400743484497070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((568434188549580514781142392022211661354475078337405268062265860167577095766567691751937766514859650541525413314003771942003240120877256826730760184692878294306553724689187997653257361786507848973816566736319 : ℚ) / 568434188608080148696899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((2240004039829943778985446647062091557492852002978941351839710987250694777964503076478427004824917375347718764338358069429717779930713783612117925658286706982733902148196848610883397512507672763013076324551 : ℚ) / 2273736754432320594787597656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((132554514216592224510571242696617002366731484414236905815371286208776536175624164438295104042071384107099109117144807737000077152437643101037672739049889278722951627426719777624238740966921428725762931985159 : ℚ) / 142108547152020037174224853515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((28421709428669668788144522270696571624176122647469053982241995956388158158191432357369698963866044059604603928520269826764570059863648033142086847195589762791306398275860356566426121004884598198526739754031649393 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((14017406030015455527500724629197107793383706160536876174939112521941298272306830030535403002706820658041414060629560712634542716346788896889485370909511715033799052570956294034426927307495369054424275396262400709 : ℚ) / 14210854715202003717422485351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((6658417043990007342157113164884766172080003039223810530765309411776710168838390521177857540360170298889448974739038986994920582654184328692478230519846933215678396304012263081223660242240210502651795581727575977 : ℚ) / 7105427357601001858711242675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((1421085471468782433883520340480044383941949508129515043411528454119039724915901395098939465181736608235097692668840439554089208564777573238563448758807649697473860789684431991124835209431813682791722253487776309554271 : ℚ) / 1421085471520200371742248535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((28066707879101490242521764197528421818491386400381781016450294317909555044037011609177686740908457398258763318809730499488373185357478384312066033546267558537340616827875242103793712256173587934641620690511425965059 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((66872946194407082137132606247871708320970039566075296265400075220242584973038411404706242765044530069734698888407031054818551805879880109648549121846808249350710662596843105529066596354848866612365501858038907706811 : ℚ) / 71054273576010018587112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((71054273574485630983414711970247032100726977067515732492021584079267170724581728660498258324242945224345941294553112511460082766319960713803690565352370390581007550831774355240877989454024980253726189649152104249355472337 : ℚ) / 71054273576010018587112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((35119967758632614829894272868084594880023053568172814241288825211865705030809923240445262045224514362505424933099300542309167483797766411331403405067794142290896447558271123264654483638857264681870946415420386984615772581 : ℚ) / 35527136788005009293556213378906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((3357224450201148971236556489495388621189017212068336695438544933900347278121857643057689067439774604028345071602672043530193205425265954420791977087782156054439198835029222365342111512367625126108586395458829252343008053 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((3552713678755307410068795187583671573190252689120638921190963903198033810471674509597791864538830597066184121559616126627257073773087875282138014191001724969555130859509614309826309753343478589582220344528412434680641688375039 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((70307069546702479544908286880506567082611838053471291857116208314293778170674424047777385700682999201216034803552147006647168656122374658008461266915659801400368151333705981571490717465929562935112198260542360037524961718307 : ℚ) / 71054273576010018587112426757812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((842495970182183381676365789506469545862276171680359924717944091149055880196872176539560980255217620519185756762054598483090213576608953858339494042011072504589345399184950103434279850601694350187384653816482259770255724567111 : ℚ) / 888178419700125232338905334472656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((177635683938685194201484532016381001755371421474359582096548506838112108379053734186045735407982710711221160651877939306118290466150736238489545706720628140172400964591881535443420605257374109745344086554233843450976984135254781233 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((87960836308505097486184346519206954227746758447706535012094011730570396556237151825879321562212895794388136592468503846252746919185891724959291097336570564378405375873643390655973302799188821581555891925002117872916057362553169029 : ℚ) / 88817841970012523233890533447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((42274601878412054443099709172495910694001081160056660939147751647130372591916101414343708450376565528021860341982565243724708183474370939366785274437213355632703957221276341545828950203336554128128489163167018214673265784225686633 : ℚ) / 44408920985006261616945266723632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((8881784196961529723250159975194042090291496532450338530416373582229509677113806057413697917640463424455573749846225266608488957449970877262499561567146462471691171397255511881291090684065370231620216134073370756791114648657898499214751 : ℚ) / 8881784197001252323389053344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((176062975710369081908817002803757515627135451348901420479433421710738308343051111905005271012282224001230629707711618094731732792365880317808372426606335957977912008894195172842545322130265311868151014884940924605044257759278975713347 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((2120761468609617239659554395591852923482767670621802659226146308243752821074331670600397938026096851526820858286553714678729073441879312801410473772241146262901085629073295025581501554497802591569865519085205826588860081872928132717543 : ℚ) / 2220446049250313080847263336181640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((444089209848884960243134895509797492413371997697555186411254227592358273397393008184143902164286819144834394961691040479141872121519286598201324501781191172898228158414434160744636965510486031256844547726873222826586175988760716806219722897 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((220240787220945531254936241074644603296633780278002631930074308984106322198594027083775426995794091936014408241692910648232656667508436408548324351086025886156921682850940763479098295117166527494545071974608210605501998727888950001304943461 : ℚ) / 222044604925031308084726333618164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((106367939480348786666452832630426634416230569323539208090179947383252683262623896924710453189669112946010895532160352444361784963493191096078186105003770768484187922748898035464340276040012107490048771326537654052518628217213046096445641929 : ℚ) / 111022302462515654042363166809082031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((22204460492468216843225090383439952585704239615739418611534454085430645731412510513635314267464611327186905307429254277085119082786682289776874667504306974702913770212512729563596252116489379368671670306458610437139800359538788971153996124727359 : ℚ) / 22204460492503130808472633361816406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((440778987904843639439002635506729509676276970353954639475261764425627210051964950576678784882945459363918908373137303565885168841376131809210918175091829224498020048013104366087550734772099106352603816996646447936192592254037003419899481799779 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((5333864589941810374599946648273555661142188280578295213169158776865109732773961432931527326473971187217213560610581738288437475946875508543893118612951294667886989108229732984563424770400155680594714924258562014679389244727479254765422648891783 : ℚ) / 5551115123125782702118158340454101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((1110223024624121446095937761410893590714623591887826543576161960270762353999186699197746162087523332017110181649355101552742525447376769845015003267500188879017284545490364893371938086497560630143009009575578423629883661259246476627802523109792012273 : ℚ) / 1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((551314853252437407168450984074713153402342308995507215504523990578045689421542384232524115026738858562779003797181523389964424832239706577804601290647950203900709374476618788314688190858943680909951260405914839571361222226777185142002096663319610949 : ℚ) / 555111512312578270211815834045410156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((267418177009147444887990963123978424607951484833858540588737528777047946318131296698495985075066614920877245487618168555429167846042659772446321054696585997565579769281238892328461853225550748769142242965886516339373343085496549851338381085590833449 : ℚ) / 277555756156289135105907917022705078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((55511151231227139579648442153201228104228945628698393537402473636147291509013888071115580467408804224311265555358430695734157651938379095595159801871578099696225434920152847993797848450393180001849788106887173525355160905352880292584461402636003787857631 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((220651139930125101331823375789180333938043997399813524313816171518860970806990762326930369514072887523443513764691318355079921819204294248216763357973316389873690945043951670524326633731984725212091883949102625127648803033403125506197385526792467587303 : ℚ) / 222044604925031308084726333618164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((13404871037378939972745426884379865973325825720047502496284924289814757847081026483836831004344014946837893795306937456692696042019991180297147600607395397766553030675880989224961745263642100178386117370485532080974345713085798492657368568667837975139111 : ℚ) / 13877787807814456755295395851135253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((2775557561561981560479946131548580100621700551054021273203371135890858751367734739644363614117268818838156089919711394836430571907017125047109702646086675921693995469077771484472124813008806607514840668004884033506204455360996842034251527203949604298615186257 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((1379787607401844059536329543584749651174013671029327997639243787781887520135467897568933147914159037231373208871657263600702680573326825755982708018794798630302069768461236862254599528450759746893856344765410744086540959821740860279682031600605907303060456741 : ℚ) / 1387778780781445675529539585113525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((671833923377369487300225691789267074655030817214466278725906647755668018112534328169941569263357745379256026774720277529374973874465661675369381280763961693675129571065016072781624598220574836816763464325522804609451555506430743454668856639682980085611069833 : ℚ) / 693889390390722837764769792556762695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((138777878078117594991654401313651918793912806237098568686660344065756289401799231826236448067734668672094813597849683722715657165327336706271661354348531681050461883671748691200145084331272089492992481284340796941358443488087473375789455027015493918641044426961279 : ℚ) / 138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((2760892799470441830382275831108110723357708961408233908790614976277139821413755900122981934748059173829055191117536684969236839521738016270202711025594096425424387259969356471840542656235004243443377120076223204410344541488033667173753785733597517988370141329571 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((1346645559822486317802565179089446555283725840326269157540865065294120300558641969786806021300616336729734727194204100510948531042974488569027073425025004582379206410164776662407284117812021928073108485715513870937391175268665502449988898881768981412770890525663 : ℚ) / 1387778780781445675529539585113525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((6938893903906428722122849953327396664022195466511261265853419220517476711895141825952431975864129722121594938735449573327351087980459551330835944172370918748103043465216333448010701315169223637198748092636851606920453774091329323172029973185928348205951044126121038513 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((3452627203071623620634750985596884198789378586941834031750602816160589230627615546439927449526887621556422262277426898977983162507197058712734893462117472689785502910069327457941009418375489893462438891798450586794584423888648497192438971357828606223080326161918654469 : ℚ) / 3469446951953614188823848962783813476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((13494321010648921580112791154835889052829402454390189299135452986334167264192625440006510482549085250749690512621787766192578766688777127620542372403409318592638578765667293481276947834296057152374974270426688279031070487796534661889139451058948362765826755363322589 : ℚ) / 13877787807814456755295395851135253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((346944695195337711495039728445375240275219153995659362748756319630681632077555269714011750788443853871738925148689873500435977705356684318305293236878280628125010929613268637733173261890821973172031284702404739590370693040485640444081172615043217739261830605207110428794911 : ℚ) / 346944695195361418882384896278381347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((6908027646338843922551051978840864711864354226727886847103122120532081289037985333714358153266020866362325908699902113677583284873316551796628172927771275024072787003598858734070707420271779809941455651874154687312999977102625819570090756107626364878197772224017579604163 : ℚ) / 6938893903907228377647697925567626953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((84502422081349519313680050856510293079418324993001258022655031417486840122652174383290026463273282029764573949811574230966514380195797770628851985565875701012782011074063395182569397004001198425008470253326057267557069977525681704982359186928788880797093537539528564128359 : ℚ) / 86736173798840354720596224069595336914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((17347234759767368091206622623173935317287078508509313127412378608090818346203281081211306375624994935735443913883208679667425431030709619984797028593730385782022199030244575302875387695277199038631211497572193314635719936571277782245674524518186276315895491952575202882482726417 : ℚ) / 17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((8638215325765928060361205947457448151480047756730603765910112690903105478173958689384261302263445415503923625714802558566902698636190545463169892300713400263425930579710657687410467968437701939719909037688717886909399322094297588711166889477246130957667567729668817520741064421 : ℚ) / 8673617379884035472059622406959533691406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((4232738244725762180182456326404754780176364765561066085360355898631876739564718650676212137929083358100857966115217858975519225487720445452231738003894660356679763454416311640458911995579070436049772100744908675584785580249136020614529600986364424723558197529080997254185352777 : ℚ) / 4336808689942017736029811203479766845703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((867361737988382709725661730606932438793992829041775606288394788594068491509888674214671600118154224859748705714895487726100161753767448103689277506718324747279612134649660924004346619001883119898299527268522815199005188959528672410237512628390668533937353649917997039856965390084799 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((17282267742214791727569130227352571479301211991572973357120842493781113989567593562397905698616218533401590320282280194829077032855417694861918999796152308095288103813491984923289744939838047872363556549103171585483745635532623531363969990018763196462517331248640140134294218106083 : ℚ) / 17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((211992926977932095034815176800507140445131641141032364225703150173384541448266691114544223007875447304304748362032173007285257488814827310657080824174449545786675030686495210934726939016126697162854176964651367783399064853506209684087103993265031353371155843330025424937762948474887 : ℚ) / 216840434497100886801490560173988342285156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((43368086899419559591519642812188464935044646027601521399632040297448348567793669524442368928702918304416969878329506524615691495513943533930076010241678173782598660955958497413956864213548828855624886084929895902204906837083146550946311536893898150025640723659118858240639452919844035953 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((21609529528927312136680002741042919614538944314389721316510131957534623851336431993948716108871387704320896100326160869662702336208036035663581597757543357074033971278397583272140131340510130117317776509694308172095731751119731153135404893579133616031129138948108800626173959125736667589 : ℚ) / 21684043449710088680149056017398834228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((10616280349311185799770250116218007834812744380134080258172460533146607890876049513255611954276510431360410186605856520266801237189722044086085930515972143936210796606825201810435906616207016029060956181976816367108832291219976315340076710738729882127693093272881089665714198138046792361 : ℚ) / 10842021724855044340074528008699417114257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((2168404344970990553023930324697188366035225652030302304934891098698451189989378920391142911629255418971049905982834879935281405767501883950424963475635032818132702501361301572831579153339082129082710997759916623812668872999004045795905298134293398453810170534321896790260237860714616133898591 : ℚ) / 2168404344971008868014905601739883422851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((43231344913113237540989085983579499692277788108738334806539738760032580777993423196330196800194329588969497848400028853024735918112260594704147327961146914080338654981622191541176401711361915431749913637311839430954091770763975635401858151406472644939159526724911180878462672369533815749891 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((531590950224817772435557020481139220771103850903748549717763526304178936575215785908669269138681675628558265403875702989175136674714830208084091993190066878435062941532704027783059334431136859553050485103212350432908310995647839301784108820938043914894460888545290869774180511935454011838887 : ℚ) / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((108420217248549900416207836048509390793144186468242372434404716403112982429615116852836213901072535406234716562673105685441287836789128353478248892162151817959180231057858507729737827159043767880915132950588248146174194077801472945711204373787396383960110125831041274140845271856606224521691527377 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((54053272403080439327419752568067412394456609140151886156831563925236876425887666689957064760850781740567899413453035780523335838565678671917747627528321255742615920186477215129758158577878397172485030812698002397010706103728689193409522026210432494326271780648374308193279112305169633826302478501 : ℚ) / 54210108624275221700372640043497085571289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((26615824661062349328097947640937638892181315504064918664858515099393799976783860956108842119674450746558649476837820988389476438543301207428613163536771982996833266829565478805790310243209619535195764455727668739840877070346945416101332085738214081758018271259181903118262642720414989011657591561 : ℚ) / 27105054312137610850186320021748542785644531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((5421010862427506072174682400940750274109238274348981615562796627203090590090799369336035233525097457188640641933569564256277860497287288295569644905931314947035816310172331178663537361784170586365490946586089792789626331824580268421500076069674940595265384900512880654453639774732804738394588712145919 : ℚ) / 5421010862427522170037264004349708557128906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((21626480792462285921769342067310196802060403859543486101523412882150666187634489025884365231587381281328190721008541170852352766666708797174088772979924139742188829140203584481232275688085554488654674661088970667194577508969709108450822749862864367376339869775391140618364329757064303115378490772743 : ℚ) / 21684043449710088680149056017398834228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((1332484598222967247928289751913723934040469464133343375875608808979901957648644453992362969238537912517928161389492258048990995210773436537232392577075895144014248027111134577034479418166978301608202930204844569386658823513161990227513938325517487013700808388745046800446001773188153481192836393826119 : ℚ) / 1355252715606880542509316001087427139282226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((271050543121375631248531243421220041639761216025874257956590231606690026724421928902705436568318564313271629111404536871505869730163076236098753262526145694234770846147679102453837892164815305373977710093437804086834051859603331217892212755237652963827832866145505372762587058401503462079184371548990060593 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((135195164112036184204618754848846037425555041116950258030386315874579102625714023441391932128140960662362630100328818351477718699126817375771274628997744400492358205327047680662972343504885809182311672353593905596633523239454499242905067421555661483378307026474381390689993791650048822856748047294720658309 : ℚ) / 135525271560688054250931600108742713928222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((66703250511431387811049903988388616097039469619824418005326150182144007389593845495555087895513341453099683322726951233912446259792374575327122326790040873918167068095049580577165311770807671496320794591500905222457136535885167096722527673431511701859895246209730399712667779803989796500264331761282602857 : ℚ) / 67762635780344027125465800054371356964111328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((13552527156068791275963627487735391487656232216831594125639030596443539222298936926178508077940940476195563988265810304629534519890144721171619737974112641396978251275740242350448931989010279358422317171140150577762369135481659960616850431554530697418603760982615797786292418520429373140261579063312908326400671 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((270444756340206049397708885105859720433166481703710831342663834681413128613661662516506198677686222172701022853659611152850735039696249107529362716128996155264250898316186404944528202842753419921674518589630260607412710402493439276242981346187017611715165331908702240613569084027457541214683436141986515071299 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((667769792039671157128213349784552922486809145392067826209795863014782060306276609191557018917291919822087330423368952666366157549130986275664463023767569284606483802248745985513115234676936801126589954197927113846110040277971083800612693711503422435034192977434742264845969921287638901549376947603708506129659 : ℚ) / 677626357803440271254658000543713569641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((677626357803439851775414749830215197092655888798031271042820340092761607323496583050414228986715062297769885560116478101351809911183120548575010371718517479496214215571870964963759486678187752139146437172792044178920957759624772852407764744297171586369345701851610556970211331875169625489335034490037793152800693137 : ℚ) / 677626357803440271254658000543713569641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((338118371753057107176463242024388448206879790788961053501410327247116922200597352828160689722008490842418495541820726049603621199273201184215510847228798294199504743703050636635401871079846220736872984786096277744440250984367551356718216194443087617136451228817857194109281735495897364938260281532539337521738170981 : ℚ) / 338813178901720135627329000271856784820556640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((33422875733281856685771562122431603396913610566254027847839165419784133653095141708722849291261075217087406585670283103357673400623101235408024317394117849019174369386716269226324063866803080554378549832758639964591224408570452274346193084868811230963223484164070282216126237459737247487499628411606109882026231797 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((33881317890172001126431775373282592231111547748476483092606494622730103372319703197695630646769141451941983797200773226270777108436845974903603332490338887714624262849059258498280577501548232287669274422861765733772469634699595640755333001374178246021091992022794698182495855356103153886882315767526150453601082149432639 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((676351303308785739902036416679798669921727793145147906486278228574976473176509272428690393960317011450567178904282053242824040544288173415202092121010986906661063045196087326653971013737797194885001584121185977336487437144136047119693229028266257773539733238688872868370449320643020156270840988089352304740409041472867 : ℚ) / 677626357803440271254658000543713569641113281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((8363735428640575803039829377076850094972392376609060179282232840100590395338925700742773580439437543673904715998598757467449764660635260030914866023175246670853587870390832359932040266701521709307590767780648849908872324360757570558469475314803811849572061014989685714616427267746171670295294201576889120470299682305671 : ℚ) / 8470329472543003390683225006796419620513916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((1694065894508600309437625558745019126021042986763144794246504746080079374679162240702082361784764736625723993635611323839249728933827172617967127998341077004075465520686059836698524281188400442632530978814582768709152407259938911961473357491740262459787314287499794417016454623742390203284400015559847782497911282484229448433 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((845570523501656298702216557155230507055046592257437422998298799681516008960148218302537142115776796815680454450297094586201104922759660052842366026456139880174746865419563491070728324437257399418238941493312355883389325949582705859528890349802165718410867633673182609331610806200440568395705524085954022006883980427285474629 : ℚ) / 847032947254300339068322500679641962051391601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((418560454898157521940313718530958355124860441995874208786815763965460548937778873560565238872205849643661874453626846588428168992145072594916600019946325067131132177721519006514807999838572413446063355866084715418381759695874445649923656214173988211816301770369140975757959851435790477441662589291248396570685984686709046313 : ℚ) / 423516473627150169534161250339820981025695800781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((84703294725430022976012420652779087736409807961770078715026126207036113221113122950094635779832920146742839239314968917862236713701174186604871443766817909939825326291779615978601149364392507922726645928915935343920241418035408922921800629557623561145314506681506405081286830230090642356772607261302807207715575791809950457693151 : ℚ) / 84703294725430033906832250067964196205139160156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((1691382171431648516384449499429645984856031886212222220530319944538385402011497333494831630145040320259816201606149001754337119319159419466797292774653429805122262845194108126671141304482471531311024500206681573981107944291107579079042520850348017590355017601767813921775462141855875144233093058643369796054400736289719995929987 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((20945437398754584423202981103060237491458798384529295479521027445351003558634284639133141078879675948189036892805554779726068014267439299878491892095623605722882235339137569335983132493259212684279485098841951339440183772109417774303686542804816494727353090813995879043656131935750303535532145356645045177226119489117472989958183 : ℚ) / 21175823681357508476708062516991049051284790039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((4235164736271501371275597020726216899484538903302753773664379563659999648666340756101455666964706583590484954927970883507861731851098711110274623693354850575986001448572390274917588275206144682385076871854570735141203397320495768337862623264494865717275139179586620391444910655831497273951237487475844325287143675499789601219228847697 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((2114504271952640543220705952336210162155366386100316408068919306501002566185801013052042182537089643744433184104400748501851028870048016156035794993492163027370959367782740104417362488016183681665919167771549174021451374267256815614849650386824920934778180636618178878452898460705812810575454427176558073239696726194414657225204173861 : ℚ) / 2117582368135750847670806251699104905128479003906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((1048083243363078513974415127504310085002853795222519767922290432280153649101666110782471446160064975652403664355890069499664768431481269287852181535777037754063315785987579827222964708239205505180174754737820311650213337926435186661552197097613552751444547382295589551084336707807476392409753884518761011382482907859059248623594099849 : ℚ) / 1058791184067875423835403125849552452564239501953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((211758236813575075159495464155133916687177991199224553627827860923828009584011004396139856158502656083707107458749552783357576764189523488286311768636891255026256984945825654480481739595036571398670374019872458584731257120360738043912613191922479283920056051257204534745167266213436399680832337791196356711787948547542262307346477647672959 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((4229516060403952286723142125639895313968061349648691667876326648974250200294940287005067655202034357779483804497929821227104981273807093152195448085737512096273280914425769874682596226416253565514587320476616131635286654020429998612896285079795105635562297323835873408497201457677199840207767946867753857540304380782096880491629909739939 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((52441956343505708223696092187407667223963136538971514029768883142847455402395173718378483945140402708738252105758694551167935216600666633685672157979966286080328348886538414668539358972399624734569516802638883105546698799753809790640896827891560735177350775097027124093138623208306082133570700288362603869152565799444608816894395915199943 : ℚ) / 52939559203393771191770156292477622628211975097656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((10587911840678753953517953989890443441432759221733800966404212592808729000137174247332358315531128244913664614829547991368202078327926802857224285004777915037763440832688893178382842133774049232256380578567158779661527579847334800787877243300925743330377901751622342841589973941429748941337636318495598387434377310588985450625901022820560215473 : ℚ) / 10587911840678754238354031258495524525642395019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((5287477171553091305160828012626408932647941804841168713497706071405025794980928442240906590676647280843699298041383436742928023982987653400268657737097272375429755190773983431651476607193492400619615568075612009322223148753795668017565289960823226212867412437214653551985654947548756776468494894847625978088847071494510619695316015408077004549 : ℚ) / 5293955920339377119177015629247762262821197509765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((2623857888139668523460139215397484562953185139175583958845064551415953800521282578139704197369436215756081433134753222657209116027338294294898137726422518583553784789332397180956269481501847448535719403559024325298779592383507941253552545758745466226338846229512053776517832060657484157890661831291860557818745596966717305068812326896893341929 : ℚ) / 2646977960169688559588507814623881131410598754882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((529395592033937703473166380142441387378556678479261528500985690739000388667066804910662426980551359076955414835851609300093087016188045924308128377536650847124572730366727616059516120739999237588704915012780556340625308159733934838958196632142545512515713653230347598224617957441567766863836903934439005392266984127031651654706087623561148708128031 : ℚ) / 529395592033937711917701562924776226282119750976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((2115204511841213078370951765891508743558521527027972016236854730381588511131342009575042424442983034106514393333650301768815330941802917627090117848459167559462374081588004965743627851380250878586456987236798736068538895684735957453869402970126847433582720026437020194036118511815428607671347817905910503194099020665192457792973521303399451350311 : ℚ) / 2117582368135750847670806251699104905128479003906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((131274842642642633699240733458028825589353635874875089582412643703026886623771095639351857650299564752276368242619499612194614482531163819319290466208969785942041264013176897720545424559767545081598762482284754347270512048952150200614685756928981168756693324350653404129727534125742045912009351474288935812449524311989242909139018241131719447394151 : ℚ) / 132348898008484427979425390731194056570529937744140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((26469779601696885345529943582290930345132053138500643097968722773339144522812529565186408972692406142554497183638492660919859750768926997517963082008829087664702207737182373633316474431578757396792334615383905153830518511011631966170593655553130046809553362677320115244565248584270159584212172690944313192864539278414107376607071379775717375749871735057 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((13221253389463342308046011548919901466509436641469420530354834173668894515253288274331349805581313305899938527146841234836205571458867844511954105917554248557550594161672637093996932545548032154644005037397572278287082192145251171711670401941780724621033389510917447957689568245920600375349629757744799048305821613045524681388604147886829531118647879141 : ℚ) / 13234889800848442797942539073119405657052993774414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((6567556793122251268169082818275246400447630215068100650544946967722024244705582310958954829877566935866625992817479062201455572863446710356409499619444408881955463233165639492922885113164852565849424006499140234323733884782606847942853658096566727130296324581370114202152194842227243377402496008525437990588939036584312693124394682292429308461672730953 : ℚ) / 6617444900424221398971269536559702828526496887207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((1323488980084844272371975232894577738618129143978427394050478724061185617667823064019081466813411764908313178003330391918291082031046378695415051492315755961995426352784245831106933517473015420542702344342286636095613382295961852901059590106183646497762828543294509456655625924777857421193138283768426053228854995987143041394269845196210693038856447329234879 : ℚ) / 1323488980084844279794253907311940565705299377441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((26444755150435859964226885262577953876873483830231356020661304794217340777292279315344914210927141636315287937756868621838850806148987900496158095332230022600010296363822004666266261005125457527421866589921281980211978218497392269522624328975200684425530372978393097396877239572741044116934064077674084809146731976644562265437342208418788749603272521807331 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((65711074758109318435588802267831134256442465584992559471752478043416523978907946479114368326885220521429768120585988840135159690921186961054098487167389979392692903355676102741408760239630320057352233790448790427170787912813559926963998564911259676145536918985219791921427319025308765808413459761968414994159528692980384820700578476601365495448030965914267 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((66174449004242213769664399505145472550611632960593378357664542732241970006997950378973708246617218594236760788264736129201575708974431989182970031592685217005278405080994536154827257992522488172829496402715771900326649944928381052957713667878026567719174577823052321861469341791889138966112970698882527200075864066030829748215918100532058416522977093969826457713 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((33058522707747273631328667006909508918372006444823392647035520184017682562528763095678176257325326747247852960075104403561667852178568258965318948566963997458754383127573978909885478039340528292815019416999667124197187598617561442358057789326950920433751250915297947049515594958922504694996582796735017667555514387341982498656949796895319994710556556832471376069 : ℚ) / 33087224502121106994856347682798514142632484436035156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((3287205889577780848119301123074422592118248686978822767237974933580272983814335706913438331044444341644383944034828527155770213857447535713852839566664147857471071124180893999656224921931577663411288117047348418023825843405676129666684969871088214475210033262746254482446062496040212017383398237280018387060307930395876308949432950807273064264826487991439287381 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((3308722450212110692961862940905044141397980993835958958482180698382777684797468234885433528387460679663337247089684632022439115043964985183307512526628338628555488875436245013382163717704314206859876079851314489528984190917291713077037337111579853653170368708720032186226981576104137302928351242309770283900649141965616009545357323926473935874656701904923444991817311 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((66121777767350904889494996492923970763355259488295622426233688702940557631524694761383527321193977121318358483477570439555465810337786356580680158298707940306424495279950749737712997608458144205678762115964317368419671927434955088105952925129538683349154347775414002003766591158341207432248482326360241164458729796102600527378261999486402524551390780201277364825603 : ℚ) / 66174449004242213989712695365597028285264968872070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((822185774310914279704254867323282296286769771588853166822259277113239263518542248549066340024632585955883057872864106020002726800099919399128225221193601675787781788801785245114415405080965429021407136187927567553455813859578841516940822342531771365482390858277792384597353917177003516843965678793734289220595951305821892439642398117081622720807005143987981638405799 : ℚ) / 827180612553027674871408692069962853565812110900878906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((165436122510605534780871475047811659494525838096917028757746211164954210021190540759648447816103046769978959364467880285569252443708429915729517823876950355320784578690058355911741007738779803290774746139351920671065794308124947417594925933347007921255541921107422794225071322786759358619916829280757759606802545111854617834991208582448172776875947241375265373672407819217 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((82657649980150280501200685748764444242451553698396575555200503677204577383844830688667715163049988520082229328876439442246388527272535896143007890878084078047906437433613613384250562029209660077041460809478832968628179134652059958954896659264290471246496709089683075934033900757410074845752728714619315158695178021231012270549479044923392157371885117977902293714860838821 : ℚ) / 82718061255302767487140869206996285356581211090087890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((41127163553298880698703034497355452782626303326087837532983301925820203163667991176514351792874613449659931349952441272883780476012638544216024261854260984306080375025947765855594812156080337832841714812054802396625269424310844152028870271897972087365166305565196765473801476621680098058714060463564653146861237106752683273519078890339007577262694191945751437829420441097 : ℚ) / 41359030627651383743570434603498142678290605545043945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((8271806125530276742980052842682463060759202300692416827362151922407397464498235961901297532404007027589566208278379246826271627198623821711633014924479947184195300404424160077715385656431604828161598898793366392135087603852980316089436769145938743841463051335071763580390689506659054705004674237686625299062875054931153854953984360843840978316041207865052492533265874616326399 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((165325260571347703040698446834214200126936405315711363583648145956550489122788273873613315487975830108690366096014463599997521685627699035982698090108605440599919542130381425055069820069028238383871795632418968297511608176344508936983835651294212062622177916760755141463979171808478818075563690924677867336009496909342749932247435220456842779561946908282584934647568723153443 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((2057189426107335776808072429997876982345022196166653152557476163831497914730864295245469592504547542183387805119932442407831887433216527613493500348449516722851090612991109259107919200438854848513894642875786099100716787845050803582186552348878866085378129484153934025907108013910461702994780039828249565613770597885356719512110777642560100866001339366239641092084479185458247 : ℚ) / 2067951531382569187178521730174907133914530277252197265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((413590306276513837265707437724006521948577809540283965469868218043612112629979201562487767943181596346947869376829109530658474931557600442284783993466056994169838071089963073824028038556227788340506922552526933427628942191429307431103531894869645938667855082930872574867842771803920994839273577124695380241317056753543918337820774345937353484135673689575211246133733384750228751153 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((206668000037025148369810972505270533203814426018582219543458636116947229673712875036819366413218536827024511349085528653726103320987053105868031218209418181242704232979959169387083739966077475565222811331016063823021354549399326956733939481461676276281762310430331014241296122178959092138782408909931414682404677968383775129851357593802132082327935935864583977905089914605090157189 : ℚ) / 206795153138256918717852173017490713391453027725219726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((102898120541891041167572734416575486857565326599625741341679362164672725284074257948609580045441586786639736836389405829776383636513075046680863328079012823537873189551074013515315589556790462722849452695815701996071970404041391589721646780594798894791585541635112093904497828289616033111337937842134460685716456818038280768035667356419411131747338761893602442780367714530934606441 : ℚ) / 103397576569128459358926086508745356695726513862609863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((20679515313825691866745318961053598335521973266023592913738308060338968303140993388723074856211504786897963483414852610255431806295888180312416991054288191706153189293604135249660959259076485240931008732914765995328915249149304677409926410087200393143685899643651579227106934655670845733999943741015843938014326781572316546961372497034004718744170317874836287814126793657690031785432991 : ℚ) / 20679515313825691871785217301749071339145302772521972656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((413356965077381391020592433029839158562424684093721612841927748206447582684039456614379447281461492104851603618359627132733331399767369476102499041581809231361472842606839226731677984385123515830043076225004519434676678154955124989461762190633004979313965624153730185926592297840566655980272087936953224859068650792102594044062767984617244048153786733592395764664453584328901907505731 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((5146702722297186017476082323897012754984443585761927715752634026427883530940281041617195027502412522997955364470338435213810427420501173442818660106338561189811759614395869440162428205756518525938811404931856883715036869922922976211078360271420698500665073600932584864501862674081839055979992457084813432999735647190799205618563994978635938123982283681971600448340100321251308688266727 : ℚ) / 5169878828456422967946304325437267834786325693130493164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((1033975765691284593439842998980854878818844288746941168586255869064869393283221030995473000262102482417163923392800135336242786761254196881722226533786482019512323602987481797746698459153840557937881615904724067463516350391529435771172088279855230055530855866735338369346039291736673563475896332089896725230310746093274468667763810419567137896608417414035271424825417051569536372342731884177 : ℚ) / 1033975765691284593589260865087453566957265138626098632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((516720252157297337368430593442305489082683778322568628844263683717743668632232642138020764338124169735456249509395585569624939401739009960239652694305144061016422999962032373849449301223474052562826715274806266281975310338322497546805026475736245071293289511788686741535572428333575539134346955309522155608356316522822614642125180456343831786361720719233835911466810360274533198323475564901 : ℚ) / 516987882845642296794630432543726783478632569313049316406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((257418645119162376282103729967609613818105234675514725844979671090795652330273346629369574492932985110802675087606166518753279689570766547465815751476103230912083795804571089333121589369141046086163759137957087974950177360257923117693870309404604387372664325448106076243484123907761809159633613277088585590025384253882572113488813082037263068833183072209841277143283093470914210784533691081 : ℚ) / 258493941422821148397315216271863391739316284656524658203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((51698788284564229675033251777910347040623493994937550298709540250166182902667653905922788038770552296221658836826345612313589899110903174952418850047167832432481857857769872857796369218533911021184376266727354428090869240057673182307938901232868005456323283881102576636002026882117161136369898557469168212903022689427308172593193687508906937220749751073903691931799139327882044830844972170195519 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((41339385250499559665389400298953013013409607137584398884117444204392543758506060321423658367751446200616058657767378805905998965420683517966566872312744541877642165340824513972193568905354572757419740886011517100042832777373602735322730685757774528840388208261092644331825886155771300477967027129804055369119746459411671351161088387601392297439380754315738589364543216403135757657732451807707 : ℚ) / 41359030627651383743570434603498142678290605545043945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((12874813040473121311386690376538585475746443223566078536364004802445792638659312072108678133887653404738180457908060009406359965705111727192690619249183565937539428186843861158928667286899032934673006801912570996921915351541195664237524541621356841175818563606704693940203379411435795466781559984819195292408006947153162052200059763498230192383620279389184033926312637914784415084117519818675079 : ℚ) / 12924697071141057419865760813593169586965814232826232910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((2584939414228211483841822134815955181127425594790762827387482364796676824515387935348892896985430563926083519535390668368260999738940946427814361647348384728125789639909303420615088958221874860045053203179665876729610000359989836835883464604850837757763616397223048089527552090974127476209958382533288430007935913673451405392870413253576563967783567870088022754702049083653718983100060889929786551793 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((1291906400480998626315702848736377182143978743784876948669102928211293204557861181841528490270219138777427550800856476342825446616798895466870782104924771710307387147486330615470103663359309071217725294715997815923648457853975205860696811076187928355582563674705457620856492680563090796182165405090162988327090459803465093549069830343941279586314409141024224885863009077494178825534777377664011555909 : ℚ) / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((643920968296625604817778302354926074344193572404865454903911595142391220105337538195735785361457594539746803606442581935902647423951633776726944182311897701088571700585672239309761238734563692010079509786938517661276306469361346707326743385096342474426729121914717911068583860242254330853185685805113890447441916129522427790048718809050848219314833511969945878896573432883768643062010188725977853737 : ℚ) / 646234853557052870993288040679658479348290711641311645507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((129246970711410574194764066798700979375587830024904209227638720919127077816407706119288627716927059928716598103665727145113833859260382238745412379758937562034745285454391118510975542344403923975755692314667554247402747680672618692673437075140012787004417935328471706710223336841109957287196636166964402084445276032676813815682429141728784391952879436644499610608651649183081806691967505203748381901007071 : ℚ) / 129246970711410574198657608135931695869658142328262329101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((2583905678959663953852392428567327839628203238329053873531468211772946422961270793411188493492163441643299172376165343566525270413898280672672925630596947898005982400009238013057004568419746626235186228909353566835394806406664541927832164764157894148646706786512547473686818242334846251028564347245104201308664481317774196334357263929398372927941375838086432168442562144747530039282149681064592489809539 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((6440885054980785533333339305336994362232330581146209746257735459397219938117285494623871315851974633462956407611387594359580980798655115593179885422871039445097003478087759678707421952169569811563631916482967362376534771967680552703526492129894664076521028477754275296117944350966934864362779158651568196977974733169034299991297608372099558366623985820361620904356131532511408073165215922747187958094907 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((6462348535570528709817448586771705741583204567555458275175906721589360476023039263318549945923736545706660983979377812671189832425492552232085240822713221901644093477866333490494891903884543134109229010052948980772749260488901126381689388966675959096319978528683200688837991267328386903693518672441993628597549098540769499193536976764833270868227016658199479955714695443330826322996760626775528278219156633937 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((3229988625119003765286410237617419384154654221882835915465080869307301807195045818814816504335423529905866894448497904449705770485156280811576506966696339706971571547012095634326851982520844880274479327108112902785753136177990163489727055188114463047806445713502546512474866480275479529586124145212885896387014440750768027759812550324926488461517245536417547073059627700884511182146806604921959771285026329381 : ℚ) / 3231174267785264354966440203398292396741453558206558227539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((322122072574087815742715844626636940737863496772806710905554167328545869209560719448456265654093636500147712039731623919481899148695921175515801282053779095751111974199805436264291536399201012798269899153316465157349405748353926501498698863829954497704436057937422443751641712920921628324084937838977444535441312288308618708226303281687633771766411099478031127345851205350181676635476328567166114748965442741 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((323117426778526435493221813171551650422474874354672830694345184699959770032655045039605050246801017370565378192036614012262764961918577696024631134670978889718042439338303188992702060274465050296936312461039778432969697325714451693837945314695042159328598403439870850821979927102484686533801748081887785107031538124438193342590790750147011981430326362865639982247073575808429007997884962302014086864363336726330239 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((6460172739000820576589747616749938081586008440210901825393780955011042570063111839891427320977975269028911586859587381290356943317877600048953386718148264936629209443668137473422291498719894592665267342351405264135096744297658317682174386743225379496191183687667436220760680975361690210674581820719189120919319888194250460616102395716771952355876162882092534112262303478795377482649100682895761366736964790475427 : ℚ) / 6462348535570528709932880406796584793482907116413116455078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((80548588784140270813476879098633749186601249876014656236398602115137485962610122866858719593827847171904875334252391391960796438689264453204228836948677542910415984720085298127013477470588181624040834059949084635085817398277744927131113993116657170569949671945794082734399792342777975631738845754166793834438519388202446950693005376005999803624684085159822124819440700686801152349816483422766394150883622175212231 : ℚ) / 80779356694631608874161005084957309918536338955163955688476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((16155871338926321774730742841073536295162993027010793372105505597049707302158124120289170924666909761985151767259309495621554192826000072954042239249590511143470804199062674644066637980957065346153270855532446311202252616615456349367213564744763914897614956866781851114319238898807363501667620425383727165068164010775219118027789173369608464213464885679877628553678990301992494800113295477367811633267779843925512595633 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((8075440139587534143871141185977909434195793096544874552696442492016532361771188172590098574354345631613445389002391208450248454724953902007653851664937039960775757238891413147655656180682455571719414118292147251050099757060496692406569918168728830903532719440059739796945563674449311526079377022070644687344005945838862682282718262503404582448300067651482116003470467614745530389208026935551744532606414603428757620229 : ℚ) / 8077935669463160887416100508495730991853633895516395568847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((4028268556615804624589479005240159704836611226693667115366909631545221549415129054436150130239024148289366540097771452101363060518639717926625933832184017664503884563573074090789207888867187165434823284817000261123027990348123226585495283053150685349949401789036205578963487760357479054137922593822220386991738349731160616187138376579709933835829775751462137262600615652853995092298375539155880735275360928983633109993 : ℚ) / 4038967834731580443708050254247865495926816947758197784423828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((807793566946316088738602120308134356297091275622679389128324619748232672387081905794213050403599873713573794443936748616692217154712424162868490267032609883870478932089611115172643616221434116317406021053970435788213183324798434389689780553988015784969590626229481539986222475632941905733939942751351359262775858427452921192169865622888782138536593465751332053730921025483171493338958871017523511491489869032859671922731551 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((16151291742140961625209611053029883493054620972478199994740673427370156737723458591760180946798686796264521813958925629270260871891432850666616978471095502511486540722405136993182701405444088335910606886090380137242572771890636911610977674507355989311850341142939925502035220865073099614816264988610915946126951632376122749600872877337838339132282465324036972418254020489668078999164774469123919817723279337377400942418627 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((201452386968109792437434539786708518282371579430231046371910448052077747441677709583129888836850256221974869073339486960122296555662282971075519180634373601771268051676960695634545586913835353709132535158634453464216533740492881072339293197258197262977159590043366163273191698202720455100989208801863425615022968263340082737618216779743449188946144891355284574416743678675626124976622616499565641854664829197577789275550823 : ℚ) / 201948391736579022185402512712393274796340847387909889221191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((40389678347315804436991326425716620548859566115930095750763074767300854038259817261081034305315525455986322283879392786239074161985759239156562130946715785227108088899660700731523365290116857246462136306187061509813156246030299184351132924084082703976993453295825439215971537735089828679294117482749313748063515874798696754584260006121783724061194386479129741396960615642499585263020113649056519545188200147217190693493222292497 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((20189586605124933394924422367227689780687302643442213704961292428823308808121696639661212633812573160699268884869143389390528366571741214271748301897777195576206544960599260382701717870006472830602844377393594566569876211552375579049361481497981252474049075054553909008470901093475084870931165350697825195850888218972774458231783239711407463055295292736317700877855877034145619655863632310528795792121675856081733794739793964261 : ℚ) / 20194839173657902218540251271239327479634084738790988922119140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((10074427916336754105183547025841978148738282666707079200179520734078470223040491164195276363340818392129292529810902625804640912804880295777600108784866987868966579685557527477895421126348445008975376467813638292602749697017997464707537717982803091380159216499399532500139853485217300496776590974950067684490214920843696040509633524425902082314262089351418750708941904896010523132109457404288682485616505001784844399941840413769 : ℚ) / 10097419586828951109270125635619663739817042369395494461059570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((2019483917365790221851381322790288713798024610016205543786654615907418419672288802339269424049689383193626496750172357933629831680391804163274597496177282884628073511608240794587473210756094466785862955069527812581430643226060279918458037800320799924805924909861336796435908179232208150855032701011068904688839055140156962683159556401492522067242229975946759443195691371953185204292757309353578634956194569764548052489993561305658559 : ℚ) / 2019483917365790221854025127123932747963408473879098892211914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((40380039253749582689479270925082956268382865457630952307941474845798512866874427272378604996692341177253954725084079558035895689977239728810437725853896136479930945636982942881810362732123512132294230290924594611872707834266733337382971640188067134156040278903820818708589813585538803224664207203650446398800238237119722424238236453763877913813638362827610795115736310216468975351951847094925823205343645017149296522174471945488099 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((503805341938860092564550004950434542145811462931321781991761275933856896346190470405292648235637779478308875854379895192199194761166656852298811041043446469535010431977803321279634370964697300625644783852162295989729465471801133754273149438982379587687959678246887358507874725348451462110105572536547422957690760757769975104916672090656746513770679733593940226534097675386544902365652632985956023202676790411269544731490469863236103 : ℚ) / 504870979341447555463506281780983186990852118469774723052978515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((100974195868289511092622875489117092717269288282011745509832036311869733888024346122952320614801141143541444749152359895658323619828575818028601991969167905680568495398649514837134818279285932656800479028946291059601674279723009118742525446666110755370721255802659052003935369789697275048399154486875159817310011467740233472667631368635048801727530392096893577212422662104296081751667375950405545790546300409809556112170839112028859298673 : ℚ) / 100974195868289511092701256356196637398170423693954944610595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((50476042375778977512933946693794681731159456257873220375337769737773793695606211581675875283922690532013487581737290278790481644712682615339640495107747553760875257605762170615937177822977372936180530982574260611817730806201140038223341338620164768165295409127961503155271493449331311357440834849010692509667630538708329134570037146387955861229138756225554472670420080920374605985968543840102898492013610660704119182289887327728537438149 : ℚ) / 50487097934144755546350628178098318699085211846977472305297851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((25194163000020470574751844561530935246293965439067615531884708308723255066036231266463323738209162926063864623657198030855514182678881160096722656765613235561455650572223206905652344610891046720719791609309391552793549688075885849587201163722323769811338189489130065917584366794531143014838246732999811921151118997212564615772242215455334026068018961462515435931269646535287470985740730417695743473147737099996841676496359443376820234409 : ℚ) / 25243548967072377773175314089049159349542605923488736152648925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((5048709793414475554632739060243524608753845223139867206789444726241127000578257789507167449267009431482573212478120013826582320357057787277093963255909920899711814183083762166376535957525990045476163801771170691044010837370948051343359651917310185564475773070781432914760671908155155113359889733072387863103789909984094701764177267185923291824816093534496603883616694663406065935691682694801673216052326168249623910057528867154319591627758431 : ℚ) / 5048709793414475554635062817809831869908521184697747230529785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((20190781518404260901602234822407861892419404298783470495004080214946797029681919618428244312503282784996429607223571337242412175012761182300071802720013578600392693899630188108778405637089313782174049501577601873782503236939240195738710391030358188005651834305455185183501250988839903890651370228802898042736059899918986761783777219621947796654646943969821486078466684632495203183315610529040212855127330840291208599938236401851370556815719 : ℚ) / 20194839173657902218540251271239327479634084738790988922119140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((1259888933451419621682621988929827086277394185761020772565377791217157284726254620112638345421724641908437779110105486524176462342694548733132441107509871729389626242877932120056964789551615807074650673806981816780018815781126040626139921488148929498593247295595037822169950127798571611942434644240376408580996023894395905788747774919365391477941828890558150937828524630522810656820894398957497392853111934245366292068999436325690274374241191 : ℚ) / 1262177448353618888658765704452457967477130296174436807632446289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((252435489670723777731684248449923282123973381002580892462659385084026942186143608685518993368419028615163848030338824049916686051625692219404004728647961424913756155085884296946565161532773026878231828231109897477381789295536496878176583600392495071430013244229457141623909640061075883645780650916397082977438059461298455623202563440261067832730322725017220815337584146685999636795451316852785205836303313910096600061475558324524112932988154203857 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((126194475196896069323561491350965390206193853807339773734417694593449107014160177835955646184067507389543858080942781074747509382910328289773427428919028216852908050372239855081719002335759007696049003974622535139915916773858831646331233657562922911113796425082089656468405543910957413525547678159489610936437530515537628512475485757897153031316182530705531267892620827397481768348979755515399609169225304769122483397124368200722199979043754661541 : ℚ) / 126217744835361888865876570445245796747713029617443680763244628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((63002834577563127118330607354245432484268839486818202590029828470836410493442914003225198452266541348960013607574392076513244175945803106368706131306081393387863440536645997015497467367304164460103413115760641472966920626822972247273232582522492615721417053240252037288412481749142748652524075863655335481138813015943724330280716023955749731338168644781252109076662032627572084033730677397916050226117247927038937363100644292776977747441086968073 : ℚ) / 63108872417680944432938285222622898373856514808721840381622314453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((12621774483536188886585614590339050947541845410191178187989098653843959254992599566699581596393518941353762602555455116607879991372546897228670528190226112364418128729831211751574817343962121927858939011567715130511937907244770522947301174000836301382685602651670715877724049098890716722446458957718424319032106148849115313861086398313419878036955877828585545512313357196799831232074745190734522997428884347492633902022565877647166376124299807681748479 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((252392787091782382973254213450195282253490830528778134350126239408657506377651304650353111238598428879733832473120849060565781016862423717696678293187625001180998678824385104297839007483159878539014880093282006633997851899567847933452251061683228386331840387450920817133775492468511264556761212005590350342335234621662857517390832754047345902959240691198754224351536769826460552789996735502763743147773586486660415440798915600783091495738318487053091 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((630106171626048788962126367574482324145650270134634554418404667828426290034871627031974048275689503347487479158624206296265846628443948303841306764612503864156448483351486278480083134338235954392436276823312750884028617797661474556698007397840820068774541200130093949739834332737530850391330663431897513868736842787597847437766133178813583714375030656211676840669158451630792399173348658755766229354316090705170761325160936345142127850782273255737819 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((631088724176809444329322299586990613562393420056320983196744601003402485032765599353942495588278656054314999877961577842073818104221897862138395149255633553267904262453305934798938609796445028795233964875948050474287423136085711693818637905602793827092480061814081713626884883634813078670370168719478125786344850994929721710039628450797959124161630909984075667803554100813524596537319970669706403304774134250114117293263010574605541552957116398340797156913 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((315495384365487889446426871787390262983525051465386099438322822615332126964386911575690338605277510541740823878912750825344763199509176038200495126971602512687612197989810622794402148178716155983640390025830858392848940263040815235067447074813302414853019359451926976635573066279572762048339424021669524846666568122094241091439114694178561752033267174975125966920872927335063383191792805622998727101039845661057481961892824522148976692229246292357626337669 : ℚ) / 315544362088404722164691426113114491869282574043609201908111572265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((31508918612840683796543818161186362450776366101835822762085620247738756937441537199394794198105839844181687712474871686029214884998518736694495741558190927916939734904484775983898485009283551663960739847461213463420812791146159802666416630588786811636388016372250189246727675967220448935510892466646202701547673466185649791466547189508067493178092631768482472378162237856979169685775806125753023443455120418116859769193166262908500299401772504435821762837 : ℚ) / 31554436208840472216469142611311449186928257404360920190811157226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((31554436208840472216467347407215949226315294183428904361705476846592404723766401724046333166705697316042276801381926898283962485335866605918817000989981767953733557668953161048984132964635205768692301356677231852411199233715533094586641157987406028591810756392602080563896256145121303343340464392026367995187765797446681459537544864680807094154019871588297891323371968426818563713541925170444785738776638758113133235393368474505330490420519629861609613310999711 : ℚ) / 31554436208840472216469142611311449186928257404360920190811157226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((630998844177930306271436211332427125588410205994602440655994603144568793700986905181519873517614557550477149306609519771907247407195332390977181913512761633214696924171711811367287769157344520342577240608575882134985202418850366926215381984869281850650576943213373129834873235197823557295733960519879955126441022008239589969497415127064745992587174110359440362469557326482188483501459471836888019966105821197099214127565362728856510953069519131910542562399043 : ℚ) / 631088724176809444329382852226228983738565148087218403816223144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((7878066827776794996238272230748351014592635751170280134337203766038992967553315642926669628968975551083365182379049995509277159423998624825081598612721889733515974529796762456525736303675887913678236957452365155521761912043144717333123319311952022998283119975460892410152777679722898243898471175832633328417000613307962436553967275185957618031063232448995928956650554845250017366978397139575486424249413194619265932778681520388729924642457071401082222059115239 : ℚ) / 7888609052210118054117285652827862296732064351090230047702789306640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((1577721810442023610823403908149753172014120349607074536255061755103151585345502511912801639393323808328705380330569986753424635802752437265675167628349989474524338784211454365619232590002539945424420658321409892728434823681964409655210150410852626529661413494771473882477832305934411280220014747830405731953331692596901765230909592603191887920384227132978267584064008747949889958415377455528176562797511009261780061029707195163659533049497145466507140205831208432017 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((788757817356297378016162965593999363049062907077556241199867997857490124071029484851203711587608458950882898884863940039752264095959907560629960634743814378968241499534457326969667004875129456696193799212117882862540759534988142053965799794157866643531401193943731199306298041025238735230966763130242658970353515500888008203621940246094053837249294301220242077751928402536419140965608848999605417907743724102484111241756825207817461378379775925489574204977552773221 : ℚ) / 788860905221011805411728565282786229673206435109023004770278930664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((393942165371011659868055204191176155493423778856062002757922356305360826460854365355667560720833750410390962955209111200222138442709948411170192879248199900345633138495963319061187232445874562114381447456356480932032505555346658497682279200164124658470003955233263872507730977833894984423236752920636366529005027796317245537401264965403374637297173124331305393349458096437375058374647603255839821400468180979923219471943156106998483209603552495010540889155699625417 : ℚ) / 394430452610505902705864282641393114836603217554511502385139465332031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((78886090522101180541171278643316828555780167152348829208532790005154463175738112970678830203093870945521128410660408397278780177644201507615471694677692137951223071935516987577513388595805301761997799257254839089719907217699198853048015329230547818724871925879489886193820294374037491224682777228928038735220424690420346633800776691906829901175631181811406699064745667350470387597140695424043850557257808891583993469347729215017014176318441871645537185682277836384007999 : ℚ) / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((1577532631839728870821302399608725762619440403657772234119569051318941093181110855322232322360237649948562696956043703353702501863356856490845514179312241775411985829996065627770224848706256961673108403882158800755237965502188585178049243318125674765982631887538980305342446156347468973738389742166709556871907808103678183140266881798619259317969400642898019021354355731243622422140571828409898770347885470578491790453261846244662071629292839068643276053607131468328803 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((19698908524462601827517948529972012348971414777845255975640889806161631142081468342065647200332471835225686253060788184065720683776420382690124457782355916463110502858458321702773631547199474970934447466578897588779483795269804559329891118520889074233605059318909709944679962063616451128680278249304385343755591260686772775672560052929975866568490504152886547758333162985981452777642202579959606092518539022372137216203068932630188200591032499548527607349143923680489607 : ℚ) / 19721522630525295135293214132069655741830160877725575119256973266601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_open_source_model__apps__self_rec__minified_sft
