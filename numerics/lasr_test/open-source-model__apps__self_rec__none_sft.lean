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

namespace LasrTest_open_source_model__apps__self_rec__none_sft
open PL_TMCERTF1

def cat : Fin 10 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((43257 : ℚ) / 100000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((43257 : ℚ) / 100000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((43257 : ℚ) / 100000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((8019 : ℚ) / 100000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((8019 : ℚ) / 100000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((8019 : ℚ) / 100000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((43257 : ℚ) / 100000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((43257 : ℚ) / 100000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((43257 : ℚ) / 100000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((12183 : ℚ) / 50000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((12183 : ℚ) / 50000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((12183 : ℚ) / 50000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((8019 : ℚ) / 100000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((8019 : ℚ) / 100000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((8019 : ℚ) / 100000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((43257 : ℚ) / 100000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((43257 : ℚ) / 100000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((43257 : ℚ) / 100000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((8019 : ℚ) / 100000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((8019 : ℚ) / 100000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((8019 : ℚ) / 100000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((43257 : ℚ) / 100000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((43257 : ℚ) / 100000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((43257 : ℚ) / 100000)
  | 8, 0, 0 => ((0 : ℚ) / 1)
  | 8, 0, 1 => ((12183 : ℚ) / 50000)
  | 8, 1, 0 => ((0 : ℚ) / 1)
  | 8, 1, 1 => ((12183 : ℚ) / 50000)
  | 8, 2, 0 => ((0 : ℚ) / 1)
  | 8, 2, 1 => ((12183 : ℚ) / 50000)
  | 9, 0, 0 => ((0 : ℚ) / 1)
  | 9, 0, 1 => ((8019 : ℚ) / 100000)
  | 9, 1, 0 => ((0 : ℚ) / 1)
  | 9, 1, 1 => ((8019 : ℚ) / 100000)
  | 9, 2, 0 => ((0 : ℚ) / 1)
  | 9, 2, 1 => ((8019 : ℚ) / 100000)
  | _, _, _ => 0

def kernel : Fin 10 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((56743 : ℚ) / 100000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((1547 : ℚ) / 100000)
  | 0, 1, 0, 1 => ((98453 : ℚ) / 100000)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((5657 : ℚ) / 25000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((1547 : ℚ) / 100000)
  | 0, 2, 0, 2 => ((98453 : ℚ) / 100000)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((5657 : ℚ) / 25000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((91981 : ℚ) / 100000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((1547 : ℚ) / 100000)
  | 1, 1, 0, 1 => ((98453 : ℚ) / 100000)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((28933 : ℚ) / 50000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((1547 : ℚ) / 100000)
  | 1, 2, 0, 2 => ((98453 : ℚ) / 100000)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((28933 : ℚ) / 50000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((56743 : ℚ) / 100000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((1547 : ℚ) / 100000)
  | 2, 1, 0, 1 => ((98453 : ℚ) / 100000)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((0 : ℚ) / 1)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((1547 : ℚ) / 100000)
  | 2, 2, 0, 2 => ((98453 : ℚ) / 100000)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((0 : ℚ) / 1)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((37817 : ℚ) / 50000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((1547 : ℚ) / 100000)
  | 3, 1, 0, 1 => ((98453 : ℚ) / 100000)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((0 : ℚ) / 1)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((1547 : ℚ) / 100000)
  | 3, 2, 0, 2 => ((98453 : ℚ) / 100000)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((0 : ℚ) / 1)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((91981 : ℚ) / 100000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((1547 : ℚ) / 100000)
  | 4, 1, 0, 1 => ((98453 : ℚ) / 100000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((16347 : ℚ) / 100000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((1547 : ℚ) / 100000)
  | 4, 2, 0, 2 => ((98453 : ℚ) / 100000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((16347 : ℚ) / 100000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((56743 : ℚ) / 100000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((1961 : ℚ) / 25000)
  | 5, 1, 0, 1 => ((23039 : ℚ) / 25000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((5657 : ℚ) / 25000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((1961 : ℚ) / 25000)
  | 5, 2, 0, 2 => ((23039 : ℚ) / 25000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((5657 : ℚ) / 25000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((91981 : ℚ) / 100000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((1961 : ℚ) / 25000)
  | 6, 1, 0, 1 => ((23039 : ℚ) / 25000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((28933 : ℚ) / 50000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((1961 : ℚ) / 25000)
  | 6, 2, 0, 2 => ((23039 : ℚ) / 25000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((28933 : ℚ) / 50000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((56743 : ℚ) / 100000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((1961 : ℚ) / 25000)
  | 7, 1, 0, 1 => ((23039 : ℚ) / 25000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((0 : ℚ) / 1)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((1961 : ℚ) / 25000)
  | 7, 2, 0, 2 => ((23039 : ℚ) / 25000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((0 : ℚ) / 1)
  | 8, 0, 0, 0 => ((1 : ℚ) / 1)
  | 8, 0, 0, 1 => ((0 : ℚ) / 1)
  | 8, 0, 0, 2 => ((0 : ℚ) / 1)
  | 8, 0, 1, 0 => ((37817 : ℚ) / 50000)
  | 8, 0, 1, 1 => ((0 : ℚ) / 1)
  | 8, 0, 1, 2 => ((0 : ℚ) / 1)
  | 8, 1, 0, 0 => ((1961 : ℚ) / 25000)
  | 8, 1, 0, 1 => ((23039 : ℚ) / 25000)
  | 8, 1, 0, 2 => ((0 : ℚ) / 1)
  | 8, 1, 1, 0 => ((0 : ℚ) / 1)
  | 8, 1, 1, 1 => ((0 : ℚ) / 1)
  | 8, 1, 1, 2 => ((0 : ℚ) / 1)
  | 8, 2, 0, 0 => ((0 : ℚ) / 1)
  | 8, 2, 0, 1 => ((1961 : ℚ) / 25000)
  | 8, 2, 0, 2 => ((23039 : ℚ) / 25000)
  | 8, 2, 1, 0 => ((0 : ℚ) / 1)
  | 8, 2, 1, 1 => ((0 : ℚ) / 1)
  | 8, 2, 1, 2 => ((0 : ℚ) / 1)
  | 9, 0, 0, 0 => ((1 : ℚ) / 1)
  | 9, 0, 0, 1 => ((0 : ℚ) / 1)
  | 9, 0, 0, 2 => ((0 : ℚ) / 1)
  | 9, 0, 1, 0 => ((91981 : ℚ) / 100000)
  | 9, 0, 1, 1 => ((0 : ℚ) / 1)
  | 9, 0, 1, 2 => ((0 : ℚ) / 1)
  | 9, 1, 0, 0 => ((1961 : ℚ) / 25000)
  | 9, 1, 0, 1 => ((23039 : ℚ) / 25000)
  | 9, 1, 0, 2 => ((0 : ℚ) / 1)
  | 9, 1, 1, 0 => ((0 : ℚ) / 1)
  | 9, 1, 1, 1 => ((16347 : ℚ) / 100000)
  | 9, 1, 1, 2 => ((0 : ℚ) / 1)
  | 9, 2, 0, 0 => ((0 : ℚ) / 1)
  | 9, 2, 0, 1 => ((1961 : ℚ) / 25000)
  | 9, 2, 0, 2 => ((23039 : ℚ) / 25000)
  | 9, 2, 1, 0 => ((0 : ℚ) / 1)
  | 9, 2, 1, 1 => ((0 : ℚ) / 1)
  | 9, 2, 1, 2 => ((16347 : ℚ) / 100000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((43257 : ℚ) / 100000)
  | 1, 1 => ((43257 : ℚ) / 100000)
  | 1, 2 => ((43257 : ℚ) / 100000)
  | 2, 0 => ((6780231951 : ℚ) / 10000000000)
  | 2, 1 => ((1326129849 : ℚ) / 2500000000)
  | 2, 2 => ((1326129849 : ℚ) / 2500000000)
  | 3, 0 => ((817300701595593 : ℚ) / 1000000000000000)
  | 3, 1 => ((34537541555793 : ℚ) / 62500000000000)
  | 3, 2 => ((34537541555793 : ℚ) / 62500000000000)
  | 4, 0 => ((89633093710638733599 : ℚ) / 100000000000000000000)
  | 4, 1 => ((2866818678858319341 : ℚ) / 5000000000000000000)
  | 4, 2 => ((871269497581121001 : ℚ) / 1562500000000000000)
  | 5, 0 => ((9411750636422773660608057 : ℚ) / 10000000000000000000000000)
  | 5, 1 => ((1496743207610898942533619 : ℚ) / 2500000000000000000000000)
  | 5, 2 => ((349280004422548969011129 : ℚ) / 625000000000000000000000)
  | 6, 0 => ((966620966362537445823882978351 : ℚ) / 1000000000000000000000000000000)
  | 6, 1 => ((156390310038615062096580592341 : ℚ) / 250000000000000000000000000000)
  | 6, 2 => ((35123361517689395614498030983 : ℚ) / 62500000000000000000000000000)
  | 7, 0 => ((98105973494309462288384591840570793 : ℚ) / 100000000000000000000000000000000000)
  | 7, 1 => ((16307849126955545593833115588323507 : ℚ) / 25000000000000000000000000000000000)
  | 7, 2 => ((3543509902009908079021075084850049 : ℚ) / 6250000000000000000000000000000000)
  | 8, 0 => ((9892527253987601818629806894809508507199 : ℚ) / 10000000000000000000000000000000000000000)
  | 8, 1 => ((339050391633211223058561356951380087233 : ℚ) / 500000000000000000000000000000000000000)
  | 8, 2 => ((358535390667584913839772935188143512871 : ℚ) / 625000000000000000000000000000000000000)
  | 9, 0 => ((993901673973018489994511132632175941223992857 : ℚ) / 1000000000000000000000000000000000000000000000)
  | 9, 1 => ((175626885401820754527256953376778362777838979 : ℚ) / 250000000000000000000000000000000000000000000)
  | 9, 2 => ((36365576552325591361907308720106835327459441 : ℚ) / 62500000000000000000000000000000000000000000)
  | 10, 0 => ((99653962686250988177758545198947559432873026684751 : ℚ) / 100000000000000000000000000000000000000000000000000)
  | 10, 1 => ((18134112433751282713093128126482083820894778941301 : ℚ) / 25000000000000000000000000000000000000000000000000)
  | 10, 2 => ((739142079005817539435176165596405577168938896523 : ℚ) / 1250000000000000000000000000000000000000000000000)
  | 11, 0 => ((9980364804705939822170553130223881364899514153172825993 : ℚ) / 10000000000000000000000000000000000000000000000000000000)
  | 11, 1 => ((1866588686272521397524394822759219080646243253443331667 : ℚ) / 2500000000000000000000000000000000000000000000000000000)
  | 11, 2 => ((376142881646886871221316097839543128220678326243759201 : ℚ) / 625000000000000000000000000000000000000000000000000000)
  | 12, 0 => ((998885840113429143329423696268293700288493131593485665320799 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000)
  | 12, 1 => ((7663553694166353196061383358982704998104125620747823395053 : ℚ) / 10000000000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((38324203814830920964816944559931765141452114853322246326343 : ℚ) / 62500000000000000000000000000000000000000000000000000000000)
  | 13, 0 => ((99936779225556309879941488797351789435469965766009157107298097657 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((19614876488452295678474820989142377991397830048695735709556693539 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((3907511046616063817870579662039198860907715854979926974392938833 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((9996412663595741691517519898828132587936872267460657601739415955351151 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((2003604581731125684220090862607011845258215028834748177137318219285461 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((398565360805804929025170263294592613466942607057022487978596347123927 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((999796443770413170801778631619204727437301943072520094295499679554490361193 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((204247149067324868012052550056013751616560270713785402569277692504914551027 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((40659257975194496505999188965748827115210922567491905577521805993571405633 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((99988449608864554550805324893968533848974824155764007710609538316960446565174399 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((4156640219136434152892200539913452752896055483652963892817565980417852192548737 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((829504647456609617235699261797478375709890494199903444968090621629140778415739 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((9999344596155801418876346550458456516192378447070517089523117032719286619447690922457 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((2111374029856669520443797406898393054357284075927065921652983357096497368996914031299 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((84595001760737863259794706428978698040349833186929764068294606214454505725268916541 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((999962810419668639911300532312664198098304130222122351210810229787590480647320326012977551 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((214184499848532762908435109415577343545603125435839971088407166757747332598016531367328821 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((43120089383861721562438491543272553262627030208766472959750289014762578488692359779139319 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((99997889751643257634486926105017504592692071261193888574755004868837246643370897258954385176393 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((21699313839274355501455806287167080164259376027030850306347649720340428115452206623999003805587 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((878758152292426712074304575245154517832716864979753053076622817691280540485728705163538979949 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((9999880258177493367953691647977008263103126199573924819397323241272431886284794823164848678064067999 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((439163565595027986762678029258421753224751241778051251265373714435096466815052776633212348807716449 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((447466535852121391527952898310596942929071913434378109247394003037375826979415849954917537643656327 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((999993205489765506177796325181159379873260689942423216027062312679521602523458112650843008539389410467257 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((221967552941163060235063971643378488654846107663854922128897051013538988908044501065277854341303222716259 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((45542724838647348367858085373590197162940237180092341554459831013948527568236639543334027679148452253457 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((99999614459105764117046696879754526692148431329402920547023596808374094291988583686146784833550573318143563951 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((22416628484811253136637213964447441544407462110847306130339705828368240924358250399080049084422882426565855381 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((4632313721548005797309290164081243426000073714697409330587567303958990463827091020344500527162900385616167191 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((9999978123253038373293580721047911108092578438924309920599759953697571232410308204103027011810160181791420249271593 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((2261926058600572247493467662688817049809717152124203470940299203660325209531748536386154848482667827179482497399347 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((470854511781692889657780520945352502035045826451026021591224015593074845637115929103463766835777520375339146055937 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((999998758647747156415797650854421620006497178359882117824592179052661284440658118425418061731143919195390559204418001599 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((45612002991218708858007343543345115545046768037977733364454068536344373439272886501489704437385692079609072827831163201 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((47827705388669412116637111774772675412218538517736317052274767119373303210425814442312056554392424776808719521331049639 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((99999929561949116896501606102432445984028669391674791011720834015985159263016263613813497076810299406904046500936290664732057 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((22978096304001988841324002951228083137679390743303108812727170963299029172136291212388670829713352421984429464207907080892419 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((4854835707127117783373571676158449533207595196252879709907905580651822712232072007892816435835155008572151315284668765717489 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((9999996003133678740058190635070324282471738787291802666378075284569045892061331846238619264629446819245956310602627941188891110351 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((2313669304862589501895094465540245256210662154016915560919669722799132229702166945915578616750688702937335916891879950940261329141 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((492462286278154566562411241175416346215268428153497778928030928949578770075018095026864574957892429069486642790685640559090949943 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((999999773205814332747121911205795410760293874007298758698291125872301371053236152951117972932868700864473298932524917266881248274646793 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((232828500621061942145898437401699747749276861227462095460880488607316728754765168818269995383214813320434449082179842151522138515716307 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((49920459961085150249341850588686089749243385748940912729855090614686479437479316946236181437267635239787726786043402475157438049392609 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((99999987131017522683069938607550448992771355292796153464817133355371996697673779026905287138129768693152808401328261380474642670848282975199 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((4683508571698237249382904493013121350816658942041261947020050241186292688751906998710726407891379971750637845764809379215205664984186869793 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((5057046597891665574926454418595688492267605381946451922731312368845995304128438428549968997479320442079249704344770468959743774509144953031 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((9999999269775327289605437526408235127196825013379132136054118597983873208616103243323686708078897464955569807116569535512272649071944120861716857 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((2354167054431039121752154881899992486504124735042945936892405148643704430647241987537689782306062539790531563846513586321893240588947108777583779 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((511958987820805548953121711954097923538170782505371796781758415278203143060472819943809615361079235283270339831320623300659238828834714549845201 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((999999958564861396394081341560982485822529441734172094796118851605398917476503546335915954876520878853973897565215505153572886926289325250056399616751 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((236560617636176258119107848285662256670707092933854203879058615449055600872823411063681089212740217345714099189594898920219960144545092177516837494101 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((2071864563014136955483194408409909340304730209519370411458629400594735729615206989292125143052712265891771753367927860146911418332200689374735045359 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((99999997648845930215589357564194829193027788112322127175016171996645150774369240729738879027558424228811040869543023408929186322858435182663950283453301993 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((23761480197625152441553296377414577580443663091652979490573714833321355231207337724349325645002144913144271338041695110497947078343150881526602275754820467 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((5237264137912811773909302088023773814459324538954965584766370220925809680772082091726005733025327355602998291095164593775020558539010094010562589328532161 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((9999999866588464618223186916265107192899975780857494462291942647605635790390033826727573212660747666015424892060479777292868819517956187569900530933990714988799 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((19086903715853843340452450489123230972407149666901085354588143819719871626845451971169235167310877892227375364589954588063671562647334432249356526642505281321 : ℚ) / 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((529241576561036005774271657420028886280563535534665301210744668867782094549629586522550811922531273957625826608065752415617268813351933102311073044915412764903 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((999999992429829247831838295189630977446723325733196808273831701653086591654101689430002686806008804812713254650187804002929255425907387951278865826787435140609421657 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((239481587093158327476677672952250934391921013094128599382732622263217712990401040316096775579865384052569498725724582720470780320990681076121037449819895380270294339 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((53451464002907507496962185787346514036182915742831744045920804457988160237846155590005051393919871026171201063138020098012732516557188599681702766120468885846210993 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((99999999570445801009722000383945230553259421672078786491882032246901092470228692163326642457433357611487788208615606562538214740632262914519416683609399432183600413083151 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((24030665125311993981938942525454503456594897324465314145740091504230794364577091684342449719164657598986325416936892928837449501151421593023468183111932438974924320974261 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((5395496508941627741071812110078069429861029889873988387685416327888526830053126754612371293170195652414921992175693286867304578005306998182540354553694745484753467469687 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((9999999975625806086694655467786204217283599363938766581908862155785908690038186679423643672962141010948651566321475363178105919027696494558575260878048151980394038239577237193 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((2410669974445896333179630030128701817660901083732371990725404537900066127796084926594546342178364999968311357800331509219081435334490275902043309999421278132685166133760055827 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((544351510588761466304796183108770847656655664184503754895333546552691666299311625991053232792674444095561735253556437577993559162415009468429210021332792477722767141567000993 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((999999998616935114777314835208592585901323278707977432157254565305759816798836826750535812934890767384259335827779476532815264163388582190737236028003086287823498911828331170042399 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((48353540423447645643302040885773878235690227725024878888882731856442932202868177314719355590493632691910001442200752750157186892379719738371613872577703946725857375842120533385697 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((10978516325941260879630010307930854100215957282757261901989375322986376575217496949176681419650695967001689169334639430203238626572490608723293841926961989999042987897310402597531 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((99999999921520749217809175694241169101798786803726763432899095799144729284616398060305653633364506813685027492875690836901536534423158319249002983936979125229968798753874995581715846457 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((24241344353604015919599028791190937674393838080683307438879761387376369301180117760334185398152976866618823022095538405698279309295132270722907960057268476782762443006627656797914608099 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((1106557443303823670729698532114678365679690295918552015340831909435617109715568144562490909222287551243843179917358707472867902366371074944450602100745986589881211906690935827747418653 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((9999999995546851872866146056418326658343368559603867737472993392930869373796988275135923704118002210128929515028245325158303887572773272509146176317536006502924119547691128874293302275509551 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((2430085330096833880302691890817398984930065963085559063429318417277179503446687688917616576327213533981760593337765667046694541171406023004787600818538049810968224512075127206204363398873621 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((557416815002953346217164185087326926117374011029570363516391739310388712014353700579519898717223645497577572388649896042922397777904218295791570945654039183856461973101046245690166113411479 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((999999999747315015822043725679345109574377762177602267027430064095076320877362505696037718742767799409345847471247724485457637492541873801986481482785945616995423315494637725714024851019238452393 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((243556943671671199595865386306804559432226504639495965682576808106133189161648844667433419591786092771685960018605521894990616059722301843419641792791880627131821896567817726537458479148871646387 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((11226940267146411962652512287760123922544115742810373548720298108833746230130746837714736378472425602922598256916755658562024896971533670475871299454569350141356959572255868453837940994547885901 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((99999999985661895942790227126223079552578917359243685437937464126946915675544180660710268274620873241884511423061009630478322724239303545146118918777722912145171305191112228470190912121384647504135999 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((4881246740102203163196719657309415347782324110637533651816867736703850969124283760568384836471041364021843707673145452694147528144528612641575199848854358085777640764357758997382245267458428409916609 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((5650764702835870926558516634501753642076473827570215512482872083284540771865638912275033164292016797239950992418588100788286430119658718596817894918341343067939962570873549627899402529078712164027687 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((9999999999186412961481745857823276203051985507715564442804885526955348836177403443230682752706812210364252831678750869462231466341510801062226225808204331203853455370459281180084042926503729053327188991257 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((2445280872876176151481596119089555862953746560641039623227971682871343351192829609470353201035657972141320670522254601577777288880669168385016559786078225749481302240880539270843835353009529936476985789059 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((568612496241244623123070495209062426124205209958361798224435947865551398124313421871990969610093660540679101211062596179911440767564371917958994758612681792800124958375950666478030254317207688747367874417 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((999999999953834630673358705210466161589778813664304273178077619456027359011214403579238631436842645252698798427947360585895400094616347384673902731034938365500256618085970992001508847778601097672944684930895951 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((244957304119181445233403675578008554740550411623065869390537338925050956940270293642525238472700154825179847515570925518017079739582650562572611712455713665659955515292057627438029298970820053499547719988376181 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((57196248995318320921585094546020975989154552334339868578321171681608458957233366570206562422618716664155953086100825887249939998870654497674446594715209703992021149358460847130074117244108279969633802967117751 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((99999999997380438448298393009757481407088819223753617372943658360793360432373338902296737663620762219573887919197017081725462687568815399648551262667115507673581061280052251999141616549501162085255900257033828947593 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((24535285318316754977680005547484680513547719987130958939256569217730265638808540626339442832937803895409816371362158986147322880066521402465787128228628262707304863695321451829493986926448729602840964210398282296147 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((5751338795790269996952300580791583839102746282116257098578609619122334070222668175476947959263815456514133693580742295406236963905245613640891191950700519979447873805766042835525085804029820773794185825134909152097 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((9999999999851358218871795714552668767482440869213451510592942006366497651014160369333023785246832910625281122198996340268347929280717292222257744297520135251922010160214004935187292747868344440203675548284870555973269599 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((491434750757932382304038347985226527689160971526364299134894181374933228003584797509668319254115314099594286345759294804931263933146558672869577523025535937720455895975245236193832913849476180825719743635501488369990561 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((578134072574067278350366703202046658763419765269469599656492480295806869493143756547505263529307210649415154569868080747292073813462263240925377243865097142395023096150700810588287515718938121980948119717723719403395399 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((999999999991565619413442304230862083873256142241778879065575308267254176211496501837063768646261039847610326716937649335846866551175741312567571184674185034599810622521023282037332552392293468570477161636328409957591236856057 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((246053304453948596585262381380870462881644659004445720167649300168426434693130571480767027788780293768547231543031199683482458084434757915332691367627143434611850729671653163611296611122131458048114551222553006971387832381219 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((58097041323317271112147489902282957988993935213989242378961358462521598165585304967974192936093435959354024962160932734909799397217930339018205272898897272123904818508901263441454756018888575522272437007052639178807063840849 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((99999999999521407942376956668971807225220173279225258934817939717008803720768946003740509424294790184072952768899193036263958748713365089299021691731967281418297054153710424092644361020395908287094585582730182966223599552923242351 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((24636288325241547046581200377132218923796300490149828169617482085833591955130885585484048263218154651675402520771497968378605112536025179159344512768193107212939944474384595601837859629812434139748750296434434922382053496398345941 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((5836501470225819634514763609322675254144630269888110677924323228102424638980908415302413865712424840350350645468787099697656573553592148594529132901187605285124411735392416687552457150087195355062891339769369462833035314616850903 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((9999999999972843250874295652267467257380668292383078867738374353362230549527592303090247726262759279414851558965646910456725811278242475262094387853947019449518429743843990594288918977380325023934608069720858772052425709431523540722793 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((2466481786900021490599738313982850481110028627770808297570446658887134764313469795129203090726174343630765455084029484318012355857096845350723934456151991827176974046176812933928645384005991056733678314645945673503805000737368446789107 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((586180390895929307996688289120296742030517092412992540675413813779326718853936262553743470852765024859262378427054451475727683818087983422208901361180271635900500519001091744233288283857497758489223113639093939099632409360267668207169 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((999999999998459044584360158196612894585551260914693044192078575932833048071844170054249926731327749791836922010387702640045992709361312773797021849996515724624024258954939558291736129533491782833121465700170689302570792030272940271233443199 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((49382219110701025220534795567500014445779857748441965426107406880669225089539146189257363164032518751713869037171090949643277196456650074826056399664546612793165372185429687658905762824619785839256925037846874707882292092829628849130868353 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((58856810887516203450808892805890436352021099307470295650019081320725304375522064480151150560821441518790114803743411848944782659775483113989853149309443168851140571933617340944996988685207311893587588435545040517406685923450806755453305191 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((99999999999912561566850348456550405477467935198082427406591114634156745646740653741388303592515730506438202465635429410904129764307288970723564410834352291762341008525880135356147983198118924233299811328224785423095774452173777449810599267440857 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((24715338921825796587547953371816214542608708875980801888702437029879051144026734198562391905043037707756508779010065572653759458286352755827766227685272955578822451767412927953280691944343482305148557113177117649620343873705401616974410301808579 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((5908200922530366797500087995958976694097727933002706036926141582657722902033542702618477876906399610966176305763240409112607723705526875836518389826471924207082697021392577759622713493769362035019371949862177360432916421931727058221282957382961 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((9999999999995038480987789322470039658007963046944791178332199617685956218233004915247596510750120096126822922507551171062933035216088498065767215363973652091470515846784016520513905010610862117770131194197458999262723529739696653834602834232396548751 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((2473766773679606643554662724256390412529962796098326418999586962723115215442186138789578251746069530519134138073562679988262855105643718237652534288210179338467912582796956733895941641874429165734771359336599258333103223725907768992972340936922926901 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((118588588768481773939719929183545410587865178699919146008542196541399586210647917413177859549995111898621891469911184346031099936701214504753687661067833382623596770923870229546434844326933379299928312382087828907792268023175306269665474164486155467 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((999999999999718468526690129524917460314345847172788285832104002906354213691195397905894368809494064614524313091845976099624009217266509645745829101397956940626311480694065449423520512017092149148630554352346415995164721248019607228536868622848877365777993 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((247582450795208100304640552877935662626464866972296104970035379586993565938245028445092910125491769163026025379344550183452763357174452042616076459193049618867222633555779801165642165674387794810400816662844858348499661527504301497486015209312798883589267 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((59494306575926740423954842571460835889647774084497562205474263356246130271624474403810457075120790009995017196267931938421193687695352950964440820206016427728036496681165756525576189128680118107826854415077500949723736681445222757931675946089236575737121 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((99999999999984025059609978019632391450616926406125525702971077436915257147479500463374164169357121708421953097770616221820965155015353556828555580700624270681958792349023355796638824413385859819140743545615192682813631777776376572968867536266313848366340656799 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((991088333419305824338211765400696082587237139480190307125413455636733587026133720667177643310409493587876342913279453033505421680753137114185388521649442969475838633264300228101617725758175972921110487098643283509234113043842114343099280679953477697213725357 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((5968266502820507775207382596209176626656877872663630004453925593228312764116723563938383678970920883489794840508162198626894394426672047004649134163383220216303554972552395648456823572230119429968087596951720944744148513870701883716521604313262084484348675463 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((9999999999999093533957448982768000788082356255062780704963687847002882436319429294793240197461831157100986884626798076274787025791036206875122729315695522991306387754260632277968676813688753843717503211008842878400893907966364935879972450610359446697851267888745657 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((2479468411364707361834701253203162824307395438330822604489766343295261330415716779453787308358961747947323756462632710254884053679272260922312514108782075852182705818974056096240525813048911295118281449319515653727922004957927321694658381997163058723257095877975139 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((598599673379808182570192382335022006655030537996205816497279361632139255193896982414014070282537010362031171033193720761627683110683311710783384280234607983832223401046320892061868842127733463260596522214693782357881952836242762451450207202427699901845539421595153 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((999999999999948564397347527629204668718157140981027365541754539502484558084073376474452828524576685347381298794378403242060240204460767486715089029560511061095698360340011057348776628439140959354062284702274771449101923019735445556637276764983626083976174493811094815151 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((248107890917724194057329286145398722782301834630993400901792699000690755623413196374432767216351129742908603381323531073823952208443236479238747722396999902819701263839478213502238472058979115600450369040277625469494533242424791897353563826977473714674967264060507143061 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((60026789054675794009496498343997690343767796714145086352527708649773432670593990915854757572649404714648046484158223275318388394013184177687608401896622184104172665857832872133581256134512320089970483023332890403933424297299283494319070382043363870310784695953232167447 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((99999999999997081389598690760263960517074390650686435802935777834989481279364575601289876848970054856666457037489413735164224209921717329498674296804352079139753212060773247427141632227522175456627556220861177356336390417908848387220268995475465894883060069302322953096113193 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((24825630795413689962330436195696235052082114025717622517332988621072029493634134416348628092326749592553699980145027378397000270762242466022174324692186085235061054155017715926973239599436434798568420349576985679578427076530600330829080727775068958400263561369123653208440627 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((6018368346212359617285582031520578046696358971700132637071959001068875032968773104931773695376343106308949143024860668596010171119436187814766424168805630807733570373183662941020203884039775415903803007186250271610567429230307786613178588792291066786838285245088718130788353 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((9999999999999834389289998509809657911620352148691900426765984841690808136234984113343991482041107822731824771678261803574423574343588006427743275623569350026627016511964456378758297637486290801935417422640325786730595801483401784036039723610264361273349477512421711327532750910399 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((496786166316427657754705342126291972806732436044005864263379191939585664560836244805430723795458842605060339524152376683642200125604340876377279472473287059623068511112197793434154121864767014273463596696945092216601037454854651155044742209793328710040073911486962939219706478657 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((120662363060670491781340016615314141481696536600085936211698688877685099475057358369710439272031006251201064577132691692834086172129503760025419687284365725172689927701820676585090486398412878373604708447155309789639349501044950326375982667181857155646157171778249478400536705723 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((999999999999990602751482385442129418879073641973224505915982277872061526074381703543478108665458581185271933019339609520223516878978214248729436688708195628560896797938399148299882082843884598974221390812880006116454197563572667431557002036817230651733669402487345165858190884908770457 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((248519129715283211377610814622689554394573682443941838872167960336477957271498928727713936206754137935936811623200003525098097603163744269621927398824060706735333087930240798217334557939957961099521909651816038459344124405156877057716190213428298415469303582336821759046948075770864899 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((2418791680473132895491629549422109716212245666799963007469158193521095103085437158796496978183236840486841726595420629264288079945015332193495684349379624738587050065516001228859995019501789066877635524955750810962151705413453682638509559630043189127223169052564458651057941011451033 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((99999999999999466771927364997142749615455275666486678139190582393294387174038641004167578320004116272195885295316387463006043018263860811115654426027369144551430967005418582871980209026810543799594244378895250187065960532349803868068838966575120118871323602905339426746291325382378362041551 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((24863528918041621199710759190220594365208195691213397359204751799675575282944117796479966076162598613328511072598544499128098599316834295053036766712586910117509274672056471730332752285971623561675989253256816532253683810103803162964176506302896858084038866632109829896978459196045924498421 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((6060000166013721255434660126388692791349151783013004718936514932273084282207948069386296416937804221290006741496284794674710676785124926353323306801629700481138692831373517436474735593550429392895546950772765544794475142060568575341043623440189396622944763505165763755663455472868700995639 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((9999999999999969743039474472032871041429778707143453577652091216742703411416474606499480896611993569633211119312137773813351898985346254005135579096071007369281847360788466647904773000808310686820376208791653181364683798487124920885830129480372040905115515199657675091864808676172295397323728393 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((2487423370971042597620294286693366026316034277701442222865825838924152609023287894661580374800368509819678397470506902676603904877457612345505454602604830181254540842975662049792498309567576417340816778850148769963206833807864049671409643328303573406699351378646084099835424174745652186039967187 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((121444551101488023037693867475899791685949140693163187019942797675544431648201815456252149214935028339587814296539473460166567696614056953123173552226873921656050612839992122787789652118404744987225727944210319753165825028669463126340393258122814954777379568609524700218979232208226813379102253 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((999999999999998283129288899966561201503849933179440986356712611911631219674005018596600044516454351121697298543128633699491026804125502491013408164648357171155159864793219963002060534384865973302248607215464776470176252777554929385824659037104750717078969678974175457737684838712044557730340320203999 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((49768197635041468458479249944834059926684850188112484391239759377585329845387565184755616611671775956198601880452627259502618506359449545483294308993009195126971033719954258991443746814218933914663013763430948386677086781046154266275107994894830736616543390191407445431916048012366838826170209492769 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((60837057487017865789241977351750796790657388267168261514089126783067626481153100087363224430241285006071662408999122617124371320710519540669632105870807037606115155977486843617800805088180555749619212625458372873761597457807536620760760716044633982312858385677421762286678517423582975005647111791047 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((99999999999999902579605240050802582256932956758401019888838943737701690297962066770226876325997169245698469811232748062010219333946493387847573819486641730962857236207961680360625920902600449923089492719227117811247211111356799358139848627742434869939211976494031637998409450803037544339292700789335515257 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((24893190106274404469514604322415064649166894988643354332040969757962477107938406127299625709622887907646840176918036839318318458923197271952669645108674205343240981412340027805524490364984522542844133000663238824271083678667232179339846418259402522974362722872865080778741876571852711372031906497998141859 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((6094477047585200037908772710537044386620967229243601217548503408517604345131170168287574131470757624270067412401561154183136737886253041583414317048306548515849099299885429069853156931219783942695179008662182259485742611209868887403656098437753104646548985331315229927751082302448969499311014138292327377 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((9999999999999994472074540136202690925005146765341949071552388184508407012577261554742983643366057374508668272498779823282645875666125874306634881239130511740025408154148369628702996629776257329985867085367104345963600500091718865978929430683988981824960705182200837234943747466916759378444485720889265142227951 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((2490156827433823827251193751676106561614469902776641361825580777684423055033475368003839211371287306907916902643886021913820996014395241327639316074648284502029878923239420457633102364965513141757522416031525815117381768480628132260555129680116413687176165774976550426360617310380415093650325361477403706576981 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((610458172595665801858238996988507804270458137050902931649532221810712763638575332444344247676389622809127786044214539966804371714593925150460314975961848401704685159629840395888021055759225057729534261536572679639563691172523119491256770233836263459360093591746374752628941560621890400179060387571042077940311 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((999999999999999686328925630948549291157567042905798216167097162753560539114671552400781120875520193601745363786398263512527174922922980485781383066151982627664261734890840937841494137763394169675388056024985601903012583176704403612242392685301586795693745294153622107222413062515257677411075453260419571965440623593 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((249092892588991457783899184586556753196078181167119723469712455378106677211328965922612797287773191566817488562420067468947356270883880699305239814285222240091255347440336984535522757936753069715908521126206184640392054836780626852788399144372110613114154676021034822909413737638041298511569020510975464927217272947 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((61140580892323906161287463953509770177674315557408004279634255338227199056797193533396517182364456488444405296775295634153826652914346834409321485747125387215977558139320075040874982152244515691109460864002213988308817171685552367199207526972122982601341246125707927089365909006326925717549777110854142403264760257 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((99999999999999982201362227076913532428153826715603708179969594306125285670983807897877523141839642345543837177331596666491329486651418681704693019322661950241553203622910987335939901859108275369890544463025758008782643007195737974169470088142067939548050189226158979230121384406303266389336654444355987772034997304537599 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((4983280921886219233684807283409765861499553966955071107595699714796906232458220619564447344977784268336931026868702146483275670904685374891558194503598595738139869012166526845192561056914686371894540330154330783410355576229574556745835008720926527473700694569045947618460616884272750842207054723610627545291372813713921 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((6122942535080014144913833829073884173511263537777213820118080559946132950289618269437933132939302080811611709600529896767685814673177836923163006116325407997094579584217681662141034983536218357742780085311478360386396174808780573209928219577756674496926061197637989016572965049895263152807704108649897234037540318493159 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((9999999999999998990051896851025304570570732589323501213256014689712467084828634211549264295637406825613193952953326789646717509061061450255969395995425807042556453433174838154403237851191380869313699164465470586692353512157307759868298241211445361093775011887259938958454777715366866244730129783136091814148581852051376980057 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((2492296183186732063594156827347379350753374131082856536698866889018430138992898144370643870500010973803902543265307836119553260762784359077355087874259901028643774675730620685893606431350860514441921651020506049835046405352174206424692186161275120558785532464597489501904551082755958838461655854910687052340319394817298750019 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((613126961701928163124958805765965624166107129233391389016777667785979493776142914413151572016661497310318497428394057712791371890241816840302738088763868530592709491827457466973382281105812238852569609479127813111107262310608961033627057263916428696818353405979022032210304515688442193117986951401742132581545476029520556209 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((999999999999999942692514783017728857247895079315983429343786041538354519794431191065939903927353375505769464472430622024923691616651809871874471436968446569015780837158639841395302925390152524667467231689264197500684215340342114218206847101061044124544075499518790716319599451903062091324721754284491257810232980030951283979374351 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((249290047057756478072074886305885713710917153031735112875215821830908595842378473081469163813543966086899916118899182779930763334123896899084691463687325446806148904199086937549995943713756199453633895732962543349102241768975446684375665958894114363320332328118362982835045628682292567423188141469879152043019843160655733864642741 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((61390721097832073377651845242596538967479135272685898514696640721849867730999299681769228900817978465759164336354351449210445612272945000885632458629546734222472178067958917491436379709466270152518013288809715108793726866392093031813756466275742914399770605644478431313607647621068514031204512624858805279824271222213219226783863 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((99999999999999996748201366332774988546817310485626847731254451355010850516695409074654627968549812586323876722559130785560245033403673647559773132747900563665662452042892700520293673895413424707206093127743918358781324431057032587083711125055506826759004476069194741616123031699335452248038686503364887441926049985896268706841638798793 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((24934573576654605880830154711902970121806403405331224567071553704105925771767110130976180412002497708071162589683709538058174785079776041790794665015464287597707404637039148545833615225575005417721988536509543236178707938744112150627227499273026710794379478084632207640849199482027258604539105725450070492242403540154085277913569541907 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((6146381075772073007690222302222568529674115727284874219868681848973208167064875647185886088822141340986912284090232909584882052742842481320721424817755354040193004043165231484876353054128249499304026102175887653073584189208190576387889221851498722285896431629212664125476350852013165703776555010878921076523847451192327325172058093729 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((9999999999999999815483190129820651175112054648885924220814571333237380690868847597123127554819422015585775736868172758165044983930424653783484206871514121684080684516269860505623023937847443958160995342347573159432328692191469200088891020369024623870786190985594317223523669187715391566910459188260433808117209854349711975232315110359911199 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((498794112506036370635401323401740373417099931616803715920807216452552394657241899685127721498965672253357436373566078331954559200863288986027437652496751978640537530037418471822027707847399185025283744838815858074971037202441048051294786987847779689448248591987811323131863218525620173163661938293535048111341584933756493161103873677682913 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((615322593202670842229008059873664749829510166041519399982245561287726692282465983108906808189430155425517438290989258419836471206110832526544151963600387874907130701095168843018644911513595546482014648992216316842795670808547214684982312255021121630846849709745686034331103869302380752720733389910165438963419039054322278208544695557369351 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((999999999999999989529962657536413209629383316941733998061681221161888692541971019203557626843118463430383672637110726816559147523164086129636244350510325806719790281506700694670567247305277512517929358710828343785668626981020536820643943168799564232300020835095578342214403560718534463681200185719461795573994838765365706610607256307152441164857 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((249444351160531438499542757641632226217526045656856113619006923581485595944957732674871604647294289033465745752210264352559675002061349045051135251192492569340469105427046879897680677164043434077903955813173162049431951087528257222449927239204157212714575706738894157548029849109345146253063558395073790166461824030156102102204012844618518513379 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((61596345172307020750536576741671513046643003691225022259367336703349017283597191965797093124802483819838154706787221496983264293434814430824201894540287998150512007372143268013441222140890660190769449110671276383389768858802411592652175354589573964867362359295763932203125127037073906445601611585529317339844549203365606286031268445194610872721 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((99999999999999999405898671076588694754000097553224812252013977532389050080909061542667470419959070970430260736447573971752015707906899739253949413181007417250701059943534717517691997313843361892804865601328532711430194900784048320813799267227193673233400082245828401872271901245851801072662342138279420666255189136063146290205687544636750969017480751 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((24948793625549935225832119144651165743385550948075972376872158924273850305978329981043644104115407806955051647582063256961761897782890455495949095380246094127117779621769572326099642856695235912930976424350720303991147061932035345297378267210114257554464779687851959112078684157089857381376158851652284787701059734141947895994113837326990129243239701 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((1233126631664985591036810422788144150387800244740325598028225771675425058087048987315084026144528359939126262515753502534271845380964212832876085204168651737207048893425934787705208215106921770953463801918530943433320719006887591029135635858727226120089985708835078475812577148266401750840623951057755894257429182661699385823583928804730294878242539 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((9999999999999999966288908292898872306426227535462635521616029127120351868741022879115580274039737564075124284968244689879124627313761211904486851552129903877056530244375990476106397003579413883883426488816184931644683549255189253867937411820272650600282820866875041007438324492393368748266079279952389166865318197147631109945141328345323160234958910253993 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((2495281025356179829506752065875663260660033024472763167189230087766395876006401647418228975552399260030763480938746314067173832255285483205361679633109914595607290877373068288336232693834052993463857404806670232981722760839846168038341051956047816312399953798197754640004248415523888278741592148066033900821905286755405180178326908067738771000783277638067 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((617124673638295483615798292254981997638469662180624210890492174723103378715373937467871003655046092402189455522917324944643795996192938172360198716417493938053541954951092362810287240998946771245194695416172450631332160292442385506533277072983365310679369047884905151903705598010245809077221351676482891424619996925510202823835459949641852917442590174081 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((999999999999999998087131523263960711283543429044756327403058340760190126087971861229655371489836828598314777301953108437811168727664752447096297417622507135695818695656626827585705285174106682013197269254896781576314278635387203832228372558917731013011848104449090451885072846671876922882862136582338418495438750460748032071617154394298672081212273444542324799 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((9982604726908964332076671701808492481691513424014167627735188843459319534553883843416798495535953262821854322888553326241097403179214989072720386566504161239027734156176551940142340186279608731678025693677281625664754687521851583543055329945643889116507390157866169280792722852424113773242397898606402212814655703633504975644652667391028515902757526280871309 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((61764987514534227233760248222232296628525134948908693349682277055892217281742554211876267233892682640336498649290850519484321548877771242777740726670699113877248109811001454700572183294107516571054786721598668687258204897917258814263267484823664781359584243375147116027886224233074557695932673087455449821639036703994667809763079713840030327392375347530858023 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((99999999999999999891458104024566922640362104794286608285831739429755468324609787321754334744447811165154175408444725232086719147113881048105585204368153922400787840247643976077695674996634335457474852649330608076984801112607776107052134544110668810871331296990754739511314688538702312235142246216091628880686681017394225583839772191795689549904228032063665136069657 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((24959923030325562920920308850917212783396106441943007955576498982676659112917205806719316237356852743096565452792068053973412009059543992873396337846526673571695497184597803223789505619396013760340883240671941726040180624985588170039845013249806626652037610317532533782164982032023466367946453168437255696773240665254759004280156520169410293739620333023246907735939 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((6181411386126128221334468265349200872013288781963924112283037557413396315997770981373177829450264170112691777703658947292566936849240901488715591358487814043215011474749205518251408351284130115192640134748175643241181729128221677170443965881994843254910620334969446573656746118263311116759579978026723302246205562363965188107505471127487007843304430252973467891313 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((9999999999999999993841007196666000891382066912342205013962950390462614539143333161998306216404202148944343375201379043844296704564682952312655221251462158018787904419172062134576685686334022096863495563880966694112348569532703039642459270436471680335271951785146396184090529371751585303158676477039687297576804340970000542303820193479062812130215611223388550816000547151 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((2496306666782682576327481324457302396564401672765295880002623881269300670594557811261985557603720279087674423843465929762095813354381656942575765496350461971501115193269424990979906898529458975930082621972700784143926080657995712344121192882050201023863858689821398227410884188367549800897587283020259420226861348222327647168351897540843522237230642580967189361145791861 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((618600556762307901253223983118169609829496405723317629092441123646017879417521223146403155192275333090117588318983639400535659582044410287618804255749841797840617467445984075861828008540575877879721416292810552303299137635137135282767570190803987569864188881422125617188736625039471716823638847118336171063173644749778158282628661133276906280830958547451610093062017207 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((999999999999999999650520271360418888579692622807033739107299694006020136794610153611269889637423642537548876139051851084856927907113804763076995219471717232460082060457080321702284875899651415842325328781297693124016994880994168578432066382376712557264336360144561958673848908141300204857132779336662976326400608719660740771945669238582461148704824427648736538952319046989193 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((249659637184024895491957584049349187405789233770461671149903152117950859710572145985338219536897086453683581562488350528134367613137739246685129133955790465320499852316933543314649180771781838717762008911286789150721967433971883527523695280564139290692666058869852857962278971361204778231012218225489853920974747719418997715904428869186417809881579911300677250915928667705427 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((61903010282548087480070300265498808563109862446130804647328149621891522310637013708164682848360221063543806014281292960859234134430827103730189601131225676647913630223953450902434219383081579653682498861568715495769074372074027431025549857745432722696201217447077170301597956310526320695159430257040116903562705509424540470791064966475860722323467106000227238073430155567713 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((99999999999999999980169471757804248994677498495939515458165506536983600622136563946364287347696329748508135878758219186108036660233358623671277939738483650921482436356516108694352750713173920289141066131037175000936096340532252107645970742735201800636850238083682879221030208594661797524208285297900267265688949740579709413622513109604884592960957852498072257429771439683307778399 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((4993726704866199653654302673557921031014537972135051785775977917305536983148343439331305842644255132448359497716271422249631043476434333831581749618842772722986041062135132425712598108968708711068175132593734023438026191561348492588955788890301910759573739384690729195866239718725655448876399872613487814903484088906006373232134800849120745200011407801688877017658763990441427617 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((247772654564654974794923496543523278337788206840380230808165321514333470638059864542674910443413588754704659619845859579464603031278816369364355644541461542386345148692486435992190198598429209611611826582470397550106423838834917421242581565422975005673577501459865006431123612983687447203765096588318984676150246768172344245884398722520959442064768513064702777637646621354740063 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((9999999999999999998874756335953086500704985297155095925642685337428060450101895048008548756970332838919597154168377631277328324211621468382979324134580777804237677886177793555643658133717627758966731515473442421078116914650821581344155317855023555773536793059582417615638917126286894376916150732658754865456988075129714451257182261378309966458383631424298114103337520801949933269694457 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((2497109391068247476371941920039072984949441381350926551663317663055070171915103491873899473662452382566379543815948413768142852103789028603935614629197539254754535058305754408269476700799135657572999368279504663496609393471421904798232797031377045170845250950559896325023686176648539302678239980772025339459243428927386426818016821743193035660057694835610920449016587064734567570801699 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((123961381838544336806820936280171739334305558911267239303693109543210734624559125868502435991541497741124046034654183436057226261009940735319439604894365326810555744137370894663303804601871848987243188887687022203100007338110157643327099035729480470113795144056055117616426834479044512257797501356160671364102243004183131279526829587828333473051826406149065633711503646373092765786077 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((999999999999999999936150298770985987309502980716471608108742894101680434120131830709149082116767596278814701318976251931569441100740036980455395789368517074945858556295386539727888093481539351927049246382509543299235588088031568990211405201047601625257798248579885122764199074496897247629353141023255727330625874347085387107686293057389442426748062397908947888565680942865045063522272573551 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((249733613043285414430326076757924812628883196107497130405270008503199473305658093586275844007255784464908603259226730554151813522255771419523312956396241332835269019168019756411099108439065413694631090285009452356927722534382618179601830221537284167636320597789638926673150739779871387850748455254770585474367191051561593588756492639128563238513167226493608586656217475830302628196672203221 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((62015757039449292815012329124374156173947169983962885494167476952571634907429871965253269324034560451367808217271029483065776849523690777112809121431082029766341519032955345237573570894717615600842568336864534735861272401851856794201595208661960396599062063592197033788668605383661915930699961277185655841830607895594108013970503524917941040642193710997999477702108177409738171625250691799 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((99999999999999999996376976403162057877903127634794748458914398040011652873278640469929246366551743715648782596942669463353044796379291918381980523276137764383652852059869118423779554088422987446396555387482739015428524974879175319211565765323044059022003246019168421521008948084177440522232385281082599735921703988076666120651443326955449131620965304644547430040882433740991252039444312641004393 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((24975450843617010652115920665593222553741295165667506373129307718954245993265805792557478030363645329450872871243811010986222200955554083456263459952603678252735880359343281676227637988627810933571366328461432305814832186119194467749190831495244306539823303375367119652231473960242243121374736152005242556271140198142344662883616156337072570407272389287044439721367678031575722373659700076767987 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((248194068836214869054325825572324611757260613784355421933009299708638630147260112094102688716958301851677500202486904466324057506473952600371730164083832991553477262983580781521439814040904154382656771828039663967598667334199361159065655884555449462468719528986719671241383703937803012643396134088597056714999022515139316126520688196306755482085852982475424252221932946699002175927611077757801 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((9999999999999999999794418772044624650165857171381158411804179687984381218988449896185195226577245593657058870898317893359041820880950161324748720832257885164421613784433153386720523237639385576670879742351933059952460792649569045138021876221725489041085530188865673742366610741140480507553032238004469956815405249395434265684124848701433050075568434281445554822809791937765066614474188632188512271999 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((499547529588873846729858007117001962632230166115817443810007123340882069007980602516091639498200013681452380598989844469216322799391966713388495844307330145803094206657008561476693182409476404555317296096109081356785402483947709634173662146614844742645220942260784310654748452294631223591501578472079622219573131524124851403060002173511779109112261453908964979454506037848795223263266723472728044929 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((620791174296088394703060589961306982455439407917650436589166698035601816389066817412808398952543340127132954417018692592507977825239180953654161769999798642293671327572543937914327585664538218522936385984733450566653455588241648525627527812989474101706276420751598372211049835938339399590136210920801039618533953901186608307805784818048133265746257841717024080987713332519751104694369833896739746407 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((999999999999999999988334704382128136524361233475681071761004568035297743509061612459236532741672646720882491511383252222872110042247755004050216666184809177884775630970090422622682650073371655777035729220275737620882482757314496328266775322449369424658316239506804925163108593284534285440081708281087638759576540066445126537714296289865415560437979666432065117310696023924603174905108885556272751850039257 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((249791510683961291095780827731351673280654261855924813404323078661149011327933652273783873487298580913301120378234141923402578230251373688552983356691989297390580533174689818748589630659649372806850698869917283238146353370939230542750200943187991844525633630475289780872275915511696657481803593547091613911649917237750695624508556629814267789094937532358087616240577294109925158606231924749485301107774659 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((62107694986049230169441509488256410518772490854824583670868366068526269677774091433165049339150435186902705139027870059575831249510780193589727133829534815758814913560047328087711749638026100212864611675031445413123796724545104654490803210481416528018480001169651289755451317255482464855943265630536081302948529610311797243221153227003326763402957861216851472831055141572797619968310676636238046550412337 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((99999999999999999999338076130755096850801829471110571054934682204026899859934683075774458577360730992883035215830419880882432140127264362194821444289324627180715823628135840850878881613113327863756338383146106179821734719098296465154841632121744569263386838378334631868530270908744328958726556372993755886134651612990295815129522314375833275145932280212354670951560824485553757953640593493119584758226777559951 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((24980786458591136742199902315703798078576246534440417685812127595014067162958323480975389485801908082865828615430368140702140207179893441205231209101695376488158384627579062255358106679864529417366900070057057875569165889939369457197418664527755789865859250995753649504310315221326888900641092196864987631249539368032451999112668279801589742285851941357865202057312916018910409742504827781789418275266008457781 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((6213437891585600947333877951580938399071360674716682891858422700665620119639027062223648462807340022255189191853969545522062760539438403323707294107667601493252275599595288301817148265365505711290985374008105675921841609907590495633587604714717073563185810537152427518993904663314679176586124434393529763435270182471123100865949876338784360342578157159254374145666489700532300701826459520522894093372145434871 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((9999999999999999999962440453887436460605048209679227133370158672303098378752273721768670103055179958729162067251865515300911846927241361704020753213309147320115357980131312017401420379372889562973125908874859502961624693165794636322281178731484152093712359370101842016116013162174879458105020988272784690246938536475908355437894484684627907531605635376089641093804415863783776887563428196580084597936062039084299593 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((2498229356877924797612876165098409960653694963220738962092429342448213124094919172224361706723765034761626933941844459760956882359659825381973332158227204709544107823873950445113355166032910808927690222425527739799582473537404291065653958888810603671203626724824587536813409270788648402615543269541730555438142601813472616523696051251886313342656144709271853070529739865454878639577364112898593136286296986230329747 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((621592904582259860053954864946988107136908333793228287663982384616363473452015450292475286520130768841449105079353369361048112706552256534903027796834640116505435302410985929825018362742237886517188539164472877164244369712815013221173037301228395735215901547064492017118354806301449603331628065174022369624021105636520458853662419300567928996353188308171019765002431653155338016982571170853396877306600077281680417 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((999999999999999999997868758674934807084112250561828385228822913542494711305540267794319647657660076398168843182072604934719640930192456587171249599582800946385305757866591037803408796586755872471784083447286152776551469964306685048835200924760605242253520407737688821520470934861289185091253205937562621678682033375252467812612446744459841357065898568145454504585743969358682851931011606158543740340685968283760411805599 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((49967364922488407529747712320176466246649682513950276839825759927808780916964916000779327903385299688512075707645105261847166116512226235640543819084977103021498603523193056017198108808975832988106104009030106774855613690922230625854879925369934082835842272235540880247236009313964724161756390341178130368906343216550327746674288876727078083815059664560033735550537833309947956477080689976355258992830520544337315933281 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((62182543483520350191251114693812617934150820231924615182625214577246538195794072333885325811434474366520134145152846092427986320892322670804573134007376643012090891171603636171821681717464212766185227541417622365695085365861030173190169838912961631173786934978656342489250201109532929162158596325748539114285486653195399207121081869568087125052873121502690601334872911304340347305257039846559783765324465111968217142919 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((99999999999999999999879066973491825758373781433629828063039098583141777403610271415453079767038605715061294668680345821810796585301910564125858216029126874100741404618623975258078825344722288471666444247049358166999860060184654229726055806073691023261191508496259676799536082256834132229632980664515115841913454619811950781091068065620884778123990282452277524953708870053319741067121391568254247458151543898325417047085104057 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((24984962408984208421552971518652459273823184832129754025688635392992562199789258459983759540378549800289403346048755980830922419030611012225892601422757622186107711122593281376737029227106512590176699192921020745312787109103150837162177401025413773569158555720266134579323051874951653691218057078251619212496560294770930108493111836684188788361509419328105580950469466756470196458145954086981880513524532440224202603287998819 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((6220424490332300228054114045022325869888003126342527301184500850672897070862439531389177395571248283166890384594165941586204971160555266291121773883712002408548041974355212609299026357226640034128946179115422603660455579215781567927020389343115095764656942259162532229263490604773540740273909010290933938883220003250151172887591823208225637708179235396213085833689571469766828759521043929317726747101944660795770401748663569 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((9999999999999999999993137897276846669007403479888457333781027570903213875213057630927054105221071604089723043384928862967010030639786311140193572752140746217098369522274580228069166786535576814747769045910321730470073059395057834957345584604039449732909789766603262840636075915499539165106064221846581218217695155491989523171450475247525864965089580597189583598448302413435522067371669121757450763517893055422679139502750059506351 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((2498614195762348711296398493607953507150620406781097704822981555598163587572258644883966833626288341202705453603751314326025458551962035058940166538348769230294496120670828054035670241954228181953261787991293379170531934404532075494010416004608539813654572409118011124495985425893696330870201543186470362312825295034361070560010798898150657030144406991489814144505687272583827437029523593705248759869801989145917757937942708219541 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((622244950615081492531220311081154935501366081567028393612334274400269916936185713294729184524946292941895470244261566991227744185991159315299593585417390991069110577700084398002342387290934110174523671199879007144491319879160844965557520883714951175256845098602824210030058744900290613349160968682822733347427777357566725431383904371314936082611885588475828182333366772677269926416845540314775893792948420275574678448597605548823 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((999999999999999999999610623705180110539487095659310734490736847455761064921214529151693831092559266030863154650791018471337050168593394653028003898674722362596812781802426505881328730968388235199232658972089385952063355609253766728984660507187010496194500200726368943366212855673190350845613402140240558065326676208081961513317614316970360155714078071826328542126752023845571828668870620975883028674295805643849082412804546626568874793 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((249872289824675007838217442993494459722896092431380104917211283304245565985601873692174800620002749787496470670385151623307508828399234259037609583675017180518749487129721281974954862885930118469805168433155773564291354216457766363577378588729225955993386872666988431619539377778954075370447285352933508478225628089106370273467569565218370170466528638258824085737623237324982260061008619449267265661820060393415070693093941085371974707 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((62243388106773415848559376433960111063586259230588801240896144222159273260400329797006521689822102009451824350347125295036919917424598828611331013039427020633572461291164471596267814387655565322053749809346976098961155198151234228689673320344672387081546433401122287714666721115208720268641743456122880194861004653726301208222796267882172688065294110401889947508489401044383372942885713380504480086487636319631004790425266587775852289 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((99999999999999999999977905620903035012342116268996269007207880935182250106824476027654563057685090432389267984349834761119078237716494992796768025222499771020830947677815087223224236181339253629910058768053268027077930987335886485502776591159312536585564524889816352953429016069463840078032641277643669986300831588075194742150181389187849146315683932029641360465898290089069282274157725646034530696065566899648928483349768389231397662379199 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((4997646148216550004467600621918866725398229297738834659817371596409360365455925592728506505741896426020609479474043044043963747794114295858091572887691202768187645520208230567943445197108957065385812069274034150888566055904325710711475164095504854956712795106224679080454282861714483609569437582116390428337093318844747077089858636505568599538973744057246324543269393555536446302840393124340076150712196712096629461080854990119648252913473 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((6226101234713998601310582300358270630692454542912077952898676393496935541483218067083287796863071025116322903815214961022728416722672228031478573231248145204504771487009936478378543188828095240138473302727598401335439564059298821418100773922181640603590024773813789861038743070917703766878395636519562757363411201551538606251249916780342730145630106697822124034723828411040484328904213705033783974813183751103401831095588086131485885945511 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((9999999999999999999998746298646900915705328703451655292275996787905046417811541243237202871582225086405064233235962673850179856442747075376267008055200304507035010464082261494307412833637733268721986464675646587660483038014400206846884052112152871263474687835822849315636422658829586677547806164017334766032668086802150775253827742566686124109390853355157939716916466674524058284082531826332937375286848462586779148930715907710157197556382888857 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((2498915392175221911058537687490366261388198985815601918073783138707397461654264192107671825871871497519691790469359579801132128132734031926365897052651674462497352791197743867141723405075471512956728110524241914647533289905760874379704471007190138951198413762355137494833398757533018348010427458633049618412301790201498015070821568233233271471493377977408088130921297709384748589962419643825294003420150577690096471832685258158614292793395698179 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((622774505869566527896182846569731276484623479120934729666839750221897370144222794626830476496512467847751929470237941994861624518615872517357527266862716312608421585482529406820138506267295268976309033025396463122931158643590655780132508905528996374315011279072116596817740649902602420132273763771748033617427722681456336888556251261746364757780325673325795874690765534859881729813846772785247842640616850528792551012342798843656364425011114481 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((999999999999999999999928861224121098659867466619957276249616885736096048885880284765008602542190198077882559786508230002280755594130797298075518838076230878642687598763419763971485526419105898867091677965090214323618789026051110937112741768999890374103344211868095938717157530929967236844095165164835626628991685249414441440227947596461470740339165191931726973356991068512518639213695103421609865485901642312561609247775612751197449860941834262412751 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((249900046881299750435508140620008765880189015324291306390160788631800716501538803265862759616220933119865047603870024239573335098684464461019035211580415508904201699345684598610649498684898747688004051210700980844660285102101537944962784856330546225734314881529648658481829720733177658353920200765425314110594145896028268747139388645275116855105459204315484489578056302854802569351662589607802684372124906472741204369266076545884877031076240806432501 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((12458556089394276622477283762729752750859843910610651261703994551290876093063001588470666768509468598722708482673932383693697594481171156863440761385050083625139801691053351147676320756184372488937775814445294970036131327492787509746498391668606010470934853764429680344740800459189295522031653844105724417550838604403485557971134197316573687194720441392941861090547770687730150535528233622867740345419120352036337102471471752297007709623834646048011 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((99999999999999999999995963372440303501256859658416235726232010947323298101931504998420883134051498409533290089965836495019416914677763831084699165428959568746822022416632727667034003225599326019415383082773114031365100945705218187904588306198360779497746060614031367850627669777559130920244491956948267961808875196107523650642854430466013234219065250485781983649195744200605845144902701253452408597266516889741683393546531594341196897459422501552086729993 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((24990788720393059801134548703838029302926698998267125850417156350080711181781021192193030344777691291025011026723588592856592831074456000371196301399872260391593922186075976026711098318113395659614068123862901501009129679149355559403668487829006603002388180221719637906875845662040386034715140640626777910995366803968482854325664505230634613020903801374275905216308416131240234632669873705706441127215396001476871745588972526767664926853168984746184966867 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((6230707466805323592709114275946452662432249536182111140199071915850771091221087465139870705201202190767504972997683681292185287713554280467594562080912572345753057355620450639701778744955721599668924284204287639729627412167347744651063550016324478653462353400253549128532534117943004978673782971988034738089950532239149510415079556572915327738445090484702415837365170187390566602259309826965898460415959217404348911844935530129895456298411036427416643041 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((9999999999999999999999770949642380141571817987597512463813582997183965904197899388125396171675484174252147479574931460236886773989560353067239084743935452809400922017986990866010510445030182556319687082265794809481749922962151195636270054258613585711040604717421981905948165866188037765807433207113115568956921005252729214508427488947932988949292419508314727098206314113174977471057213977224650021034693967874612340800010842257702535552540011005570057319992799 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((99966045012661712761333902180970114544259102986978379525207377362629560289843978811585770251168316279871827921806481429201009820407226481718602456608512709718409899157561377026905666277178334749258705129921105093700172706648637751955414833312996719795326606455076418532045251730591490845992317984207075945551849097843454392085863027287128613994319907026015551642007650054718525005499163135244118471156066941315441348849684025332160644599942739352522555364461 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((623204013991602191279725985222347667022145644992000468028853715079651935310043118995320457214631041714070234914979494563754405916267316487499560410173728519723134435071453238140737585821959848627592573926025481570402447096505985008054006419937080603276159861368558283424427747516416763828737534362798440806879395551613257159144699710290859419198138113203190884037405427822527155912474578750759669568562529198011323813081853839642036592195431852092276876112583 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((999999999999999999999987002995557576373209668070245649734174140009209777301901404980399354969381998499589604433520335848221666216489623114094347385625129398763836518066635822710034394182347648793248004109007994874422935878641345293988871688796510694001577033480675519289216775745107826945211182471219516729322568601055613818851701005372561591949699760160302559733520881723887746640199492709658316143571639819109128054015015222228814974857777844489061762508351393657 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((249921771104671320030836728066985754356140882445378210529663712963240001089903623484126357974322308342905165556496393158260741489029736943596344044963209854879479774746378145620534575518695353421760037117148457646769539497776575011372805810870954384315803594462715067173543408725704477818830077922963501901681427227822136563577646134393712205111076068453042409267604006937002140580912718556626463236945497497098760123923608287630119581312339038776199597708687576739 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((62332824470155832007698822448572731467625156583819410187890334642083317943641934735370744441635064985822572932691413053083930538064995096488263974595202461057550222304644291122841863248247199671206829261721186456820658881569055020191839227838891264263483675065740978585795081966215151126125909605913805009229456978476246678330148381414315920936695149402303671528600559650345388268664603752060351016808874622569921069445727081787960699791874410558173286071773899473 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((99999999999999999999999262510976923556145036195309948902866243226542590393441791422802800599027642740862212924371244417035642006122270684363055553702526717474056375544655116488035481629088952635475271497157440653159380650561745856016810546237380406309731485610793970991028027506104653424352118126964409037771950510129698694923102070147855262412001813490776048146959175391658562407604839814824141832934685558255709253168974008754929648118354888229842831590011383130279151 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((24992790737922090168761764024615427585712383321722026088700404620398405913730186980969711780576604746706463651318614986491039580113560588700803697030840446137249221533455897236140361788492472729219277316625697940844437059215113724869584469688353629711944288613961574423771220471762178306511663789894685953557555164633846875851829742832722535256029687394032929588102749312346913138536023696508108304021493253027906338094227490205632006301116018810502500242720689404920661 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((6234440365007941313081963505310027705422856200613848236123892220396743890551567143125198112750967095493902060841399288303352016725905002258364885514968332526638258124984446836278483052097630520959807990229905784560079706845017698038101208075838804897108892408099809869279850198189629948181985108449524041659747116102216198689368918307163767644064898358555113317963484632740690798966225064464418202712688770309364314678854620801293970748973475034439144762337131817818967 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((9999999999999999999999958152660363573346337788830472430595339239403706206695067570704099314390625532044744547967597521955853434353396005442812861283742473529630380917530365274880597334079394439394773330563204654982222736254825145107961880825147676395233093688013282295943903364778896349258012238878341462030293787796289493046021580766399751155044218902907105300002904489248881806694721425612566280026212862632103710152567092178780973023179811422825971792912015912961429865193 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((2499335623243948141592407679236485091682510813375617846028795191164685515147258464398361050825510794452311663795610292996875137518951062424347217444384787047190963812080230349126788760454955752952098727796883560557305487084779604052730391869771420076507321304791009829710466555735186529380043391868511884859120848702361131831745424940052322128644607427739910489537383908571684568076238890652271370999789650605779182338875986618558640212645741765319390205116180175118345850227 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((623551948914737058469323248047621766716530719717666691208174904923483603974495118311527362080388845560627413539135796801392637069995193702564150439394899767200021039193173697124151133616342977311571067965530191143914646537130288994868510076495862371963089838732824725758369238209489169163728392346257816738122020909362809729962920161209953062643518990110703597852512381216363397934200579509635324273376694585817502112547306542857291532698888078161169227693915991725974139073 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((999999999999999999999997625456407010242391245151607497129271334461484501286498219164462707396467264564814939885325386188340991425514749536841530187823399175491816704403425516792549734527667078674577623096147921737656264723307543208861081003661354601694711435138937677318744908627648915545947388470673729579984960400924854703910402557427821079790674113207657876038064809433449300357278577853533848427527396464333460825187114511500568752254292039565414117445206518949170414840646399 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((49987754739133856987317968005016898615285126984267998931005421977088685241047955710249219951079157888377395549462544180395090751592692735090299638356428685142507127609068550871633839276123318972941352172016809147027836650716132260128027048289753916396332159777302869689828750081732653108488448164295001773623709410176663232189915940131674342020482831075880004913422569436349844055712443984515392588197603692969548340646127898116495907107007317664987090885717432684704728827832577 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((12473050112273578133192332941211875759663601742266175638208606781600500660615469194360460320109828223881232618963158054919202401299428020853529348260262990069125323784675089389362180925759974329732841788928217791462294845289806343231701342613234889504132272851391473140610100086446076931513363763303177433105421788645713854599303129736781407627049642243687993046735788169616851747604338613971811420453578034217706140250089078304510010388879405866562407107918670291381189794541307 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((99999999999999999999999865261272902982184006423637664209606243331348015056499768450049107405797741993201294133913018388485032876457983432968998947447663139414932155257963574099359649586303413045231558067344721523159829429194639924300404319390756244163963010964088740624097542350258682414823692663991439437557086608029679030463987972316126851530562221205742130860027911481682213650173058343143071161323187057575673567603592438726076772709165293201060293266193353504732776849302798618457 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((24994357628698098622616368640871700691036410043553310849299179425481895492392900039950146938262726677618138418396474189757786600704315382316654508060196895323103886817041724309061630491060858057632762972713451393295030507039385515054368883159132725971025261706493073080901350228479591422714909973934842100956683329367416524202837766308988860453667590839144205758917496636180275221991803230355782473556073054113066401081114744451171599399937498523260528822630928616117568132791202418499 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((1247492393190125359994603169788159760692133016176431228018453999062246650637374220223281301584107558419106945905664842846888789458023359143289928209089752764374769815941900966025335104214814022836797759509793801527320831434581728728971729971561481907196021102216123526207818562476802398446291397821150118003339344507790842582777804382621040785980553662349111376850204953223892633845477531962820938128775438163280211356894265908436872991234411876979964874664244864867230899937128371389 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((9999999999999999999999992354520408333918067076496471980245687065350680418350966361161136501527181273920221033040626402417806220508855353936959907275022749519821495285802627085119964596475614566425574299415341533388658201300791453224577842295189681562595753131135287409233166845580728416264340792832866248005301765399428077225618069513133985936398692117877425731390563781205093849151769849564967286906961603208016445246530645750633774313836166232107764220803609457919051956759988702007105551 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((2499480021630301976665833804245528611631214240570452374143053022307483018522756142012192040865309211751244901882348904491137731445240993884825819780740372501788643749972163714234727892372945428140903989883443825507413256917372300416903511666738308489391335482324153663207400112204622503367184504872026521392813555739529837783176597605683102179819623017156633744535315554419408264325865985907571052180388238194749643124101855161984006465583313253876876529273381023769711584246988838169988021 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((623833480244022934777263947479737659586843451289184023821818924541272008741271770172825796289858287783165267972887732173104435930449165890768092610490422390497213157837927948495223766713072348093757519816413866050010447532730803958757211116171158908826963141685578314717686185016109487936026088746915776733554759171189368249254121563156050328713761662172785327718274649250054767533645063312556321301620605655991979001549805859158289843324269739278942111968969999849729205181433558911299959 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((999999999999999999999999566172551530091512880121639309575081021149193658978488884231366368506156847026055102077824263952393578370333979348444916018506615876003231107002298468690962151097815797342686362471724724629072632316410809430322220505355948100906370819920009613462117586318787272524087489607715329510564838074059747386013246118383761763989070986844718768276294760636920640282418876573864938760961722250832477152623888431828212255890005580508490865181059211470700765182432038917989190280393 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((249952080873362108961616565071265455476299509091020190544788986658921089355369360057512558397478238196305278623662414017426606777485494381520386625880229380083204205677893670962935834223209839040513699292852133930436334837228213756993557169900802522692598184599221003596047404924512999844600627525731726817814522804680390190185859563264587710904735014012244371220653435808018177045401126472295018734360410182966268360873177160624790931271728538205440759068713579773500801645071841215029350048787 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((12478295705557039950715047286813637072858791244552940001003614357354087487376753209306568535005010346637913937580145609570346697794118184167553555040477447258933741233481500213028028568430648259102526144072573916304960039928261410148155466800068628669910804833202764100934559937275570139867093809722962865821755953797069086454214426935790707493514340095167872686847814475700901352634723530599337435839577973986700173406637529345848399096080055876768548828903499898752809809881707233336221106157 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((99999999999999999999999975383329091471982715356742179343218822383068695791416394757940421848144857970799444657201982209450668817467860990168809869638120904652051342704631422008931265339743361788616052265733076049627468375530098559504773758135412563089730199434721105496680938200486946204834296422810590942417980606836372245924549624495449793774031855006529877068301793602820787891545294313430818220113251005678987251071337301287228248035966586654793297162968842836481973518746741184323460624080339999 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((4999116792993111702693347063994382573076662863542118273184461547402620135178047089487567356063715619247360662403369361560122036274035630745138646041381978496758020595856695287672658303395388541041317685767826687898180461046416972856472025792076274301427294295557789931879311446998912371019750199476412555558546562210271440598148009910072380381063865631302977155760070411186544899877961925628433778278792779631064382952184791925870671459215543222047549835871285154260156815385197965466084317047173089 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((6239905125799235964164209572922739248620897166992594287320776626419760688659339658857062776577063492626772635539181487865997927300222831382886805264902327962314652732897955156917372174673188599187709360979043643792585139813948819745531441602311096465521685691042242030480475488954807201743221316222106745603082987610591738819327394247035498699945722991529463588609437341732984970453059517441733235424241503222388558157982741183965240351715627810318281257915902013283154776223278939599336516740693767 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_open_source_model__apps__self_rec__none_sft
