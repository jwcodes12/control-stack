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

namespace LasrTest_open_source_model__apps__self_rec__paraphrased_base
open PL_TMCERTF1

def cat : Fin 10 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((9851 : ℚ) / 25000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((9851 : ℚ) / 25000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((9851 : ℚ) / 25000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((377 : ℚ) / 6250)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((377 : ℚ) / 6250)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((377 : ℚ) / 6250)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((9851 : ℚ) / 25000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((9851 : ℚ) / 25000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((9851 : ℚ) / 25000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((8219 : ℚ) / 50000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((8219 : ℚ) / 50000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((8219 : ℚ) / 50000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((377 : ℚ) / 6250)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((377 : ℚ) / 6250)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((377 : ℚ) / 6250)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((9851 : ℚ) / 25000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((9851 : ℚ) / 25000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((9851 : ℚ) / 25000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((377 : ℚ) / 6250)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((377 : ℚ) / 6250)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((377 : ℚ) / 6250)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((9851 : ℚ) / 25000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((9851 : ℚ) / 25000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((9851 : ℚ) / 25000)
  | 8, 0, 0 => ((0 : ℚ) / 1)
  | 8, 0, 1 => ((8219 : ℚ) / 50000)
  | 8, 1, 0 => ((0 : ℚ) / 1)
  | 8, 1, 1 => ((8219 : ℚ) / 50000)
  | 8, 2, 0 => ((0 : ℚ) / 1)
  | 8, 2, 1 => ((8219 : ℚ) / 50000)
  | 9, 0, 0 => ((0 : ℚ) / 1)
  | 9, 0, 1 => ((377 : ℚ) / 6250)
  | 9, 1, 0 => ((0 : ℚ) / 1)
  | 9, 1, 1 => ((377 : ℚ) / 6250)
  | 9, 2, 0 => ((0 : ℚ) / 1)
  | 9, 2, 1 => ((377 : ℚ) / 6250)
  | _, _, _ => 0

def kernel : Fin 10 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((15149 : ℚ) / 25000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((2221 : ℚ) / 100000)
  | 0, 1, 0, 1 => ((97779 : ℚ) / 100000)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((3373 : ℚ) / 20000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((2221 : ℚ) / 100000)
  | 0, 2, 0, 2 => ((97779 : ℚ) / 100000)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((3373 : ℚ) / 20000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((5873 : ℚ) / 6250)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((2221 : ℚ) / 100000)
  | 1, 1, 0, 1 => ((97779 : ℚ) / 100000)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((50237 : ℚ) / 100000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((2221 : ℚ) / 100000)
  | 1, 2, 0, 2 => ((97779 : ℚ) / 100000)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((50237 : ℚ) / 100000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((15149 : ℚ) / 25000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((2221 : ℚ) / 100000)
  | 2, 1, 0, 1 => ((97779 : ℚ) / 100000)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((0 : ℚ) / 1)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((2221 : ℚ) / 100000)
  | 2, 2, 0, 2 => ((97779 : ℚ) / 100000)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((0 : ℚ) / 1)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((41781 : ℚ) / 50000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((2221 : ℚ) / 100000)
  | 3, 1, 0, 1 => ((97779 : ℚ) / 100000)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((0 : ℚ) / 1)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((2221 : ℚ) / 100000)
  | 3, 2, 0, 2 => ((97779 : ℚ) / 100000)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((0 : ℚ) / 1)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((5873 : ℚ) / 6250)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((2221 : ℚ) / 100000)
  | 4, 1, 0, 1 => ((97779 : ℚ) / 100000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((5203 : ℚ) / 50000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((2221 : ℚ) / 100000)
  | 4, 2, 0, 2 => ((97779 : ℚ) / 100000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((5203 : ℚ) / 50000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((15149 : ℚ) / 25000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((9229 : ℚ) / 100000)
  | 5, 1, 0, 1 => ((90771 : ℚ) / 100000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((3373 : ℚ) / 20000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((9229 : ℚ) / 100000)
  | 5, 2, 0, 2 => ((90771 : ℚ) / 100000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((3373 : ℚ) / 20000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((5873 : ℚ) / 6250)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((9229 : ℚ) / 100000)
  | 6, 1, 0, 1 => ((90771 : ℚ) / 100000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((50237 : ℚ) / 100000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((9229 : ℚ) / 100000)
  | 6, 2, 0, 2 => ((90771 : ℚ) / 100000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((50237 : ℚ) / 100000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((15149 : ℚ) / 25000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((9229 : ℚ) / 100000)
  | 7, 1, 0, 1 => ((90771 : ℚ) / 100000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((0 : ℚ) / 1)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((9229 : ℚ) / 100000)
  | 7, 2, 0, 2 => ((90771 : ℚ) / 100000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((0 : ℚ) / 1)
  | 8, 0, 0, 0 => ((1 : ℚ) / 1)
  | 8, 0, 0, 1 => ((0 : ℚ) / 1)
  | 8, 0, 0, 2 => ((0 : ℚ) / 1)
  | 8, 0, 1, 0 => ((41781 : ℚ) / 50000)
  | 8, 0, 1, 1 => ((0 : ℚ) / 1)
  | 8, 0, 1, 2 => ((0 : ℚ) / 1)
  | 8, 1, 0, 0 => ((9229 : ℚ) / 100000)
  | 8, 1, 0, 1 => ((90771 : ℚ) / 100000)
  | 8, 1, 0, 2 => ((0 : ℚ) / 1)
  | 8, 1, 1, 0 => ((0 : ℚ) / 1)
  | 8, 1, 1, 1 => ((0 : ℚ) / 1)
  | 8, 1, 1, 2 => ((0 : ℚ) / 1)
  | 8, 2, 0, 0 => ((0 : ℚ) / 1)
  | 8, 2, 0, 1 => ((9229 : ℚ) / 100000)
  | 8, 2, 0, 2 => ((90771 : ℚ) / 100000)
  | 8, 2, 1, 0 => ((0 : ℚ) / 1)
  | 8, 2, 1, 1 => ((0 : ℚ) / 1)
  | 8, 2, 1, 2 => ((0 : ℚ) / 1)
  | 9, 0, 0, 0 => ((1 : ℚ) / 1)
  | 9, 0, 0, 1 => ((0 : ℚ) / 1)
  | 9, 0, 0, 2 => ((0 : ℚ) / 1)
  | 9, 0, 1, 0 => ((5873 : ℚ) / 6250)
  | 9, 0, 1, 1 => ((0 : ℚ) / 1)
  | 9, 0, 1, 2 => ((0 : ℚ) / 1)
  | 9, 1, 0, 0 => ((9229 : ℚ) / 100000)
  | 9, 1, 0, 1 => ((90771 : ℚ) / 100000)
  | 9, 1, 0, 2 => ((0 : ℚ) / 1)
  | 9, 1, 1, 0 => ((0 : ℚ) / 1)
  | 9, 1, 1, 1 => ((5203 : ℚ) / 50000)
  | 9, 1, 1, 2 => ((0 : ℚ) / 1)
  | 9, 2, 0, 0 => ((0 : ℚ) / 1)
  | 9, 2, 0, 1 => ((9229 : ℚ) / 100000)
  | 9, 2, 0, 2 => ((90771 : ℚ) / 100000)
  | 9, 2, 1, 0 => ((0 : ℚ) / 1)
  | 9, 2, 1, 1 => ((0 : ℚ) / 1)
  | 9, 2, 1, 2 => ((5203 : ℚ) / 50000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((9851 : ℚ) / 25000)
  | 1, 1 => ((9851 : ℚ) / 25000)
  | 1, 2 => ((9851 : ℚ) / 25000)
  | 2, 0 => ((395507799 : ℚ) / 625000000)
  | 2, 1 => ((230247423 : ℚ) / 500000000)
  | 2, 2 => ((230247423 : ℚ) / 500000000)
  | 3, 0 => ((12148422647051 : ℚ) / 15625000000000)
  | 3, 1 => ((119099510073549 : ℚ) / 250000000000000)
  | 3, 2 => ((4717024557779 : ℚ) / 10000000000000)
  | 4, 0 => ((337958329680175599 : ℚ) / 390625000000000000)
  | 4, 1 => ((12604666310640255143 : ℚ) / 25000000000000000000)
  | 4, 2 => ((94718523833388567 : ℚ) / 200000000000000000)
  | 5, 0 => ((8967777611324980149251 : ℚ) / 9765625000000000000000)
  | 5, 1 => ((1343755280858700398188197 : ℚ) / 2500000000000000000000000)
  | 5, 2 => ((297760089060240779152343 : ℚ) / 625000000000000000000000)
  | 6, 0 => ((232054034908962124281003399 : ℚ) / 244140625000000000000000000)
  | 6, 1 => ((143161497210004163744084824511 : ℚ) / 250000000000000000000000000000)
  | 6, 2 => ((4820537666535736361305127037 : ℚ) / 10000000000000000000000000000)
  | 7, 0 => ((5920415871710867220732920491451 : ℚ) / 6103515625000000000000000000000)
  | 7, 1 => ((3037587598388058973376689820784777 : ℚ) / 5000000000000000000000000000000000)
  | 7, 2 => ((6130181535489505779247425501150097 : ℚ) / 12500000000000000000000000000000000)
  | 8, 0 => ((149814112462422927526883012524991199 : ℚ) / 152587890625000000000000000000000000)
  | 8, 1 => ((1602427785522172760666147887303377804119 : ℚ) / 2500000000000000000000000000000000000000)
  | 8, 2 => ((1253054896043452839502603472109904444239 : ℚ) / 2500000000000000000000000000000000000000)
  | 9, 0 => ((3772677300240119929104750756741091673651 : ℚ) / 3814697265625000000000000000000000000000)
  | 9, 1 => ((168107055248747992088844474715780974276641013 : ℚ) / 250000000000000000000000000000000000000000000)
  | 9, 2 => ((3213246300033609752566967465470275251555813 : ℚ) / 6250000000000000000000000000000000000000000)
  | 10, 0 => ((94730871185009451806007869213870797764138999 : ℚ) / 95367431640625000000000000000000000000000000)
  | 10, 1 => ((17541080503037547345386084573311189049503194568367 : ℚ) / 25000000000000000000000000000000000000000000000000)
  | 10, 2 => ((13218243208904726852998193809480036805958027981897 : ℚ) / 25000000000000000000000000000000000000000000000000)
  | 11, 0 => ((2374542536673505060409213210720928715328941695851 : ℚ) / 2384185791015625000000000000000000000000000000000)
  | 11, 1 => ((1821406370459095663657287039661427475621876439859577981 : ℚ) / 2500000000000000000000000000000000000000000000000000000)
  | 11, 2 => ((136171978627802448562406722480740138465148114061623163 : ℚ) / 250000000000000000000000000000000000000000000000000000)
  | 12, 0 => ((59458559115361850035139170929211349108518137750446799 : ℚ) / 59604644775390625000000000000000000000000000000000000)
  | 12, 1 => ((37662011382295458574863535671127658876949335951141559843931 : ℚ) / 50000000000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((140414426113209554464475308152027945258713892278340006473379 : ℚ) / 250000000000000000000000000000000000000000000000000000000000)
  | 13, 0 => ((1487903067720989713057323300406622727644941268781518558051 : ℚ) / 1490116119384765625000000000000000000000000000000000000000)
  | 13, 1 => ((19394687312261875268155149888312699672455304580824390992944101189 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((3620867846989542101057991512452978609488886455865657001648320301 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((37219377464964599334980390677859927701093215280771224635914599 : ℚ) / 37252902984619140625000000000000000000000000000000000000000000)
  | 14, 1 => ((1990857499903597576235668338993766086547391323241933642675723011188383 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((298734550112243150214068733725343038144950571183590902252071967608313 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((930814696518231869622492938378900044743861118288403282009470260251 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000)
  | 15, 1 => ((203763862170063785206862179015882296395379364789345939567951389203568905037 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((76977896553901208485742574122744515895011208003364227264934185264564241661 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((23275370520091773450333020523501956777824752080951021319161464972542399 : ℚ) / 23283064365386962890625000000000000000000000000000000000000000000000000)
  | 16, 1 => ((20801841320501322964324713644092780399660364860299325152850141162806417546032951 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((3171051596031170372918561888305772523609016176197524444480661046451851796841547 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((581960055072297247434641802910531143227267169274327021963977032869044802451 : ℚ) / 582076609134674072265625000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((84754107834252040074055780612595527465645322410392547051716998606369964668336256477 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((50974306739488548101209584001198395594094860748244685268294511625904550774620575577 : ℚ) / 78125000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((14550149550875905287276060547291636288749870347336780055732288070933159712330199 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((215398258056139256089827266393407918289138216904967813026573744734474477033609643271439759 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((167618533035661481936323164761770049201601724372463206866134960176894133405720579278051569 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((363771132460860946344161838105920998138271785891804881064288431986566436482090184651 : ℚ) / 363797880709171295166015625000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((21858885328528171792455232391988523393804444173231995367608654583635553830644713068040932372253 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((1720281238578013757129500583013539081396904672682880569686818556037132233191384609940013650551 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((9094541808515628904848127607341597200796679284474952143242905456164494946267184207277999 : ℚ) / 9094947017729282379150390625000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((2214860916094414560253728805974878577518585470377095664754395560635141293672260029772722760954423207 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((1763252135766635364956588313952881641976205555715735607158082344652837825693171781193599555605171147 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((227367536928854422996554783170492855994868894480511050017986774755435933941001573556054406851 : ℚ) / 227373675443232059478759765625000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((224116612260540532749212253682733928831354836943242481290984411423602595810972083987719228306153934664421 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((9024655550515430534452807049807958695787058990199162634368230456779223063764809178274834181134268098087 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((5684248893726494671900070861421671275466268882485261896722481650770098963272232837800668209385799 : ℚ) / 5684341886080801486968994140625000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((4530095344316969627941891718153429112923358468947958083499650395837759940292929079396451495114429539887145139 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((18451912394069251477598794863600315804690316422136548689519268068874565491159371241546360227152267653647042949 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((142107138410844643232745734758973773152038507300769232473448874527516229194611055259842322703985469051 : ℚ) / 142108547152020037174224853515625000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((2286727647975187317752562357461018912335740670292835722261139834952399399540416940432810682754998924928197177294829 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((941969894792783294677249400949027126161696544251680093429722424697873308321422249667576959210446919153644023981417 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((3552692337780434886536154167846115564480231347099353102740277000217343356069162876131351346642675870653599 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((230640826613554476659586288326868030857026891373430206004769830210142891511665269575636297027650522126457620478727417623 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((38422261620726893727567121748819205215918652936534217680433345592255402039529229198481133224025767935030635030177676371 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((88817518674899542751218425288261351561311024677208100153412456276292534501091748410513841550289896764531371251 : ℚ) / 88817841970012523233890533447265625000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((23242734612973280773448775608928924253213728483768592520760201361231599615151418514938123974666461149416931678145581195597877 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((2445839967086437327227037237034875680006282676124515592071387103347810529801462136348775263082300196857300780127433080825359 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((2220441151652646539515263569680884886677300712835025509224045300129555605157038896670874185645341646085885743081399 : ℚ) / 2220446049250313080847263336181640625000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((2340490423719956170555665483974936185435572941968855400929733322459479805900681075833582623562298160303162969154977361741289697391 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((398119582992470885859192385287589328946342355706537515767478185685335861930620119620496276280828907859888251072236678858192420229 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((55511077037550776586543118941821066945149428498737801439235062251662637862523982245667073038341280596555083121940113451 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((47104221072177688742504120850742652499403808891892581211808228541879539471333669959232680525101994624273830228934312310427271511727193 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((101144474729779674699840998388151770472163556265310575356914660398598323372589490019614235752146026849093736616360631977347641750127167 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((1387777656820977568495201486967780888073943692327378954002971958050437300979375807039610489457832059757212954214270778669199 : ℚ) / 1387778780781445675529539585113525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((23685733170946668017614332651577529651332987466425012121307026720961104980991173997253501949332435596609488419025106047043946917420702891399 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((20535594512769301151381387186039368414642505092833395631463891984147368170611333397409599629746925548175291028721515691996312022510237472499 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((34694452492659010534775301779028251296479047995067463774191022192506074672536564100843059304796697873262019043391988026059695651 : ℚ) / 34694469519536141888238489627838134765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((2380702498796082932233635616518354109022435691004520938175019706534569930373452230584926797642439613940961400075136710745028168621997676494799493 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((20826320809532490339466025723053885315176669711092165917311514889007907940841288886369193374821472270545283105872634045863658246961524326009281 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((867361480048241884332348407974332444466532973077277008715219795194274525214256409563671505408365176082046326488345226606778329416999 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((239171235195013325044230872147439728790917463544621774926891757136713556202768540779143557267407945062133367283696681006575361702372092973873110654047 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((211014099981596417441951285195580312466558207626835422986445608670621227057227053986530094598034061144027722041609923201174877241706869015989349085997 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((21684039542174579649276680065498998840627804884147669405026864677398064782470770348480059635431324052466919799971941837866084912338117851 : ℚ) / 21684043449710088680149056017398834228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((24017061503745568672133633625748253615675548093844011864046607286187971762247390301847394475319739324224408106539354191974937637834899070338191224536606861 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((427225443980885327689131336550734835998266646710975850814058767425113776228138155605240782135581153781659384082004220158070575905163325070124882882224669 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((542101027047496790695040777139640249421778038064953043816751972997903283389649700009124423417149128070821368049774946901833320337010147324799 : ℚ) / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((482155529635817967008203064502297287550475728668528614697040704883906279982000391799947647999968947002673100772507662988907427223074173243640257504384834073547 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((2160637499397514957258628332234368222539002722788185833205432557541478920493997591217915155374167719719017260040631953236147911733957292517166454016369116210119 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((13552526259319880971942881503573308038118201045520973660779975638945236840069803305438225890346392141144872904586040670615872969785366721823380051 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((241901195383440082772051650585554178227901890380355282428209147226712263562960543734980949591925742670130963774889558459885913612603593168416250848223477657800704469 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((13648268335803540642057280172294021641381532415600979324442828875466589898870628964503122549089196571628329121643473070988844707825737195212718492503729950989533629 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((338813165316870679086555431164754490960144766310472229987155850954381392890217450274083684012857494546203679631573930119159859619278520468902384392599 : ℚ) / 338813178901720135627329000271856784820556640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((24264863253483218162570423314705715848626587918658361157474907497528047286978867804770009326988786063996450257357260418877761236951400669251216257918375473515742806742863 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((4410875514788267905165233347912577945084559161732912561934788507486994557557747329184149234847578014231007933577930168210788372863103683299554460721430323480835602830349 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((8470329266746118973547046208392926970822536531634218812075423986107923720893904154202093729110778184880439542738713467375152713372450306583402221163482251 : ℚ) / 8470329472543003390683225006796419620513916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((2433270893130914355522715310735300194509660554015584116158636553391636125405700191139385353631646504687928590539931373100398295940184553882857935310261663269959944970679066717 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((1112919164865312975260564708944141057416663689124794522959624679680098131665949692528547233530263513116718672559580826449565107710804199480219382307526723354235716442998964011 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((211758233695958082731884652552895980362673192587648655784130597965548936447821754032007517902299178722753778632948770317266188454879249694431960248405592620399 : ℚ) / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((243942931679811974085608585540880337634758520690673770165102457191983644022452422411322591830049911422706626800982135795423548801136347866941861155293130297170705067500122824617831 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((44899645620136771348374515598782668268133123340820654619032848069947156964053809229008581859643512858000046843180889807530104931453355845964576597570284260298624153325863006243231 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((5293955873110597155345831840072609448556200861258336361473794428580100838248051751830881888701930258470996992510540921536265488902965753620949765803096322606424451 : ℚ) / 5293955920339377119177015629247762262821197509765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((4890038763507931054447188090800925736954526123835153292593891541149172081512388683231625929060062586302489469135896768585230824183365457965919260746669020334985250738796029199015479201 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((5657319494850039767288149353260573135716186270325596606743720959552670993650963748516446529977009290171942679689531718713134926387612542983564837073115415617605125543917047061729891951 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((132348897293015640307346787508979666587229503515903709414966511798559947598619735988486029731945541485577133439542184420352885891391028201603768002151106191164724008199 : ℚ) / 132348898008484427979425390731194056570529937744140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((2450093540953533342840015016570237458001341817289747878021079713014723776996175989806237725901973582455403124172423702083841024921996693776216535882937925005757766748442969849281394396959039 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((2279733030210205317373515914229270654540142383759272067049682306044550540760155697454068850386649029157718012465669890943605357994461311614481999591010079507460433798329319882749705376867029 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((3308722439373474035041316008066525620406230165479954590802327687236384646171490380489574864409243007965007994475624551783925868368682686226095481464587107689954404000206651 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((245469940681164870921662027339793413610953403735160867911229054610740922782239197220481869301314754344904658666350168071917643315100387918681858339314533837836867721307653169237083581411896722733 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((22954556017467070608438191163843184808315764794797996796442325727338278287323780102352505159079583321815613714250862001737377076952035520341884799453921003684982946562953086381609149565313206029 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((82718061091108260657473884308524612905441241194794064517939462133943991004851907774036569620935622327661906108311236334974692979917174013639120448707030094395119266199130555999 : ℚ) / 82718061255302767487140869206996285356581211090087890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((24588801978011980180685849030367506353551853057681697023004955261188936283866822064531220438708990343485996248691505556001153904415902745754566253626749965589139069245468869874113627034511839604060887 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((23101522125161505255721449351651050696571791824957889322051396430964756560543953987854219629729962444894375819394395648732762476675193642271047121925852467044292322624606477138339485524780845098686447 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((2067951528895186603215896575947959767952210873308391093929139911867117519732501550868879993187553742641750215634806919238531623952765269132619035677462798899991661763650628792828851 : ℚ) / 2067951531382569187178521730174907133914530277252197265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((2462675143888138684270999487565353466188951865714823409674843289236513208044158691222019044229108860950246108767496105552655081273215745732818236419507608929281197267951100353194206246226666770854214205301 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((58096957956952688966366034494999480972886204190314923836931000938515365268023553706626850085976592324138491172035564805186405803853459213578852756476320742962490572175614668409810202611784796453968635169 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((51698788246882870915013234792988652700900080280960211945604415524874963306427665994112663016798251647279874016651690019544515571260441062090045771477883940535973684057543375582564263799 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((9864479418324722810928382812543342862706947267696098237309513103033138543965424663795211689947233246596423786663158315034836956077931307799913635940929782216704534443450262754724032253921592468921114782397831 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((233668787731365733123777506956564562635051982391045143311971684163962909226790180301457046125357696151884820624888831675408463393933801968398821246240120129186265438664029467808704605497398617985141022217734889 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((1292469706543270838063925932977810354170736260206551132355758165786330819129072712144812732041476714204642811478256452106079866389024421649602103392118463815179465339787724596700266032291051 : ℚ) / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((24692466530337165091487201475394988867828076528083399463506135994909631251084984871640107078147267563411414995994788881127467322919320083731195003098391513811319477194895361409495101431984256515050590978850579130109 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((11743165772478385315964929604189192348472181950978370484687109576972199061990697030848853875503959414111848465559820671122457193710922919732832238497466484124157826921218840348273814043695214687760529967947376583447 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((32311742669205065590140174936151480415452507206626165143852302328497125578986322516281768077696330743486133951084106992955003895927330963569822264287202608336153720432444239915412330123177131599 : ℚ) / 32311742677852643549664402033982923967414535582065582275390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((2472084879323332321124338245789522778023011486746839093201128121301610852241815706953370755747024801126190299035206790451711563196535635452850294248347909733491536299900190755079877399411446969556058106028421135221964103 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((471952914855150544732048126524026941917504434804439405635953075183941589785635689150945835698192186459883428626539374172167703956778154749378605784980423148366505533992720000990911008047259873644564807116982926900782247 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((807793566815313930232777534544524560816690621692107826759091574849402955396063799799152504609021714433071443224973136836275354019403136767119237481686832313684392710831097790478581389036010366593251 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((247466116574883314752203068023024627463136952731189025539849890493069612059330636250969169690613624280259937097817107341583766487771682408790795268145790805343676860201904486271200248399912661356048332023259484314737000111557 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((59253265380714846117755055033488438360585837067338856109014673592275094196874850714768795241398076668836000942273487783497004824011094200843395623540073201733068439410511199132090526019114343508746705198653646236379508354693 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((20194839171673350519289947481734147171887060978486942742445304439268605371294970503157361292322069951946599293415118049932735338039938118885089328610073822720004865176380300427960029462506521043521159399 : ℚ) / 20194839173657902218540251271239327479634084738790988922119140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((24769996867244560130770100108010020240015024225956604939680822410327950411327559460541210103909852912867657570560096798084620346839236090475244222061123424251137139705566232303493939005583494673153941374422355204695142469739594271 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((4759555479472213459933411703312722088114447800502760949638551677187629950214734147776261543700490481542033905120036224407740616087377796753950741221428288344113242999545884945894572728321381250036951753318124454166065037096982553 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((504870979311383581771563429673769210508792455524928727477099571247355102769747508152330866217387037702039032695945623338431007635967022562990218239114008340385353702556985171183166486327511287288302043735451 : ℚ) / 504870979341447555463506281780983186990852118469774723052978515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((495824477122796513285474883176862783380226778968827134656357332679799499434090214234077702613627456334572465502686084568360199105575555666888807870874519445420895751474379372539615884486026691546533347364425160476254646523235511898409 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((1194375176611830742652477911251909980048140682539267038893259590737454222700425106450165005482585070016557704863476586989049039247658079912380171291226721944415630281950784185023963434347415279787029231473370645164835458632438866059437 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((12621774483080749749128414777952395145044581127792896089345472762248057451858905000999660292327196234148189306310880247953891334677264424806738816104338112348497723240035768358253789101375468491130487660548347199 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((248104918063192894117896858671795402009054691776661338274618184331362655428478011418004526552388827639524212761865752941069019192083862920733644385715399564244876295866579248397230700477297259038602974780844595875769130639005029257158442679 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((239709078809296421788174383448690574736980120505060144903477741738168262398866667611007371012425297753504765276946715927572922070825127159701905095753386255042049587097694498663460944787906166404511642054270052694691329494864919318714395159 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((315544362081505274671321365016812468428452464981078352777366850810842697338210551860143853768464695751110919801303524876253499829025878771397286325164618063967392009363301854859186651096736972172135757569646911717651 : ℚ) / 315544362088404722164691426113114491869282574043609201908111572265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((24827981517430828292036782815269427007946196480461811803283588484176806275820757530984651455384020419668160811028927781348990359718122097375891647300281074473314857417106133032431692853059685799506359213715856687450574312217800448670576150941973 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((37575614189693519878044448544848581132174981669955659224953170810170964520557734145461740390188833113544609388332795914616949511585327481732425674191246947398184135007808573783811024303200010991204989242438377700761406212884001572645843172597 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((7888609052105598324040222597279982943626929028901950214221137521322127896976551650129319240738471675933579324069947098350364268909913037507897490539918799051042021549844659799261818577464468391435684591422581065610694999 : ℚ) / 7888609052210118054117285652827862296732064351090230047702789306640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((2484385710313668861575777291896970397666242430579856928539535786630737956519102517692775885493606458224769676105878775375538656853487880227399736378571972938865691334442533403430252420671437739700182191420801491766869990388173327067449248930455443727 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((2412034129816478229731189957475369898943474814462850952977767769390886062236699266368790235934750689604834408949533953992114711464150075777055870971023047100173788975130499414351710805037379486760551759439622990025002056471262052661187678893716932497 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((197215226303669581961994713092201733098111913781425499995156189770225712386297780947809057177947107418717793180335628592909668309716272605207139084189229886824235584458596751299017289630009231661859185875460680562936418539851 : ℚ) / 197215226305252951352932141320696557418301608777255751192569732666015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((248582675310576338302274135962576255236521848562267369075451907449365000438727766399722314976945982612448629683957311918849473429874064010429451645202287110383281036162200053670129419755457483841912606765116169353364805637214298235784317381819915596259741 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((24187114571805639531441269225691394089705990377542894344623633397019519935600222624334808715325374884907682347553930175575909073841320617497781063094857374658266646438714070312037694107442467229243502520071659539507590480924537941761415591924075296984167 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((4930380657607337320919992432783945841830986529939561304424625555322069238815025083578359407188720730286155848888904437553988565223891813696282949986382643555500344868963282185428812920605009850445504806827353849847923804460202799 : ℚ) / 4930380657631323783823303533017413935457540219431393779814243316650390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((4974269604119560146431823151133013841602556381264367880006592245734221384833333209531149888977059582088568674898871657508243543961961353453445684650712972638440341804688801672636204787160431055147471488940040032184774305944359797532627983786450348388248251963 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((24249055278415006085276242489650951588744884665980626174755663924658778029792696634437986463910230510309840747051419991371070215700812874461164258015404895292782518321626093058261359733189719047033631120329503207568638746665863093534308012062218388863379377259 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((123259516440419723669060328467998540236089843643673074325678763449897024945683814991128566659501930343104974954818013324505372774576737085684990409343710667222274724419924761827061086934245294224398952318627583471346197713767612202051 : ℚ) / 123259516440783094595582588325435348386438505485784844495356082916259765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((2488322131176560485599380046405320405443422978332839622434343221160793373469835294785370131282958732729649512723772857759627581642854054279579807139272096994253173835194552029209414971187075873439256338071062498810315986533257438333148218274360771274215785357371749 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((607662166889776405080926571584284862595677972557292918582912642321151896586361756789596345235610487016702888988453219168115328221375798020705897995630866968255497885787421711543809888561220519664517450570141870734844829505352385430086447718681344175473381260002331 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((3081487911014072658723678993555573502991330758898469906083460360310564982074039113300606656324794742767697265590538083852931892162062990111041919711147872897750239800237440216918148405966881962205419728674889262007423549165865557248870599 : ℚ) / 3081487911019577364889564708135883709660962637144621112383902072906494140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((248939988168959553757918199911416239483662917553236985226424201349665635557414947100559709710621048606889648463461730865310747023150197271677659494461778329546655356693330438511735186907760955870668336187152327535178751813512804773741528099996687437370138105914025881343 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((9743885406065442119359992870615327482901059666201036757048192296505043090556627281510719214205472968493379483936449933307983551316476412619848892317359195418481669427530029815669854413897908575913702030674689071816432252633471936394965307597750909067892585778794808813 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((77037197775406043328532115013219973420685812605064583185352160318546622692736493527390890236664315558187845876431061432288065234363092237192174041704179126528018382733796981846093030201992294845449903469695897430150459346313697326763140704251 : ℚ) / 77037197775489434122239117703397092741524065928615527809597551822662353515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((24903781666080506030558673164045316236813895062794726510209565263972975859544677795145045800583184910274237066313844698288809835347836699566164968018255984392873139358984778520986704443105354010589828796568204662455341910260862318773418903288373220237173454250055195219532397 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((12204511352830241943521237444224028873977513620058590911752602763953772904941136460520651452867723164085399147039587868281713628845175090934110357293931520193330536338540477513489506457534951172668482125165266937134199500290865851859772730616877811267265476086327567314017561 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((1925929944385972565922110558831434137946722948616914935127245359670709631654687015446444596195227716390987677182054149637731900235366484301224244557776609587772950480034290477986463314529981274613720587662423150169349308637306200803134818528698399 : ℚ) / 1925929944387235853055977942584927318538101648215388195239938795566558837890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((2491266165611543858996095749589698712936908598869778879377577494765464014975283975172519939463862859338676420928831220779039396661243137842682241029048761856391498728190914599185718978459386532644463967223248973442208466631998533480676658124853009913023741104369676600479703426711 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((97818736040470590922670339309211714935567248605888369690564603551796097396662465067489349350003776487652498633474853340164251263129438450346255958947816020755977537244615435588963931064769176718092604477211234045240687846864074672731469764803905122506031314757513544880097622039 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((48148248609661758789608491568141514770673745285167433463551277028777751321997400471998189187761504675607072321630938312862000556665566870679246080805757858645172426822039466451016932751814686329123253182498048301915472676546551635966689365891252046451 : ℚ) / 48148248609680896326399448564623182963452541205384704880998469889163970947265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((49841444223742062707476648118790688172546485331090685623939423839249436363775792306451774881466593991740585557879023333376370452050504657072098844875794794087424946667217620699576619823869589352819609546533354940970992233509753983987676719565627643482712766743648620286763707936344817 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((30621188458833479811339712738609342979013012192387064925916456678024069539252263902861759970942726277231783565653853893758873234615583669819951799212299527959207258449156080429003890639900718975840669122315860989238962981529898439806983866044956278170271289806073036862951339272208443 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((1203706215241732493615140006575878782633907550739246177322054222587108432578452291625300568005399034330771538600387084501546446432926672523919898878126425800615717093927075877266455514257240683199888162461662933725717495577003710733259377203886577251686199 : ℚ) / 1203706215242022408159986214115579574086313530134617622024961747229099273681640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((24928038668165536804932551515882098071793741706140403950193919311017686987453382052610951251684967647256527751996652260546019052313076370512464953853238163278335454059776853381789575829927454923488007164315062099239698291553273052742828851416337828378896450101089203663441743988035872142319 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((24536060624478767851277446447412065678106078603324509851239586226029547770186171909794535666484813635033719128872055306041746073544199699746406759327190674392245840617465529720150860379967887497934127897738645806584785706986910887828869202262489698214859342597282110615828359439343692216889 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((30092655381046168288559780154870562062445340071504958534819697589925962590168815562706678304713789971076858038257263943113927117012406162064862548104737224453527498255901272464709534585482939109795105773131731783010894340496029213898146305261677758785794228651 : ℚ) / 30092655381050560203999655352889489352157838253365440550624043680727481842041015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((2493467997947998370839535996164656238322929748117259208076004947741949768224202996641403817291975736369385060353016988879455467764087355959716104772377172392341660967982128339552368534551952370704641076437482086470738334239806935151296128396364491091514446222185989385151329413281431176350257213 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((245722362781306197580102760941811649677195130310833887176320816264431031385477627338750626608429358488217621367002243589729454267547793276914062700999995971415430510420564417808834974288446559756384954152509832662339075894165404520287785382828983421476983272488084672331925986993424935022069347 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((752316384526197471972992714447448504292091321377131571708181053088634830904413431881318469638109204271843322421559291474232881895620940949120602741238664213246488071078648376567884739435481044574286057357172604780832038364174346561343018378409156367845996769833999 : ℚ) / 752316384526264005099991383822237233803945956334136013765601092018187046051025390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((249407083641734392770609049662913197562990948800649728049307526797163412301044352413157113249016968454285134716642248294279328538739079383771369225537256054709226024362676372037960293443780300218381093698995823543132238575962868496445852493325300070854629238421481491927127421443941493383245765602567 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((246056862073281525569913154843095464951969110379821212960151617794097145909853066567660847108525057064293071813039600319201817445190569643539883785268975267222421617687357590134986403716745795185701319228216222381970246666592057541621737638817744429792459310454713833957974156808976076095419090784147 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((18807909613155592217158881753197256381723563043389740051412171130710889644019610202616968496547716335514154491364201706543153927836761634438228010927024524166471047788770444256626885917708102344255859482903807789824824549178877176057785385414520309816499005066215250851 : ℚ) / 18807909613156600127499784595555930845098648908353400344140027300454676151275634765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((24946180389243668518309041294797375532188960426051697616660054543130718109726191117630091235123307372039323578873035883467400063908889097675017056018700043123782475201218963475879786288342886684571658839788512848854437104245860813939292794798269447445343952802473431952041392563311875272004550391391570181 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((1231830270109170203419326894880082217473201579238397383088649083179950658175480551691708487553155277832377196492065443504108604720070808037329237882756674505497893981897113802584059319998269048275836678070622358865669434499539448423212275993701233699530434865533834105559736558010685172284563073015694909 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((470197740328899734353740277730006711681797046940500518828966389395918281983469353035616330754201354766703926389676291652422238852799102000104716137533494516597869902952083460043640694767360042413132015306509784208056267095510810340099390803644568173410143427748094835141799 : ℚ) / 470197740328915003187494614888898271127466222708835008603500682511366903781890869140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((499022948022404934118116712448094628736652219630528958896432340760172926291568722073709545704917901380095448089449933719947174476710589223633608006069834574893814789536963205257228879566789668692809791352101701344565067252140712245293275105967102144635728783929713486269079395409420514123945179458996586221971 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((2466517607773919587446988573612883838031771526753002494510950961965099421299593920976769534482702158219005127365044695614749478370726083809570977447110704728760375156247708153406047518366374096832831261535377427813991204814238954908313763287678322413274621404001460415400646954110563372354171489576305652897229 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((11754943508222643772124820918602408544144213224006376029493097056378241422922984181040848669595396323360797780877206142242544496381053596199586344767494908431941131159821112336201112885030737282516536899878316720967844390229893265842165671284411563258990262786955888657563113051 : ℚ) / 11754943508222875079687365372222456778186655567720875215087517062784172594547271728515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((249556560074707842135854106550977992539603069854490515312630719475837398883133426302364616330522862753815092681521361109496838777780992489683308175739101394344253012852148806896643000083798142258729284354631625061429129848611711420604041294645715096047322293495305096605869375013184669178820732755257533806060229389 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((123457841855870165278515547755666202752517374964873774118764700066456109627254939240536837200541397081440909434070069628576693633708493746601570017645889147696391548385471941949707582968621826202721317131385238754324375340271658671270803393575350466119783182098526596095109396686368828748104975293233118945173612677 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((293873587705568372913919148377671308757157430128090932214618057892560863544745461156195238370700658902592725582508795848832306575676580928827533536882780367835476195940130030781110659095330639092843017496256620005941874667592653084242967754287550771810443490959594757273423599609599 : ℚ) / 293873587705571876992184134305561419454666389193021880377187926569604314863681793212890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((24959748514541260137668146909739321060541437403528156015429151695147220412076274283979587114411843632182941479488394056350804394524938441114992469169100558934891501460535344454631860516108225840452157501699989692721500785087348232755488958947077663622439337748089309311172298742122059615054286498466969095434255351294583 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((4943188203825572044012813424003625934649101203512041533377810017901415681648710914190012308635016361862781014167541844438123288146169630286565895059473234883900285106521565724856586455012583325480049183994966856325897037479286988640119777356948315788347683178239777208974783711046690244087961993456479731808167569927803 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((7346839692639243841522967085817428199410096508950908075714927223651576627561478335995387212952744281715377199849425748313960612314924524490808305550237239792339628892297029836303045374635163851617478872050791536470013459339361101573196718509702106642156408444546900977935094110485815251 : ℚ) / 7346839692639296924804603357639035486366659729825547009429698164240107871592044830322265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((2496346332413421972846643493531162070599193003322886750355892311776500543099218696283242252011897105669126492590491767191758953642770865611698949129932077616627441262423866493002264076776045911595798371291954362236999610413905573646134780245880785832369032073569188193064824425392046877168883661344976035967741848570478129237 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((154615262580497268115373422773821865164869047032319935124848850416822544461107976707909727863403265987165552756200505784595376168665654651672476862511178379790167347749976619126661467890181176341705042749076555465744795668170808316835123072153772351230751899808570645050753725391758755557367375039658891653847414692917546067 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((183670992315981618961481576059150358369061517012608770028897389127027036973982068935498759560896123123706249200518950661208189315958791621511255020780543945614153038089407704990154834380348097188153187432697440985984233895531981327732357088703477213522027431526441002914738740679749615237399 : ℚ) / 183670992315982423120115083940975887159166493245638675235742454106002696789801120758056640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((249668352939498559191023423780260741465659739999160973827721974206463012892786259824592321625778664328437223784369860265107990350365434161144980354887829920097596607083329919120901522242799190213113089810142931465265297248464978222852046684900744941591472035364506265932069320296492059019239271568371874760579461818700480464915151 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((49518418459390510354602129627888089423129040903679665423703402032870342088946080761611365054008288819791287725569373257717770725292866906584353591622435581542957428114543981395971380958864059328304831626935259013596640593207690721363846637801750978788799817633470058836845345428501708928111266261230163980985685677182007967898157 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((4591774807899548395803738087622622243337862046186796846915065463283565149195185202891486675384890369201025969138661583566642859947459734274274002309804460232108804374016437322895855586027893324303332636417933533496675159283413985133817477536768976307645193560194054753155377182557526921231357451 : ℚ) / 4591774807899560578002877098524397178979162331140966880893561352650067419745028018951416015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((199759168517369708916776907512344927326991862453642714939763547247668585961019376820819364762738645544180158413127182047646025743332376619161334124834274623705164473999025860618199600744685650354315557985111221732278563153439841103427915963274974875353978889499629788745764676577957891408089907469711882149260034010361402013713607137 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((12389185519582656139880952360166587604060402299895895589165476814789908127383073937991144311435621607696761014497118670134090237735658350880524411510530141596879831311849205250017695626932020686462305031950255547054418372368179878181645077327231332772069218323208790940841756003234484159128248993147560052877823113071113480240559986907 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((114794370197488829901937170586958940974449000261753450177598799588238542597066131653293530815327579203026342406481584329451072685344067514520976860991227768056216277461975009004549316272736555969871186109095275098941131987984438460792200967204513222084517037243379735455550808938563975329733834025199 : ℚ) / 114794370197489014450071927463109929474479058278524172022339033816251685493625700473785400390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((2497267435686270118886086319158981464556239817380096209626761101600905974728334909424375731180298302762050321563997477652977479845105291598348937658583373457199118720476211704920216328373037916281919731670158981088618357420678094177024645808260324289741697926696257210673936129482506980351136773543982322194766981517148937847255291502857959 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((2479604688376925191395384613298291563603934541650784254070663714104181173740658987435706060261059987870390223343179763003198656387158701312832156794206603028552628702332854627954383013913580882851737065690887225694253077574351148137794240181273323504687223929230980740024126843356441395692118298218740717163985870328359255827902101176492219 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((2869859254937222565532104754660936912075021108067044635332506037086121035600661603783003677569444372346646061115789521006854300110277278777478278467156109458283620387271459411409917592215686086387578598366684322473859208485976258242541052452181170801358348597199959612416139204610305662270137851647739651 : ℚ) / 2869859254937225361251798186577748236861976456963104300558475845406292137340642511844635009765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((249751962404678387869112238461565258783315835649690920964698473429320645226084253440241528815342639289197979430923661813143969304599151262354789634968322696414106429249113178740982907883912579854469300144934917643750345007217056312947729838477963684226060133404932216832477134672349508613087774759208318068911173637884410754471591519577667468453 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((12406173916630523173767507368660873172814113977739212272244679709981269528119057991380201920950982459758707669039895149441133720020462960651412502500899675857062066330536525262937798852525220862335043119670571079997995246256843309938774071582939769035699506672285255527501988711865079942501495566532536324461383295399863277907341035558562565723 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((71746481373430591678937318864335931162351824843651199645453679508915031413257092019890222192700684671679341179843095453732835792370590496200018440498947902183538565246775338623448841604475428522685428186656900801156493149354054336116254403598092556469777622898982188168492092810641520477730318314611607972999 : ℚ) / 71746481373430634031294954664443705921549411424077607513961896135157303433516062796115875244140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((24977485379435059697622375993628231710814637698082051258047427594126792093618442756601676356834957599972137982635228388461611174729536632463924013537370284313427056515165439423697863915118975574181386020198238154117912451176308192442617323322899742877919354840003146074967565080974212645326457028196905270717113047855203325194658196444814075715337407 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((24827377112762161221765045075976108148701420644678318252861638650373396561529431833711435240769629795095161228696400927071928670711694435026059638831305939709633404693322684219443070049711965657377181151349952504984132464031204694441243823712413642344511907374194218018884591823185217044206252154647230661611665683638855018831563380907907946131201397 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((1793662034335765209186508041875259968211651046495060535049016429707988407002998421613854463027251968966270339533443053028598729418622075426934079355118561770178425724923399604806626501466198266690161551599665390236719714719564569137825137960107504137960661209296681168564486713988408393717136592148051249182961851 : ℚ) / 1793662034335765850782373866611092648038735285601940187849047403378932585837901569902896881103515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((2497956325376699667614595723733392877967065425796316353189881824242553174450190329910737714747178934220087027846693387552776453242721927234750206420234947723890403888773906661997900330667183993822473747537293761211887545908474817797031736551747954873366790034104707811740124438064352483707208516947004879195946933036832704923329269254888248637614388936621 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((248412306046934030221019181463662226322488494465369487719102351119923974351859266517849755933712988982072574133174153134835824690075010914276001419729286180731175208199605520972437449755503786025990412186959607875426890190448262962717905839914654045627400807008137239891804894251465634482336358624271301312860074208823818040258134014338090128305213093629 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((44841550858394136550023575286354186934267883001818384835958515864332181280777591454141718436150572499745029373592128810330242151962705820642624368150691092256432971306864580613215584870711437542089257345183330996696066958286683657868913014957668580185966056659635423022583409230210398756420902234450828373872689080799 : ℚ) / 44841550858394146269559346665277316200968382140048504696226185084473314645947539247572422027587890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((49962898722153679455194638508653896020481707946354614369458380428689251950862839035644666659453372611925728531283543354078589154475108883419779104130103173436626945711395981331635615531540393204261246647442159463184609564929123117086558677668574468772878791483507069071256303966400204265396024148621871864342694103233625009256060147224407812263635319285259179 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((248539973248764049804336425140716322325944078125834741321095814491000714005926981365663600327992331612834279446420643815746400316405068823446978903754818691655279585724358312025469819669295782692639367262246789786828252655961106867337476206585012499282750091754108602416739828999893780148095363489741210944795612205088396907060116652108191437040468172714054799 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((1121038771459853509497736266012626419762963692056164531642459706095914836799728942066628821983013333345512449980547159347692838360083030476915116553114819356592703082327691531709602895206407567325110159522182281268948718351084970733056163263593721321237199792336817023369116066428457330761020247949695599035797366885024051 : ℚ) / 1121038771459853656738983666631932905024209553501212617405654627111832866148688481189310550689697265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((24983161399543057689034255626167196831368498384205934035294649904859063155008164332406425671317654075754615031009263571023879105912834421575490654507803045599046430886783414450312494425008581381402731914489951452950086624613566565203935968116883668052460121629958278467839934840479084791063820612536528837465945749860663036855256084977133878684072097145190692503029 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((3108219984162167887906172280053724415714174791093084873066980642755561417788070466605309226046583476500736640338390920984134124956707300199813928604101532299809316710704761987426530809988072366900525404038452725521105141275987502211631162866118067304239875051452328206532876645584861967956182971708181966981267016857724312712859343015272867928563223539230719121873 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((28025969286496339187916934793816448680382625282499281983914725819325679427109823971563258259064876750523043104755308916958198808316897828694787100663136398433022858994182199013868774259481868237408093806601539378943304134300586221635067817280181284295422339654110441087018739290324700103698695736189938629793294310941229348599 : ℚ) / 28025969286496341418474591665798322625605238837530315435141365677795821653717212029732763767242431640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((2498471543397922859187080543599777556140100028888777513832641559364356380709870905000941407315477897463251533337388492046147882286350212230346710810782784142821113885111283717292349794963145938461586922964192587264111167681869119262210999593914728814748987713507455414744757949015908088591383279985626204566857817340168203445483755257463161326526800982654211333411003823 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((497531897203091202047429291487190002213406150257263964263407504672092963497979580643524618516077211885745253352486630361237217904006355129643736831407143162984306281566635946969496607255164546419277308887724580149097245537731979667256580665182788814128283209777183844212252145322769903816706695326497341447965184084600801576241760361393727304864840059117811548880545461 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((700649232162408501671146847691304657243953598193092760125901774728931356752054979050109255237679011985470454993938174782999753747192685206897329787945853299861863290902866132861098061256890821928495213076206720051612114330519580671549642363977466275791353023420119072027246881509128881870931541707541380302738615516448683401926251 : ℚ) / 700649232162408535461864791644958065640130970938257885878534141944895541342930300743319094181060791015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((249861260465772854014954283859702249641795753682609852561604247448224489615416889533834027380343196050946913179952045908515931194596741897425784841404694909231906588793684210132642873529893612284256085854059236595794679879783932295744188692645717072664775806012624556110108490904041883616313155472102036417907335206143386842096273060435543368486456767178793947760757996702077 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((124432866539564193786336793712400482760091215745812532087965130992163198492973460577610276992364384258046630180731789007846608168721765208019163986845501637545169193733058797569365989471753789540591544368637386355714506170031658866776840366524386824733755191890692039818815534263466775223170646749197397572406884709474454574491786863045738810915973915649915038456615057242311 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((17516230804060212874651033658170056157209583253739940656936725817667747101206087270252541504373229204862813797703169409787663269516221988199287648957591731639607366993887519046712774529980639061394773982891455602061871919993041127593305532171894636611963206951791383822140763007981793431462741925327544370206187286458681104855780776399 : ℚ) / 17516230804060213386546619791123951641003274273456447146963353548622388533573257518582977354526519775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((24987406473738667620517998592744061045131274424585343248876158491028579789763951050614395163794287689244013575615905302219411141655550804037841659301515292156765987782242017721762923888873217778717050915284128841180839042922414009009469439023443241809285123707355127057281735846685814906885487344673437508961100554322322049265596003885144363635884628463572261245500392069852859591 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((4979152206032836107612633457975560100635322499932621005920882282055791039094414090737655828888200480665698079601637574350436493832204006073111527360245997520105274335332774360730400308097702921709893912823656217666342395946082665029964854252799511159887720191982105264225520196762337570291959932798964728838151492108981749905618894953161828991813849219841993051074969254689418439 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((437905770101505326908959260449980228341091231578725821856670455219327850280401175872616661169190795531839813096405313388873310869901246899231008594058557142608412002590402026038651821354676701141069431066822660915635297715974580041910985506872031850034630622112687673521610418807916188693229077426786969664253531202562560057460222981668451 : ℚ) / 437905770101505334663665494778098791025081856836411178674083838715559713339331437964574433863162994384765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((499771374605546518367863058291042362094905350145934901060012116726732549655359702004760871258394938982623825636015536348894227739034864295338833377460720155364544723228037518117612529727467502943148277417105004213129070070218750654988017199873612813134139647520622804788810665633769105519796601072844061376939948719758864430758409080796312563797554312034213340795713141580810390759233 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((622605474703791748772573091770483192214840206217854459871525023709033451231981702849464759796677927559140850801740102835250075083638506886694318230944532958950543146176191972260861464100523471603105891175434429436053947909810076706580773094912919954032183413606804713076681652257658525935125909501116322944260310616740655574021712272205814807268813443440424038807588322374934511699421 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((10947644252537633249115592625615801669527272438881603996425100621304576340003551408683292548038090019196167500472444092528041786368133989276450549191393082153374833427242000292459536441701997345586060811231296490210959125099298913054909519443604410496174619294385105566178876234521122342513727293938395803443776744187620222310464917949295364199 : ℚ) / 10947644252537633366591637369452469775627046420910279466852095967888992833483285949114360846579074859619140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((249896237221600314685264387312826641394024979927223223750671935701223379743820732511768107913087044686939142158561688162597968857950918659751772364390164588351337240921097157033603940228140337663270913265635097948284459039991375807820911034422567971256786092790282588161430847267617001890773016334393821277370821381519041146558398745283250447663319642500679707285797461805166519119095389599 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((249120036258524467401425969277234269161002448816887634717407050834725775110959418046404753250235643109236273106472940422653662400685567447356930306767189736436895923939594277329899854015748452086853676652953744796775052561275726139906595472081530491851896156580852221769713549193989963604840269881809708212132704553641936987595446165674921906738828004026941696317432581359427217727457381149 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((273691106313440832385146332411930059251370684469004581969803846691817495377357650174868767509879492142910895761532055557707305021690861803548949369700413801541475351589289062430469517555343557788283235229342910530205819786129279233868824310051163214606549307690639964222043796076760482366740454775872758026369773897698258747781233042013875472250651 : ℚ) / 273691106313440834164790934236311744390676160522756986671302399197224820837082148727859021164476871490478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((24990581348841882139537692708100642458350227447671472600658178224721148566263911531484749512827429205531345541188093013705545444012098802357468594420373583131115004059429101364789365195076374659105810154828480815663450848021582115068454974190958344935116466533821987269397577483152402372737532358010821334398090570550004265245725450454395717171482529537779291919630045449561311920478983355375693 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((498383343690813474694502833755478178388776196426121012458574134118109678085052377516826274504140397921684941782580421903146244887253173421497700560530428171040159426167634356195509408264580198413402446839876213758255711370392786895516815310659969681652346897587241100568010277266410005936498006103837392013847060711373429860852274118493949095561498674683365954699405952351528995705783305897701 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((6842277657836020827159937282870235461591565356330629487959558408026204947537687289617226176498426087525661017313324109643707963773594865461963034001591568679551810101226140006759182721445899556934702730489315751622087963940072451113878819472965071538074615462205504817999741466766844547373751149399696411341475704776230921770137899353468199529125111999 : ℚ) / 6842277657836020854119773355907793609766904013068924666782559979930620520927053718196475529111921787261962890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((2499145059615726482187713414415054261143154074187276546930620870413001945414063488517057785163086249373540229048296512847397003933677371705335321409289426827462984275038063433433742077074178685775243794239276008841091064356954031529086888846387216491934696324769542920884068005947949914960858707444117499969245902545867971111781685070589329805879595888766706415561110488875052900065830010060565448247 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((2492575799776403225840529202143986315774494455404331541725335963237698159590964107503064641404650747125311980526955284252012868635830550079095466536901002574391375936097588083806770276264570321238035197024032239400289446716487364304614613085004159964069448881685216217492213286479478653941087711734653065619605555267209869458923888882734330741436252075088355638827254574499033271174583360368773144247 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((171056941445900520944579777227248871857464395015794683005574348685485521501900830928364839785056198326243835186826421936992531943206188616883278002090110673926530371223474794962394859047183932388003811664182644321323010565728157561924150236195947868730292349636951192487878083480050928048164956162256000935412015451655122233895819037305689754666716321672851 : ℚ) / 171056941445900521352994333897694840244172600326723116669563999498265513023176342954911888227798044681549072265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((249922396206379108423751028472078339314955495544941312718483810830235909508591085706777210175024162012464007566595400906343526989486549856242385978768666328342344052491027060509417464794149671426747428466616223827991527413205281930471111795302321665011200919323788099778196900959518688708732434893950993660212488928705811869092144264349673077752768255724074640186359583681543072277013679756091307457159061 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((62329551919174359229220270827362079411314201290545238406393292683022673649614448734421151716052918990695024139574746655977021762061720831174528568576843256217683866742460113845596087594032226930029354461525677172049525700213150825569028985375555056275653314205186718223706188963480596665515059423216988456643346572938930641511653372322786715127343206891318265800300553420919903068123912841720716399579 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((4276423536147513027637786228441785031014072405912823075163320767293833734023605842182635968835854886602207770133905340923499866407630551357164778453663086599313008593664419668885319719705789391745869742900702878823722287060215858905588951928132414263395198804650173614998865086639291509001650920902016158170556622077123446721287762596143894093446085557022019799 : ℚ) / 4276423536147513033824858347442371006104315008168077916739099987456637825579408573872797205694951117038726806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((4998591165209847609044705589894877341630354388788195032245055579515192162800430040176958091123843453534027679175645740192140856680223765551306191072754617294714775299689063919966015520874297828532848392768470035198399632459260676374808735852493267003117061074953490277454242343646502887665670502714193665637482480851847820760913821933857162566874200913434714984855777309222564173494848908273053207252320723587 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((24937396823610175838025011054850744234515329729760590716625789370674851648251399634276416322376656030030542470525466269803405380042389214889433510991210578384813022332759076716955823650576804400260230152626990100044963795832663201287223210884943158699177681219315254772389117112571786937794761477255590757281993907411984630782468552452129824509876579163004886074116238736078243099631262020692291269746862609969 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((106910588403687825751893503155319398215965790022637092323446020280169626456506358764445677565195329131085343281975328884650099476209195222509689228794542098892992767185422293563943708433823003495558180735202747911300568926675210046560767032759277943676173866691645480093617807197498627069866009800744642780125762267846343094380788315568983851621614750103326577935051 : ℚ) / 106910588403687825845621458686059275152607875204201947918477499686415945639485214346819930142373777925968170166015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((2499360593286315386269175025256906458904316882801400032156542381530348515142569607437284463217587885100243723942480826681277281823951977145231581399683032978518864349075148494980997196643803070697274798246043184037101640857706017476398739472530772665266777695471878654354518690639302862767529534354902964116138619334456587546919490438050241766593789077604727098120003270324885605084225991984242842173943551338992669 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((1247126218197263844456368108952778009920361849085364919850893808341127750657926820203435158556680600332615038923813635728745624791668318543046896706617718612816238078185513003630814427398625792756834820134202784072705779875679627677679043595575238632070947042631096899898829281186410773940950329699856847665042749024300887304883910643885057533617208484177780718404887475123316714091274543876260005547425402879709107 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((2672764710092195644720651668816303483102005931689522700552805610635173151684183675453110701267668127355524309684064179148564356965093098425799282127008518256129947430091962325200183239063984679954210879957586428108292318670202756995349059779270301568750357906511737377938216161234906701481400182471480593476125172595604251536774562192554536368215841849315294329138087599 : ℚ) / 2672764710092195646140536467151481878815196880105048697961937492160398640987130358670498253559344448149204254150390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((249941960413192133906811745744078749836523220014881957397074259161427854295445500867061468541625488033267626887195704879711370170578834135244868810242121115009851985799225529373201923330159335897290449507362019923822102239867402029236169933107606898590817696702623758748635819998768434937065894146076002184087309543614945551683789002487247111936674584464262092602634181967470932316768699880669389616920201010200497809063 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((49894477363881415510035239108720243037238054263605887835268738678601720111238425140082144773146405627434749744914426121381889249976460536403032397330093716753327218453513789433064987181325396441625291205963234874321112746733279960630178579803981294534234191872968912300494223672210702168653906965386562258927006812241466305914750976672989359206365868406363338713841918438133106431776096984881314223502805504979142809039 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((66819117752304891132003576868807429453720792325079414114297498430784325087227919662702252309317006620026648875039386296796601443664195348052433324942052043062112573618463137264457575888580303916626340620477476799412520335534901565722542906596165798464999171925746309538386036626547601620741731364260459510569820239650808806530597842655008671442101788175277393792112889037251 : ℚ) / 66819117752304891153513411678787046970379922002626217449048437304009966024678258966762456338983611203730106353759765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((24994731688665863185629500930402602340548787944196499840327995496580094923077796292784441338282413744754180698127850808843360772495018292331821014424443976988558206426522731881151649358987162714425387278781263133143768842391111347802619222196559677386763498920840752623628606448095832066289430029109046782665934199656983585319134374222686477805533823167101936990255502523987567662455887378332213659138023526456755883076050917 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((6237893094159437510033252261790082171476737478831548952073372932694400337094695492363523027296755888774606318505016506913658395213084639245843290734993554896876812177040138328432247576898619578252485024696472011440490701810092257464907577912396508624482378918843705090407991466879955529697150020712413409545564614136968255691857248305468597304667187736397676986150108689529172563486299707068001665920605581896362313469059443 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((1670477943807622278511982804433294948499628894580498912508068959609753916055521284051853377629170887254728981498859114182046715270068895327646312439547146400347943377746098066419267817136103024032972434059613296034300270563018223819130802492025315680946272455503130843197010068855569616952616488437181701125622206810470102610132026718380726363676399989067277238556718156025315399 : ℚ) / 1670477943807622278837835291969676174259498050065655436226210932600249150616956474169061408474590280093252658843994140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((2499521790111889067148502424408234656165144447185373955345223702393629349700101655296374732601929726090278353609794039492744919799111600291411006339797962325858120228321199350736252994143265545595525673663547258329596363220035772053132186303265139630350979432871423788780043987680232742991514903230731251679313045176418551553975614160198506765205832971281369133439032521096771809341029660036424243313406584890090646561555776060031 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((499111110990896492046617605661295162429876902940212723348199121666470269607755080027085000790804742314035098842219469702210824267380829395173628303069518669961004831919763975474328550228950183128331434380553224251528593724488620767651775164079324640002800079781977425001832716534023641536869033571798660629733137817588256731706517656688786737487010569218279585464478819244578270599533005491141263345860395244585642853701770543041 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((41761948595190556966009542965553265167451193415196749727849140566173216457052730159140950752587498620220521282998403000040700689626273695318513987146699720818870994229475639608185488161794824711075499403569081821623614798759163072636012526951691507250655081428416929143591505533093024127215187183334865590352050810971811584440890072756749623683333783434380182886895723345627502979451 : ℚ) / 41761948595190556970945882299241904356487451251641385905655273315006228765423911854226535211864757002331316471099853515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((49991318482049256501927213316506089540949604221196240925619981113879404641944208481983986019598169462539862133424529358969688779363608134897721650067586894308052986152455663806017070274736667056405573050920058458937741752635380242532947463126593789290232416016949328044458269271318183924528725417299998980043364537021162658740945627289661740449344111529383320870976356608335604481328104095819908965647081294776011182823334628371447241 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((124796079939857975799265581146135356793179949943502030894538990956663334740604960011211452720546947882511789355250153306087718256349063642117979625499805895130248219789060413948423131523554191542004984796513430619900677370492746559390476682243027929068490009697709867185428906762425083907392193136822549920927956679067342535630151257080480661839125907192259018496744932822725089015679707469829038708687449527841031757241707663534949577 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((1044048714879763924198866452914998413837476011326734854183796727863084415676082764856811861323027737827686475472947464030038449747148420210380168391285354070685076691582326464424401960163029799548082740464668020515776140586402561387362953770791174643340173828559088059596267717320826222503182870640339878828243217735411973692695043712192000049178823485247425390553583312962911042635703199 : ℚ) / 1044048714879763924273647057481047608912186281291034647641381832875155719135597796355663380296618925058282911777496337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((24996059849670465309409454195154982117925653383158425949639938149713368040785999140585583498373600976317420540383910081471825074751956063766466263240658075557192077310975180763271758618860922500603430353835479699101240158479481845184570814716366337880603318432673225649442485245422542797512536595961272944248219310997359961989357226851778938197989069567046792224765334520421577639236485483540269808693513492154530521634652470846947774537239 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((24962579335795859583831703390921878444814593959430346230169131524754540242681421150756500584667891542335857201277698238763432836417855409102237622714854559051580627362950672275353289850876798542236504118363347319185690864369353817176548778533740446705749588177643771451188661426989152179913171560826347810679204167992085049490969855484186061324633579470020480077527272570194804578875410816989313044472321528530755623304556869079662249043679 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((26101217871994098105708325058455110966617871152586688619945589066051024802281751696715482846484540231100767380859797557151599350219551417767049170959581828816808226800780663609565265294509738433353905435299255842793492753743412402457161386673715504671960293328841625014823859649693196444700717307330508824369056505473755989470637217195996608745009996978013247241496233608075139384888267761651 : ℚ) / 26101217871994098106841176437026190222804657032275866191034545821878892978389944908891584507415473126457072794437408447265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((2499642348614437806583879752633993230851501239376088897325835961310329065235992332588175357085778089484930313861742958664994207924324101359740224044606322836544565777251001500676542434140678450959718929938708575114384903565271069483580502899490127158028138724745957877883452101886947241565481123598884399668661141328430953749494931057366821325706651494109127485864273333944311807365882689778631959625257853280220650478448718704613876714746778933 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((62414173131053367365613185031611378957015034084115526768697730670429976150421231633594566616934478664995039204609526324317475890234273896302998209872452413974708770196634635409258213333685133355885469351587676041320242271806943832203522830632587475505692097357201099447863767067980924500028542399797375128140721438850104677913615064969253019828188894127687596063989683268953083661540335994913252110605738337133984521678603480416912575478699131 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((652530446799852452653867845391681475918142806515485303751437039652935949459885603751033848623944125729674149150647983807303250431475984427753027890866705124745827827805026273021304203946528027526878313439348426762478621726458954484823537846720116180275526483638621777349566649833202232940771166488749878180366837001421929484490683203302152625878156444219922682461426442928730286541672368321250999 : ℚ) / 652530446799852452671029410925654755570116425806896654775863645546972324459748622722289612685386828161426819860935211181640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((249967535626081134140423950794262826387156986334067405813836441380233223042028904914386603268311165417791032112435944314332289935081833375568012980251210624805992843327922317401824237815265382929687181379070273027962776744870419916610937125286083650025597539986289024082258240491972064396826839440898500118277200426161315858394239915922890639362553645851724476522054643142824524445844347199935599421141539013420595903785742610785366905450150656735087 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((249685075606516454882725602977234982699816971292171943646278608514357001549058397901976766625975028503867010012294478324904095706231798165101820548040966876214401388738998392479094901425161651017790443544922939117597846725171410643981803295633418293106528787059100485174268059469422496004091458176574405634800530702354603340909958841221401028527928050993706368860017680199217667951846844887737826648653243711922712743957143885761824323751477975572697 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((16313261169996311316515754716867207675805162286526825812727552485985551066620790693661686747367875204897049287933239072047178737661429688096030619518739715934774545763418343009999737385585953089004679570292689317024788640534126701490591774839963040014993950700641481305068585178323180626819742401138071904554377213734540809760549359846824310129428191973487608716608149183927335110819794707698631383851 : ℚ) / 16313261169996311316775735273141368889252910645172416369396591138674308111493715568057240317134670704035670496523380279541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((24997053176315010626999741710275070509351151925540716546554871839953485969140614037921549742490998633032039167316786991988540182962093193777407740169962602357252703785027134993385428789779791217485530234832017009542433834728819797364138494967902511391714514204680076612107771381004263655219843370344987292701797441221503819732570589118348649826869341741519221528383133851814278528078029556149077644993416508600841870729491138921818502483664691423545037501 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((2497111438417220791314185834972684823937215812803884758497225209095487180306446459941520704496962305796530580119165342210684237516123679146757454476096502717719193640830101815102135918806043244359393934796363965641854261166894322097527460567720627788965896422667507154300864732759935956710570065134588763146805925511647248391485831416056015047118556471431528600161470715092831447376778743761305590978261884852979523807777252620942470686164484773171739731 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((407831529249907782915454936381536954008802826244188357891935511917275722314562950279212766899969582584440789724152457836201255618707998344966767855089387956695899593770024478258486021654241603345331890810363950463608523115451485400880974797050600093187143359164017800290483996866417863315692277634840651282094260410864558727062562252319541474150707680206363784447896851987315199593809070026926566833958799 : ℚ) / 407831529249907782919393381828534222231322766129310409234914778466857702787342889201431007928366767600891762413084506988525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((99989300554691593184788661817346692098612039341794081237952091639395893121293326799406628051274518805254546138405658734661826229756991040658918212206818512013532864968062708620555034295838226326177736322169229568053455563958629915694826283242460200601573671958801352536308590030761492427536428996642380272747993935819988785946381854477742745115943421254700534225542719258598115112228500721985748281059140838481216202277294217232756966940026596732050256795039 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((2497350827529906717560380240507184367266851946561029507143671206758995390445163243109495741252387080978821462355134199927122426584317782883674905036526141339055974462949907147440313917160311206483639427091272220233834653264513923021020285401984463327956367093414515346083580548648809816539775488288231453920332095231210582589747498001641445107672162049615593721138016525115308009634007968273274535572522336457775213180519963697665153025960105910603617022322739 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((10195788231247694572925171035636793939480114583913046275078076552711825147501428935303091064869980234208078275062481062104576444414682466927901566236749138155986182946022100821137804742040106049078432813886203485573205516675974552337945887200519540811692034747975705656600542068529364211369422313890201026272445950964187200156270755560388733791909070647446204970601189410755837958646613601837910560967641846051 : ℚ) / 10195788231247694572984834545713355555783069153232760230872869461671442569683572230035775198209169190022294060327112674713134765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((249975720016247765124188478487004319518584638497024013666325610038462368304535116175579595718354038324333353566465628124309733514686731205613065176221828185458971788409815480115104706606847981940273873527480744880778096460092113109343438362450416136517744718323667877105069537546597607374411257644262616310314731045954456865362256339169477106218152659789885131672388885274677121488228823659926583462214566032025519892974481396690465715209380426663806747034164498309 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((62439265834049595124308409702221236933907920204606662196641168863055097006627078891521283046587685269717739529305383018284919910086447806997520927395483144167943057061545572531695573715616470823208448162358591548733634711616887048459930280106162087631431370724755853635823122354062140299368825856915342623058061379268570676222862273620343202183846466818661959605151810475545418362939364529303391160150198818141823120969851583267947864129165602535600804058073178761 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((254894705781192364323717021128684056969203270060194659055486418763956819913452016978988948019273856258927796577203912568421319132609899691490780826920512693925034685449288805339416604037165566537489178697562096602948490372124338493367542245200670523756322634397083964991841611796151338438035378633122655347001283711156471895167345675984328928213630511238162559099637418383540189235537549454242507088098806325826599 : ℚ) / 254894705781192364324620863642833888894576728830819005771821736541786064242089305750894379955229229750557351508177816867828369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((24997796081594825888074210861243664538676532450733947595389537424670552272626949622938604921217587333069296887929187280056249059298029741449657244059732427882403287331082870892437926222688254798109599617059618819942953279177187967844130347134042706845528098000157251069344168472609797345438460394130593233490907296363044057794451942814906753179462065644018324146910798743908386666378496303117427634572425019826497456503635922610646574663501469727114757574499466984510303 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((4995544863224002764089106019255571691149608185651687991826356242103693207727348179886707524514386507633093651864645393954043278248174331570498173382762570848134857513073679944616091404847098143540120754273385329677020815572579185797831183693824129189898578762727277039862377863763969493382894452846229989375661562130692679563225997901872759087001408291117581764296283395380585567020868008863010982952950603519153845829295816213863178077028267117743270961799949238430537 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((6372367644529809108101829280823991418526935693854286915889779684528316383717706356166764110482942790739237660055121745463991827944204245426393838747018846800270350449871276112086822134559021167476423568089368201438066680647311603836024897472544957764384531588481424985661408577099896625997797950913175105851722446940309392739890119645486598933508288614746924607800407251092250326729158336682319739877608817029947148251 : ℚ) / 6372367644529809108115521591070847222364418220770475144295543413544651606052232643772359498880730743763933787704445421695709228515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((2499799948122443940685566056010314279028699132261719474421239993430545872338976971362833054985061051290424606389675534879809977689833580128282292405629568824469470089488553834520426630228288695794874221332404119306548920660579842551136948545575038932431719345699476446755030986507379751642308698597217881548321724864988659774165989785681833570584475736122116426604309673895978185524446357710612537554564143268015511400416368402354366063966565405919769935944889343661096975757 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((1248978836967784211308349052203827634957075570543385227944100476576128103858584863126291014178197000959357130172863552340325717308793338869383667593030488584603472847687309413365022892828034815734077499898295260444908899032609597062754075424530315147479399140400519795522858418096156097060172556436978478389989230859480029846276466128996617750262139781896907592593264731008993081532131596271996294653790153334082156862463554298758264961859559618417457170011385771203968478261 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((159309191113245227702680614968841561986776432719008543135269670607747827868160077363371822933180178893727223054851531171158443811634171988964440263178588510177295538965099961822003268516434611666100340632985838883585272145126123486511941171811583565172661269033905107107784678534486333987240641158383689678547743348698746990616595422509476487243717064224801160883568369446796500199620019642400461739405895969186669348854399 : ℚ) / 159309191113245227702888039776771180559110455519261878607388585338616290151305816094308987472018268594098344692611135542392730712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((249981841091022358939919940575281095633715886241782421844173674184976631700614858547694983571740149356668932770435525898148650364401073354844063897260647212136709628614410016772033057799496097636167931195778184011468476827364338538385782130894941787937193246319947145900300402397236066683027365959319760037767892680614436890019215660222641915575342910223503539445981148534395188375656392428959524416759902125050539960317254500428263878141232298904336235845238843116770196223316471 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((49962553948405503283585478553221293397306655503846130016172302523590791217302326338076141912079073678104588163642462106074635531154486887205913411757099249861422481434147877771980400676032794578297358335042615157753958267390900567374188651769438901362223483317610326569182588782497795580080942644007134150536977229494140783881700026744472324328202701370759882135139527955444120936342269937144398886625888898959291615167960247698100276422051120875595113259408475885711821893943963 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((3982729777831130692569058716003953722225473276580509186117585194207480918655270606322757581201598493981536495624858141939990055555131618335822305546892437340675850119782299321641527514755467932129754060249102473247433287726515644697169396811773679428800645564594628467575830095118933473572708472908354514940319763989437318160850804055596059305255069805941512786225177228749520181524043677562724594890259918037208853965795290451 : ℚ) / 3982729777831130692572200994419279513977761387981546965184714633465407253782645402357724686800456714852458617315278388559818267822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((4999670339534638108666493765007130492796497608704637706726330109994375467326551226329705659119431879272931056645301603239302806530054688317547082433810651140969948579256332470389921989596068966116653126796515436495714651010541697697182570451063725706123568318470406136672773800430339576887662804925114178347428079639178255742123660791937353001320070298950134446037379645756239214396035835705841737452908370061181725121291040732454692851703589330393090742296217082616569052426181602449 : ℚ) / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((1561427333355164065214263031271344959152386002988968456855609950056090492618357615606514024430639863911803465096768694229157350200323572011543481075052299572916599592111098444436953614953275841776083837759787685166516581380402666086023423364678006896164018468212551685910639765350289292025955986508401245955032480127590868970413519185394203062301329796817433779499419405002626543817659610503096162970741871434328795580988908750217109267930965271973833703060283944139650691663807814889 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((99568244445778267314257422484768217430188622099924352814529921961316855293721534273809400487294314683337866211393783397951679107921827558044372106729873533273898453464582052423547500321030583703833644258713653367225366875768985501517419192301559469666900979658044026655306250110956723191152960656088662546830904104675985932818728830638224702415309052490207977198525209838326481229907737671397714887992547498345676928727832855042199 : ℚ) / 99568244445778267314305024860481987849444034699538674129617865836635181344566135058943117170011417871311465432881959713995456695556640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((2499850381949493178808649491217769717771822042353613057978095110837573396401986197115434739765370627156313533830717550549271363765783628564880154580383436930680969534303370354749784976861904475332935783092308966927554508246144397097991402684560064185247635945582696563878981053664429442195374150922739878159002582748633108509591522535904075419758769413494943623415316445898153278140769560873572857260612228714504111480503031642322920166925894563623032643450777681691952990810863140745100879 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((2498426915433531433341437268570754089185634060190661999732735635350352697627158732358486419825563961463262400893678100783475097367866508873370223249525349049431460862398047732245930415536691425383163455132724212341092778306569933092947404309227333446256337986105761356485480061270635768999290013754934825705190120793534692888234785126882624452936378755735698459595463664737316282690269561718270735919039823327920576364633082853254437407391648508888378917271019479573345305852454136689639809 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((2489206111144456682856904493122361788154800622016909499638179384148682212269908519179587255223804050588174581215724609838139230713836232473689193044850854155566287671534953512164321082363292312529375876875253134860097082801024361362487383344176324405983882940839708959801234382930883399622776200979087148921941366281736510896270923055338466016889516836174160646580458403840807864151872317984003982838199102052438659793297939921034272651 : ℚ) / 2489206111144456682857625621512049696236100867488466853240446645915879533614153376473577929250285446782786635822048992849886417388916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((249986419019937445333628892283601958800432461717390355529347387500826523252246729112751678875981759132406563182199624923654780433619904280541043735154665422159434744809182017953565724362793940047860417719101690013072654380161878739314197461304559355477925967813141945993505285393461175442559850242376849945994757983067547908813982393263748605779315603659392447396800756335065570355955866612741906798021700448117991822588355240111989557578446810488009058716011358738806829526150666702291254478173 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((24985582871582895428306062845988471615478533490644807528981998613430682959170875590809051802728087186400740899524374716023604347937302798496996748120502419799919780177281899570768111530013953377630279432801142893418773313626932603759729149192867911661578448747858877067758262678586589870985566187741515539961524729073707256659297984223612141626644171895402991957643978779106499290003962066403135686976535406210483708204767204269975676812690640772798401096601493640468716090972657036739183111503 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((62230152778611417071429716163825860286378904268563048981290419399385716119309869068692783510429969498617487880320016743002202303782116755665792585436445589602673691936083010755777300076721515242507515158783209739995610707352718050280321370280927138426249842670780751032028899667019952620885436668632191219018489757802026403567608213365322421689859290551202359635047364359784398334036713745139676336015878196992393257208670491863748196389999 : ℚ) / 62230152778611417071440640537801242405902521687211671331011166147896988340353834411839448231257136169569665895551224821247160434722900390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((24998767240858741850378159766163759602302184745457975324979050841389086783874725705005350155075290998248867083914635413546957377340318474658808185413393216705550255879419822949957107403186814224443987246138571979556664753521582294245752330883079340645729598780182413729126659223245186590124058709429544176150838114532963969930053764667865402312745823211144604608175583850822663637821795019856806467943432567534484931406821869069331541076917605733301852153483371239122220751253656334354757366409997927 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((24986788089499512692211757352817558047855210823982993833312597000642293211963980545514869656200747675000796693515790511902195871288047219828822210868203658657694606924564493903075380587053190893110484739077514912915802251786816972643874474384237910386037152469866468322748912894876086679951693142161747018930061233253225213592655616767046112958658484977348782726898090157799080619344613100263785352264413227006999113305217169498893173226538907149870672262286210622190306512633635021813969889721446747 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LasrTest_open_source_model__apps__self_rec__paraphrased_base
