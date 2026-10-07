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

namespace LaStrajCertificate
open PL_TMCERTF1

def cat : Fin 10 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((42759 : ℚ) / 100000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((42759 : ℚ) / 100000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((42759 : ℚ) / 100000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((3 : ℚ) / 50000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((3 : ℚ) / 50000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((3 : ℚ) / 50000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((42759 : ℚ) / 100000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((42759 : ℚ) / 100000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((42759 : ℚ) / 100000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((17691 : ℚ) / 100000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((17691 : ℚ) / 100000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((17691 : ℚ) / 100000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((3 : ℚ) / 50000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((3 : ℚ) / 50000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((3 : ℚ) / 50000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((42759 : ℚ) / 100000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((42759 : ℚ) / 100000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((42759 : ℚ) / 100000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((3 : ℚ) / 50000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((3 : ℚ) / 50000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((3 : ℚ) / 50000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((42759 : ℚ) / 100000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((42759 : ℚ) / 100000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((42759 : ℚ) / 100000)
  | 8, 0, 0 => ((0 : ℚ) / 1)
  | 8, 0, 1 => ((17691 : ℚ) / 100000)
  | 8, 1, 0 => ((0 : ℚ) / 1)
  | 8, 1, 1 => ((17691 : ℚ) / 100000)
  | 8, 2, 0 => ((0 : ℚ) / 1)
  | 8, 2, 1 => ((17691 : ℚ) / 100000)
  | 9, 0, 0 => ((0 : ℚ) / 1)
  | 9, 0, 1 => ((3 : ℚ) / 50000)
  | 9, 1, 0 => ((0 : ℚ) / 1)
  | 9, 1, 1 => ((3 : ℚ) / 50000)
  | 9, 2, 0 => ((0 : ℚ) / 1)
  | 9, 2, 1 => ((3 : ℚ) / 50000)
  | _, _, _ => 0

def kernel : Fin 10 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((57241 : ℚ) / 100000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((5531 : ℚ) / 100000)
  | 0, 1, 0, 1 => ((94469 : ℚ) / 100000)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((8669 : ℚ) / 20000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((5531 : ℚ) / 100000)
  | 0, 2, 0, 2 => ((94469 : ℚ) / 100000)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((8669 : ℚ) / 20000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((49997 : ℚ) / 50000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((5531 : ℚ) / 100000)
  | 1, 1, 0, 1 => ((94469 : ℚ) / 100000)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((43049 : ℚ) / 50000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((5531 : ℚ) / 100000)
  | 1, 2, 0, 2 => ((94469 : ℚ) / 100000)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((43049 : ℚ) / 50000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((57241 : ℚ) / 100000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((5531 : ℚ) / 100000)
  | 2, 1, 0, 1 => ((94469 : ℚ) / 100000)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((0 : ℚ) / 1)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((5531 : ℚ) / 100000)
  | 2, 2, 0, 2 => ((94469 : ℚ) / 100000)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((0 : ℚ) / 1)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((82309 : ℚ) / 100000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((5531 : ℚ) / 100000)
  | 3, 1, 0, 1 => ((94469 : ℚ) / 100000)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((0 : ℚ) / 1)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((5531 : ℚ) / 100000)
  | 3, 2, 0, 2 => ((94469 : ℚ) / 100000)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((0 : ℚ) / 1)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((49997 : ℚ) / 50000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((5531 : ℚ) / 100000)
  | 4, 1, 0, 1 => ((94469 : ℚ) / 100000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((3537 : ℚ) / 20000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((5531 : ℚ) / 100000)
  | 4, 2, 0, 2 => ((94469 : ℚ) / 100000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((3537 : ℚ) / 20000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((57241 : ℚ) / 100000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((6579 : ℚ) / 12500)
  | 5, 1, 0, 1 => ((5921 : ℚ) / 12500)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((8669 : ℚ) / 20000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((6579 : ℚ) / 12500)
  | 5, 2, 0, 2 => ((5921 : ℚ) / 12500)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((8669 : ℚ) / 20000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((49997 : ℚ) / 50000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((6579 : ℚ) / 12500)
  | 6, 1, 0, 1 => ((5921 : ℚ) / 12500)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((43049 : ℚ) / 50000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((6579 : ℚ) / 12500)
  | 6, 2, 0, 2 => ((5921 : ℚ) / 12500)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((43049 : ℚ) / 50000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((57241 : ℚ) / 100000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((6579 : ℚ) / 12500)
  | 7, 1, 0, 1 => ((5921 : ℚ) / 12500)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((0 : ℚ) / 1)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((6579 : ℚ) / 12500)
  | 7, 2, 0, 2 => ((5921 : ℚ) / 12500)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((0 : ℚ) / 1)
  | 8, 0, 0, 0 => ((1 : ℚ) / 1)
  | 8, 0, 0, 1 => ((0 : ℚ) / 1)
  | 8, 0, 0, 2 => ((0 : ℚ) / 1)
  | 8, 0, 1, 0 => ((82309 : ℚ) / 100000)
  | 8, 0, 1, 1 => ((0 : ℚ) / 1)
  | 8, 0, 1, 2 => ((0 : ℚ) / 1)
  | 8, 1, 0, 0 => ((6579 : ℚ) / 12500)
  | 8, 1, 0, 1 => ((5921 : ℚ) / 12500)
  | 8, 1, 0, 2 => ((0 : ℚ) / 1)
  | 8, 1, 1, 0 => ((0 : ℚ) / 1)
  | 8, 1, 1, 1 => ((0 : ℚ) / 1)
  | 8, 1, 1, 2 => ((0 : ℚ) / 1)
  | 8, 2, 0, 0 => ((0 : ℚ) / 1)
  | 8, 2, 0, 1 => ((6579 : ℚ) / 12500)
  | 8, 2, 0, 2 => ((5921 : ℚ) / 12500)
  | 8, 2, 1, 0 => ((0 : ℚ) / 1)
  | 8, 2, 1, 1 => ((0 : ℚ) / 1)
  | 8, 2, 1, 2 => ((0 : ℚ) / 1)
  | 9, 0, 0, 0 => ((1 : ℚ) / 1)
  | 9, 0, 0, 1 => ((0 : ℚ) / 1)
  | 9, 0, 0, 2 => ((0 : ℚ) / 1)
  | 9, 0, 1, 0 => ((49997 : ℚ) / 50000)
  | 9, 0, 1, 1 => ((0 : ℚ) / 1)
  | 9, 0, 1, 2 => ((0 : ℚ) / 1)
  | 9, 1, 0, 0 => ((6579 : ℚ) / 12500)
  | 9, 1, 0, 1 => ((5921 : ℚ) / 12500)
  | 9, 1, 0, 2 => ((0 : ℚ) / 1)
  | 9, 1, 1, 0 => ((0 : ℚ) / 1)
  | 9, 1, 1, 1 => ((3537 : ℚ) / 20000)
  | 9, 1, 1, 2 => ((0 : ℚ) / 1)
  | 9, 2, 0, 0 => ((0 : ℚ) / 1)
  | 9, 2, 0, 1 => ((6579 : ℚ) / 12500)
  | 9, 2, 0, 2 => ((5921 : ℚ) / 12500)
  | 9, 2, 1, 0 => ((0 : ℚ) / 1)
  | 9, 2, 1, 1 => ((0 : ℚ) / 1)
  | 9, 2, 1, 2 => ((3537 : ℚ) / 20000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((42759 : ℚ) / 100000)
  | 1, 1 => ((42759 : ℚ) / 100000)
  | 1, 2 => ((42759 : ℚ) / 100000)
  | 2, 0 => ((6723467919 : ℚ) / 10000000000)
  | 2, 1 => ((1225857771 : ℚ) / 2000000000)
  | 2, 2 => ((1225857771 : ℚ) / 2000000000)
  | 3, 0 => ((812448027151479 : ℚ) / 1000000000000000)
  | 3, 1 => ((27730561016799 : ℚ) / 40000000000000)
  | 3, 2 => ((27730561016799 : ℚ) / 40000000000000)
  | 4, 0 => ((89264337522177809439 : ℚ) / 100000000000000000000)
  | 4, 1 => ((2362477966285313079 : ℚ) / 3125000000000000000)
  | 4, 2 => ((582468233454630531 : ℚ) / 800000000000000000)
  | 5, 0 => ((9385479944106979990097799 : ℚ) / 10000000000000000000000000)
  | 5, 1 => ((1034893501786418648003469 : ℚ) / 1250000000000000000000000)
  | 5, 2 => ((11890857115818192073239 : ℚ) / 16000000000000000000000)
  | 6, 0 => ((964824257480627641613188112559 : ℚ) / 1000000000000000000000000000000)
  | 6, 1 => ((110767907944898899873481739213 : ℚ) / 125000000000000000000000000000)
  | 6, 2 => ((98472117900247483322748654783 : ℚ) / 125000000000000000000000000000)
  | 7, 0 => ((97986505322448606833580500750989719 : ℚ) / 100000000000000000000000000000000000)
  | 7, 1 => ((2318886610699804068676049523113409 : ℚ) / 2500000000000000000000000000000000)
  | 7, 2 => ((131179547645685521102163114725247 : ℚ) / 156250000000000000000000000000000)
  | 8, 0 => ((9884745551162280703760981443487402505279 : ℚ) / 10000000000000000000000000000000000000000)
  | 8, 1 => ((1193858323394530979983361683494941148861 : ℚ) / 1250000000000000000000000000000000000000)
  | 8, 2 => ((27683380637555674494954254649174117603 : ℚ) / 31250000000000000000000000000000000000)
  | 9, 0 => ((993402720094080109763982338806662406804675239 : ℚ) / 1000000000000000000000000000000000000000000000)
  | 9, 1 => ((121582422043648788209895373140491993421478389 : ℚ) / 125000000000000000000000000000000000000000000)
  | 9, 2 => ((14410925779811305264695502186823615831451039 : ℚ) / 15625000000000000000000000000000000000000000)
  | 10, 0 => ((99622365100905239563000113055632162827906415355599 : ℚ) / 100000000000000000000000000000000000000000000000000)
  | 10, 1 => ((12294712662862508842063563841927856718756546727533 : ℚ) / 12500000000000000000000000000000000000000000000000)
  | 10, 2 => ((1482507486963267285410998207476757859424079136583 : ℚ) / 1562500000000000000000000000000000000000000000000)
  | 11, 0 => ((9978383800740916817825689471417440632432191121369842359 : ℚ) / 10000000000000000000000000000000000000000000000000000000)
  | 11, 1 => ((247558297882665377983168927171488543259771282402853793 : ℚ) / 250000000000000000000000000000000000000000000000000000)
  | 11, 2 => ((151110329251448490447284349607802435637899101462103151 : ℚ) / 156250000000000000000000000000000000000000000000000000)
  | 12, 0 => ((998762667138210819569160291033405719241051051978331146471519 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000)
  | 12, 1 => ((124279494295604959866008939743750688506415615911784085213981 : ℚ) / 125000000000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((15301224284832889704263306931528501401826180972698777577303 : ℚ) / 15625000000000000000000000000000000000000000000000000000000)
  | 13, 0 => ((99929173829658325522958304219043176775077003266291653155176219079 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((12457730672896504720878617012490758840058769765474829161051975509 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((1542423184894749350470017137306777834085410877398423192904469503 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((9995945839183472211259656291802250481782182743965800518255441956301039 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((1247531821139083759234121014104747324739135410739944493808614321231053 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((31004182303816118358344838617024830970740877745533482170411971658363 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((999767935780701132844713985799052619827693922447346387465459753020627773399 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((24971282995940836637055824587976135439577669281696138478465799159715410817 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((15550542388109841523991673729851293616569041352510244742007244986945790607 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((99986716412023113545164273261123571011557027814808554564910381722653754377132159 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((12491671914259860502105674807988235103355973508458005320375099588109708019090301 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((1558028445991460794484388951057071051314549781807099748188531643900486648297591 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((9999239634140615042438748165739974328272535829147456471850035160186423554301421913319 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((1249518122509361136277377358089718694060799439142264276498073118642919699495421851829 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((155983400953639137156489770395425940303646543776783917874942147098452020614155380767 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((999956475897842945644236383755121870524648223396229555905167862604231070671767691740292879 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((124972171980034524667391334880397086205976961053251890377462108802744300889448197045161773 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((15609201464361065564397473082962795228529128995735657296981082671311244015431692439354247 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((99997508636868428051621734842526930990701388955423576009567713623328790716322654442906104686839 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((2499679099456436820767684783867919193117275470578845958339944907568325651696188368318921942881 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((1561568574420502091441147097171914114534090209039350801636723137787925762074648095827451276463 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((9999857391882985690102879724121084056838738205197400914363665495512963309393025062966388338379351199 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((1249907607237219884782237857740262660685719960389625583340178539836362361470411996732532735686649821 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((156195324209769832286537246664174429634843561626467106571520789325198539810498047379005649374569879 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((999991836968773983887178938288414972497506213603704425739090576628657532792966147629259034877172441981959 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((124994685320810794357551888550433373721303241735729485247256132369948597950627187350482479502202980259349 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((15621802265182047037731039166061802427594621446525840616874831362339432409857512034752072467657095200831 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((99999532739929591611686009606567161440729753172889645033731283696800985834602175256446416415404227751489315119 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((12499694549693729747122268091856410150491785333836805674129505381739663095970232895670549279517268264724151693 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((1562313564422757420161577737991316623102756056058400301781825106833186060307306895640960401292974692599219879 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((9999973253566309753444518875889510888028811801369376171375812410088585230158463113854249322034153400722999886726679 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((49999298293035574954998794087066391645082237352704911433963381054539921893430628112571342074764735101620072862477 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((156239159362012221484531016069496008183216804574686650024899507566939600813024675253337555998389733152660041216719 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((999998469007389136596917704974791492741657216322184461425722878165880707159500587100131085442556974810785236516121832639 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((124998993073825479729621061642381113118447938314282281951580905690758977735413078636954089574599094530695106538520084541 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((15624371087406821098002691826650131681447514587679897546480566973376248664733355376215264840278654685814162316409450167 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((99999912364451961567944166350462039836025200719498160756469803269093177558516973106198603461817403795144157723419329822088999 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((12499942231520578453503812028905461796942004768254574703202315156213200429773401071407003726096192247010121877556184901470069 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((312492717020196826582273694197997756138614971431776903988228454986877892254474444362617124053121351615017669304121294341139 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((9999994983653594732110692026066797622253918514384794219861088008926162576627070057571914260757890010637846732246245858346196391759 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((1249996687068396215341073238604883674478758677396261094158102100026870893114989628016087564673021133924628866758457137312357752813 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((156247895040237302053347281072022821725951019204248888912940058691818805629028933051628917174728109709580376630430227818526944711 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((999999712859315416060748122264089562695436549681900005939068538718942472048710117165473944200042382098920984800507359177594627660676919 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((24999962014102558334166440001145918289903674187408731336109415656959608811340064521726331936991564690345642762412529836454277619325729 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((124999027971911513795134998772808853711284809730054904867954387329526854326714874108059189093730617126508292757072868301487887782619 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((99999983563780073730733283266518750658249483540341638239958222224810986042540215816668894039954625993724336090965841746684694081924807520479 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((12499989114321486038127641546246844520754063254903104068717285920426236274486244742157317534849161013090263190852321482495226166740699106461 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((312498599015118345916679874314299240994179744161293061804895431082762967263502038407201229538263300898995104016837724436654649169721390891 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((9999999059174335200420903867458799806428858687332695714493448598370405652061044493561944163741042746506774722182975747421978573943457907279738439 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((1249999376233289255728524395373047391839701820470157871507685543495781437023736520804372470879596543280771993966757036834272475431156743952075989 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((156249596573861685691748215165356622339102512761168170425962457968125789616532826935014531265614910490038841967965269688913380060343873640031359 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((999999946146198121207292958277209159719794300121610835393319491219320389929626247855979245876701027852794291872475714758181475551097474070599507986799 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((124999964263726396748917870104041952783158457135992243163228447152987073893849963240605545853877049291391678707459144763055015654197042219515334637133 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((15624976786749490341284691453111891277872006101344182533386052899692928476735089516629734802906512738336358814645873439957127602559948825041713344743 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((99999996917354526656026656224745729511520745533261125828749000996885118439961736053524108013228243535321798061072382388473065842020370513275186436672361559 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((2499999590588005880125104408718803656245835299623551652041690803494920112310179228685098190925852826615634936648788499306093181831735155552895306827373313 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((1562498665325805822697103932165496073410640674506164206012310507572156595233626628383661164316732802677582498548519446500028168267021996706767264291484431 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((9999999823546290460317621828960670302968958995069400103563421566062701064621849733439773466785197888205355042813844240298586761863088028550384946821562647998719 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((1249999882754138743518829099463563612401558617226166920096893727458244073616051110017913762157907597674529087839694271909419409359680171847985176035862562147581 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((156249923311545223636231728583620264277521979651124717704302543103643310697469771860873567021860928128753039032308166826487269490827225881918642893045479658743 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((999999989899613212239040991111537728812246181836767531328073813862995071640019300591826073012251512318762728005707258158931404835805021842252584741013067534094674279 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((124999993285409088941429530796122331115469809809330657952493412565368615583192258375628808723875583993150124659462919528729780888846586519928344383605798504990189109 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((15624995596060752946811401164919709684287515274845427795534866694681164101437748406313713763928382528703500821779721861129119275418839886162616749697718076844273823 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((99999999421843759881774945372215531134941783694518410260750273179331700895746344785176716245294288816638297313774689164275392544206315255272380203160328998719113250404239 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((12499999615492813048298284695273529298133341581352468194501105587801025159264337873330409145980141362132675092418987623664481973557646348976145571773764434891184139796653 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((62499989888756485669209093339504224989360276090978584899533989074448700123149005374541197046565483628422483882426736507899094012230452017694376315976962329131600663839 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((9999999966905758659392679648050989217695202640457928321735606387058125890973416521848300414596890386153192776537776982452287744622913691527046315209100392215680761566389044599 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((249999995596594732946798103009904503026152423790348066908520883345956443987429671745118487320915692433232782361005257153901397934362388064547810560074295646899731281659469537 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((156249985496592647374231823342845452484819693210654728489650923524105095208633131033172447313946195734248774846594260948742734033319056609267742150079515007306741961840323887 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((999999998105652531422296375734086673810091094342452275064467845201594184125209335127118564031940602593794907721798892252551402789960202616699658128884115550817782472821675301891359 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((124999998739370482771264102121393240559930678222078746595312640432111734430696950753353830964718614446388707451222519871883608158648537165763941160808667661398696087093502289559901 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((15624999168152584261107536606614712020346223208585792840053579403155047374809033202834985124788525102131088342698744886697632310741107828851094638538610422170872413758640712299031 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((99999999891565656551143666843394855295563424331256310676965203927184452693511107552011393723752312033071414312903490391428294847100111957982505130955455658244360686526785515955563280519 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((12499999927823589032136525845240711245839385675702419586375903105569556773873005379086177297902928553561116992451223233420918430214012081483173415735113565993963627142138818263016641429 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((1562499952303370017432288321838771808623543832967347909098219810571511384869509523758202429307866621480536698938547106030215705370933521650579619735257123021731906051907444823195089087 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((9999999993793109746644014633782764911973345972145442479460165237995965256629269307384684188141306093085040826684908693495747025342857508586876576201021237333565450057479729718812397740188079 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((1249999995867758219724217140400056763282431789362007478911207854941565279535426095381237005555632380590659824463021605405888816001448960847261859613096802169591718047128553452954223093743373 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((156249997265857423228158836764697582317257342640443554216931542518693465293809429510386493114358393080168651048657696971115479884388364537622453329740971553967683628834883131737491463834407 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((999999999644711395007650041652359246326266296791577272966779318388127047254716004424006707613396502074280821960270858524390055477650506649021402098322656646210619926740197208834540459046105830039 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((24999999952685768075013537956425339823806974429848887266686904154729503916879605211860454350588169478044971632784884339874932223217458785281232152195937609117349519276908892355920480847426692801 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((15624999843303115751037052346562168524838964548405177479904449783686030038100733338561145665391433795327379648015036932093140571637240764832236143717734202042085151162709497351127329392645841743 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((99999999979662924961632896034222695618961809094646674681891414963854780311907198809234567950498429175233908529827864212794611165596192651096634077510087189085742095226535628430897930416258143817262399 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((12499999986456653578641535953630648965450949790557197339090567515681623551562542291482570137781837646326864609185393985287941122734285621949918827330950621418772728643566859502498648363968868178815421 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((1562499991021180327722693426628568352188702496598735593505779689523466902190510150225113993740859270997356661027635039759573778080051127290399493302107001334244701876889141484576203556146949291371319 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((9999999998835885487728828601894941319924992914386670305466146483946011479833879967039395904054480584419564158155876775404576337729891663541422431230754900790456963272862125907013028434957032410243916981159 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((1249999999224681150035675098060727694672630331712793796290205621130007744062451964228900604832779251175074807025631260951094941960134992792088510608951332652359523854883852900361233459913039676067898184949 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((156249999485589593657451207271478065250176258530964708887058616019016981568690050531527028591983731823787232583387723592540855366564726904300159163744528577514608820250511222508344217634119877782103293151 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((999999999933364921203085878001068336093826519412407394955187690887553643117171123193302060943982523132760271977000542500933354147996728712774561386079641276146547034701900949043332760645375492194772051918522319 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((124999999955615987338657821416807368385039681936321520482336237579567016346577320944746749502493515334557256055697614874118172936692631593014666745591943217377382287330298270526549620602743179602978931043709293 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((15624999970532585158450855256176900498021583966433206716355455305003117331132581786239309369539940102509970788431537756928728860159166101582040250564541647179585298038907083819251803833660878399633370948756039 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((99999999996185741454585838742659152626346723797685611694629898614094458085669992262707803270494503606642330728235488053295926124785480748247928668300584746287904498813371512224189410552101938548720947023868136061879 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((499999999898369036194105827049614400352953773006956241344699308800725833934901734319979931575382954162309517367318847618834806104197082059970502950568685051059999085102614992882307546439866571783332453410015205101 : ℚ) / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((1562499998312185074486529918875763099395462456781067418993615313923359062285220328546072471193272720161744483896859688727023488398520203150181575107990603170728394465852983068144489397938295866641831902437239493999 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((9999999999781668026601947995468552555484712816903322099012310026569380875281836027109657367006375880947813653214927571658712107308845703510459684902193771462265941416576198731224826049412867064467335728593235976318015839 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((1249999999854554605690780353480107938026702953859811220339363024463946972291333512878074872688151833547106824327440255252858075363553862418140192302812983883293374614271687853494170728516368648017857401798168473031706141 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((156249999903335829836303505101292474990216337468124729298058989004921053598769279274849060061344053594467370582216217197729503332448920054631449322510083364764155938580776702926185707502238253005153898829259411210731607 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((999999999987502459510722105208615416828500446352363060269563638230857930682007576027783897344811961801333801323675669129316339734465636914642222823486473672271564752626238191574040267894441923637174764440405420520419544640199 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((124999999991674136509375099645833360070982791140838493974436935407608196961975085060363086387027322972215022079243198504760048267805715238417778895971178243034088197308476121697040009647450602536440471166790543718762082691669 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((3124999998892865267705133675036730415922849241326766039200625505826681519514237280383180972880219208713829241397729443106120878333652261199345363333772849958067130017197533050469142763175042180731522745234902034861105892403 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((99999999999284628284853244024246355074680194049655613932890092215972538810168795659406378067914381505470148121568518976631196602740547522631035476639189239474496638005078500323889638974545750150915520691333246676009335154749630959 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((12499999999523399179297120450191315427157017287311434356094587932308399399651763671826068936612228131238856244758054053975246165462470544674804534700080281305913314237635917994911002099457973556555085013481961736474162517126846413 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((1562499999683010354098462640165636907614163397231407720582096742846645578894586042098081326957203875225985947791979244268070026378436002096003523208565143444989885323365528132317937995500954504171695706787749185062240061585216871 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((9999999999959051407653284541191885610829768987596336997132561768534484094032872032340080486985487111754616748626703594741346324737471680742923101718303831256759662056048698437039766824541973284388555319892606372981450353593023625724119 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((249999999994543588362199098784035799837978918303610461328794471573293519118961049650058358939651347609002049418699758155191220563011273382309144720096525754280243050048749923442762856452132356333954895509378998682954709218872456594049 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((31249999996369855530706346756234910647026741706655849507455810504363373486277540967809124765856136407424987521854742092718617106414270052139806784227028377082776916473317008212031113956644644196436157308563985932458340487469215059331 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((999999999997656061625481660422364724249506806619001926052864968192682404026535628003178547155536267763946017308141140466589404974297616477405661265457429604968179815750283547234593292803607092771685295065972681395831199690018265360074295679 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((124999999998438302678654193552512454267275977180423402765246806522607207922777000099885211255144544875949668973539933671278806148591416175473788921712382065481954580640290318885468580860784669512126182902014779375915955207686255053373544061 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((3124999999792149584613406104049506774662426004680327504551305660451382337581639306210916565373039685266531292060841132350898495180682311411970230868780923103066696005778805791317426638496922278617877156948263317983845704161403670862639179 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((99999999999865830623504195724236579180766019117678289249192043644317333488882925882529943217730051503076033976735307021448044130133769864783177456496048728017983580833361980527255354673371273597344037974871342255778773701456335527476012758961639 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((12499999999910604750716535684114147454569833767828709413686009357102515760976678837364274348469959907302984767808900141270826184972382220204694279109116543048834879583590387282223265011568579288795310587941670340381560429038312697172126826353589 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((1562499999940498300942705041065064621135457628818494332970489972733538213756785336940138284190546679797398143388608837409330065250175725653253086794907835436536095468041122371563117118544713413188136183163981917745445085884954717403252009531679 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((9999999999992320010720003667451026028886227700315022954913001770244368486237147560441896479726085878087575260862305709214707494052987120830053860787290325240477398150482473127360623756858445071985570077719610502063032785445062101928254446335723177999 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((1249999999994882825503974965954871391058323525689715772477913346363195703589304092549435443767771069727865010014513566785823177061921872947064483099128136992767524554418197934673164595464090072748582697766299601383962306584568027274913991451925426733 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((156249999996593392174018140650956957077559293320419518796786424588819689300696977911200031184121681358789492043446377439825912001703626399469975877560072085676126442910613042425948592182335668096879983082179744649136528890841594288652663578076832903 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((999999999999560389733623729928564180919476559793732228962175134330557896520700563507254596396000881747610895507019241101159071667087035783433113045325285507090166747531767244283249464466334254365526016818748224748590059671660799776475212762703130431840759 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((24999999999941416605799838063102129659138632161048598546221287607393910871714470011205779008101939804561533487116117578486886570888743509139494957111816928566102581105141078094900800850862945738909586153822279402285643846748176376908822389907505280308833 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((15624999999804969909489542587371628024622539081514271833498371265646675576709446074580458861677641670342764559999452762453604481587081377408831051677429507829724301391307242805847082788051124515025936607241175222045387115521257689706558518128560803425711 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((99999999999974836268742355924840942280011757759153026518023866864215464554741420955718760352303486472114995269717288379871446421295729015279494823827464667711348234795465888830017482595517439054137074728721967132834043605665535840005217653749889889048996885919 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((12499999999983232912975144166065132134739629927905714414029199965695914252066544084768204689968153224329885672629260874493359747947055621123804436367557774712741942340953109636135803900242393128274142049321813224258305891243694494836515919591517445699424361181 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((1562499999988834713920486326364363831407685736150861677387100105956374426842620532679341275831459840511847715736738766196228470833202088418245195870049698792060325113757057241159126461493542266109179401741783868856032151226792196164435976402721054332428140183 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((9999999999998559602859081195493820377050153025891678390918204163174557406577953676926297561326203869150334444233887304152221464601388824563613563210707905044465284307927262942519030721250013728897860294546774120650553490031900937017738663718297447139053630746889479 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((1249999999999040224433862588487701738218544144722505641825814164074757607597531868674974044112216119430102578420572869354175710546460731852916164987819366721466120361525636979857165777142590909237257375232537470573582606338104881122810413023231523947943683652882709 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((156249999999360812063449069775769690280571283245685711064370264393254963715027042925645056208885069788231520439245749170474763988170795455568947824834676732217442718649574795695362956087720814451975190444193027502367925397802958829446441565236684176874969016398143 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((999999999999917550227256666711261772202727809355065562774548924504274840509928646420938198707873235674034293922391943176977308855248097706845803971744131192650237339070064458092731837515072035855842421120151897440158332322916041535832378849899064171686568877582700667439 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((124999999999945060978193098276639300196548955804556999375856030513418531534556246795894282177472548400305149243240440249586060072777289023212946535506275070149944294746599835360706931646794086511169430227838061845889452307943228273664986312687109731094030243953534042253 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((3124999999992681716474367501359849684989980494582201075853824413845506284327512626662921851743347567091919104719028310837634124055367878799945074004326516222440286511094044922595649230356853026166615418523079869127152771468304513348037750268394290428747005424212516027 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((99999999999995280492558398859219335102656342535293307878777954987549196145628825649780923432237371883217397018411637219393358136183256360837560665146605813598492235525709559645686063111200238404424276027338614761372103100496037133552581197747072332251510889121711368904875799 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((2499999999999371042272034457892248314206375439259446456785861165534646635488736172606254553496323538025025185813845953580745241697198372252977879164793175327861694561459779014231609739451400242751332171916342529354978649055023894826240858422569791385597592248241517640904257 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((1562499999997905293905321592584076755386122560575029001698976598922950227345973638169034893812486333715657697632933521540811955160075112898696966584280475788639240972425393916305644467021975365874284877191952845088181569128511739753791205724734998666012065739640792759817167 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((9999999999999729850674535309100573960611151703062724236289128921442303536571939609019109838184699403967247022730900526075295213073265777350702810033656863376191294053727140903678715938548212846507649984080889647555700553575493661561683300340240167370408734804215880467483995610559 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((1249999999999819988012250347102004096377014036573901971359643524308311870591244319069974023710758936365534219992281436912452606221514106082345592517389135292315244157459777254639583059900256001955932823580527311167500209540355287552289316608779418265647623887605260134096942109501 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((156249999999880088397245846689888056044948573523757464948448026578044507443326055690673588387371415438776477308823257691383795417651778403047185248290069079566274008981065489700714569493150740116038197858016509869269007227144355108966774870579680704440892326961209794244565100471 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((999999999999984536382461075628225954079342934635013398009426028592278896736914395159862866247530378582489186828139477013075973291526806361331579549136552516516565862929395272467473379038438251546944392738774204315735855387214832681452313794775687420449566388928121213839251392744007719 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((124999999999989695879752042240100406124047167938882251329909773633605031653272851593443253180548366676463143095140981664718422258309695726098819813575117064678351008830025589003070042541064018617822455232630590666651103867480722060191154782063103545537115714585022239627481160964711029 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((15624999999993135728333336299590702388801499377293044669253180869373196025195264981117185636726092248852813810493559643772493317674670743311290724012907113249037258569342984674417264678835348494684579402474815219658518212901371249608049606038778108377651905300053591956000341817517407 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((99999999999999114847068454430035281837455668921442801915457555302650636328117716893345710326874886400440263543229531803705481787180285922928980944972125402597924746559941514791310643689539243956798643984760174229237036098219564237519011893926755123633953629668634586401372588972059745843279 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((12499999999999410179292306153387174589171863417892727626499179999585206000984388240034957813698717393424902522272967638763409053816568526205049358783195524125846617398473143597460929135779005690816361219287641308891155680587313226758409392172594336284139794441221442912522962545439258804973 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((1562499999999607062372582159736632962642855740373523271392661072155957052568331402258822011915269242008111102998391451578397963509033291951173354568554079308899268151005376848108994803184732965982873090111903703320682303052867823785431701050037999663721299736507799858281022749198998394567 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((9999999999999949332961045400029649567657799944732307424442705923079025074057786232692001804820645372447601125478001629975905482979986746514377798271149430170107810417837612248169412555432915863331111180331657133055757183298186076519825759820261390031931139715862312360200968365349671911815133239 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((249999999999993247590316263913769161029702734442582983202761682911298114851462992319059461991958144624049455305186604169904704947808463807246108732762803722096969896109746218347312403227411725510873535402190835954741344553649273208745983067715114095898982942536344850363003590539909575795378721 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((156249999999977506900028553925539051796628480136329305374065674883154443946533012093385868516726335186782640420861660373790022900555093307046199190637912981927885429641377502268922318621544509572557572994114046790088992553592176795911904206441698106484506233547697336608544056170503039631767023 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((999999999999997099768023199743097170902300126636422009282524929742966474264141741745522875309738561764273136023486291301450805751257421357229499550838864532367141176127442762697465344085535536932936135073364385953244596929171469206071346317871582226817770368475674621810263630200980569904210041733599 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((124999999999998067420841221632132152603895461461775204287150639248648751483646670725726722852090392878092640799000168055211712492364289373426259927093434534630585634933585945334084034782573346534850668580056849865894766553005060064183332303615147307492790088300966067377735941259107675439209257861021 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((15624999999998712426324006043788370357574769296586413769413588447232411188898250849174962822125756212535626943719488472754701074011653076707525110026369090566339901763782871380009153892631029040113092064640261717084151928370847072670454191463219034092555135165420391293164517963494713477066523372759 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((99999999999999833987821415976494625159618561548795432233341009503417143953353737439255474905604745013948758579120378800386345572007726055909173783789567444697227528062710951179565613760800139669578197307734450816349673972822704068824729934581287238245275993661916091027041300456334328801886886998872940359 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((12499999999999889376964231617380672091907552751662388275743482992708970494461164017880018404720587727696645171265556270911513248375834234149667957771530696794825002153276544994371517058319672576144593301947797159634099505279762781026979471982919437131552592156841624016438320488653663539604261990926190549 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((1562499999999926295771829915399964959078629912997724316434746913185364989206643792928275748602355515020359060886726835612682536961048642725253413472076756885281011358974928985881212466420696630424859493506073932282563777695290574300516217366713813342891217633447688852052741644438486984696244786588505471 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((9999999999999990497296885671910528838761726081614599336468672724985100737033921284760422639071721209343440889827429602912914806887294247166297016557898630101914000933837637556469515297281960794826325592092027699178671687878344403603596366185367462804397843153201738966478871079421033314948807298702485979089519 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((1249999999999993667813918818961445814574607475170269156508567803921619904450750655811802481198778416932303571164539841568278327067305345725027926147273430264440330609120978731103752192950790369472972055614248207778312530433292373480483861868497216638463053947587020009277555080608770283731588511551776868546893 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((156249999999995780989167719243412981874296331272063057886997466392796685691800301257059206744453122696000596577838571455628392071835565535080469183524232274355144635218330825721191482836100683868420023821910267537593221667106083259843350130402126887314555700661011169948181976708614703918148162689427734772199 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((999999999999999456055771032745830581259559962637701280618803295450872151288558688260971352283104393744027899974611897900338156461035610002046007524790675485663659327453800211369871525131716717856653703216939757528686346085844312006673459596816618938386536939932420740180217059457139367980984678585028999929063157079 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((199999999999999420061961467923304215319973444439692413504200380150138031012750920315091648755002543823231765076954532116752438897657005549456305404285540691530402867898496540830296760026417693264573018241134654942303342361785313565330592099392813912833362159190745927135877955023659534366153740533357155145214677 : ℚ) / 200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((15624999999999758494442668435069338139508011198840283706661163570094330759230685234530229028878018720861781453390565070387908789434508937790650390408087732081407426158428813624692983836403667034242002842282384511694233861648111476980363136209731134662764306350085781739142518748058760991864962987771952958859531279 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((99999999999999968864088389685404088301878471821344659003900919434903372811908387874746261176037178602301901022446759647713256413986139352127115516726543055474873523562782977899022815970064596646832714625840848660699535136299814263573995500781380084652183760978671695588655804700386114562599543986885644984939504174359039 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((12499999999999979252325286882304240688654458816830530626982959135116124291459918605997218788062394116328735959036210599602780684922288927495114604999471286192938791619453541681883320344423660095876608918493038124348117921519423936793516869789980791885076713250657429222503314892643960416856879688900944368607387023007741 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((1562499999999986175732038129349500929361031281322126801394709934118077075673794288659845361864370075652931977910006703001705898230237219058938173477096907324218682254712586507601033748496395152570241370013497548840816025432413730658049569424673371094537500691513311718561540994370957438534487978660379820067987877613047 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((9999999999999998217749283513982215418487825605525589626042292529373303963126448030338350735977544140374363116425874968994754510392980602655108219292944051038437235362257260437917965008942467576661351417897756018187102090736937668261239076460226977425575650662180146527190246916854801583677760497353321204582922158444485751399 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((1249999999999998812380981704781260769878242871348255086325592957274409865167418708356831911830088082526803771734304455404290029431013792715232881594158882646356317592949824573985120224341714912760995640774585173212863891368248551078088623487852509726939030716735822192689303558958599364733019076993580591208111706468938793269 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((31249999999999841734624648901941351902526202857918912664677101661846811326806218474819051501490794526970967160828085408514299822694723089274828477510929579599386970221122129683431226228948101071543880657913009942715608259671772734795007898171242374363594405846335555267934476500013625506200607609292836863609689802228547667 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((999999999999999897982186737623855992769661625485890275784286866673857292153321011704597534478090604139168919147333509100228742929404602676581049580547410425491185789370967844726862235076875786555672416511885452237047910775873049068941585975659852414817375819553853767362896923767685697451298688629001459071531047271520808895830159 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((124999999999999932019434877630567755385824012988777001078802929750921213266659190969042423491563875192652576002476364864606900037963680718203108110080396864974484623191137806841589466580450846174517872490559887328399881461289510286957593801404430965228510212696825609625691565446738674327689633951119425649296880192426964518020013 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((15624999999999954703082980481691704389623265735469685488438200823500141297577232465855741305543229270711645876610512760257350873633657958737367504621659850562697023471187461066471957576008210668839043015676113129400196201532369872051594724529458705437805582166051087115360529528651852285467084413725682192335485849618957550369031 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((99999999999999994160398351048327140882128201104437845276168364535278265260148248030982867471060384271530168100912517394406193474022048861810175859040114320165540965769383570400010321198035446898233244793556835171500859460721749201755285322832745612076561409287082143497619582813386097007809788235812672518713508676869122622006214131319 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((2499999999999999221744279566086416402709463136264812222297112094457788631018362298765229739055951144951431907831121521455420908146163301853814310029741930377883579787917882616986087299510712296268866282472907026647836758010566062619434799463758250999605517454373607882446051386709744345817219330697365110677499476190843171403047718369 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((312499999999999481426299335877655583242202206562178390462757034287773071012997832965596971662394083797506107880715754574423798306408433126905974443027542955224193388751540657401492157418628607988744174536387925089394262761601796855446789706190230255883268701074784716041564474357454935491974991254754563086654293702145556161986785187 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((9999999999999999665735362012357293871233900359419126701453153354363863181756145865541490316910967456086658352264333408173204920646496098898876276347315183800595730421605284953266990795696747015901769165227986802051880696391173646057674287164269191580874451629001868975947242539821033578824040088406153187643679950172665448006257703090830879 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((1249999999999999777259175923978851120681230684259054710800759698728978366516904250635393296490117737292694108986626273079300234750928375872906528164068990903067041050767245828668652819177992305391794807837693718784577812159310854269134960043913137548598268265593558712949362045757602983077730823085775525313475149526161254445276704388461661 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((31249999999999970316056562207135323180442192093923465609932575669581026231213486915490843806953385543955739839714692352336520632871563023251526543103000814659155663863094727596945348856086576100363705331828878563950545469443068039422065080474884360087083371164834368688069398094527333435515357362413179207435909637942787928941640979887467 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((999999999999999980866357856949343858483299690473510231517879951157141892386903545489460447230300688153856410741962708617242422862726083197070576934396668435929900205063108116009955820136477495937233168786815192536251702942127170673987333871569932795280834485695695982052196110221895783085466878700456614613911884027833542909326197182622250344839 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((124999999999999987250085591846328856263276365516601338110070681327754103137946404193494774463101151873674459854025562795591808692615273143003543448164606555320598910936484070119920279183712038139416275795690801242087204907919767962433823922613804510812575788471838985107742290052928718017509313369551096904556461274941172282997036362107228311189 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((15624999999999991504242954596994791465017745447265154537414629279521518925915315305995103944847324425879111966661041987316097791115658771294743595259924604095152490502333065590871603320447556060782758011554538574969784615179002344693360795788576143775252832546019394652576209143747123676535848322795254544526473847382984786086013687848236951999 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((99999999999999998904771190089637391803442557582394199162314966284185959062118745847362205459909641690614894807280687403959573527085303728283516894301799697941063417638017371668525881100432108344943163814526088435967583728110301376549708978142534523134670246795707333708649757545211536519595209603692837077114930153637219829672740852930480231988929199 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((12499999999999999270181822655446638508440503545415595996753960231795892867451683699612620759096323589316433140636855518494430694165675159591319171704056764952408942662349565728669883125051957268358927169338739024931186675734598224708728041107429279928322700029726052912504935004376979871972667750659200425719956742690530327501460669664766975663096333 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((1562499999999999513691293382107446827471055775079776043554411172167669553027306048603378204852270541581946047016434414487387429558282406686509726965747055174233403405165641348227361622832601334406377359951165164590860478741003136488287241761789494654982112284396075368927066400979231790147343836012442283800206971930675195797159798592298743001601063 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((9999999999999999937308007691920933944220855438573826354250070985073088482674739131048860002730687800012487193663553827690049948263889870710676790546729316509844411089017752371678089960069834313772891639907287828163220460180761761095081891617856818638751659596833083488816820771645453561918149392924981687131135716924348100270297359162593618959278296279959 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((249999999999999991644892447028584154708531671654763477492622350288673455603026116482609313967524037692259239588557242926138845471186782837579772834577860211003992604134138103528573359125440790537801347378600905190634236760686824292864713043675288951869557041735404444565748103235455096267603641999184036179168407293708861962501230214422062309892942460353 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((156249999999999972163055396173848976070679042779268037693729652768223350562762059969996250781537063907766433987324337801613427300232697914877881577554495966114986286271483892311752826430051486876694664633246355561362156296661758289535911850218222015465627738182841000186707248675380402013407563955824245699859799256573221699151975085444508791387349926991 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((999999999999999996411447668293246179901145986159404394343628313256568657836784742600367795416307300360514779452495484650806149088573320089349850167685332806340003935146465163507225547404357385954674090359933062571890902361206983966843582558097742155700783746982322531983363637789757407337756789400418876753073339572466609607572091135826021342848048957361133119 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((124999999999999997608725709759397695620197649045091385593963894453165270352537814170911639878033588123316831551266418046999562771024009106657936003148352585692451988917777061292977468222568836781284725212097885006835640041930299091766622402217935445185133058252178044923877644626940623983878751427140201648309987465087293018877077689914424656608136403535854781 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((15624999999999998406578345050968154067653074237451813001596398405071116991518457358354215789981550863069948131377169739042162146132111656274122121959040076563911007121100121926595528530770053635116248196366690146476515837703067251772521808092835370500324933590130941700834232811185714274293911293022641740424703729111913379701908723750749232114364333575021623 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((99999999999999999794587675980773704583721497393750466936623628279119246543235395451187652977424846179936226490640294036896794779979025415234474773448476135167708165251718812424317097558972821129431499606292928434677607142057848969246093509208072858734468562461015124053259717990723503753420536382069376924222671030467561200547034068705817287685965170368308620864679 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((12499999999999999863121033629584416663707161682910610263201612425372497725967218003215562283786580731297098410938355483567928944191589136232005776850332969811990951700385858150039793591139907902851695704324652235664260844140535154896665299597984211809884838974685869569872785643707737459743470615066132861835616987293512720326386203598465861548811519253165264056309 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((1562499999999999908790609492881336961361871153547273704082306661258782983303592567580950172297429077545198737862855540530159260008552820847095177637668822007949978220402325861665475758881796277772258651735889364318271278036178327306693421789933223123732381844538401804039306963800887278934692295767051880604668773773382413740912306548572489442618139151644012842463 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((9999999999999999988241993160815467624076802232315670477919273106325064791381337271021432444080775620185729540550741070966009430000779393793436570506964222453134783087173636541980334981373163254269788468963813516529380910418533332848615638560579298506819714983830966715932639517507004078349544923046033204519429912454993670680512777126789687364432332317052353766915090639 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((1249999999999999992164909441243664850982784565949594108923380827813369995291560849049678323196880819097881391611250517014389671085949202411865259172364096607322739419334935395790667127665597347752808958032251303270688685052847457585815291108437227482624693724983938770932129795032118039186882424952087012183890458163565195674819198830067702865530068899837034644487967853 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((31249999999999998955813374141567809283263705902619233147314822015406338978452579996865926405283307035272916852130236394045197670384318989031114076047887473853132607916171186436896411556564476035675530770835498893492609198323655158385723001880139008484437563765310670510785389802254726675246159568482760315699694927100319672221365794013417716609513400100329574509648859 : ℚ) / 31250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((999999999999999999326959930518238182269780236579981293826577111879153033723459126730537814531627677275051344630664969643165345782674613280130102732389139057439888118692906129299496354668781237837656961751957649499658292693267266505587607766846119625828867305389468365786700218621618420448806300940077986659896687618836292703423231875514568494427471134160393781971986703266999 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((24999999999999999910302300683566975632030764241261033965142720163675262239893694440767033372559454688846072081025007999164597195994873890322450558768372029522967451749114514927500188869143611243639198612276921771714555728645361833547188199062901159254666679448732628345126791903351989422333180550770062009131970523266631909626385874179959260501005723592273618494528088514977 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((15624999999999999701147778745630991005263915765358718821216964912312998522679887872355559698139577347078999302668942339003334262328281912029790597866165060886952229498670523764621345145968695455155122842658860882152650421493657911169153435967700642377642052618845512377736893642282314045575799905959237406328131070792535133513543783757153269154119476971789907352951576270447 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((99999999999999999961474513382794471791304490522074709239927100461074598803364523873182715041604899874901214018003893527344427557946077538767927210504686708786916635802100639747232470837595706835065322147643807815009940332055311602046340256182038733502070193427798558725996507214120060004910121472111004034399146295989808230636649215786329415189522875190475100473858490881706289759 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((12499999999999999974328066276775491509843050379359960216389452662617796917763060186111472465760559737298866507995107729804528009803642212953945136215089377331116635205140911140090531249133884650677452950697795528471127286401372842997576924564138131576203374362795148075770530132701512762918087135529154560478276206574793071171734672949791897381896528167235314495837733004680739101 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((1562499999999999982893362164608984445352993151689793505406774973750539865403604007366769714571818761766029580074140098846429362100217434231184132170410104515251167532180147338222702589724724258179299297161914263946357055859100765450795215763092177661826409168915534039721586997708392343758484464163058347253347082924156660871429505280158595927472914662767585011872111736478701911 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((9999999999999999997794762620544538359806060341974078431602667157492371110103388711024851791696506073739220391604560869398722377844391424396614921456498771897671895149948042719771333863214815854945974105053279203138983994547178091412734562604116079144391999942000617300034766069443446354741060263185105981933041533128752612929872437760825282054863478898777985226224133876559749732094919 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((1249999999999999998530512666943706311753237853514252107619415987656289589927935837457397310016864829913347795775159878461779871672106168470756666330146687482529457323339134787780850709849516003401184345778001790207570754746852123856972096308175727844211721239378367291911429492287501131326207640600763288763046970834351746544621243178944003817717545742103738063056356748476462930060629 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((156249999999999999020797127048104333850738008055051317027734326023978058266401087585376525192076633619022531905051681956541655800461261543686735023807058844139833646678931273507588581358132565778244012070606351636422587439168516991954326366973615039125235349446020295584026450650494381006389987363122055646083123787007016327396715219447233264768034280558216100910474634171317734665727 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((999999999999999999873770007162589920253658700034938223503368270762020814713428073207773541408499704166906714435836668725252267630190809523886634719091446202194636950278175913322430921664279274352962503747354754866878582831875021130556339098022208486304142468680057334871290044581012312791733030524978651511829230397822928316718828209867399970102440395644950652334295647228156634414845258479 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((124999999999999999915885067288351998444291441635110555835230443732445434829076659078514495718450166722465789346644179082751783485202576169228131338988693712987238732683436309680978941910242147558796863727957912676003587210974776066261434945298147561215575779285296563100189318161542787156501238991471767717265489160935636970791249814928689103476591534387030229374182083235719689558564346573 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((15624999999999999943949361149837249910866309803821935400997857337894521876098776591376332147899239697265774439683264911317514927687035519170461372393727820276776939906135784332317672741871989162160254174633955442089673117298074435729911952962294310660353062066429367774709459544172087782505800988928787208615751428662148489913190765389049146402295981238782072984775133519653628072515034727 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((99999999999999999992774468979993809625239677648699898851556303186688833455011336338486165283763931566217907241021726754502165051419752127956794857955513472059823213670873067454489268386985009943237926677002333523334996959879358084534175406309889235964535419049715161905367513441861725796511590400280302991188616977201782239777302445561019841688633790687112620290267417142986913910540157440596439 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((2499999999999999999037035348887467309531603518980355076246371102412362059396669296173003352423613410204767756809042183667044229773220192768329659016423813672203608157125826090143376710806728678306646030643951467981226423092071791344920361082954152662210869362926404961409596965194887749577192459274373848305551239472495259485626618405251953971356628632758595649340717596364722550565068584800641 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((1562499999999999996791601196635558651542908757304829782914447595697146227967542189657860968513374832847187631770488946504712030643827247089418290366752715328613413711798167313644383981264475471422531486210296308876331236481178241611588449893034469712596876895880592381388583203873133450784356432568471552309600566862664205301043652707364325578556451744050901112195572450166752892144687001052303 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((9999999999999999999586403378883825656758344388289230910161934350709255515798303903351286587007931206781879228383324661154458429708318031556374894464231546654176340573734445254162420211739408954160882160918290573209218560980454336116820734432584369755845971921824745582625141836925607046318119946102444823518627624392007217187092569286358336758099086812721013498035197224681713939153229152057180764799 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((1249999999999999999724394683449887031113916816686103930802579450560569665448026737876514595389891505847044807261335491097572499252780019705078949811939139162806279478674354561972642236905440000586708365505711817926694611044172579900281278316999622799928700821843565801235661816170765508625112015297986815611716666649676302612070681092445822317045625634313059722479524892906731795493274539425867786621 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((156249999999999999816347843283886379353326599772873957390215931126837072470219974937324503634516302210991419101937963049762619405926887281245769711437603970432897871029109638547973557326523014003239592616842099098096501197254152524948876972357033613169715412497535991127183101371148417819095141445733888229812267673598409637479523353883196399892838305086797087767542781151916299295947464962862574199 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((999999999999999999976325315810689064418504391130063866528579284168948494979810713731730995526920990207401548911889886929142354974933832444318455334027077962031707910781133380793511095340175507945123055773123870701068879649082186653662935659655561909194379278777170261895045743887458672938295503834850044143029763847822885119006365758520437554370349828246963533641032724338005987591069989892905084157859559 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((124999999999999999984224075195330937885617159503342221152211949507469255951379171899882857810353560258380801873888832488044996153656708302999570125372112489301633990980445742218654680050770453457215645593955991072695119248630775842029087203151610701410733349802771026061021637053510389370281217066043023975824846206736882584002446035321925209045351087187032560737983697668387067694614522974908697568276149 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((15624999999999999989487557263087936794906833115019371374409918430854006277751947681320776611229864420097949326992923629672085228603984546377764030504124021423568019045105444021958424740043631891165407359736654600218358914771146099965728934474148486589354002366092104234041828234336024536499510608646978077579231445051229862592943073133940312093967135883497024367565760728037359747600692715243658582837791 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((99999999999999999998644837402319652736379609852675985783962406805114780801139345064718013914956484400461872061265489017711037541120187502945232701775043969624656992521022855850001368608366986250286788835509383482799883739993113446242320100094344019244195464296484002961134313425862021897660972935010651376791166712413229767097043382383468366049713194518684439629146354173831800735700437291459779922280039016719 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((12499999999999999999096970246570959220575254000599004509429498734817315864377103300194709428332440636893476613453689783400542931186500642547654755341190370305446405229790830429653744380887909506132355284425889330473754567780454296079682256343759437505013438588532661115465978852986270732952526809713804400103864131475539415436970744126434911972262721817912131424861166084575900014920150187780897735088662664493 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((1562499999999999999398256803148031630450622163364726056223451432042332804268677829698131868055052290791086959249315435429155362803421023918256098451742474713907019952788907210488655803140405568715744748178642320370404414611621522727886012877705912317345735092429481373813554669979073661911988945587887112315724698283308606651454619954591430653576400095132974267338049701125992174887218559187585941053549268359 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((9999999999999999999922429137746179242283105247577026102259792127931575167838017250849523834506024123566838018658897856862797499891260652856088065082305291865284990908895869291709928340511534659952666079733392619938948145160945806776356644849500346005556992571795040813498289234809767995444011751772944695458903173785245685098401860251012112741051632967444016008811966459264306105912228731000449262531231713356012279 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((49999999999999999997932386876377367668514003388845158243013806817667070430180415212176112389909990358360354260685601196305513341898875040722959855839180789471560147068821656977159902716333796001084567554460070389568849659681570098381224522280475453533801540746727333887947805373479996565728273234478342489281156879227999586725995144819272291621728148552371470786119103168153225957876434041412778240974405991307949 : ℚ) / 50000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((156249999999999999965555595503706302983349666704201194498729119609344341344335694049122103655030843860314389725633398630400403169548434788280975506851828988487879621130498830143118632365016287619772162647963855336492147612750897102482734222476766993993516192332156051193451132481365436369541766255714155884454569629261335894025932963616902173064123366546302637739430349913360843538217436797008097054972833413328559 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((999999999999999999995559766273729046007527227476556551119452761194931294182215945455877593810959326857089375026053972224683391691275651030135336933376237211660778164616108454126768008139220755470350559070019126957925330777157698925685430707830249305704087811802119931205455574089745929827210676683235127312763076570641248260717620882628184345410536522689462920360405772094748145808521884791196716236550234504211498862239 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((124999999999999999997041193836238192028034832236879691118144122443143177832625963187597969599346543291316558840260777936965333651261251658364332441461244406073931481348524530262512375348907867752312935036557605401905771614008777773284696445749401808445287238682114082302113035999088475575161574479183456327230869956714928472863309289086390937461829166808532477026896169307226920050113826013092967691154865017076077989341 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((15624999999999999998028366779311727706994147719824909583035496813991214169802416947741481891261946676166691279550067083087155604243987731374202070097706695875028737082853910617537618377135092609251752048828571976903296595896910735881654057952360699191456883412707546074151608532180440425100612124241493516859362331909876190654978444064755232298185132859716561001988276308278078276140010035162046242484218598542922094487 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((99999999999999999999745836581274524322516866027985573542628595503559062210284222933839889347333122828626652915866355424113102023800309540615976821403389194232674602920790664022670327553897135263878336351726964846198603859015283844205159739146911300507807690435365146982131482516471146769239366344025061922509871265980075691691737336942519900115644521095267547024349986800475478614225601207332891234096371973255570406373422599 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((12499999999999999999830634971949794073667475562964782758699130507788259032000625329424359313664148474015873757441881612584365958329845476680662080771818489642426245953526287469174692921075001229930995434933316488933663340995288286797033949869072875044663559635740526877887182511141261383377472501828965861898940128867921504209850462192254990734147843756160542924861127322356072800208057190629470889714887638932067113213774869 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((312499999999999999977428338370209796675467990095819560999099118927714959951209419558365111243879359694047094627960647127793463350695397104022429357752339543553751286786513384545718164941719985731500758130884856668218684920601723341536441466734547219412494879356551917981203011358065236573030758719923804816689233676626905964382546150271738364212361492346477845580426114008552383758779771337138888170820064704624930172706931 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((9999999999999999999985451431748735046745187928307922215153603435219224279978879204955929106130695283833418239557106050831658072944353518414399129233951400867072526945788978399321672219512625919639659851109203194761254283493893862526147548628508349752367420008210736378404188190725324912218030568898338569506387541135965512668126736903926781602519608032014209659220817594446016871356887638708942027130910428121122105631221082989359 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((1249999999999999999990305376219522941199319444064632918051013943710829324109265523285905683985748000006718657675991800560136344928750357007122112950012395726239212630942514963445014939262569911160426966619933037170950379924726367980027650061245773391156490288200024579147203084663602943802649908643975337334621439083098623787052136632867572823955940367327577789138020442165690630203245483348779868533134828892982552722240835273613 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((156249999999999999993539875140058183455276160503039210596508214937578967286376552970486052871596820360488547341896338794939147499830751241198747998487857940852792726890767275255508194912549394512364658522145058633995484457003313795047177153170040608364496846070342682584287894950842529271196996484759520338217805211794371984800968420993204098220014359919120024849929477495566149521998209300639263257811269901177437999937334401191 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((999999999999999999999167225404729342810741302204273775517607414235383617010271024570882337964027128741908693450488307455654939753407739747558620556480612137032098514903906912555571839517122220266093769537341900071328956441473978584859211831044446448175263488689990761036234136225308323300272287794309798057115129242163801910636242547117672905709824883360525375103458819923684451733339605327338550575000443816081150448436726011393898519 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((24999999999999999999889014006048258110253190961358270463147197097200367992477747119282367605654151107331661594968516063470803369697189741672338423489270685412993835735766147535520149835032595495431285343060087184609573905476153264007494890105609245402625177641095439779713173964225491367905268797085998645529774391924346543877738282023321097137624296912438838012780702251672955753624859166066226881834358056322331978058981478045498689 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((3124999999999999999926043175156503492811968758641836259078604372167357329147188487760791369472806855775964711868259166384762910411646324708591735258100881285048573157266534047761533092405217432957227631653901317784556131456821548556879319428858885335485607242145590778972399620406670538759138615691760540741035088999996331614213655814648370666658354375459402322366099195803611205333032642620860675415099654393181019508130822236143043 : ℚ) / 3125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((99999999999999999999952331149392112311829642879474835184403365998247593621284923717461875907398876876315595521799401207069144406424812430890002999273506719335854351091614535581593487665799593010251473462086987701982940795666412008175926144420815159140000257356103761152475078191672873734030886025634087150587327112950698185166729159639562714795736086148439832996297086311251621701668092348542185973463600404476301132818966633618198145126079 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((12499999999999999999968235253130183797184232774490009945622121338755523971649002698382670845188463628253448026363105919223178918716751938216864796860284816382747636185211657960015699419112267004268576530436523409372204688201429444157323844409053906863702805564608493174284652503913468834567175243300612080625032202267557888222079374431890538692739876388370910837752637097564142848642152908339685498926577281925378994483754393689256367859261 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((62499999999999999999153327253320949510974615898824512259416148320660920597911024517202372413357315055906179621014713474977572981923334883851777560768326876808453451723801333882111073057145957025752076945634862241673048311794867087189513696942198181215030657509343848465819519346012535557878328272823219676552347164044420429614742521211938703961340635888739216898384325364116366295462607733842927025730136416368164123142235986348591907151 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((9999999999999999999997271387322353900841440588064019040790433073105690506475970318511235238815419111277181003263319524493844894968162688356574661681414798121503638910835107631225992827478034503499804592443321263049205514084741089759998188432791880524332754731320735392128825950769546965409661946993320782586769191272410914817128743826928209357622729307222844480541041517542354077825183274122903267307029950752627953143690469074939280025161888039 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((1249999999999999999998181754102121253004549958566107731782418388476642577923503472954172034189664356112389629050685861723071440071643946792281781429898371888928575806652837843841327205437805385872638377000787532946488359165414634512633533966112608392301936187130181749301648959228389028051967156087310052398760550433112325409515366949358474137438850175534938965845305444879142737629755878523293264232571139751290937363522459602846821229541948789 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((156249999999999999998788389863726147612571207570757762849848539128999254381525023985930640902392634699483532472648497539637736031431124170986028486005666494498667275993833037302139219192611846930978574512762691376848958454504685917760855692286116739451140062432124261946842203632794756070256962266351983619405376370379666019362838298006585667290555227778537203052641317561061096768303544062383585081307579482050248359333656011115620180594292319 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((999999999999999999999843811481718859638064900701372513913885179537642830281191017001901616305033405348617117807795672901552175632872600444218690209305864459272989794895112395919007055437670173014832314676048152418199572831724664718952056304081440033093331213575530214580846126247999637847014459507844674916049255277624073175047266425397197631839682648274742840910649757505641889768791315794069105923921701411031176665897986140318599327920291633240399 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((124999999999999999999895921785503045825955360066232572308429853413323943473185921232378637551662663553424245769342267049743453537309172798354708121973454036476141219203915796092911793879155954516540349055457914450209983674110872037125453318606159816296143306689341567245736053830843180966195746198812759990662844262296856038579813907294572892306003391226958082771639940456946380674058157214345935935781379793740688424767671462511673751286483091645933 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((15624999999999999999930646211302835883629207137618076478068156179250268201702806684731060411198336119308547335688876315733647284568175015677688037352417799168673971761244903485559822219290959599082680999808724344393528379022240843011112232395263628327276040652414327768553570004441793421089823708530973594815439529211590008874380523659805351238429215334258113690493778452092222102587166199951732043517462953329499241199530879661653933583546919649223 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((99999999999999999999991059613025069244542472981047264068944701561914213248125655004205850418916417155560192440436032112557748085401260522027522046270876987513245208849591128654799882860307678373542016524371672292570161748460751533177534654901925708934295371996276925012822213112561747270000954676688537036869575421346479572612880577456160989644135274469894554956566502769380447412255383707368309692191202110468835583532666624657976944129485413378313679159 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((2499999999999999999998808491774787330448536495466326850829031178532096146971565283558164407443594364197430338331938447526311934128785947086996115441732370615471771426373205576416038654038458264360813010462530257287376299267040071168108810244057674431207348441074828927804682412488993882680453647009494586302081131497593250850816918194683498396524808155727616723015641090838850830511532971507663788255914654330616608117867582530681805445865145948034627873 : ℚ) / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((1562499999999999999996030119163817268624708597570437139830292427504984928288348722830159926010031448817385383113413468243933585397382361982996351687772680416998281775529210610799264350814341199053667390034797273913164134849500931383998721607208772978018738308332740048650543002123516158346784583667684305217788592021345611418178252340808654935943111382835295555845928465984954615009977504872495555958840882836331709203685889259677525135699222749882988271 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((9999999999999999999999488243309167988626855695908126442570463662105531480535960618095747083829194634401420975482998914154918058156453553541377389450591269642245668999759445795329400094806871817779918567871558893699008628643641878510615261181241129505108001388438887464658956300776146975482124646648328548527451366693293837215933897134168111208219947245931234220268823185022106190324910418793469415090716600005346617636993370262047258258915874547188053308740319 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((1249999999999999999999658984386032561903276313328554801659934935899375260408164206030585948164991997682949907396164957180649143132916556682503227523635994357417974573643690044138303024160432671350747880111786898148761296861529054792229891112802388851365877657147668372920618322641437046463374922575662582985349831880928474639727620224312922911101701534339965021738275457674027394223579638382651201075456745416437706770697171970191509117226585700948446960628381 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((156249999999999999999772760021483325615319804868081288197502272323869428837792142305664833558100206277856381806745284395156677146269621451837308404202202657388318532213814245648545145293968798522923060910333210084187002103940443258872190758068542358837357323158261728204613948883412167159344014877548194585963168847480428908393889980893538046759436864264802231992909453259919328273469491548544969809336687492396993725597447329799183000769534759177056472303063 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((999999999999999999999970706535260084836989846889477065699175910482582727477358921740418658825466930067771738057622340845141664566933557858261983149541294865591784339215230436770450190826840149721540318743535902634224952912190704767826128165275423494001887107475630357364543317612727429023572296898796974446259843680890832536077272205856916853669718000304349778002407707933850380440388197282156982789207708900906045740159137507169847109998603574955591359445604599879 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((124999999999999999999980479925128606589410476033126547710698878476673898945460007017708715257191612445972919811244191547958194516531299385685534726535029743698508875953771703898215260872165784465716309843162107753156302877583428186119683285542608946125604433998310196118495122209685860968574041382863338751612153378011000141778247024030946536091944431209597053084847219613363766235730105956151657374424059628320996691748163024838040315950196450128476238349247709909 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((15624999999999999999986992554973330392508123382379836499459999578719036943413850508209956788957572923725628534181279884521272195735957455344818358368251142352622726953905789988266182038236200593250389852456109498188470487711450567764338385459317630706544050789735051767040901475367481862686350912344987014608519925912081391187569794070719830031039099780917782003056249218053284968254633316590940381804090141234604471638516579509817638862685029799238643534025606783 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((99999999999999999999998323212784822516154135825800556717686528291933517903531502039343304449828552544009322058156360412316754021475843785364774177462893259401339327361019005431177339373119157010210689385198738602685670529646708131615135402308530516220162019919012557285903824043470130764738301846784037614278359712137872145197599138335455777620908328055421285642635819609841529626788260800627947851837038465196762964212449190047909218423430067234033005006025852901673839 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((12499999999999999999998882651388967935069751631423007927195262790748001009322093958545040780715399231256715530300112245663870769044910466450657996067343467820239317603875259113763452282442530223590063921664625423482073719914674472987645255068929311727116046109714129490842207435402533617905497333520655924868307992786205841970604378876630531501896298541538510400000883409142616531971377608850302496281916373333369846219233951820198717822609718369318498011919798185573453 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((312499999999999999999851088154279563356811262039701530539021836308560184619561731408478974171281186506618282369054880352804116618376050280639697793012256158950304645050494700022110142413030209140206413797860900323641357338707472906068515395604356357573586033816610542472954566020546032036795137654763050110966545784907568254106378635328290833971832498270090502033195654159413644088230767605160283574326406020944916369516883575726101831256801387385116247803885125117691 : ℚ) / 312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((9999999999999999999999904019023016025647178888804649667077094565958566498316046708234050090012636176171637603930928226361423316943298774118065038692153473061392064437472088889886022083056713666421470071098160996356330466787507220161781965563542595278958294182184197791602420792072273755104385136011765097078907588282483939463255772277459824166798413606220369811470116950286938997366986836488744362987003918786327908834484804087532371571775560478543283239549925845944712218199 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((249999999999999999999987208369580796096432410975037380428208975500956385219380539709040218335269815594641086211973282401047631059081779047749923454249260027462101486193701462086492584690097741120238054661326495665313578875892798646874951250778573180820495760234424500021234988036427440542832177108839722662699868309690411833143718589947439715429955951918442559774028580507482976660212036476670479512223538166916913283453275410228873522765824710410116350752652217338871101697 : ℚ) / 250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((156249999999999999999957380681947591830251075284614879645879565611650492765627056620051983539052847754665405470131396326980732769442649707245584981424075423475144622649654494462686318695291481073765517584516946293739782075418121240858985319393421701580424583604935298799545442133819390899794827359386476117989914988237956699627160924620504667868864556995070094423147870679864801629696268288232301684782193822160834211232718875100057322269810177740037330550292505295761683727 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((999999999999999999999994505952896460324070166774066951593159970050034304930108829626025261202413307360240708086610262605154232085151365129292160879777556951507143160465339840145965790056249346979631368339729833592432712249383700789280561490822741696362851717282405665789114168559009022015930109570449445921893749260877663178816223660934077795131707993233660188378360964351374675148283693507452216081739091315248195829594744670774440481140004857352296075915077305347721272081928959 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((124999999999999999999996338971403938180211842124773643340317218907087919267779358318160900852718436528467998654705329005095924942202891184591841760460072444175022507924245127087125043042432868218304032463743368428401166161961460432970227005676944006485792833278510935855981620957590964052996122636279002489115969833777538976290518036656559805395797530767687748846542828423330039855882025116394085531766521561147853054275149274250481877702569336801868216945257113295008493409448701 : ℚ) / 125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((15624999999999999999997560427459853817407477093105492248251957512996620833113745271707500338416555876428709457252045105798885173511454553108542601427625013262536478874010643689043699117339332069652355845027733786952356174470899178425959938003388763943551759709109969161735393434453037564797945848354701277746458461210121630199201981693745094546680777374099648236402338494157488440833127776177063089759356244968846257376866922295218309772658172348130865631514750080211804325103351 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((99999999999999999999999685515249746285410100416314366376144069845634013648504359516623311976487340126607538371585658041781633398786149291365812580919347137461220381648196517789795227788609768870461079155134475404664440881866972416879208620296184557441505995148962182715434684122486235429213855401922096734015120101441898318018619458575527547071134097240687942842965759960437037780162906900060072300734827325976121977481832779699799747580935018039702779681454940035408913335241695542119 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((12499999999999999999999790439061567556192332164972864412275545468150116252011358634924265745042244050603495778777890941992693465550477380817359486937529258719647961008057113988183247971614024555543620182049678450921121252648485825281610526853028301319590236374737452884852719536468889141105124527899250694624584235473688612282361193825633222676159644324888083666704277481223991315693978185298883173070478075071469383837809096011721869508435396302151649583708232534440620564845776690229 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((1562499999999999999999860356420784864910571084285106756351145706665355356485652284405421442740150012675466072720421232096007683093643400375075172886490558238447301010937744861368817597966295321483515021246241314910810479451882000472191993813693133589148190804040444466249585200483162435874010589768945047500188209927023470304291117632032824598186127017576969837323311237988340244677231439742711813149213131962476034763503639450573821170716475974605753842516437230167333625412258534047 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((9999999999999999999999981998578410727123159557930250645736862702033936575254038043091035000846111836187142103927934651969622477379917971587070477944404349495417715865924416874805668633847811779914062631919052506638397260518947368114582780634373900252509244668321744300814196753855234602203630297061422739151759489726635701621703796428321772321898786860154218536274203065895376479574304953866338598566362250966199198113037590142796237351280301367610626811746162222566841608222569894526433679 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((1249999999999999999999988004522296412813431440629366857869319873249760882418784217078957389304471226881937382995813182397191270206809088762452365147125270744389653507893134265931326893540676784545753640544958882550519028057256288102587640948902842780314018258683585868334548405845295283724665493326777181316062781213303931220835382447100990223905321258127784723088319950510333292197484123176732713808536834437582268263482319117528224054210539335723523925005383609184338555748169865234368173 : ℚ) / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((156249999999999999999992006661525790433273284433773411803201883468284167347995105866882747236348349409331875661200657429293622242636291277363968853849289755755335689758106851521575740385716144338952616704096793133305327511851134842894506019133089546232355667115185476006756393606915259921810747885224559329924054813004645121579315954172971807553334764582024609697578048270004339575821781318814125560882602890693761890946586436155898940710494506236981050623535060562651101864648227085754887 : ℚ) / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((999999999999999999999998969580626808431256776255485477212623757927124563504116391624573934483432287615188201170938907413393160227703884611615501228015649369467205473881379546330751278270082594094060859113678484532488497589365066298246832946292196424353881674059404965522905436387427483864738001834092899011785864951442354196527947011353566569477808458662087623234871657694917245067312789864263087720537141607556208299188384697363799422224635730583399889331162071781948580496268123332587590219639 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((24999999999999999999999862673371900131177977442270993664371352694555188441401857416018394577428152569043763571897512179819660473167722650314236061337053207990120452008759744505596317247063906326083575300145811757965400179594054117933842298052235149315834547510042570233265497866338707089473527762453976345091737500684663379007543934491241729006343875221590302102679104277259829848785956047624423365530174004549204281498060959501706672506783585990412439014826602412422199929835119502502191758561 : ℚ) / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((15624999999999999999999542453295341741142854384959583528216322262235861284373013538864962635325464816477498329049207668101901665079792840194350586972070313377958271380890935678436199303194714890574020749184941385438271439170053674665151050917127988277620149363791417055261030814428559703600905786424184002218219665984730593620845019236742743263259469685944037405352933944861048286394774183889312023714250967491235856155808083782050807076225842061158382308546027513555420751391866763974945697583 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((99999999999999999999999941017764659141413569129640244201127796527506537139539126372982236583766147575380987823225713999250037884593998059053482905792843785557672308530444046611518533919457797768538137636526070133124174090512845759977946964678711615526440540904834399631496630084252736603901467962985311632333634695685511796563456214876889504003479233982276557641587288558114758024898051404620283404211266522758124919253842328461801242727560373854324393065205048150870518696186883647680646251762355999 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((12499999999999999999999960696432344599737430508412301094051562875581003333755197650907868486684584674672648139871813856541201987603107289360242051346182638982104872666420253924015444436533488960814460366195424806495767204175488548467617123824347733039786441765915307602221795380656544803417021629326096940170066315177694922943104068832600805558456985257019321623260739693001078656684316674836355284005580265873545836430361140572340644715322502977477469928181247785611513542467097686377712852152592221 : ℚ) / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((1562499999999999999999973809568262402409554294470269889154046399804981201098095005008880639734595696185600743547971531977818609336351863836412793841375391880922139667598193636727756744435894453533229424345688781323711880438353512670972617374270793785478688675406922190896873059931063785748399401037264299688865334223386720611085344596295426938557756335498010151484386910300640238105761687729074338548411713707770934874267032575396823621697311747907567434583929317618721436843856200910774825700975639 : ℚ) / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LaStrajCertificate
