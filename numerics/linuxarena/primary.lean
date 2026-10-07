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

namespace LinuxArenaCertificate
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((1153 : ℚ) / 10000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((1153 : ℚ) / 10000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((1153 : ℚ) / 10000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((753 : ℚ) / 100000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((753 : ℚ) / 100000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((753 : ℚ) / 100000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((1153 : ℚ) / 10000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((1153 : ℚ) / 10000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((1153 : ℚ) / 10000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((753 : ℚ) / 100000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((753 : ℚ) / 100000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((753 : ℚ) / 100000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((1153 : ℚ) / 10000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((1153 : ℚ) / 10000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((1153 : ℚ) / 10000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((753 : ℚ) / 100000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((753 : ℚ) / 100000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((753 : ℚ) / 100000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((1153 : ℚ) / 10000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((1153 : ℚ) / 10000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((1153 : ℚ) / 10000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((753 : ℚ) / 100000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((753 : ℚ) / 100000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((753 : ℚ) / 100000)
  | _, _, _ => 0

def kernel : Fin 8 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((8847 : ℚ) / 10000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((6779 : ℚ) / 50000)
  | 0, 1, 0, 1 => ((43221 : ℚ) / 50000)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((6551 : ℚ) / 12500)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((6779 : ℚ) / 50000)
  | 0, 2, 0, 2 => ((43221 : ℚ) / 50000)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((6551 : ℚ) / 12500)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((99247 : ℚ) / 100000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((6779 : ℚ) / 50000)
  | 1, 1, 0, 1 => ((43221 : ℚ) / 50000)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((12637 : ℚ) / 20000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((6779 : ℚ) / 50000)
  | 1, 2, 0, 2 => ((43221 : ℚ) / 50000)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((12637 : ℚ) / 20000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((8847 : ℚ) / 10000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((6779 : ℚ) / 50000)
  | 2, 1, 0, 1 => ((43221 : ℚ) / 50000)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((13539 : ℚ) / 50000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((6779 : ℚ) / 50000)
  | 2, 2, 0, 2 => ((43221 : ℚ) / 50000)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((13539 : ℚ) / 50000)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((99247 : ℚ) / 100000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((6779 : ℚ) / 50000)
  | 3, 1, 0, 1 => ((43221 : ℚ) / 50000)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((7571 : ℚ) / 20000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((6779 : ℚ) / 50000)
  | 3, 2, 0, 2 => ((43221 : ℚ) / 50000)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((7571 : ℚ) / 20000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((8847 : ℚ) / 10000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((7407 : ℚ) / 25000)
  | 4, 1, 0, 1 => ((17593 : ℚ) / 25000)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((6551 : ℚ) / 12500)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((7407 : ℚ) / 25000)
  | 4, 2, 0, 2 => ((17593 : ℚ) / 25000)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((6551 : ℚ) / 12500)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((99247 : ℚ) / 100000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((7407 : ℚ) / 25000)
  | 5, 1, 0, 1 => ((17593 : ℚ) / 25000)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((12637 : ℚ) / 20000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((7407 : ℚ) / 25000)
  | 5, 2, 0, 2 => ((17593 : ℚ) / 25000)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((12637 : ℚ) / 20000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((8847 : ℚ) / 10000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((7407 : ℚ) / 25000)
  | 6, 1, 0, 1 => ((17593 : ℚ) / 25000)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((13539 : ℚ) / 50000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((7407 : ℚ) / 25000)
  | 6, 2, 0, 2 => ((17593 : ℚ) / 25000)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((13539 : ℚ) / 50000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((99247 : ℚ) / 100000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((7407 : ℚ) / 25000)
  | 7, 1, 0, 1 => ((17593 : ℚ) / 25000)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((7571 : ℚ) / 20000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((7407 : ℚ) / 25000)
  | 7, 2, 0, 2 => ((17593 : ℚ) / 25000)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((7571 : ℚ) / 20000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((1153 : ℚ) / 10000)
  | 1, 1 => ((1153 : ℚ) / 10000)
  | 1, 2 => ((1153 : ℚ) / 10000)
  | 2, 0 => ((21730591 : ℚ) / 100000000)
  | 2, 1 => ((21965803 : ℚ) / 125000000)
  | 2, 2 => ((21965803 : ℚ) / 125000000)
  | 3, 0 => ((307550538577 : ℚ) / 1000000000000)
  | 3, 1 => ((324054225453 : ℚ) / 1562500000000)
  | 3, 2 => ((324054225453 : ℚ) / 1562500000000)
  | 4, 0 => ((3873899614790719 : ℚ) / 10000000000000000)
  | 4, 1 => ((148168046795310039 : ℚ) / 625000000000000000)
  | 4, 2 => ((4374832355942603 : ℚ) / 19531250000000000)
  | 5, 0 => ((45802389892053490993 : ℚ) / 100000000000000000000)
  | 5, 1 => ((8800187700384135986379 : ℚ) / 31250000000000000000000)
  | 5, 2 => ((56808940826279992253 : ℚ) / 244140625000000000000)
  | 6, 0 => ((520513743374997234815071 : ℚ) / 1000000000000000000000000)
  | 6, 1 => ((521679843132241338682450869 : ℚ) / 1562500000000000000000000000)
  | 6, 2 => ((38622254275841702985121793 : ℚ) / 156250000000000000000000000)
  | 7, 0 => ((5757985087638600536408933137 : ℚ) / 10000000000000000000000000000)
  | 7, 1 => ((30404093514134182862490812829759 : ℚ) / 78125000000000000000000000000000)
  | 7, 2 => ((10658895792829342401793390629173 : ℚ) / 39062500000000000000000000000000)
  | 8, 0 => ((62470894070338698945609831463039 : ℚ) / 100000000000000000000000000000000)
  | 8, 1 => ((1736195239765499017155554361255384549 : ℚ) / 3906250000000000000000000000000000000)
  | 8, 2 => ((600247028025685134211971693308106091 : ℚ) / 1953125000000000000000000000000000000)
  | 9, 0 => ((667979999840286469571810178953506033 : ℚ) / 1000000000000000000000000000000000000)
  | 9, 1 => ((97239915110998125221551899946282732069239 : ℚ) / 195312500000000000000000000000000000000000)
  | 9, 2 => ((33980290069054808352453627154557654272369 : ℚ) / 97656250000000000000000000000000000000000)
  | 10, 0 => ((7062619058587014396301804653201667873951 : ℚ) / 10000000000000000000000000000000000000000)
  | 10, 1 => ((5354189847945971393466774368505458580287852829 : ℚ) / 9765625000000000000000000000000000000000000000)
  | 10, 2 => ((1915886537596925600205468247962381819664428907 : ℚ) / 4882812500000000000000000000000000000000000000)
  | 11, 0 => ((74012990811319316364082065766875155680844497 : ℚ) / 100000000000000000000000000000000000000000000)
  | 11, 1 => ((290565999315909011234520882044031413149670610344319 : ℚ) / 488281250000000000000000000000000000000000000000000)
  | 11, 2 => ((21414173583124246856047600704064859682180944285221 : ℚ) / 48828125000000000000000000000000000000000000000000)
  | 12, 0 => ((770092929707741991873034035839544502308431264959 : ℚ) / 1000000000000000000000000000000000000000000000000)
  | 12, 1 => ((15577509772822564472313045712000159206678208428377942709 : ℚ) / 24414062500000000000000000000000000000000000000000000000)
  | 12, 2 => ((5919617915411986795598550565166271441085703738919301363 : ℚ) / 12207031250000000000000000000000000000000000000000000000)
  | 13, 0 => ((7966012149124393402100732115072450211922691401092273 : ℚ) / 10000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((826629708590423666306183931083741612031655534512435247236999 : ℚ) / 1220703125000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((323670290858982902436353329774725606169907061586609959404081 : ℚ) / 610351562500000000000000000000000000000000000000000000000000)
  | 14, 0 => ((82005309483303508428385177022045967024880050825463339231 : ℚ) / 100000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((43491127884608248179622074023805315251500366600218429937161906189 : ℚ) / 61035156250000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((17511509105693440501455432638990769299012822413120065907876445659 : ℚ) / 30517578125000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((840800972998786139065923661114040670269113809652874162176657 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((2271750172601865233203369071750899073602971753277569554777788645619279 : ℚ) / 3051757812500000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((938298743634222691750671555129855178622928384835860549579098856099497 : ℚ) / 1525878906250000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((8591566208120260972316226629875917809870849873998977712776884479 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((117945354350281101018719431157355767889019542456154389742365973427093935269 : ℚ) / 152587890625000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((9968366624395155082855296810651598750640713985072309397945850569763780199 : ℚ) / 15258789062500000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((87539586243239948822081656994512244863927408835268955824937096985713 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((6092094662715706305733550169091481133467986231967913271981065390271871005203159 : ℚ) / 7629394531250000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((2627355979902371748972387194480469940954188562366506957202318255913026628947553 : ℚ) / 3814697265625000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((889762719493943827228956419430449830311165785965624452183218497032602911 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((313295303169697395315294668624889701736165488430282083881106473208393924130240461949 : ℚ) / 381469726562500000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((137570292675580088965910821927450416098011452775614247401684521498299503501688398571 : ℚ) / 190734863281250000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((9024730779362921039494577442701189648762883708437879528464934043247437953617 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((16051739994308069481712945178253970953487880387632286138701460913307992585528946802340639 : ℚ) / 19073486328125000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((7161126628660909617454925790843828361584408750165862304383027220493740126243099093775449 : ℚ) / 9536743164062500000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((91371793205023762436408526635577424822605232168549920188329271480610083575649599 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((819794466870590569863692127572347077378614468790357601900613239172086961175247324036522958229 : ℚ) / 953674316406250000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((370866639693902636450816803811958107583193736314528374471382916765165041163002593678520061587 : ℚ) / 476837158203125000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((923666254484845226274906235144953477405588488995161143906149064788957409393772002353 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((41754049560542818548213883499148551073669444344312868856471279348809018419092881688355767950823719 : ℚ) / 47683715820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((3824306240076024503427761529571186555113130435258634828285584314369349051957293238062186487720477 : ℚ) / 4768371582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((9324675353427425716854095462327403414607241362140190640137700776187906200906700904816991 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((2121623421622626491090406898820231745175376753275709846102494850390488144785897274154009149109626736109 : ℚ) / 2384185791015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((982082441911515647874666320975652168443722611733377044960165614563627978141067574037931641996414805243 : ℚ) / 1192092895507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((94025402851772435317008182555210538009030264330854266593298238766934406159421582904915919377 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((107585568730634000095360441679327580422387380828010213867776919733242126956203715965034850160244940838684399 : ℚ) / 119209289550781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((50270417485057384005624653069410753735374839427963787534049566670878159727300744769757408522740856571639561 : ℚ) / 59604644775390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((947142739029630735249571391065947629765890748535067696550909518371068691292402743959791138728319 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((5445962857667901349541916965942430262120183599834419228452799694482503133813773143520412337080340825843845747589 : ℚ) / 5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((2565701217217035152328243834419066169121522429905405482291691697345643362529404929621697311418094056121844936739 : ℚ) / 2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((9532371812195143114752958096760438680538835452289743911385896509028844711863887075812272204329438193 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((275252762495967244982592069473527390321679318122890868260768836141237695803476351805685910446900576297184067460994679 : ℚ) / 298023223876953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((130615009915744744165878566524604843178234088142625140525065351399835708066118259527724735780311141955728601396490177 : ℚ) / 149011611938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((95862893422490431136219420282039601006727077246407364384031026415378189165859808959711172191702539693471 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((13893505821056235296614645829420945581275123014978278288737052543608774988199955492201815971237160703990364071162783384669 : ℚ) / 14901161193847656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((265384678028120958072266508013006535687280933388906434228898568946110673473231456702689523673848816379500358256819638211 : ℚ) / 298023223876953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((963399018108772844262133211235204350106514452398965952705522490696850839550361729866564740379992368668137937 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((700470208654301184386011207061860939085045998529264235031058808370377163950352269957287197527730827193304797727331431768666559 : ℚ) / 745058059692382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((336354829644000135610293915432162143037821509227495652154125974363956450258325121219259690398654760662684116815714131282549433 : ℚ) / 372529029846191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((9676191113208313353187092519797852885392333360373651783585757475195039377502050224129498258141792485607016328639 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((35280059203050927046206314249167629162335247776946382976762773710671453727936888884560806179496549196088150367854442592288229279349 : ℚ) / 37252902984619140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((17023363871356197644330986719103261140731723334784922205570129127569555312169686978794497738454968645698011971044061338418297552051 : ℚ) / 18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((97135262778553948235646207522651604477065973239225697329383196383050513372760638332873671089780438120165273459469233 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((1775358804836326403887856729661337679419762948807329349477307834417793305973835556071032544741453487566956044086660837077602298753252039 : ℚ) / 1862645149230957031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((860303479694537386944680268341951975703203597541584131434072428357605830976831142003805088796807466662955178987854198534665131938604529 : ℚ) / 931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((974655669801866780040761997952898744808602665247429744273053138400847891808813367330933368131287536049102174295924304351 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((89270526753610386581343450044204528183205266826277230955956979348204222079261020285373931798048827004155492938472146283233812606337932103629 : ℚ) / 93132257461547851562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((43420720903954662170632874718481450408555105944914067740217691593723313786098980526364023913304413504411184346416534649874527559257076810267 : ℚ) / 46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((9775778710737115403020621395889295195321707779444010947583701115432301298832571860776767507857500831426406935996042320593297 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((4485767425801307321263373690487641419480344227381004925896566394429921858454153951743567480571804359434493363396833595240410052811236148187743119 : ℚ) / 4656612873077392578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((437805655478108175308779852864382250865684273831996367439614608489779438363753021210881851648335351037198333721655075142079595335032913547526933 : ℚ) / 465661287307739257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((98016314253891259970523437489432594593011148724741164853273003768229569590771763252292062142015309855629422162756986410288898559 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((225272528611415147601493987985167211491527204844794496886936068462092328831579711180890643364065004527707899168869085625532911609554348526729388369509 : ℚ) / 232830643653869628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((110249228291173854610671448439872729388890743987474224409767265355149327796904987342195048489086993198305595194331123809691780468465166630043026605123 : ℚ) / 116415321826934814453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((982450332204175976959220851469010164364369632767785085456906264337527002169557789493027873770409446292753497873911058771825885551473 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((11307171987310729101840797134217774395010153571538402417822289549022454066453687912749030956413549479763457796954735194734470044733124293044600387343371799 : ℚ) / 11641532182693481445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((5547822966077995246615351553811495391795251724228660898523606457885002127517409805339331971534644431212313081651548239596137263855384412582178513780811041 : ℚ) / 5820766091346740722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((9844738089010344868158226872946332924131578141096594651037249720594101388194077763644817599246812371351990195690491136954343609473881631 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((567285236697500540873190717485988914096970746785745934353105850918343186931694972669926245511678020318980351942148987943923599953868136821182743398833167228989 : ℚ) / 582076609134674072265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((278957921794430911204742544145562331799547934673094609084261315516751002129050047780401807044573159953244379993035099945827905387353807579697888254943972203819 : ℚ) / 291038304567337036132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((98626397873474521048595833144956207379792071814281572877726548278096014981353005974965701300536549049351057261273775088635077913015430789457 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((28449500698620558948818109582216236859213349676533602539967964918805057766719783783125739562799219083256814484556587430317512600397468761799052239731088237402410079 : ℚ) / 29103830456733703613281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((14017295184477232547897794802724476093415155950849527050992273685524568746515819643767361683175350302617544221270430580394542783817732362933750476493615875628696857 : ℚ) / 14551915228366851806640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((987847741986629087716927335833427566689020459340949075249246772616315444540030043860521559405846849439608803590489088209154534296447516194326079 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((1426246070832039165943759837395033915219396123034577198431422043237705250880778722734146721490300187438427429960857174794169953055013429992861861563334264931293691274069 : ℚ) / 1455191522836685180664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((140787600007139676912845509120827816447819791668135170565951371610491307758599813693442148225172338299516827171346402699624839644510956408166504841118507754862195813111 : ℚ) / 145519152283668518066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((9892488973355707539031656140118333682497764003789376468730086197336542737845645798034034236063527076992219085365056963386390164920671175771202820913 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((71479132723422116397727662831621058915115152915310806597225947784922726607484771658408557154208071458528560384465884025058143194234434292020602573260548696754171726686969959 : ℚ) / 72759576141834259033203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((35332967115908997461422339535212253957695003031492133866449367881695418567244393222379101903333222965390427377975041720645414880937297036845861005297595969658998480667647313 : ℚ) / 36379788070917129516601562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((99048849947277944597813061871626898089057718141524613618855072587836393601720428375207100886454024050150162248224658955079393789053177892047831356617311 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((3581336937572808393610174540356891242212221219426238466555487410675284357978430119972564743543166277855748462793753631522813274996244573707783151885029584756743043115777793336749 : ℚ) / 3637978807091712951660156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((1772671717022761600835575237479795551139714314309789366690540053528257633688700923596463262411901968553548624489168620956235234640354188339455068592542095985279670520342224841531 : ℚ) / 1818989403545856475830078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((991585175483567975856852158378283167393893632398068256686010827184588574194420629835457221542458750771678485410043557775587396851753464810947164011993350417 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((179393336064113971980012540368910538506236181750951379831765160731080284026196119426879871427084768228080968240742140075825898231242498659313447454876580095815290439490874410223803439 : ℚ) / 181898940354585647583007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((88900189731764681458471113126387579693467910435594396978149837574317104338516862596301943406649415285602690765189220245655570893952686028365615849509600323631246207287327638519409609 : ℚ) / 90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((9925554047503125882405571045172671181933776965825709866901137788102055115898039312154290038986132568077039560422655355640621699947462903182449560014105171139199 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((8984109810687896826693149464501193637587305678746836031242088084706697968648384319225302747872283222293225894654309496106144514731630379451059475469956962164938781763605546337581769289029 : ℚ) / 9094947017729282379150390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((4456808516128764272253717472977593737810053294816121322487064730425033297037088983908379388366783204504612009023124935105279345673432398163607264579115625756992885334920817045471658574947 : ℚ) / 4547473508864641189575195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((99341376658260154681642087036642621946568124816660055192474366011338881610349953794629003974910314829777568991059231931352580179435204304455131257444788449068493553 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((449844403654122503666335856467645967485230747325431644219887649272015170067880669943741946811626950889431772661612878158027278714299222660922812570714196086437834522464653599614591129565102519 : ℚ) / 454747350886464118957519531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((44672513163254390295767092217549990906438741678775571867288001209631546688665119128060410922512727132245040470238428880854514295496515716475736549257346725328250643983510030056886788748384589 : ℚ) / 45474735088646411895751953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((994173159295627588468487544013177276361288200252991508287820716102315085606766041221082798166031555299042152863901024896676276847463252481514546234614043408908962463391 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((22520483443451798145111798090992572498186991398049204270835304327332267213506877876822201595229962111363736958181081867795541425162677536138220864212299130035992821748602821566830722444686046842909 : ℚ) / 22737367544323205947875976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((11191232738677430269390854222689423581332871968986458547348685870968294373629646530472964693631384909613891110033613381525242753443516352249031603822125059799244176103914608800253369241192015101003 : ℚ) / 11368683772161602973937988281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((9948449940288417275180709301884579363968316707638215873822349875357181562363059166682919515374881169730625926386932367260895021269507394703959190537630442038617590913620177 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((1127274430547617325056205279462162194465549762174472517828210737376098455750665995164543372239126193625726360036428425842228329319048671736146916530094832072381024107074118717327877488125845589185299199 : ℚ) / 1136868377216160297393798828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((560583936008751530319629685139532042626849478386107986481087960208440509080978187254843782925982238788545572246889993837108766858843518880410227953305792010272804411084240524591230211268371792309318521 : ℚ) / 568434188608080148696899414062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((99543936621731627633523735193772873633027697912475295835706329347284985282225984447643788952521573708606847570745190653157138253171331920945926958686416520715649826812797705919 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((56419027869002879499793375250800151966973814813418409137749141589196081079266715326944237305541643822519403056165080464953383965736452915978067459054886661745409890656773782307557233924153359830852990350389 : ℚ) / 56843418860808014869689941406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((28074428079470132872517802606295809826274652834919913551877117899638949014268481522932706104208818770199519653868896673365894305961461566875754491503430018833585141569508084437514614768237068163291192646899 : ℚ) / 28421709430404007434844970703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((995965207292459709673784485259308613031396043431668942258493895735430264791853284408304600862958362600044780458382701708481202125806773504608615803498726958771354017812821304265393 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((2823397910372094268318244403375308398083575417320190228934932657515415224716502625502537843409296161927566991326552133483892392335349067294267822474188255626429837801820788316201804200548718802797169716173865479 : ℚ) / 2842170943040400743484497070312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((1405722565829940423707380932987801090166674980972482234719656162167871432570179351292586162704838453041641516978045749352962072083769893440739843207259234146226777851359434864570465666911393416660692003999119537 : ℚ) / 1421085471520200371742248535156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((9964304188916391051483971341089103299488760796239975132160895495571351552613526007160270803834592633922596172715311762014933195207012525195272424013553237404250168995590030078835931871 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((141278118633765159348438263267150503024287418653603600905902871865853845445004951136616163888316320931034214103795675296379463194524708986716579331513713066690187593684869595531515981190427364672617737585777761603469 : ℚ) / 142108547152020037174224853515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((14074932504683677198800228360781935692641933799317681787313373583251080959177893120335646905413020496024137424229057877889702883673491602410902776831387164418820242815203930840576633733881729786188348988082568326367 : ℚ) / 14210854715202003717422485351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((99684199159343311632478694454615296890577066764335059994227442449319747185971864585346915801524641032313208340012363158546113977996439810402575135247905491315401245103984996107461489262737 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((7068693231824185351292507555656276244283991312110460568006415638000608365802478731035652213922015874238907850980797764596467290973609627847881927332401389949671920206541619237619895687291494862022362951731311848344113359 : ℚ) / 7105427357601001858711242675781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((3522649900269297864878806391532149722307392323281201628752064386411742106359318409729566285990071685001696920911432719377418112206521897076759828636468016521177264824902656646884586045479308211414195819771222125854641193 : ℚ) / 3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((997206109962710278012539009839981531590935309664072275768930183349131803354293085986564164096088499212874954184089376863657470363334503002631582221538219881667354815434955260562711795507434239 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((353646429594428638162523218087514663531013525416819012875886556473255342813599551137578725968126347697590374788172939160686160038951809788970256648202143686380540364124547773509377796048228115633823947529999863801884556634149 : ℚ) / 355271367880050092935562133789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((176305770158997255570649285157196258270519429935774541936493658130954063919857937525525595287367033888957298311404440706379866920340205984012132766153860724671363153098878650470331611952003041169819536497944048581006252667011 : ℚ) / 177635683940025046467781066894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((9975282454840097829576932620054316609985004684598047423727725332089769064275430931723133159758094952536304719666638717112777640304420348064281607913948631293111088052153049190198311254854270712433 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((17691689100034969995393208348011185220559684914778400651194061284509986708996950605259838000138141324368157843952144162412741944991358441503879459700323239521095272442760245729706673347544165433808148839954319664799169122277994839 : ℚ) / 17763568394002504646778106689453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((8822953932820410357378675223915328656280713844482541460949157578793152017304453265049189219027208311812903404441073611057884384867606542860353594503123021743307246382007669553833049433472404659101004190571368284551844917330590689 : ℚ) / 8881784197001252323389053344726562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((99781323877970345498267122889620539048537336444638925557719186012998186911644737452954559064379866045088687854890752730296743783773206819324699385214703541050153795997398026185684459671695732992894751 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((884998833892167930106904178576131632043861564934953525948285016801701333571040767797473602937533694626326664815555794417667278761038428877232326499369628837528525491670422316495896422862213221642018338222045927783940689580070938514429 : ℚ) / 888178419700125232338905334472656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((441486798244177981590603560662403603028578783495726317468351470501781318434414905717180391927714564449043764338817147889673899552502595793303636734187180878192761454180847001041107006851419663703344891906985810217408660949907271755627 : ℚ) / 444089209850062616169452667236328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((998065372348403646623169236204472908962409815525720574409141638656994959607320992246288984042568674900899621452218489404935292255041560730565615460994482227670710633188980337664750414715492149788139862097 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((44268271822441140676544433197786743294672210046345983241321982897226271778263343667950335909425873122241681732389184856547560607667962286998578942342531397876765184112234106452152710563269948141891719557902852512045395121020907567226901919 : ℚ) / 44408920985006261616945266723632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((883573633826357372741952645447229606988498227502153078925614478421035169927760873585623849893075069632050219932577677395909094537494719131073664180397639487186571713744404027076699837888578624790732927913995876216215593276120908222794689 : ℚ) / 888178419700125232338905334472656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((9982884349166327061675178232700971825590439637956049921797676077198434407645968818402918641824605066848258950987776975765462530580352687783313999983418184268202776971822909047320046918987959049175673359972159 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((2214224427057701293262975984543698183843207922482994945822769669427204157654192636893425107816923989524098030070647984114282703115653527755603626300237514054905144483563233727181904734402264825954632166612802483315378545130431325653701386156309 : ℚ) / 2220446049250313080847263336181640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((1105130636384176791923623261263661931371069525635553653745388703262818582288551438998102157639560927218277112555498646153759216430903826343447422922217913638976867526714583028909114139540828693184160186804932901070314288286741619268631010692883 : ℚ) / 1110223024625156540423631668090820312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((99848577837074495514640301824705497740998619476997173658144040254974549204443886136410621224222281026406546939388862904597047008044380228818978957853300676220789967869717276341640455092286473708057182215673690673 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((110747088776589946299796106882206974088366401523197510378620005652616499212579133069070075016291705406764162838906292001676034612454272146101059643433196861269242063183939866704632484220915137495136009872097489318287316553670216765072799113188466599 : ℚ) / 111022302462515654042363166809082031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((55285886903030038079823471188338381164949093410844134424394501854452835832149575794056822292305546775507292591111064981900663771315427713806297082947018775905722465984732190672432458481601173964223820791019397050977087431438395444703016909499562001 : ℚ) / 55511151231257827021181583404541015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((998660368124598061818022750243169538514614786512993995353600324135759836811715060648824765970694520240618720772773270116970074880168631884361506840128151082525328845743388743794493106201458432895181891062065141384031 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((5538941037698163826259248275877356099028402539331742059438226437250678925058111954923796937625210007751822587619655070734400081985246371419222776100275975524444272975748142562512940242487065816506431467274186753296746246764925145416250734354797579111789 : ℚ) / 5551115123125782702118158340454101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((2765592903138216652119258420909381336742428736836285673231183324119707891257588612532285394822735630790901751258612837309571143831953433324158917939483491800440026650142229453681421294757937330531651783475434608016233952075626677696214576009038560665979 : ℚ) / 2775557561562891351059079170227050781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((9988148276798319052904047271401320907238797016280457876893302067629067276273243141560152704542734420568753822676725120724834252464851886280946251014613752627101584298291760216349880510564302755823674190226090305824522257 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((277017235204830373040903903563872461221251780452537393208587148014655902116908651817198141144121284994777768149843633750736800296742000431609581884766785293440882755118258796447876227378889649778430239178370295499936537255729250643819058046184592951879360879 : ℚ) / 277555756156289135105907917022705078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((138337088156051590582570478777541068340122475143151761132571359663191820659694948170681557819222706432426418926284336402504271674135833378046038789193410293199841507643270977517767838053454479414949837531466543399328207287520800833517175260820016464074158217 : ℚ) / 138777878078144567552953958511352539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((99895147804834728661042106210087486066341637203033210836875043392314358193189382073382670977089571418771765069220987143052608631556544637927531482726287869491967716286987202634047392876962386480772045560930220935629548407679 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((13853966323584239321508466245878059118737986531007200788585591266619522239780416776249151980750797494685799850288906652007468718537387521465748766915065080937453389377164271103797167604171744145002910036117162953685637595427676339852485875560011763321227338372869 : ℚ) / 13877787807814456755295395851135253906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((1383879089004201967870460015992832670176272269639776467741332173290724733742393766068717584976335301297534981005226491170044556584822286087372018771405382649009248371019415104045919673188856989720651552995274114963358446614378691529380618335060475859896751410823 : ℚ) / 1387778780781445675529539585113525390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((999072372629372844464239513640643989228924464335234816273833508891805126935146463203216490134311438341873805567398073254586428563380750411744871027679468781395438385990975781703417284782486233195390287077549664617514614762736113 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((692835646685964507625298749286507528109739103751446041794415182187606777238243272843159428072479013226636716825219445381503415776364963599731329430649213105169278448727683301122039520442475099551687472663338579130289995226765727396582863077220379394535665607724096759 : ℚ) / 693889390390722837764769792556762695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((346082176687297712861863240096837835556603846632896210210786043758888003637352882326146953446307826600413048699339428162965259638174214162848160378993236023943914321030101455320624268548215719083590782355978401043453169182200441850051295063960196648951966371033931073 : ℚ) / 346944695195361418882384896278381347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((9991793280652061554975126977178777372708294735973822419574605053165799957995240759958856288218253295010557557854770754083326133500229498892706873981880260309005443400862162740730132718470655705079617869775081882871151796805926391711 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((34647857154446874738938472046952990205235474380413939388446067590639629926027019476154108701302909114207790911475990530190331157166937729948714074267479768974180595281628793583733707945224496401578158482794257136331146587423670387397724927203816675240214206894516543171549 : ℚ) / 34694469519536141888238489627838134765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((17309081103922196432738107802012497342603500489112046884047950990163836694987566439477088587694639237731831693059357551282891426284333184917185328188074724208479414769491100018322432241054931354054574377994804874733001205489558489762394134933474829465349563887612283428491 : ℚ) / 17347234759768070944119244813919067382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((99927395153928788576864948367100643416350283529160406945976530905357832228383895003356001581866886900958402714341156861375186303076530376703777714117694662953771157767427553767239484160309891022839379293900149417761079946342030787467217 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((1732661577573968950988022168364943589534793802214946122000084360935145751508161856159630570380718308204772399892219241789508315473975359906403637528160785934790158607595441689160570366397883960904995172962098446889666686963188744895982069467355725388399856598973431042379826239 : ℚ) / 1734723475976807094411924481391906738281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((865674005665594404873640323573392529947025926945622530712331226183772496811914645999314322197174224027769337233289216656559600606376055210226208105724819894791312357330338319319408675584036659470253673946182266931160183189402731580234548567567915463072056385417209839986547769 : ℚ) / 867361737988403547205962240695953369140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((999357664926807992539524198203739392304450958382482120251054368919700741724512319094690545994776348412778988813776214752586273223318064242698321436799244683152013432768431568178767716366261605879059988613134621898932274285287946376722468799 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((86644965707751245778168465433497224127230238121932389072446075439535988098767868781171176664429535334238813104559768841515462177888680906946559114215297628436931879218333225407388717419993143076414048584468210858144765381900589615771853128385925879551283707645597909057658743779829 : ℚ) / 86736173798840354720596224069595336914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((43293429868439992749852188626332526726400271958514780291298711385948843654244983602706257375639752755513841065892182301212594199651683369453751101579120454237117821411484720695185058363009040398543645017600632440351563356038663546826672014443148531435531113805886149160674042752307 : ℚ) / 43368086899420177360298112034797668457031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((9994317261607470309997170581508482403717477628809819317861078001832592462036760487030727260415786354407855714035478171916130759206694914355152049751362917711845862839702314083677557986692316427212043719260401999939853830601942461594863681464753 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((4332774099496471714736757618728303725996674781320835378431717833677261971612377798331108827997743383228647538831793054364574054443093042911055383425529596364155541133277491294339271954287595987055766363133272919616502625475349935639366387175664543965051743977837451571358109690717141319 : ℚ) / 4336808689942017736029811203479766845703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((433020376869648612475038586494410044901102868580290853037848907921327815333167519421391455514537981735243380081991306851914273572113118103070569923831128367323916418710939116594661938698145061246031110290890378174497677085862816568533079524430235443385391238580970751351511036691973501 : ℚ) / 433680868994201773602981120347976684570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((99949724813441289832544968134605543825688524582080471505116957082212945511639220028760844072898461877446299502071875386942008826701629907300030184150307732996700348542846372698295355508266923431544950784296776493467886839335384957729758989918669791 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((216661964369874746709301870327823201327900993497830089181842381621751593228571660095876719335168666364385659737784270600338534364247553085096699848543386555600361544851264205719348294629702625165253637325040457849851409366904409580348158292480201485161645447719989656125705931735135590309709 : ℚ) / 216840434497100886801490560173988342285156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((108274132657647646383788702203882104897908397774573997422992492364646681975297044044043921857651952366255960177951821768135678170801851036715392591732508133932596708718001896799669862240572884101136314685204496747838811276611762292182811510543158598703930148247392188074320855164360763780763 : ℚ) / 108420217248550443400745280086994171142578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((999555215424515091148525333086855246225866376977665931405769719306337928941472179594447187512932692229767411694829881548275952089829319789883367039177772513821807983558561859261819010181637471598878179588673581637710394867600150721035177783810471640977 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((10834127098113327280084101028588764903423801620684441908687181018598829624710361322718337113676419088615076470584990021724568122709265206150406558178409680186140275395226031975360593415107687299811536652966411475986331111185691667756613683744597756647704110898838017041425602595742247268576873999 : ℚ) / 10842021724855044340074528008699417114257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((5414548801779652334535788229263982195173567542934588143895320357014772203026832078063888294598935907720086796499180893070329496153815556279179059510860895417884225755664928712556396591119004844581616060180180093863305802759522429774383214282372430854588794027494704912506157446175347151813941481 : ℚ) / 5421010862427522170037264004349708557128906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((9996064990860685011391003621819408363360239837121410495146844706703171657345204372872074267926915528156752291264159962057597348138719992181098148195605753429781535230542596768889312783076946711235275254820995176748823863393658533428998217853371242607723519 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((541751867405473476911553435390015963226694585098426539403224346010108185396693596826186872270162211366964080786318275144116686145031320827503820165765531653021698408700709965597236537010988535605758830863328994354268403975041065342615161658839916207791440346533672929998239685644218228562647597513189 : ℚ) / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((270764693555144262206559180953639459159037246170106079648746691886683305765931759816130696534759395038410845439243199994486489736575681545195255764376631967312415387291265400521505285880815944291152794682022026585305032516448974397114685333235791935539105656079121879277281094327788590402074250661059 : ℚ) / 271050543121376108501863200217485427856445312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((99965186974144480295776209042236305790648041839013118650564135120202959652533023086799241048349421677602787520814023184323563738983255770826175317086524100593277242184610353614363750191881747554298480179401344328696844719443697045246347233348775383350529972593 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((27089606616048680021401183612163521002918443158257317522329745345810093420182077307708447215293312435404988340630940725584728402154084159219671946306705879198684973238373207647101474157797205646720723393222551379836325931139455341071637765619362858944764405075413870298237132650023400708007461463022896279 : ℚ) / 27105054312137610850186320021748542785644531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((13539882589303648053483867636968606249590011335565397895880483831621710125913384372581940851177135573416626954009470698998473922147398924218561065293181465355786367930476623097928416018642781899060357893886304888612608942366902784129627820542261834394990170261574897836747373936584293760850915338540212897 : ℚ) / 13552527156068805425093160010874271392822265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((999692009160256217176732121396664597329863226149749060701540903408435584045959655248912885554747333581751861196641663111710568398784863804499173030264478717948723761607247798426276097947577820612878654147163693275980985232918387759294433973436615816502138667530271 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((1354569386741467111198219943534730438514236384061776560950880389024172856970414588035746629974492340910595530988725933096078657720826065672537802215266476665902357082539930919662620602544643463645691748709468200253705084342699244129450096132265934582462223373328770654806890858247016949952928338930349165582269 : ℚ) / 1355252715606880542509316001087427139282226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((135413404998462146665680386737934515913338209465283208250469425575171370890735397830372927862639251499056436928566122793873277339886735982978879949939930697446671747755676161873157973023753765225119630205576592376234184883614357414740541084708529120245198815843472978516567108174275657862702314831697304746479 : ℚ) / 135525271560688054250931600108742713928222656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((9997275205040786753362549077996291692577299961746829940026532372454429612054605069987132298502849660197758716006688793549303398624049690078404183798749843217692359118939321272677264638542220978962137453239957194412603776355628976506477857362993740128594420791640307537 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((67732408726964899786772411639896909421549831161349483012319253719592825424251734077374716541068926622497613616362171530237946218699032834593094903598631986430905246819260398536801177776799700166938711835713038204089022651616238014470131180484090640195805943941978621378138385517077929586817389511844709374210920159 : ℚ) / 67762635780344027125465800054371356964111328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((33856575788973492355538365560566567742708540087972853814468257082941947632386939393878284487095188285353780046876130969568780300144432129921961850601410800266131719493029375480285712997117174051278935324758120856030073706300647201242140255084465305577035516197588405350574291928135971036086558454797603093515916953 : ℚ) / 33881317890172013562732900027185678482055664062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((99975893738995840406998471693033192604231372761574204479414731899104338777847091054176159444854710943769571360511175756530687167626967608123641814067539862946924301125256175299375760257183029000878030048813901298968305609418249555152809604090405618917674840743641800779839 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((3386794695275171644341476713300803497646187150383468729614929491281253689279452796787405943311069386400842689103808567088357609452553733401558755503311440015533437331125510949069608217678765771983316030600674424263252301948040432106998095550401130413435057831772977281830468913159050864544454206856278203192444176948949 : ℚ) / 3388131789017201356273290002718567848205566406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((1692971427151450314742596183630811660680362290947528454988128806021419427310599443824115843382628834501297928785778148819719571282785725129265203626216307541657825845271993377611419421309320265304815656904065714417961564210416047396086208669247655613963906299706581279213178057308388501325298049904742224783231339525971 : ℚ) / 1694065894508600678136645001359283924102783203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((999786731908896200080715479068264654969634954821646987029382133111376085167613214556296482608629627719529397826442371918026989371995782429069859129055525167491439292055141382873577350995298257570767931841856584791972599726523253814436906567387818510564669316058999011499235633 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((169347443107921583466072369133871487027874542723054838633124049290010616028129909346723340177879884598963769529593777987000751363402907730703793610835218369900615427110262477587773126374373587924667732025731530354323868685655839620742840856788446189747028635974640920694190246658924283926393991381896196171094118184393297639 : ℚ) / 169406589450860067813664500135928392410278320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((84654880943654127144170307332652790599764535792170089097470082910589910045843658896199655887366269115833710720448300000794117648371164027703671156805074833355828430503387018584393991826536360928095665542485651688028305398836834524295224231977969183405247480421418211616913166364222047561312709494132712572269211931221680849 : ℚ) / 84703294725430033906832250067964196205139160156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((9998113217198004682114089843316937402516360445307110894248943731636344225477874109179554981638546316434676582570535664358784774974046687149981043714754231156796763416811835814282538824255403684728583893004905205654581589780551226496323312401680030362965629439173964254733737645151 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((8467713134018792211349900500010351783707561454404921833171930855498304458693603277349277125930777995272672790070557125939695663351273460106752349138787373369697317206878687365684465780734739831306361634600761236798527176102706628776508967902734403816844345126472181967379816479441266174570078523809223006231655569586788889085229 : ℚ) / 8470329472543003390683225006796419620513916015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((4233023151983789286427974471981307194458781694332963944739132170383125207793413220452860872750425850334249586315394997377656388924313115040104372598799825552312037624297889807403122543463493561373987978892493585629440849118125663642693982052608844614753278952772186493534573828694169136535149290426258749607158624403767217964987 : ℚ) / 4235164736271501695341612503398209810256958007812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((99983307632550747422663352843824945200062240859632010081420405193786737362802752243911522922556219261497583726001529022582168904195391041215882293744430683044180965948534311448957620978187556398793781701414396354426083324788536700812972344817663228621156923648372061761629376946650897 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((423400739890971986786431638959191173315354261117919360718209298190920239168152432255595066178435290724006523384042056552250905047416838915804508548086470985121135317693936727217222211361167526664410180020623428035341181219779893459028551875155970116816657799379213811739904913945853653448484838025383320908733253078993132543979820719 : ℚ) / 423516473627150169534161250339820981025695800781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((42332700761875760748344684554942190121229720077915385075579119278755316937392511410036091668073151316169118660029221001913108695826752756962365420866473747286599876879979197616182221570441740476198272330559823556984839302092623520055886475551729707137214987516804321158777963079930898758633266911758651034167071232440059726554064757 : ℚ) / 42351647362715016953416125033982098102569580078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((999852322625176462448302682609319290184950644885164393190326324749431265448715949101885243295854871806469123223935527262784448295416624541636910652756978252891869005746683053388928072794025311460128586712413164547607559174404184192092366334601866583611375303517147630405135097847020485759 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((21170704199482786915386277973426637767962842919492968866772280995648121939835092441476451751761538541440803340635424443557668517972555504597878290281643838714258466820194185220756657479188434533632391501003548682916812606402433947715345251045248323416734054464223619779453541211764624987291182517518304058848896493716762433160827243303109 : ℚ) / 21175823681357508476708062516991049051284790039062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((10583721325409232094583379503521708528774773665408082401186410726411569120313969598084842262347779709446349364564540363749095666543017138381752943308715216946923765637653729575112903160439983271980848254528147489838114907712064926734456591383096078031911217073833220925021282742249181029699277843039713734412000047479281840445915144764643 : ℚ) / 10587911840678754238354031258495524525642395019531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((9998693498264936163280133833044647760266258355299049386554816995058218405424790001704378747438428050871832333162157609693854014069550877319861748544940986603334365093840904973331846660008741930487757606644719266752684076015953817547441164962222713665209837310216205086194230210652590237509873 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((1058564723785216120294244675595751449749067124204356729004096920438913588936523877917188921160598200692752226737835415057069413604893713300530702532571082235396960949825203614771938224109342673454799680156515649490839416728960185783684171649802575733082131734616690451551974878126217568942357935185302308040640674005564283984599474346974521399 : ℚ) / 1058791184067875423835403125849552452564239501953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((529210224561418243162276952160085942240769963695733207764327333154283110275725863992229337968266692833031279085654506092307330835605319653656843559376589536850972081463662458760067172551589985998533250531760682671808742118379544762806151898897772933178577225376400063174211234324320260991864579092453445622914409999566070180352217674834856961 : ℚ) / 529395592033937711917701562924776226282119750976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((99988441379149890236539344020945998735075587669330689922850465955280058232793117145078638778587772966063100651485608372961526462473316611648816889377092908479699127985210486299066847401097339859025191545985831352960996020513143423842211986420784347796111430683482766397560354673643465831249846431 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((52929541732722392899842533749737434185109192081202015914976035809620938547260876324424521577282375760624088935636567002071934691834195883284663800680296706195851529273331173975713457912963496937923923502192688331069153630233515246608433172023963281692183806074863721300969330257514591099367932981855907779896358542040968136821511423430110109554589 : ℚ) / 52939559203393771191770156292477622628211975097656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((26461579870495158106927347150842514951975072131579738940128967434057638471414522614163199824787982726554254329354986370691638889353056511750600611138978685561223593413735710448547469959378146429624092184129842796268909959888710758123845920124704716881760768010399838797493274413216426236415792305864601133344891902603946396839801437594779557032139 : ℚ) / 26469779601696885595885078146238811314105987548828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((999897740881339078922663576553309250809213724110568613747458072306362675185520707382510717274166027430760251463693177275590624613501432063257083020319140961319898185285157172287844398957508165732795869607336649979645931793479779870732049443864679124952197827256772034319216457797723742209067391375057 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((2646534837352149463268672771093841383703325301397214849286899487116103115405927450798202076266954150595167686692553396572004631696715981917777227318805720489864266510297622975811559260037900149889487903780903493134416120124166597755769668206874797830539009471350602944895090173470595282472955763342809922268038724575248645507461808648318800878508471679 : ℚ) / 2646977960169688559588507814623881131410598754882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((1323126264937517397359479284333849906109298673767228026229605345376614359074752703636958780357920517475480619578944602223502826223192535329946137875175061732949885635183268713480700860752000082091955808971533891097747086787783824166974307050689356195695639834810444311604878182720843749827544347670758564403565694205919908908642188496556739075203683577 : ℚ) / 1323488980084844279794253907311940565705299377441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((9999095313577206831228804661767126941909113817206200525823761565694390587366301698213072315724546844679935944699293539357150255955647169463635413480763440084797139245217785503230559397577074742238045058416107342369927558576915612516366441429870816218452094177740662187622108002136461947323619211495129279 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((132329296470566467672513690969499826896048580229363141215324763645306471654026510037718621299783137406557138329656733023673741487936530946682526496879121475062903007019226877899949162239367088864264626297362635633150501311198142621950968699207609483768945800440800134586934516961014564748131521103741298342920132772599508887268632063364375108957384387231669 : ℚ) / 132348898008484427979425390731194056570529937744140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((2646336171934354328716867892562517037018092545704914228783318327339621144568638130329292576983324828854026725433459511289800350018673113047378429201052147752159971920053319453374726397020824051948759759911101746632477967898986545068645756011755092585301969055277368382438687066084492297548366350248940157653729013970334585285330146443917711168289162402667 : ℚ) / 2646977960169688559588507814623881131410598754882812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((99991996239217548835881234842653772055069929940823256051962818571698273526429671124091050777215065934883393302754649942692708314439610508244782503064314154430200290902441748347080758990364380244579984631807301657946749110729972423932293907330067111084645677190471638373892789494901278847972059164097408731313 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((6616577826391460635433993710041483745276215045414606119759346779254416506621440922847397337516749084826577624422611722558990903576501736160237574271995509051019054578359039682431696554601189173683861236810831396482917600201723047609520266843376433096368882364409474175312982505368059614143106038015202493164081645682536242111843769812284800957199533915588583559 : ℚ) / 6617444900424221398971269536559702828526496887207031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((3308012712599540611306101750703703329431996941588220588331156490965082775361176891193544043310875384471813332635310080612424281095071688614203909009089174535978441872466315941766001519846359904514334609790365693560005007674388156770425064430771130638937458623339743694497615044811458530627830636811892006506112150585649380274239421012732141061232907863730998833 : ℚ) / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((999929190728357654551041284652957921371203670186463346291715055903814625888323300434833526226021688325913380549470388043002390457847234166441590804609987324243981973613902147626623474787753672023799124037599197767854889382628066034529004198149103731765860306104102584693829508661391613968008807424769775045926111 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((330833890001267754425034640234877001583713136951709645914795908649318276785933715573413793603406542437273391786229150132914127458211098487619344510541840162060131527925628594406192789633288471215550443531085700256110135121948143733293618393960941059312836301324562284431333424042324578963159851186865062264827978414280391532506397169245097821028477979091540281966349 : ℚ) / 330872245021211069948563476827985141426324844360351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((165404727265608984876076087610537775450655169228109117150077553885034865598403383009066712786923021749335684386204305525423206377402340795318258455026482430763835592986505199654750105857245027809717737761141635447351306864725184297767892933570002242606457730794013196851136344383997197420628835210441837007790414880077205039651815070753586636070518043806003563359451 : ℚ) / 165436122510605534974281738413992570713162422180175781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((9999373550373780169813062245324718730371038870139641224642803099581047995233996238946972206521613876619355677721164523016442148380574480670508753848384557857586508520562192300052737881447256736394550850360640102652212206368110500207478100141025120714932566128102995566786309663127331608774973919286938199831308304017 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((16541915616749696554423252256539787453374794584837439819321673518437198509415966956085364399351422223442343425496169131851463390121588833418909193652269800340689570319256513929615884053158719813807325270384187115631601473979575139320615625338475505028707733771741727561980025152202754451958526820425885168450911521556719642194995210957668044302258941003774458608582409039 : ℚ) / 16543612251060553497428173841399257071316242218017578125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((8270417356807107998875844798884116117737315989861560743333522106364337257098832465809297325341105703105009403773584009252035881678248369721864726788145220889235713402168302953818707217506791254806310456098281366647510854190490235333766912204662789334681000199629181185186970085376823544822371213455715993151694374084971396606463648912134138937135184280489080248890389929 : ℚ) / 8271806125530276748714086920699628535658121109008789062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((99994457800156833162336161684387786607592580884125405914414879021993531613835164725963863111096717966451439680799142535126463686722942430491990945296658183366067840881413715278566572037163880346882591373140582988164121389738673595335558751947649242965008412535327201779358481589687502742832194263931542253907584565638399 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((827105561934157983093996341357329248620376363899986930363356486393656871260328890134646622955486526199790181539763147215404020027228630745831156857200449124232575464729386288587013519178726939097191098323522217504707106795909468346828244005020708738967262124902508187533075860848839715702179018062051383397129599266828012602138079683061092588774837815728420067211535478430629 : ℚ) / 827180612553027674871408692069962853565812110900878906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((413528874089879904427058504557726715385852303909159793056648944585599900087523586385690229795448129678490298633827451709165923863361455626167392674150040153332135459123426906409729885336940594752485697986009802132342589033313302477401722509715352971277723857071443345233574775726434715473776761675547354377751419886724425950733359478185799016788870570108246192551227163793667 : ℚ) / 413590306276513837435704346034981426782906055450439453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((999950968157987502987188022421778748117371563081857466124828434707576774187599702330602296943872663849195886856030014008263824236437871682562643893039534948239602188277867139069478462812788849428870285878174737696287981935018045297933688278480852852511429425700039754141984486623965336765836422653002354320320400652202915953 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((41355710763521146224278894041642085595926783872472415879654725146363809787578138497314253031039652035282475054705333375106045163561990913184056529051726741504250170992130222134965808713108998715706907385011507259169453653022421675329246218196334841686968145194896169478138914830461559424567345916246630596199202163673567883069777781976310911658435406315911973827896439425358940119 : ℚ) / 41359030627651383743570434603498142678290605545043945312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((4135359572194564499589542288360381990419545378550979934338526251781346905980972199958844792362785318085841104478975669452641954679583729119339451494785407899667040946393492673699352976404484440970771246923613992577194375552692658602962762314406559855381700438813736738089210992003537534573269824620284761591620080380736148169308148562375807401957684716185831593788664454795927213 : ℚ) / 4135903062765138374357043460349814267829060554504394531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((9999566215293715438927652434365476584594386218585193002806357161857931721237694566518838521062441457073836011015297533931110053019765850775631710521720765687075760559694290579347675960504742950897215419164211904399059776179104646750819340199720105186168616129168251704894136753162221334367354831211111828671874584570039197436191 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((2067804677192608502062686457265886230030506066745306514825016375405874773055983321053832288786784991222020021830795958742752672218982604202052728300992467484380134078008411666673020231071463268292330253051476305850086364447941042953244023609215373738734419323938981321840226616496328035198277094446404824733025464041049961522772855305444210259465086506915064835755586576936933329136509 : ℚ) / 2067951531382569187178521730174907133914530277252197265625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((1033855559161590862496021942957684931583540306591877084268779472635009100265823710988366236521295523636179318241188593836213775613282832157919696412163736786110403530237715721437618914276839301187228848472051643982773949698922296777182965512153798247732675609659096631656609831972411129115245691447085490932861211167713027857324226607677310718880446526700533342438468664355881144044523 : ℚ) / 1033975765691284593589260865087453566957265138626098632812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((99996162306703500488192941086831371343906534875823202495827841810957121937789883829992164395839419570732227189452337282688530639065868481812013742985663614033559253671615388755488889222585460886587664813345782718218481839856538809804498702746923770582033746894751522833198427855226172145147988191724706348260074449691136779717981777 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((103391080474029931766186328886613790164113290488172782616561291607746881961078733340516317355947870260071628239420131456170909448095363398510530220957368943083194973450841590063968421043066570654596625462481125832200740663353777665060648180498557521292923775854288214409004038364423784166288478989178416365298451472116640707127224193358866348763634252945349056534665954783957416862405408799 : ℚ) / 103397576569128459358926086508745356695726513862609863281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((51693470948625387262563346673877521308534407664124272442390170816766744645978941553882390161282020724644107793335167529128586951854973881633166996483844449212884311730752570589551119969291196079815124446689894142609473895572179239556638307384101818427527767933881008732340032096169559745762673337821670620761174188299207663186988776665159120346385287245204851425481588199397899103264708441 : ℚ) / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((999966047927405868819042949795197142279541114046407872480588916501537657783627102243940678409991344942268013945084827939945430563815738458590885584194165993354898717232781344319810202952213572463641070603670139708078908837210798850340400023202034598339252558777866722505306491235185944968124251532188477063056878656417487090164984781119 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((5169591473689541971145318509762791858576010887658386363348827271234013971787213858868109118959041692150309511750184728938344209742204668719962464151681777122960085630559746183081596945125384900359664096278757428978059248545174885711978675305508687469289280275102228923559906826681060886837463518817506266935575804361275957743235735306158005473002358959100181015602217169583568625405258579235989 : ℚ) / 5169878828456422967946304325437267834786325693130493164062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((2584704201869472580812696054130202808507678810715772450998810037297335831799125215368110142870375056233678127185676118375776386770011467691912111284911782551421772560908643606367759801905474114102972173581828314340967834583064129888144096556569822143407678450274249977383609281501109098534104187937437832479868305043463878554588736695949411853800151628575978364009265889468787064547308894179219 : ℚ) / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((9999699626013759721442072976838109117747100235968570447835770144289103658411748973552143181893193428704245119372165472784697224198077838143153564763365786543210788951358416553197360865518233475585832551630669725997374106482803937428961519005268400091507367387507786894004446527957690055132995253305271456576864205473325508286689620358559793 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((258481230284701213739113693880890667937391574684102402908687739692198732230941202853950119388960952947252841165353428923498777248283004294361614139444722734950938388978745156970750788691901203565711490532621442141486595509222149662609940196545256462391170013977054666900095976168585170239443396363520358401013241205597462975221040923219403421610356668445081455500819655557268617798220445977640087079 : ℚ) / 258493941422821148397315216271863391739316284656524658203125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((129236566092597699608748897562438315316623699278730837254168893570374400066711912880578407731166638542395541136688818188416383506450133483416381519642412904004091843593687573911741384962389738135791210860786967344841779081613804852712864229427368610022968272949031969341027906044124642729826082240647956492828456164163291049825906380796388352026340608013129415498595652161954234461538361046990970257 : ℚ) / 129246970711410574198657608135931695869658142328262329101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((99997342591343732255598019626086751364708595787613942752003058466525700065968743169015810730209082263746456571085547937726216342480394634052479587461497113547785849852667911246137051577239811558507860584276535065898768720053366434434022558639609535609565679277281390651257338432841683917761609005991736576335517625822510771812343071312178488671 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((12924134793946077435095133407257823500895591851036668431796974201835029421947508717878746461211155023273432931291182814176495119669821626058655948141676371271891249289564143348204490672331358870434493132248554640553474053999231340063794571708351738959450771621939248964757322695549965282593660559197506759953012273681218323467725546776895931841066783526292558374105974668406955935669476476087548547321069 : ℚ) / 12924697071141057419865760813593169586965814232826232910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((1292377657450584909719810768041542348028596175301313947593967355413461930076381371231048077748572624446606260989461120962794862627197321911165055216201000347613915251170611270668176692625511508171434911144555450987518810340494360019701333562488421305839911589102536558192483759509856007011043553316806858366593427240421993427327318406597568339653346495344537990925631561136642069159021523031160880891391 : ℚ) / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((999976489905617999265275679631989489323576946933020551526971058253352868483625470816282877530159750787364901284393842605063835981924051327462286910271864963557261413646553010794574495303840612858119042589094505728006406866312132845437797576284625561537827564566108463091673673115350377620436954876008893490840324435651752798223799151898843089272337 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((646209981225324322226600724692654133344094797909743289589379178564992589081080308849957525168079323804465145149063127728939364369520478482303742010047022486771875137257471796891248397893081869506664566538674471082172447833670307424811801587798206401364790084660712477915189644435583987623878092110419777408799861767700202051222778656602109422600652813773762761044875454026171546996811044888042680238041086959 : ℚ) / 646234853557052870993288040679658479348290711641311645507812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((323097067694039998728755961569107243959804573961388765874526864750882420286702971714006163356497407076277757217949686115589799533397193628047732772071638873166614593626247250628802987943564614785908834548226684714813766621175479294118582006292349290809067511274513273764761157016507560161624136097001763163406743565564225425595138252249178365141994914505213548620549314919659761842650468805252605865229576713 : ℚ) / 323117426778526435496644020339829239674145355820655822753906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((9999792006195002439499893937704211012045685249516432819359112952367412827474634540311654617509323315215817281663032325526999756932082082094058852295175189332591091726531054486499600559953077901955779169785719092175672681546263439283588195157390082342925160463716361572972036986051504790808005739788050680713464350282211057005885951096849064810792365439 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((32310642450258328273757330465969972387867182794029714162054763348001557900688545787481476225419015857670378535972337377129661010279817746447443824737212920912807813494097981947758485867946589626218500825903413903944687388136139528826753459885767956866143259711280006201941047348885267476577203147318574319812108395418123811447166278868864693950362762612244603510734615334379212485110387670565522573451020082223749 : ℚ) / 32311742677852643549664402033982923967414535582065582275390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((16154970754818468650002438831569096651649393907522893662049633838755448947531492610380656252781681316805582495589888242751396558267151839114911342386530980950759780232999229360198538816976321943292852696765865935681088513436676381538437440834223916961316849608786921374604695767117205608176971880970983329934610255211298232418397656053091414449089268453402704692822040682735001028800878804867350322497138217328931 : ℚ) / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((99998159878807186582255561666869154823568177402471881152870072289594501284668091778137208401104983369714335490872846983937366849578130180286138666255414900025433388504620239042061966153904880198602778315094256808478176213639792647341904762557430058487858894622498650836083611215597662884278426779904884372272019106946721221331073009353823676381080057038833 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((1615538465324986982667682201386588810091504874623108212459773863838450103625421138550412949866253389401611848437656347714230987998815815106324089709775652014849085146348741878252973561934340528658385126443979835341527077935110558281068136716276755615722388603678274005782447849250115710287446533988296009268274138176540441278772140380245590255708439649659780279100675052440216319531873187010058692053890971061611160439 : ℚ) / 1615587133892632177483220101699146198370726779103279113769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((807753729608106075442706359489029820261867796985478629191218048369096766038243157636729065312054889270885719505772910661850038402330614659033486903041015200934601101829094636554992891638009253258102750605870345599393079917707280650831222670566885998708417795016227621424618162974979172728322276316033699433927483324726782677262900553465755296895991982470323345525647619244460573076600363103941414148936011063967075009 : ℚ) / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((999983720447807179693214954066791412724107665479668732559441529546042552865458607961179882724575787871862726087752077266893884518217717704991468780361655620525009188100375254805122214563596475117038779753638889984606424962071245551033831434345583727442087640725245563946831708424392523537211241721818512041490553039157642645116002913753278064943415264622555551 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((80777203840541448648496128754431397385097513899708785037758510142101597801285974287927719145473712322461379655727127796144186397022590661795148715255091970069573796386100055704609639507725087567591932464692715733613033681317099430660188943002336380860816041466876616591419840228882649783745841813019933118687637525256727997358891184573424836176257258064714617229296307211852338873425002846523576539598060553442643015816029 : ℚ) / 80779356694631608874161005084957309918536338955163955688476562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((40387916142652998951146588030651466572081856911064413576411743259366438727375118117848857611729302189183123887907846202067164379331633749885294802650709415334072048047963654974043755058422653880912262014388712620634935976249812282168019089544028379596210120922885960648277205901833224237717864091707270288932278969737471623834037662670725152900614786380230789762964137244160272003045845072358787330287632907950099366638347 : ℚ) / 40389678347315804437080502542478654959268169477581977844238281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((9999855974801750118745872698628903628370180516498629276953379211893838465200712304632558422464321995302369537698342627580210196332672148536059524299859567274784756287124019879260916232244138015360442084480443259693813041639444309389996306699655379236680149357496247504237620124430600655733707855512928376031066922737427664481341277777975251040554394846115748959697 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((4038872603230889010214642026250356790626289192948415816779864121817011832988365807933431674814243480881381193768604728249050301001196820737335438547211232284366801665725206622618471413311977021812542674000935098376607152013401321296281422955489100316248040479472642221884508505419074863384407465825665676311500460505623766025299733402672294494907533830173284021557139966872557802144677197775606323845083499261591883327598499519 : ℚ) / 4038967834731580443708050254247865495926816947758197784423828125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((403881193248455786246890934426115172647337900545571085374860176589322809595109223529062103927366202800213767245979262410395046898781838831076129891992465542049998438489498455304149433063875844613386459000852037541706519547568330088652787837102897627501662746787564102092585704687447522995309243247970131399298099795751852166532351240573498598303713876812028347683410776118242720946926020160043284486460697203696370626537240869 : ℚ) / 403896783473158044370805025424786549592681694775819778442382812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((99998725809071083300544735764769910400190987029463373213206545887624788901630701759084244363541856692440063300017237226202119606955150498098518611480857591680020738872186203871821325906663889021893831121398481518511163979384163805173297325371851140106909281365769301669990225240837524001276113397722877342746849065458022547666426284501747045955784731203586031046439359 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((201944179171145472313492846153065048200561457449941296211762717191576754794627404666445658297330587717024767554801001043442877487425105533008165182146257041142668731163427997142390985212728748569808180253020309727326872255449070560481458723099877839894326362367604232774943176936876924196960895902234005491735553004133617384273211099749219020832209597354197968912938684556105296244751715062307095062150552935704987414231769231809909 : ℚ) / 201948391736579022185402512712393274796340847387909889221191406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((100970747700332021373075375582022835072015080895151237004887604417658168539012391234830824359290637521529998573829186858001516180418553756752667125217428060343161125221484068695394027517329491143398583318344825238387957158966959899338241464012820545648816762873790013418647157525301730233653061263986090881517798608031778586607431679067689293723352485427633661955616193577107477536678318730680331080423563938076913564134218872020403 : ℚ) / 100974195868289511092701256356196637398170423693954944610595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((999988727232851873959919277310919397310489662249662462817238311467816507412726818462618309884254806158017240015252497740210152162732216456677594155771147113593143476802231345654003270296255426176694723931012365994268267725611697184368161437564767036525826412242961011874403522705689574839289775229654295851281373682107125479204873338986956115570827516958125616667849009073 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((10097233243996981693427788011414276952967245229535991513706314486687578000987293745784451397767824594656165116385670361669228877009160801657031545425392495033149694211080102997961367309273173229104874326935724042451640719043380190134819999565588178359561174389132602414106197485226133439839290541522737220710111659221069945405879000136315909844998006202077869204082194344842335917274699325410443362289241232104638119706456841791293536199 : ℚ) / 10097419586828951109270125635619663739817042369395494461059570312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((5048557263704557017459071676684808286865481351708506606294501695277729340977495184353120376914328035052556983097164783514422741873564989168090824972057749634978214643770649615949824279695437316028191743773402454988228803391522716659601528914755898879296541984534019964312522996256714057528205969582461872434370502923823865313680765675518180776254057039859262385308448223711175633890439276324226782521132666319941122444841339930925895921 : ℚ) / 5048709793414475554635062817809831869908521184697747230529785156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((9999900269829040528923405846369703908005902041922763808544107341555772641080394162938784187546002270079978522414938847507639216183691918992226675496107338513958540339269340715000966932310971755385218222617666401951291364568486684990105124238135493972143986269113476072052847965377235668603196641456751555396286312965601739114525514430017600754455111042528537330660460183268831 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((504862736466274813510945938720429957056949285856091087955647923319881840743308539150590923537504218114131377110676234209352332245443763599516549219350911959984693620686613901158943048255863103822351657584580192415414486169326779939854953851176634248922237650827800792020697182634733156322651933907217299904251094010364186154225165273219593610441747567485276191466372787420537925500377264937547125314661981350205980683809579042961172870557389 : ℚ) / 504870979341447555463506281780983186990852118469774723052978515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((252428742518994186619534521816377213772277212256388602591101008052937074844947030331674325085373823013977485024325500441622456887570111766742076424432706189366883245477184400292710364765150051509747758836023846763655121482088435376713351133176912695076197744968119212545585038919358711217077080286787418037275557575728131610548517175068474653015175482943278783484099872711748607993322694280059397554264983803332502887009913213957669796502299 : ℚ) / 252435489670723777731753140890491593495426059234887361526489257812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((99999117687177521559385371522832770474128215364890691414189717650743920555638247159519423707219482083397569987804963983900084145577122407324229398114061623832991206381515857305613554450155167119893025615498494658063074702337401702107460034134784715171557846522846922809451545949692403960132480686967881010590945010806678585946207226162365713874664367393249969764353091241379347857 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((25243184343489091306485942410766397135952668175761940551244795167194242845701251461686821284353103965685188387901075157554220170034224124272344616117228527065936970658044624305688321211705264965935258476656409780138622664952684485107564436128240925731950692177646733126287657638357741653041853515014673301903404720999903222928184431470114076840531206859427213248731518698950014319992921179134673806079167901261706186902421421266919231730121742479 : ℚ) / 25243548967072377773175314089049159349542605923488736152648925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((12621476023279026994070518252733273335712169350789356059257964237381008709879992558738719773096257080141182898324695925327600492988043909606205781137821404866669779523785959474583598053057747722434143370133320557446944203524967146179541616147628179970718108134129763079126259211192024101765957021421660631450365622194337565693105924500696879013533988775205648025862961357659510935034346722330581519550069015965033145507308358317527976911948472937 : ℚ) / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((999992194178459533235882381862501520384612321333187946941336432056131465155731572620268341537770757991818301682110516365564044435920801937597457485115103186050473202857270789582763116220522763509693597620315182239884021891578992858544698921990440375122772268187626726095217827016928697835292056637604843300698090510606685449866095329858449470649155658328082482505231798212483090490879 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((1262161319229411500118022353786690478541480035010471251103220145722784016893728102211550692183256643138512475755547295420372575256046783166766994034339295487014192202195169839799563110761344947526233567454016826451096227901700968978766995153152213497143424552545916905542131551294814838540991811099351113315615950553637208241491099292087403196681086681434202690121191147738358923505317492933621724403898350279608409376454139273063868364080471589850469 : ℚ) / 1262177448353618888658765704452457967477130296174436807632446289062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((126215104357463908624101326135443931835273960790948595192824185491979185844789317549698975837873668539135570369927202904116211949144162218377842637339139130323207600797613860460986375261998161792850045631621008875162991364906805597333016216834465135469249225953463839193709847346463670493763594548291247225082216710195248951741337428676131070425604315650432659994273703466746061565661218189154874045703425008078222796841277472616922029009766143060647 : ℚ) / 126217744835361888865876570445245796747713029617443680763244628906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((9999930941896831490537851432337550950842665206834713766590003414400595072232757222971514017584657895953616514981631738286145101124591334741924706370813317886988536425678274675438705289202964888770259258146928417276253941674799349819544951362849425998711166256655933645764392115618768189748828825072890048681276006747337346174965345383257702466833080109228545722723785718785837901572806513 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((63108158945871605559428904846257432028725892852999199269936183822382464219626954917809653364569356590401340863772162108692467343824062634916733877391691168233068212220638545045200645854467633699983005420223129632405250093647964868642030213947079451768224532961475207358004432964611382346407237982453950820127331972693327434683157803135405310376015550570259736743379045803131780120824031256200612473444075523092984467259323868513057417766169159426152430359 : ℚ) / 63108872417680944432938285222622898373856514808721840381622314453125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((31553852201140876425612337881506667302336490541274146909195110572972559378805628689599496796158496461817082803102631624099864833134470981995456979999425908870076034849983829474296696961252618630542920562102986724930694830895953385964524676127085896656446361982700499748699941844104047059040955533693772820637481731575440949524578066283483134697793376301763757198520235482202659157650664786177353103520278642192261224899681755353079165536432210614682050593 : ℚ) / 31554436208840472216469142611311449186928257404360920190811157226562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((99999389042961268196788371621890313262105059084866712693021760207202064604043203151628984513571468405501645308042495988617525709649259538461807877262585423346187581757975696053606225693578630370950483656825875707643018621996949847853514184707128871810597687872635044964077577046879242174707888615419858260683248831693693501609918410605680893724072259726344944008937332254098307915214619220511 : ℚ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((3155412060458560235470188695818037328479994478691506084156463766835996458323063499837035411716457250927824244483118001344254964946897918981025051473024274751984501221207793839968584633847148429264336241322768888619848961299234931055790859557210369398756700228842692676514205398293082032938670097331082108523725301044842125065667919948768504893036590670777427088167489006405149991533431275111767460190081200262342152861431305698897845258050604146683681201721149 : ℚ) / 3155443620884047221646914261131144918692825740436092019081115722656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((1577695976861413860290285618894922394736784444547437202139356474192999386777431706148463996740998080770598607287929601064662949634374327909320397128100056512604831610149800727032404763122676401950057324045748412090637115763555491620579283048913661859000960808368946645058494988695521508859253473144585504191633580128952941558669953688074584711431704921627773430845341597940579860476039890681114282891264791703726639408310014137929659811958918726557713683834411 : ℚ) / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((999994594863078339736986723738863601429843457723815807195163512553116665551970218282461625991566780983473056040251962011299249953266999136771614290142093240343721535812810982986254278711090142891798928911938522385517785748807015303960039992103969128908357744609202242797194324133740655519640690580619486032264702413994106408742948178628458866776867281798973719647068578452007730125903736243860817 : ℚ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((157770784968780913246186014231039778055640367229757846183046293839245372594109617049684527190488158277852202346041792248128368217166115572066099545223955474797936140963876213198085342470837961320976972881844648982038569028860408753599283910493393138728688522658543082971256767058052147988110413478726487936868878740314230930210462916203395334826718544976591224111231253980204831821395954418813535867804604624672732866354054821997333879971880897426507649616543551839 : ℚ) / 157772181044202361082345713056557245934641287021804600954055786132812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((78884947773662263752301677456360941873259816569514110959822324021909102189949643355832775483912557327616676774919545979018127071196767987709800049610019391540462805580217017354009500378140320294575655543351452785828378811599896662491945550099333312307398685598307581307968924057397478428698422116996710728322052455256483822044763273529120653399157996470843238379780780535580188957998065048258548735439974411230493860465417838768929349969967339227145740340546136089 : ℚ) / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((9999952180753654071653121544917726281849825070482598446255611595557423140138280521144938005147391311360786126788109107913964464336553141363018471624887098897320904427335938766479391603757014494163745124083920107544675850519695664394134473810143814883452240966557612242026778185611203579382261189566740592927445822256605859398148862536325975594374944842075520497717615713564912388423870354549436647999 : ℚ) / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((7888547296813849218226143257464307787622262994401164843275802601636464072126945655879556509063714378779537702795533619696553849052995792757684812038153643430416031447744832533064726116160669827572592714090946245406433115236243194251159882904246296980175234456224321012602495350847662740944014812107009883389796874327686177627627413303466060283857751881893607411932400224447344885808401932150123815854240504627757962210296377783962258816193240613267610921000566405241429 : ℚ) / 7888609052210118054117285652827862296732064351090230047702789306640625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((3944253976627840636802986630388827736810648105885739874910132191502184144460138084605345331076893030493571651779450699999618642511678896457850623877051980512571037273264947083776396411986742089389415454084187532732117017661723011604351492050819704905411526038793879171470293435482579936140116513245573359835127522520162148262535939362714188555564277526464701382622856442156301717977199751168177155978019646088507089315420676141457800156994992605284492180332194432899027 : ℚ) / 3944304526105059027058642826413931148366032175545115023851394653320312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LinuxArenaCertificate
