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

namespace LinuxArenaSplitCertificate
open PL_TMCERTF1

def cat : Fin 8 → Fin 100 → Fin 3 → Fin 2 → ℚ := fun th _i s a =>
  match th.val, s.val, a.val with
  | 0, 0, 0 => ((0 : ℚ) / 1)
  | 0, 0, 1 => ((16487 : ℚ) / 20000)
  | 0, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1 => ((16487 : ℚ) / 20000)
  | 0, 2, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1 => ((16487 : ℚ) / 20000)
  | 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 0, 1 => ((32039 : ℚ) / 50000)
  | 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1 => ((32039 : ℚ) / 50000)
  | 1, 2, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1 => ((32039 : ℚ) / 50000)
  | 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 0, 1 => ((16487 : ℚ) / 20000)
  | 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1 => ((16487 : ℚ) / 20000)
  | 2, 2, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1 => ((16487 : ℚ) / 20000)
  | 3, 0, 0 => ((0 : ℚ) / 1)
  | 3, 0, 1 => ((32039 : ℚ) / 50000)
  | 3, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1 => ((32039 : ℚ) / 50000)
  | 3, 2, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1 => ((32039 : ℚ) / 50000)
  | 4, 0, 0 => ((0 : ℚ) / 1)
  | 4, 0, 1 => ((16487 : ℚ) / 20000)
  | 4, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1 => ((16487 : ℚ) / 20000)
  | 4, 2, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1 => ((16487 : ℚ) / 20000)
  | 5, 0, 0 => ((0 : ℚ) / 1)
  | 5, 0, 1 => ((32039 : ℚ) / 50000)
  | 5, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1 => ((32039 : ℚ) / 50000)
  | 5, 2, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1 => ((32039 : ℚ) / 50000)
  | 6, 0, 0 => ((0 : ℚ) / 1)
  | 6, 0, 1 => ((16487 : ℚ) / 20000)
  | 6, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1 => ((16487 : ℚ) / 20000)
  | 6, 2, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1 => ((16487 : ℚ) / 20000)
  | 7, 0, 0 => ((0 : ℚ) / 1)
  | 7, 0, 1 => ((32039 : ℚ) / 50000)
  | 7, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1 => ((32039 : ℚ) / 50000)
  | 7, 2, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1 => ((32039 : ℚ) / 50000)
  | _, _, _ => 0

def kernel : Fin 8 → Fin 100 → Fin 3 → Fin 2 → Fin 3 → ℚ := fun th _i s a sp =>
  match th.val, s.val, a.val, sp.val with
  | 0, 0, 0, 0 => ((1 : ℚ) / 1)
  | 0, 0, 0, 1 => ((0 : ℚ) / 1)
  | 0, 0, 0, 2 => ((0 : ℚ) / 1)
  | 0, 0, 1, 0 => ((3513 : ℚ) / 20000)
  | 0, 0, 1, 1 => ((0 : ℚ) / 1)
  | 0, 0, 1, 2 => ((0 : ℚ) / 1)
  | 0, 1, 0, 0 => ((0 : ℚ) / 1)
  | 0, 1, 0, 1 => ((1 : ℚ) / 1)
  | 0, 1, 0, 2 => ((0 : ℚ) / 1)
  | 0, 1, 1, 0 => ((0 : ℚ) / 1)
  | 0, 1, 1, 1 => ((15757 : ℚ) / 100000)
  | 0, 1, 1, 2 => ((0 : ℚ) / 1)
  | 0, 2, 0, 0 => ((0 : ℚ) / 1)
  | 0, 2, 0, 1 => ((0 : ℚ) / 1)
  | 0, 2, 0, 2 => ((1 : ℚ) / 1)
  | 0, 2, 1, 0 => ((0 : ℚ) / 1)
  | 0, 2, 1, 1 => ((0 : ℚ) / 1)
  | 0, 2, 1, 2 => ((15757 : ℚ) / 100000)
  | 1, 0, 0, 0 => ((1 : ℚ) / 1)
  | 1, 0, 0, 1 => ((0 : ℚ) / 1)
  | 1, 0, 0, 2 => ((0 : ℚ) / 1)
  | 1, 0, 1, 0 => ((17961 : ℚ) / 50000)
  | 1, 0, 1, 1 => ((0 : ℚ) / 1)
  | 1, 0, 1, 2 => ((0 : ℚ) / 1)
  | 1, 1, 0, 0 => ((0 : ℚ) / 1)
  | 1, 1, 0, 1 => ((1 : ℚ) / 1)
  | 1, 1, 0, 2 => ((0 : ℚ) / 1)
  | 1, 1, 1, 0 => ((0 : ℚ) / 1)
  | 1, 1, 1, 1 => ((17057 : ℚ) / 50000)
  | 1, 1, 1, 2 => ((0 : ℚ) / 1)
  | 1, 2, 0, 0 => ((0 : ℚ) / 1)
  | 1, 2, 0, 1 => ((0 : ℚ) / 1)
  | 1, 2, 0, 2 => ((1 : ℚ) / 1)
  | 1, 2, 1, 0 => ((0 : ℚ) / 1)
  | 1, 2, 1, 1 => ((0 : ℚ) / 1)
  | 1, 2, 1, 2 => ((17057 : ℚ) / 50000)
  | 2, 0, 0, 0 => ((1 : ℚ) / 1)
  | 2, 0, 0, 1 => ((0 : ℚ) / 1)
  | 2, 0, 0, 2 => ((0 : ℚ) / 1)
  | 2, 0, 1, 0 => ((3513 : ℚ) / 20000)
  | 2, 0, 1, 1 => ((0 : ℚ) / 1)
  | 2, 0, 1, 2 => ((0 : ℚ) / 1)
  | 2, 1, 0, 0 => ((0 : ℚ) / 1)
  | 2, 1, 0, 1 => ((1 : ℚ) / 1)
  | 2, 1, 0, 2 => ((0 : ℚ) / 1)
  | 2, 1, 1, 0 => ((0 : ℚ) / 1)
  | 2, 1, 1, 1 => ((5837 : ℚ) / 100000)
  | 2, 1, 1, 2 => ((0 : ℚ) / 1)
  | 2, 2, 0, 0 => ((0 : ℚ) / 1)
  | 2, 2, 0, 1 => ((0 : ℚ) / 1)
  | 2, 2, 0, 2 => ((1 : ℚ) / 1)
  | 2, 2, 1, 0 => ((0 : ℚ) / 1)
  | 2, 2, 1, 1 => ((0 : ℚ) / 1)
  | 2, 2, 1, 2 => ((5837 : ℚ) / 100000)
  | 3, 0, 0, 0 => ((1 : ℚ) / 1)
  | 3, 0, 0, 1 => ((0 : ℚ) / 1)
  | 3, 0, 0, 2 => ((0 : ℚ) / 1)
  | 3, 0, 1, 0 => ((17961 : ℚ) / 50000)
  | 3, 0, 1, 1 => ((0 : ℚ) / 1)
  | 3, 0, 1, 2 => ((0 : ℚ) / 1)
  | 3, 1, 0, 0 => ((0 : ℚ) / 1)
  | 3, 1, 0, 1 => ((1 : ℚ) / 1)
  | 3, 1, 0, 2 => ((0 : ℚ) / 1)
  | 3, 1, 1, 0 => ((0 : ℚ) / 1)
  | 3, 1, 1, 1 => ((12097 : ℚ) / 50000)
  | 3, 1, 1, 2 => ((0 : ℚ) / 1)
  | 3, 2, 0, 0 => ((0 : ℚ) / 1)
  | 3, 2, 0, 1 => ((0 : ℚ) / 1)
  | 3, 2, 0, 2 => ((1 : ℚ) / 1)
  | 3, 2, 1, 0 => ((0 : ℚ) / 1)
  | 3, 2, 1, 1 => ((0 : ℚ) / 1)
  | 3, 2, 1, 2 => ((12097 : ℚ) / 50000)
  | 4, 0, 0, 0 => ((1 : ℚ) / 1)
  | 4, 0, 0, 1 => ((0 : ℚ) / 1)
  | 4, 0, 0, 2 => ((0 : ℚ) / 1)
  | 4, 0, 1, 0 => ((3513 : ℚ) / 20000)
  | 4, 0, 1, 1 => ((0 : ℚ) / 1)
  | 4, 0, 1, 2 => ((0 : ℚ) / 1)
  | 4, 1, 0, 0 => ((97 : ℚ) / 3125)
  | 4, 1, 0, 1 => ((3028 : ℚ) / 3125)
  | 4, 1, 0, 2 => ((0 : ℚ) / 1)
  | 4, 1, 1, 0 => ((0 : ℚ) / 1)
  | 4, 1, 1, 1 => ((15757 : ℚ) / 100000)
  | 4, 1, 1, 2 => ((0 : ℚ) / 1)
  | 4, 2, 0, 0 => ((0 : ℚ) / 1)
  | 4, 2, 0, 1 => ((97 : ℚ) / 3125)
  | 4, 2, 0, 2 => ((3028 : ℚ) / 3125)
  | 4, 2, 1, 0 => ((0 : ℚ) / 1)
  | 4, 2, 1, 1 => ((0 : ℚ) / 1)
  | 4, 2, 1, 2 => ((15757 : ℚ) / 100000)
  | 5, 0, 0, 0 => ((1 : ℚ) / 1)
  | 5, 0, 0, 1 => ((0 : ℚ) / 1)
  | 5, 0, 0, 2 => ((0 : ℚ) / 1)
  | 5, 0, 1, 0 => ((17961 : ℚ) / 50000)
  | 5, 0, 1, 1 => ((0 : ℚ) / 1)
  | 5, 0, 1, 2 => ((0 : ℚ) / 1)
  | 5, 1, 0, 0 => ((97 : ℚ) / 3125)
  | 5, 1, 0, 1 => ((3028 : ℚ) / 3125)
  | 5, 1, 0, 2 => ((0 : ℚ) / 1)
  | 5, 1, 1, 0 => ((0 : ℚ) / 1)
  | 5, 1, 1, 1 => ((17057 : ℚ) / 50000)
  | 5, 1, 1, 2 => ((0 : ℚ) / 1)
  | 5, 2, 0, 0 => ((0 : ℚ) / 1)
  | 5, 2, 0, 1 => ((97 : ℚ) / 3125)
  | 5, 2, 0, 2 => ((3028 : ℚ) / 3125)
  | 5, 2, 1, 0 => ((0 : ℚ) / 1)
  | 5, 2, 1, 1 => ((0 : ℚ) / 1)
  | 5, 2, 1, 2 => ((17057 : ℚ) / 50000)
  | 6, 0, 0, 0 => ((1 : ℚ) / 1)
  | 6, 0, 0, 1 => ((0 : ℚ) / 1)
  | 6, 0, 0, 2 => ((0 : ℚ) / 1)
  | 6, 0, 1, 0 => ((3513 : ℚ) / 20000)
  | 6, 0, 1, 1 => ((0 : ℚ) / 1)
  | 6, 0, 1, 2 => ((0 : ℚ) / 1)
  | 6, 1, 0, 0 => ((97 : ℚ) / 3125)
  | 6, 1, 0, 1 => ((3028 : ℚ) / 3125)
  | 6, 1, 0, 2 => ((0 : ℚ) / 1)
  | 6, 1, 1, 0 => ((0 : ℚ) / 1)
  | 6, 1, 1, 1 => ((5837 : ℚ) / 100000)
  | 6, 1, 1, 2 => ((0 : ℚ) / 1)
  | 6, 2, 0, 0 => ((0 : ℚ) / 1)
  | 6, 2, 0, 1 => ((97 : ℚ) / 3125)
  | 6, 2, 0, 2 => ((3028 : ℚ) / 3125)
  | 6, 2, 1, 0 => ((0 : ℚ) / 1)
  | 6, 2, 1, 1 => ((0 : ℚ) / 1)
  | 6, 2, 1, 2 => ((5837 : ℚ) / 100000)
  | 7, 0, 0, 0 => ((1 : ℚ) / 1)
  | 7, 0, 0, 1 => ((0 : ℚ) / 1)
  | 7, 0, 0, 2 => ((0 : ℚ) / 1)
  | 7, 0, 1, 0 => ((17961 : ℚ) / 50000)
  | 7, 0, 1, 1 => ((0 : ℚ) / 1)
  | 7, 0, 1, 2 => ((0 : ℚ) / 1)
  | 7, 1, 0, 0 => ((97 : ℚ) / 3125)
  | 7, 1, 0, 1 => ((3028 : ℚ) / 3125)
  | 7, 1, 0, 2 => ((0 : ℚ) / 1)
  | 7, 1, 1, 0 => ((0 : ℚ) / 1)
  | 7, 1, 1, 1 => ((12097 : ℚ) / 50000)
  | 7, 1, 1, 2 => ((0 : ℚ) / 1)
  | 7, 2, 0, 0 => ((0 : ℚ) / 1)
  | 7, 2, 0, 1 => ((97 : ℚ) / 3125)
  | 7, 2, 0, 2 => ((3028 : ℚ) / 3125)
  | 7, 2, 1, 0 => ((0 : ℚ) / 1)
  | 7, 2, 1, 1 => ((0 : ℚ) / 1)
  | 7, 2, 1, 2 => ((12097 : ℚ) / 50000)
  | _, _, _, _ => 0

def value : Fin (100 + 1) → Fin 3 → ℚ := fun i s =>
  match i.val, s.val with
  | 0, 0 => ((0 : ℚ) / 1)
  | 0, 1 => ((0 : ℚ) / 1)
  | 0, 2 => ((0 : ℚ) / 1)
  | 1, 0 => ((16487 : ℚ) / 20000)
  | 1, 1 => ((16487 : ℚ) / 20000)
  | 1, 2 => ((16487 : ℚ) / 20000)
  | 2, 0 => ((387658831 : ℚ) / 400000000)
  | 2, 1 => ((1908485659 : ℚ) / 2000000000)
  | 2, 2 => ((1908485659 : ℚ) / 2000000000)
  | 3, 0 => ((7956645473303 : ℚ) / 8000000000000)
  | 3, 1 => ((194942008528863 : ℚ) / 200000000000000)
  | 3, 2 => ((194942008528863 : ℚ) / 200000000000000)
  | 4, 0 => ((159847695547713439 : ℚ) / 160000000000000000)
  | 4, 1 => ((19558701228389294291 : ℚ) / 20000000000000000000)
  | 4, 2 => ((19558701228389294291 : ℚ) / 20000000000000000000)
  | 5, 0 => ((3199464954459117311207 : ℚ) / 3200000000000000000000)
  | 5, 1 => ((61161900628078808561023 : ℚ) / 62500000000000000000000)
  | 5, 2 => ((1956886455255730110143287 : ℚ) / 2000000000000000000000000)
  | 6, 0 => ((63998120385014879114270191 : ℚ) / 64000000000000000000000000)
  | 6, 1 => ((6120311086122408221320808983 : ℚ) / 6250000000000000000000000000)
  | 6, 2 => ((195704659875464539345527773259 : ℚ) / 200000000000000000000000000000)
  | 7, 0 => ((1279993396912557270328431180983 : ℚ) / 1280000000000000000000000000000)
  | 7, 1 => ((612433093242624502244614258863643 : ℚ) / 625000000000000000000000000000000)
  | 7, 2 => ((152897788928557645064309472127871 : ℚ) / 156250000000000000000000000000000)
  | 8, 0 => ((25599976803353813690663778738793279 : ℚ) / 25600000000000000000000000000000000)
  | 8, 1 => ((61282306995032938382335671735528911503 : ℚ) / 62500000000000000000000000000000000000)
  | 8, 2 => ((1911304029547224773736643909522546923 : ℚ) / 1953125000000000000000000000000000000)
  | 9, 0 => ((511999918510181947495301854709380789127 : ℚ) / 512000000000000000000000000000000000000)
  | 9, 1 => ((6132010242803627216869358696740727226416563 : ℚ) / 6250000000000000000000000000000000000000000)
  | 9, 2 => ((191142099025526086699072408415443011066799 : ℚ) / 195312500000000000000000000000000000000000)
  | 10, 0 => ((10239999713726269181550995415594054712203151 : ℚ) / 10240000000000000000000000000000000000000000)
  | 10, 1 => ((613567261399000125660087552117987136793874522823 : ℚ) / 625000000000000000000000000000000000000000000000)
  | 10, 2 => ((3823141964145865507365929575881323308258192503 : ℚ) / 3906250000000000000000000000000000000000000000)
  | 11, 0 => ((204799998994320383634788646894981914203969669463 : ℚ) / 204800000000000000000000000000000000000000000000)
  | 11, 1 => ((61392213306282063266995871878369449003427128355254283 : ℚ) / 62500000000000000000000000000000000000000000000000000)
  | 11, 2 => ((1911751843145091933197674053478428268653934932567271 : ℚ) / 1953125000000000000000000000000000000000000000000000)
  | 12, 0 => ((4095999996467047507709012516542071464598545448823519 : ℚ) / 4096000000000000000000000000000000000000000000000000)
  | 12, 1 => ((6142659899572861071972879840870365482958194735535631114943 : ℚ) / 6250000000000000000000000000000000000000000000000000000000)
  | 12, 2 => ((191196151284096188096020424658047622072824110676497956267 : ℚ) / 195312500000000000000000000000000000000000000000000000000)
  | 13, 0 => ((81919999987588737894581760970612297055134690161717022247 : ℚ) / 81920000000000000000000000000000000000000000000000000000)
  | 13, 1 => ((614599173612278724176357515359050174660255269737814093714688803 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000)
  | 13, 2 => ((19121980285082351765733364412230607840215309917456902188596703 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000)
  | 14, 0 => ((1638399999956399236223665726289760999554688166538111899153711 : ℚ) / 1638400000000000000000000000000000000000000000000000000000000)
  | 14, 1 => ((61492201526041440208909142206216217328945540159895740078377070239863 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000)
  | 14, 2 => ((1912459521543730592937606757077324844227547430926471961556590947779 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000)
  | 15, 0 => ((32767999999846830516853737696455930391435619529048387101726986743 : ℚ) / 32768000000000000000000000000000000000000000000000000000000000000)
  | 15, 1 => ((6152348359062148702388826912464145267348481610302736212443396725647312123 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000)
  | 15, 2 => ((38254884269505467846709306225553488237436030652512262794918002457852139 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000)
  | 16, 0 => ((655359999999461915605707180527649683465113331405546983888366904428159 : ℚ) / 655360000000000000000000000000000000000000000000000000000000000000000)
  | 16, 1 => ((615537946599595278050303103055512936816998322099672819330389964551118586329583 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 16, 2 => ((19130504121719037486505440890665176072205810846728506491488883313167993578651 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 0 => ((13107199999998109709522849325193633338012943133227686554399832935256122567 : ℚ) / 13107200000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 1 => ((61583164873712791221805724054696706235784346748075233727337087273746609362036196243 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 17, 2 => ((1913376508198248598263310601538277655563703085048273628474354664074184408670936847 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 0 => ((262143999999993359409553769679405233916439469227028862865606613101554758577871 : ℚ) / 262144000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 1 => ((6161162343603246639990739474219679161953086106801285078044955256059935452595513323896103 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 18, 2 => ((191372097131127636925836899279958532218371655763400819176202766995685593570696607762483 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 0 => ((5242879999999976671605762392883750586748451855394552395246876031825761866884060823 : ℚ) / 5242880000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 1 => ((616391986445779694990803675110120332743334921372743081631261807878978619431569162468516093163 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 19, 2 => ((19140823470947258431644993921630170816540789309210210427467703970651765013527983298171474759 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 0 => ((104857599999999918047351043286200615811247311368001062564502275499803901438363705671199 : ℚ) / 104857600000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 1 => ((61665917918650260693725027070148548492709269980623442659726642204048133482634722706407581212731423 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 20, 2 => ((15315674029809169467254250300127669629725118466227109027985144314436274790685357427352554234279 : ℚ) / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 0 => ((2097151999999999712100344215064422763344911804835787732789096493830811105752971698022922087 : ℚ) / 2097152000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 1 => ((6169180782645535508556275468326818598913280210043620216228019892564471242858081112121679077537212634883 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 21, 2 => ((191485037887157735874674807260950743759023434051063218484949552230244829212596617262615672263222196031 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 0 => ((41943039999999998988608509227521317167630675170388122305288095982827639414510189575154525291631 : ℚ) / 41943040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 1 => ((617168941115221805973812545763352200548036989968496492528932915543266379828719106259819897098885202491107543 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 22, 2 => ((19152544767030652919642448844784784671368922846186052779291789742480556681940995694154211050138287532203427 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 0 => ((838860799999999996446981692916282387209886561873573473658477081187673497263174295977517847349499703 : ℚ) / 838860800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 1 => ((61741201718300532064858443138081001763151171344267205972510005710565945249124808160619147219603890467510729533403 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 23, 2 => ((1915670365034378660481134540203311658970122736130987929877563751695092859096740472087968963932791373362020694263 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 0 => ((16777215999999999987518246687214900026268331491861863612962229986212296995885531301769020197738792456639 : ℚ) / 16777216000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 1 => ((6176475481696448354134831297299659908023171191594689347018901370962691502168019820946166958721739163903886781436976463 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 24, 2 => ((191609692257046306296271281391933943678594676260542125432749887838172614364202871175015898009533330288634897956047739 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 0 => ((335544319999999999956151600612185943792280648530910726872336313941563799346545871463114567954656377900172807 : ℚ) / 335544320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 1 => ((617875768274459059707815586218925192373955270302665404038320401920101655130611914191771002767126663444556096257680503780723 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 25, 2 => ((3833066172532662877046916143518179683551871471305234930518513312990190943428819865601223729705550054109248818029717687011 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 0 => ((6710886399999999999845960572950609220542281918289089383502517470876713627104415646449921477224707855563307070991 : ℚ) / 6710886400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 1 => ((61809690442721985049194982920129404521459455410224352643444212522092086759382087751165228372576706752607126580320998271827170183 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 26, 2 => ((1916977848791247039463348045074923436747484351637318763329326408863737568820064004163082659836156176568970808696032633869819411 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 0 => ((134217727999999999999458859492775490191765036378949571004244343875189894972017812165978574149490398696593897740391383 : ℚ) / 134217728000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 1 => ((6183111765137989463322344054343477217322484912921234896247238559275115106945347310246981770980873063103726393220204132884581448848843 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 27, 2 => ((191743025609420705685612485518832333565665810911041401097972500327903647884048984259249084559624129439829886757701914923817257156007 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 0 => ((2684354559999999999998098973398120297043670572799249842937910380033542101036698574139082730987159770621134362761994928479 : ℚ) / 2684354560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 1 => ((618518797594810627038003632356976841292267339467425345742126644366652699315410969279926027153485544052117233985745833980374628524444600703 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 28, 2 => ((19178894050668813676055374770104095083259035450589627385725125532022238030746509067878156529274484333322818167416644549348001349926792043 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 0 => ((53687091199999999999993321693547596603514414722243764698240879165057833400941922090950597633957892274192045016382888183746727 : ℚ) / 53687091200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 1 => ((61871997411746770517473026076925950521335591558260735871648100152876238530825000963466720994128999448144701535067982940700034298088049605889763 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 29, 2 => ((1918354441300302000777747946062633150792817430948672793704208048054392088060808606661274679694468531734703160846620536149720277769377568066719 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 0 => ((1073741823999999999999976539109432706868146138919242345384920208506848168737508972305509449488094075559236654142553086189502251951 : ℚ) / 1073741824000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 1 => ((6189149061208615076061042202478486726559220653313830961327136991562105662604668068907621784684117869702825724232688515770216420996768227457753460023 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 30, 2 => ((38376491138634699881511109702229343795958078034070778079662561747821474180446027168901428660021147159487166704459147563202239872331229929432822247 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 0 => ((21474836479999999999999917581891437099227797386023298359337224692484557616774869019709254696051674487439598366002788991783721411103863 : ℚ) / 21474836480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 1 => ((619103787434869966410010321368009535330065122629266940964532927793654144854879190947435903000570090670340844837417456317812073021111554049776966322935483 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 31, 2 => ((19192989885782975060972423522176485694742014049318052167283650203766072060215144045473403470321404809189516620226938597449932166183720794275015807848791 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 0 => ((429496729599999999999999710465184618529587252217099847136351670344698250907730114866238611747229532474375309059767797728136213317207870719 : ℚ) / 429496729600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 1 => ((61928680587289160265264352653763680946681960377969799142524334767051679627900400299330868045665919260388518791779362917054282501442270954635054434045662420143 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 32, 2 => ((1919777015354009538249754950777509682804738510217760876074676264140101770397529878952092185251318139186250464382738935601336398257585630824900297450641194587 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 0 => ((8589934591999999999999998982864193564894440017038671762990003417920924955438855893525096243068017347582480460726964273418942517383351249835847 : ℚ) / 8589934592000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 1 => ((6194641434185970473063054583958685423593881810324857258979478226903211737260295377840369596673245782547583118129356810399883556706360850133178692040451561282098003 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 33, 2 => ((192025795696709156763978897917952655276876092842723228364956691762523314068345393979977018582541316582848611319632470106981357048206917567009139501879758445455823 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 0 => ((171798691839999999999999996426801911993474167779856853903383882007156209368456700753953663101897944942057253858533825492520745063567712940673330511 : ℚ) / 171798691840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 1 => ((619635976406883794957917734670103053196424009127746713202302980885571090976412891046235920430781664625400758354764743309291758067899255486120876481680893550441095833063 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 34, 2 => ((19207411718944369589689615587301932971796792427690021089771852993031070578480643946734369043451228252518814604885655434094854277543574487035835914302064875775250931699 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 0 => ((3435973836799999999999999987447355116833074751410637127762587577491139763511388389748639218476967480581447132805029328955225377408313375560585410085143 : ℚ) / 3435973836800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 1 => ((61980247569921412196242396778244729921953919070466302153959684946400303681321575972986322441332259402620237970397212487428436408161784445682310407085166999600880967494769323 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 35, 2 => ((384245211126060272774696602442041618679055025591768742939031371351727802119434505258851661423207206844945386703082529808611260121889684255595616354187184975502300114742683 : ℚ) / 390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 0 => ((68719476735999999999999999955902558525434591601705568229829970159726373989215507413186969574509586759282623777544068032619706750835404888344336545629107359 : ℚ) / 68719476736000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 1 => ((6199638068535105156167103277516061056498891421375657124742539107295547232852833813627803082477769924099905216330327545091946097671697034087664577723826660494709348910790892930783 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 36, 2 => ((192171203900636057936920522438610062220058108948535351888036008232285915027911821977188126203124656734293304033037953652956541635444807319382148320763868575892639813437527684171 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 0 => ((1374389534719999999999999999845085688099851720296791661191392685171118751824114077542525824115252178285359857330512310998593029815684777372753654284795054152167 : ℚ) / 1374389534720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 1 => ((620120130288777549211967639165747228866077142441424417235851255144126748624566994393122420010716841169104206957147801328509769961684998692586420965062427326798138694171791694184821443 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 37, 2 => ((19221985865803936670004059960130618511355142992550720197643163347083244104131268782223517575578310421563774793569287329030795829782214662325356107727946995597680034207189399099719167 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 0 => ((27487790694399999999999999999455786022294779093402629105765362503006140175158112754406893220116880902316469178802089748538057313742500622910483587502485025236562671 : ℚ) / 27487790694400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 1 => ((62027160144461389408442816364385576394567532017683840929220003352085845135108826472100449011464570662512346368265384354043445722094283619462390966377268788558778806102863648149726355025303 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 38, 2 => ((1922685195090949669850274254895893892476277418223012752742709527427958315330486418378462833744275500201246630472533001762633440408860916793858588248018207536132224047874487809502316085603 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 0 => ((549755813887999999999999999998088176296321558955123436048553718473060570435330450106231415882270602609837756225131741286614195343177404688284528842896229893656044663223 : ℚ) / 549755813888000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 1 => ((6204183709357730788120475134439663922828231111679425283859351019551106130048728432943793129786865592130474157124501988223200120694440295858074194600492511255434579995357471745550527688279806363 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 39, 2 => ((192317139197545413982431127389737935515654427321852376259891922694811775900368368162993278292597382221763691103988300021134344076900132904745573690618567309911269525534824144660059875868042679 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 0 => ((10995116277759999999999999999993283763328977636609348630838569212995861783939315871223190963994416626968360037618887807139875668240582222669943549825094455616413684901902399 : ℚ) / 10995116277760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 1 => ((620560584701926682445721558626598210277430567569337504954671351170861991719542422475728574116792212742307805248496911358197308381180772755497600465020290222050094971888358442629608431520614560708623 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 40, 2 => ((3847313467898612063937866521519338880047837961522222420522568958066587826451364011903388925405768382039334121290625402341096763076535197327292061040484894330587905241154399016059912583574600928319 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 0 => ((219902325555199999999999999999976405860574698437408641740135893645254462446978816655607069856512385610539848812155152866482383222529165348239511690535556822580461275060383127687 : ℚ) / 219902325555200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 1 => ((62069838415277887822260636144681675156998291584784548465782198870570237232936999286454733272023412387086511440239961616177999246031021357837406439311123691666371183681675677769485795734311329772030156083 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 41, 2 => ((1924140805643606460933852563532469327002487300652512056275377329867674083355952451467099538269915510366420452191986395327959698688294307358409724978001089756822087543507654004235778466347722270140725551 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 0 => ((4398046511103999999999999999999917113788198915610616558433097394375778926576236582911147636405928010649826488877101052019952612260744957868365404568851411117725160459287125927564431 : ℚ) / 4398046511104000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 1 => ((6208319063086766218425766599875054781030050263972162077293153438880134291969480489516318263756064240549450574046206710710489307208617434903185622086312113755410482223300881974497231735376393023283108369052743 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 42, 2 => ((192462321829924846757405859702076270399461843767749909406039835045303460992453257668142185987588004294012067745297990038467248890965974277510697136081572591168670999432840183138070112461457096075442668129747 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 0 => ((87960930222079999999999999999999708820737942790540095969775471146442111369062319115766861646694025101412840455425255995746093526871997036991567666250375007256568488693475673383533846103 : ℚ) / 87960930222080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 1 => ((620961283936855299500583080461492942447520907270039226952064948710595931031022122234085822013795020384162962687103391265463129908924355500439010271877957739393406111371987161382011081334034617180548380753076382603 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 43, 2 => ((19251036085151814274592897541880262610386169689325194943305071740121097182645790462495388125037665495405890021930876093706240011338274934779285515040132332828154361936704667936872673095396856904584554282898081383 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 0 => ((1759218604441599999999999999999998977087252393023167357141821230137451137239515927053688984964836110181263308519908924313056026559901325590951377211537567400492325100780180040596354401359839 : ℚ) / 1759218604441600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 1 => ((62108664568345531100408498164396813729364580231649084134854160840408362328531960595774375463693589822734386351146388691464947571883648640245911119257656301348595333901784100385543847026726877181787084405688217830809663 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 44, 2 => ((1925581637048745160002509959022794741313387826222047894240838531355701637919655658510659452498987752820112926945663198928509755739799150563916233261700824422438005447022018259065269607140975204493138164728740902799659 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 0 => ((35184372088831999999999999999999996406507517656690386925639217981472865845122419451739609404181469255066778002830440051111765821304933356801012188144131474277929538079040772482614993011977114407 : ℚ) / 35184372088832000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 1 => ((6212081162014408581505181838137393550317546291776121250940706038181831228438756324751896534589839880185798793031184895449745053398091872143415726691477829900574402512693971219998183086656787999256507972850508284884084277923 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 45, 2 => ((7704227950664189101613713172456768407442015643683260556857645757430467082149222194593558909172807820402515905815527241057959248265451696445803228667750229778694668927324741558711444680604977620048018511876313425890571831 : ℚ) / 7812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 0 => ((703687441776639999999999999999999987376060909527953329269770572768914177713915059533961247836889501493049591123943335899555633330244230882441955816950333869138366467271670233731426470451075602911791 : ℚ) / 703687441776640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 1 => ((621325816274548133913526099388160883470184901521985713990473146512495438841131359608881406256891262620167332779738301710617854066912187979903378518882667909955454773139093803778040796076444767796345017108917349823699122527611383 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 46, 2 => ((19265293660404329312155061427258602964568340685560614134273209568503201088956835207684371065435424132521077013171558123597425753177845101068225066613831506116265683053282769160162427353703206222732201316535680946511077378372931 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 0 => ((14073748835532799999999999999999999955652101975171700045724704022137195506308983604142805863650992818745083213618412939015138939889147983090018590784946522882283081399525377531098501190694628593029121783 : ℚ) / 14073748835532800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 1 => ((62143986293738615983685024926315236929924025134312357488360885615744654511039504114802073340966716009606536374544285418626889099921645524458764882547146591708212312210667353078615167106680057043709734255125712904357992900281868114043 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 47, 2 => ((1926998498697169062020188863696301198551421874515713881411612809561398230283151246165846315163349309218918509547905911210026097624410961147157363770945436403907358738125379299509568518083841012634104845426606323926036168540001826327 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 0 => ((281474976710655999999999999999999999844205834238778182260630885229767967813663459401353676999005937772251477329441484654760183095830576864595235309427517134885460464956532651266749034682910230247311304823679 : ℚ) / 281474976710656000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 1 => ((6215503695918096934355144175260241196950603449731564183672626465795149774981236289448429052490562502149923574416760150895425988688751420442489579679607216137623226074758321753382315417443319637928827921924139185387316482510074533159169903 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 48, 2 => ((192746413200253539183925667554569378917041204391102910929630640699988474409087055047621645668141666119008161929484686858213496998107324107187460113556602225188704026573831485853904822337599824293434067325203640514859925898179358170843163 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 0 => ((5629499534213119999999999999999999999452695095680827754281596299812174870929399732876955467297507859393919439858327935592172523215652816525323061642018867694852622613392299203900089358841063638858804613845584327 : ℚ) / 5629499534213120000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 1 => ((621657446119679920551276050006016331008987925827911858219061217316252235020020211142773047043912823345972446380073919932789098164343349947645594172336122293150950295060270135395693181246446593346618876192952323470913126818231411743280721842963 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 49, 2 => ((19279260311955822335398110468367797935649833075304269383253735328448212744516079205970844596751839442975957445037773952450311326031416164472957624392102429177234118288149532863378046260716074579615683695969573452310437078633464319038458602639 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 0 => ((112589990684262399999999999999999999998077317871126747900791247801240170321574981261596744556616145110050838992222306037735302074056588344453459915548412282212017263240847147103301013917608656563310980608439537740751 : ℚ) / 112589990684262400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 1 => ((62176119899212505581736444141382958409258285551876563121837792466804097858067572814673377888170550488984229043789294481303841416710163127995253918518327240183139345625054303084351089977344477063927799396102212072543648783516098183332589071498477223 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 50, 2 => ((385676795892176062660841817758709946576119610893997987281400575292998897777914394244519988722025155706231539978649463026021181753816281123538664921562752167998583860853876667892652281811850016404212663679076832922350136894527321119329742956015191 : ℚ) / 390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 0 => ((2251799813685247999999999999999999999993245617681268265375479653525756718339692909171989363627392517771608597379676961110564116186160794854065004683321572347410816645765096027773896461892559210506911474877448096083258263 : ℚ) / 2251799813685248000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 1 => ((6218617313754094940847934491523443138020177928371503324161868218442691342576832088215124247130653429727814745202713854307409684813125656293866818254339364129680494202075181326372586525698998010016165741823596400130483168635045816090887222924571478296683 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 51, 2 => ((192883777704065071879353078949453941882896482784456171500911216587232103487676520286608361791199290833986526706103653411533214753509797702147552011294999912649718425432116435459814233220007510222713947840661058585256928254661658059676135007265592026311 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 0 => ((45035996273704959999999999999999999999976271854914295416264060022835983351527341189921198634423029914931661002594805164381411740161982872322330361452508683656454198876572782345569698270628560506510780011244475161540486277919 : ℚ) / 45035996273704960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 1 => ((621959143233516783388401460490655546301544969310330340387537206563032396865425160269001694577858291879002886014942444125749195013743705714354032891617011953656402265722045707130002186656310618277476143471619561792000642285389109357843445140617163550635005343 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 52, 2 => ((19292872403847236414084045583564063137073094854934701016195994459625382959771856822248070876091719867333556521999282844831741116182958546807794281057111229856686124488271646718972300835078650517511658766925582783489712187521295463511194838287690238376208907 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 0 => ((900719925474099199999999999999999999999916643026313919797335642860222809513915549600193170802728104091154925102115550542471899443189045830468346559782663005685123600653400184379986350024718133059372370179501841242491728294329447 : ℚ) / 900719925474099200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 1 => ((62205353142754842243202547915702559814433479217213143797286730254874223825511275527274301055563483372384439517070163728099637056150919966372796588680454421903312720452432952222266699887611074275807380717087827670709770002924824365818386658528531339783646616387203 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 53, 2 => ((1929732201336832947567762622532617049721084461086854832682918188196475249766000079194642239983835542577415572699091927613014059109997090805780375847796699887698129738190607914073150273821443050517724873796768366882843214423746188840091549229363898202112733770943 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 0 => ((18014398509481983999999999999999999999999707166951440800248040113367962729822385325745478609029983829672227251883731929055703782743923118002435301464516495138971839209095394847726892047636834801437575136440589968284873441497979347311 : ℚ) / 18014398509481984000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 1 => ((6221449898120373193997354082839915235779328448533783605629854938942492205411848277000990342426211071704863706668735655727571603473182162208202450699177060826531992202760308462492192162994392141693977925950775291288790485069022187675908438365870073149274058082225906263 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 54, 2 => ((193017250635580984985116574220743609951774247425541560815980853598208465512400937399789661687863386620702549965407017299616275065968917347455056567250113111243019312995603140807591838821300820027718785300969186961538823795087018677333894260005711820150929173258851619 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 0 => ((360287970189639679999999999999999999999998971277500411531271364918261653069866039649343866353522333193638534335867550266772687388779401913542555214044846447423208071141552122100064571763348200657450201454315792558584760399982401447103543 : ℚ) / 360287970189639680000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 1 => ((622233609328271681005567621210856426686073493992436401099025840231751017435735817811744968676668465840010271756360624671770714483677379529765029187598141819874460725394903827184061240483176624929986486970372611751788333811102561197127461879073983683269245113209012536306523 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 55, 2 => ((3861216031540586264187119784345728921551542467610610417314275343865885843642910102631823024424510636790993212198989141373838606865804577006640159771617426985435440519137942370510832290847844059030031055867987108616055709500089382792701627347800569924164803361213119876427 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 0 => ((7205759403792793599999999999999999999999996386097858945709356304957853187234439397288145002499923956509252171121902704087172450796782038922274996466939545569797729953920272604937526840604642228909622557709011379258308263285138176283674746559 : ℚ) / 7205759403792793600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 1 => ((62231947809472212802715480224847144320173771734650803304544842098329802861731181436912962838440589218824657984588862486195089513362932074721924085236998767410736783696478374024465266415629890998921036116107268656818261514846089595682814079809595223203408346250572160694275211983 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 56, 2 => ((1931038603065625586330915852377271821301840423625254865887025625098624222219383460850804880834823754498981387806533239805959087559261707282564232437350230782431584913075255990901941968596831622337078135183048537722230138518280252611529448219732596534136480708421806533753085691 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 0 => ((144115188075855871999999999999999999999999987304361778476276968699316938246754585602673253393782232859217002877151244199458236819649095302733952062588358623586699425328121917661145531791044108150159504045231756975334436928920690413284549384661767 : ℚ) / 144115188075855872000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 1 => ((6224026814946619531731919171866788896047557688703968117787053106144770776583129798146300286333576958022008373668213424248215242468562833064864640730055200674740011312325869448454326153069639251920022190568136367834563006018445431645671291764472647264046015476278664176546522922726643 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 57, 2 => ((193146415420165661454983824013758303395919985545853823405530084653094283513757304421980147128699819670159292377406964465399135430938426800099370502517476842333332319755898406774807699831474696304868863489959076170844582868807354047827990380440740410422419044309544865481883686677487 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 0 => ((2882303761517117439999999999999999999999999955400222927787160991040700404060848859222191139172356984034429331107432320872696785947427271798504373595872903844660075081177692296743604253181937951931510337710899162254349876931298385421868621988316787471 : ℚ) / 2882303761517117440000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 1 => ((622483302261067646146696040077204376871424148095642173507168471226843343044325420290505881549073033808938934193224877455018622121598270821662702798597571179391521286601138385719309514731299108040282193006750772038973207498979801110652634220851749265389826878277472775260251856891761034503 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 58, 2 => ((19318845669602194026920108771308203088767676015255336980127587233842266460677591359692379463956854691687889606447041930991391505235660398029720474362748790580180349552363141359351836519718327180592815549208183872330109313239746584687971071204339829592903179218616689710857614427806264723 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 0 => ((57646075230342348799999999999999999999999999843320983145316296561525980519465762042447557471912490084912950240180409743225783809033312005828145864442301511206290843760177233038460281741428148025135395816378388756999531117659651227987024469044956874385623 : ℚ) / 57646075230342348800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 1 => ((62256142055888410641030259499320795301333514223856451283676689044712905736664143464330998284142931158886107653609624470632535805142441850569182497962304929217092101074720427177467821619271791993980984105081598782945850147388343851638071236777088421947183121615188288724313987429545911915999563 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 59, 2 => ((1932299750321097754108680375392168471045760877539458422856638034319384055249115458156931871049823476485256827923035388058478677637109582197189077255316871216458132715026089368570528574343563043970628828177731009381078673143079525777658950434838331806976759660759997625423503837715216646946599 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 0 => ((1152921504606846975999999999999999999999999999449586613789496149820640769564883222055118269398828577668299194193753779427952178521134025076474276421785805208867699734129502619664110969757637084012300645502937279703339352816338354763918416959754933499716693599 : ℚ) / 1152921504606846976000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 1 => ((6226371140647363437473268024446187781518012193707512852245412282704730429774017304257494905612744247663664384654150529677962407146666145697902357116463215838942073310821633723437152788465838054607088085694774891181232122613948781912486656190173286348867056819000679369988344317823883307813230765823 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 60, 2 => ((38654192477306852762858925765086734662935879373955487823126687562149637854774942669922835482161111979985479608166114106993141184284837387216808706406705426304797032271883167378644863087332649706398841278660467793386949315433700616672186914260294515139539373377134798783858856927983917135677922863 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 0 => ((23058430092136939519999999999999999999999999998066397774242499974319911023481434759079630480398084793348735069202657027130396003144743830093654133069733533698752229165996942702880021836758579076135212167651818663597831146443796640285645398779619081384504744613287 : ℚ) / 23058430092136939520000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 1 => ((622710458044166927637409778496737811277969309512221459612424343341318397111390252298087549154251713449588551267157685473881160108041237572593521471786808818368917661124900236478785094624386134948820063456074874266510689937359437461359349553618932304067628088275312640456616113429718832133622242611357283 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 61, 2 => ((19331141172048418279984799353040501424306422021883583487216222581532615399569443903237192340241851724086740605875771563934799394455544633491496010720217576872525447306231655402779267089032108421052998166997816600984688720234872306610852321871274295470644140125197333213692808403298564854751123452951071 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 0 => ((461168601842738790399999999999999999999999999993207255380913902409785847425490280308646741877638471879034106298108934136309081159047485075119006969473973903883716581060147259715217516712532888294463000344960838965219180817457057597323472285912801832903765167826477231 : ℚ) / 461168601842738790400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 1 => ((62278152542647598620354457897219906961590114214333528689655675918198465515225614099061683277481060796944627545245781709829545242624861825274127635725260385041021931014514028849058008662277682040071697611630024036930255111842145823975094636130740375260823999253297785306367665876715153702649194764009284277943 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 62, 2 => ((1933513169437087729638235866626395993703558091255117187159708264564292186276485690920985481268036880861718907219853056949992794655644452851333569037509522784022010755313737804846142018037420632656386856544659700172863935159802052455117003486740030567418094526133826125198270126048700466882926215630448632067 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 0 => ((9223372036854775807999999999999999999999999999976137088153150539165577682005747354724276004216143951711046815425256685620853802111733815068893071483762070324343496349264297323379559136211128036578448520211847427284814982211726643339397358140411672838990927034574414512503 : ℚ) / 9223372036854775808000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 1 => ((6228503868772381715917865552409020104950235706909204089025293255259701756542973949833244327348292880105163962246550612963489755166242074011477329402795106404276401094266016131434282276805919588948051318647125549478736775355791127540138853385347538059173009283874336560698045114823939986349291652578735815206111803 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 63, 2 => ((193390672862412869717200884948661597181174205889046187249923692567286906836423242075088792470863364505280744105863722632079967719487936500534407886123872977029575881455287799136730403819994844779760215520079458639532058607092867819616601349555843818260843615131833101401929245723656250348244990481836851227724503 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 0 => ((184467440737095516159999999999999999999999999999916169590682017844088674396886190457146381602811313702360907462588926736586059406818520892337021360122456153049418702674965476497032391245509692792500089651504220012051555032509795698051302919147266206683375126672459918182423039 : ℚ) / 184467440737095516160000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 1 => ((622917110868568698745577500566224412089258039056624047301714417785014914447360957384622789596568303861200357715789493788494120754040198723804459329786290880466040311701298471144270408444554238400742064608814365677353439445995109742059351924705026640007645044442651358242429441126103280497361912003948943145273665122863 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 64, 2 => ((19342947512947278450561929906569189070647228717395212156404059560760023195206734937241628335009560976473883885219686677615479058398628576334895287485929921303472595515635370149901754589392394679907606820942390402635535818002382259620963673144941753805942484832349910839829046569777318212419427888028200910636586287579 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 0 => ((3689348814741910323199999999999999999999999999999705503772065928686283513156261187075955238570676145036393867916074899625626826696153463894779956038110188465662607902497153718934074790445475550780052814945734324902337112829206912287254227154964346184078696820000351692574852136007 : ℚ) / 3689348814741910323200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 1 => ((62298176374720832633651477494864880633800746952429762062961462044019814184033463255698275646262573245170936169131170590202304077872323593585378294449799174190460362509689376078454206795830790838008009622448787186034698698084721499127474425613250209627630765235478213395042204264766260301176150377781351737161705579914855123 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 65, 2 => ((386935440393758131304793955556370382432418380717843801939038810744909930844829160269054645947990709170189977528135668242342677711147082761751009266245187174005297305063606155549174928462577447205839890157817770784895232449484071414642530641949732752172268915925262828497118190442875008743767398020552720584426842087634499 : ℚ) / 390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 0 => ((73786976294838206463999999999999999999999999999998965434751267607474913981717945550197830753098785297512851657989171122384827042183587118662361985561881092079872741561472501014615404738834955609890325538904364683381910277369003882865124099995389748144668461928661235496015455553792591 : ℚ) / 73786976294838206464000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 1 => ((6230444098004949798870293563342427473892757176702618739120383253256187568853784262816285030245402764370039535742433094076513771166035220532185025166757212348150641883743128297683130828209044589851399395578234467518459232955233975584232820465768158484274919720332846243774866188817422040933796996755715405883013045498474479732583 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 66, 2 => ((193505405270315860220010768904952216302336729544566652083532784847963885271554077502954327606570008383555221121236892097299803993050154044990910663872098801958561093520655779720074327400745108333572086917037085946911407990840260904381378264696291794106301028615312721849602914719446411485394515579642173187247801895868903022451 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 0 => ((1475739525896764129279999999999999999999999999999996365572281203105059372817775142717844979435636032750162647874515958152937897399190941547860877655278888276476592941105452896064343916847527199057544713618171033132720650804397310640505180963283804185232220306755386920297502295360473372183 : ℚ) / 1475739525896764129280000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 1 => ((623105111320287615711335965113627852510312599393776673338920269193448839448504690613176779691458208822871976860324422330839564023033597122813512726290326315739537468081119100836403244924671324070700028894161844081608473194192510411371732404782038675806925520923685518716276603297963570508545683695704300938340133942499222952572659243 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 67, 2 => ((19354252826579005722368581939458465415798817192090484337980669896194158821451320967219442175700011600476860540730385906785383643513693142735061227127726335112347347980500545876631585718158875342305386675284314223261218334277115616222608611921191401054698811681581627581985286044970769425259365290290312407522215277915465251797472647 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 0 => ((29514790517935282585599999999999999999999999999999987232255423866508073576708844076367789412757389383051321381983174560991270833563357777657635263202994734515262271002103456023874040179885363050289154578940634839395247646275847752280094700724016004102720789937631674251005125563601342956478879 : ℚ) / 29514790517935282585600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 1 => ((62316392866490588811965609675650084396839249630859379762047023894648907224567652835307069141148580675081094745636270333636128004055517187854977347676243893646251501405869559288650620732637832361339589402431351554090583037463569813642964315257192858246429206508692578293613178577809224597412935732438431773257693882117870040674241864619103 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 68, 2 => ((1935790877682267237198625704221789366622742512785995907726850256373393750589852151429173216686699770295624460710062941789967971232137069679369403398218332619672743764322449446043225244504415503602880650091082609853035033617952068259408942103979619748149367832228130881499525107133390140569260390486453428230291564561319345664567457550283 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 0 => ((590295810358705651711999999999999999999999999999999955146913304043042862474978169240280044207016708902659292014906892232762334438308075872911272679632120502352116358030389441011869503151937280395665800035818450190795504981367053153759972683643468222412858135050900071643781006104931517806110301927 : ℚ) / 590295810358705651712000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 1 => ((6232209203191472093524219715131790577716135932231750377501233958743216294536629527220523304656871907364553066758217452510665828573908511747113355954261340998755530824078476361266314576951277897190971071846460208567591819474978717348259201384611649978682731728278683750607042520560375423326231549174623837527382409752274434043427180015646276163 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 69, 2 => ((193615082991950553330358700374812560654770665733105219312019443759337304857937376389905953710765873268047693935288977030043440956902538670874110514398359215199496575424157408774803463502565714376154663643261381665066469172079049877987056392687156942366584778502920149988258463102844465846548109562621919263808327746299032711459329827660274559 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 0 => ((11805916207174113034239999999999999999999999999999999842431106437103209575874598308541103795299249698375042092848367912413694080881776270541537300923547639324762984765760758106274697564572755666029973955525830215520264608999542457729158784037639503865336370628433811951684602674446624422052865490669551 : ℚ) / 11805916207174113034240000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 1 => ((623276142952440879974122793517409979818382707289527683104268327626254787752964213781621382577919842472981575081761060769217091463641020157411178114442825680139762500694727084599230397342977770910607941441144918494002771930249438350857916056019791819991177089172245281673006733029195684193274212438947946049412509102709344070669243869692149221574423 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 70, 2 => ((774602054971904544342811437755424862529724944492057724683002228660113578883390123472668722052403465247804439961172312447864953613267900507699512317228270583713988266489390739507447556540355256648776259293862459121973480135473782102408598350404883565419392947018479327082847006612302951149190803377990080049045112762054467748471026377699506098267 : ℚ) / 781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 0 => ((236118324143482260684799999999999999999999999999999999446460476913543575240047463857904897632886264190391522872176316476309307306137680038412420538144422856947892365482117543227343012544344090654763298505762241547122689571415392654002534808324227577078926670017687981386268009195330991594671716468722132663 : ℚ) / 236118324143482260684800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 1 => ((62332965147519711505972602200662957404482010805526074356178771277498737380077262535387346725312396436498178998485699331343970897875452289493069543509713032521375575049788322011082864255308698114987105696542736619734148431959858961687700267051694492393795647538456454786199250508506255631714325112077721121104904938848079354422644047157640270484173337883 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 71, 2 => ((1936853803830328333573516337789929955034388828144644817533218626486005847899161763837009986409800378936160688144874632568322121504753341145120182914354716752962322139311288654588966309505625417484324580833243478070986827157405885284907806501454709755411081652507272114247770241921474650230547400709421120677599894537763549048751130952699422046934699831 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 0 => ((4722366482869645213695999999999999999999999999999999998055415655397278579818286740532819905384329446100845419849955399781274596566461669974942833350501357496457945879938678929357656003068280790470183467650742754555042008464382274393510904781643011478278269391772137878609959516303197773472081739954620852045119 : ℚ) / 4722366482869645213696000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 1 => ((6233814990934069966082721262835437920664688919012254500361497994452706477809659959707943388459647532164775637635588084856437101434515377028351033136119344383718093760823410744984026468502586912045979403627955284268024075345590074768354201807911696606931263215141563189933024157464954186662788702729301304573994468928876782333618184978241229525936357940870543 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 72, 2 => ((193719683795252906226018781479957359791246894940039533452248092845905400163904672734683492275519319971738549401338885232480505462418498615678392989389756798649610596790536092710127517358622024169714863836982605503280552002144106979850133744668969922222510345612574914896413272660548314505015410475011607857923895160199400546006786057367054304896749488599227 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 0 => ((94447329657392904273919999999999999999999999999999999993168675197410639650901641319491796327615149344152269959932893319431617657737979846621974173560311268885056763876224579078833445538778870416921754521857059296751862575735374929944403808497911899323191560373295520367556787780773133778207423152460583053234503047 : ℚ) / 94447329657392904273920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 1 => ((623431737361547643433551359483702592760725697496611412059039143678811383508205378294134414088662760241938941804359394567622658643918782543166702609933091467508963166355381776612640579811865391865257776742563608835763628472005785041799130762971207724143873615751156015049268901417809539170554222466056714085935027944880203655667683139266631782656424180804949556403 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 73, 2 => ((19375342535145430388386339812776985812637133957254259319924096509858762182629244185391562176209305838601561719642784667717505456125650833436523617314113451167173323481415656081503966489425790584417151448500178205419870702108277627172088916898811944154544694980344790583226363810990590038384263717551466981545071208928782163192234505757527493191291265167575142063 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 0 => ((1888946593147858085478399999999999999999999999999999999976001555968503577093617465955374680498912019646006924369244254231163272831633523201182995271717373487593204411497176946303941894177730171774646123635283849309489293228558372128894690579253164502322371951591387163051226995473856018962842677534594028266012809204111 : ℚ) / 1888946593147858085478400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 1 => ((62348041623384520458137392528532846428143277184631659382732337704258282633393611691702722768692240982238424988130884691575727660471369812025754625956357500278389027109002143962314451208870476310278219559267616281433149374499939374453658414170813039846753074764609689569703373551784212074703842267924218120201658177601628599458344108502336494350647771318902460332459463 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 74, 2 => ((1937866068809521744326137264368757968799078124579280018033092052356119324648339166282231846792577186280605001741530124436214806565211185063352562576431846836642795779191723444004834473201152347478614311097901937449432863513268230111521243375835489290040718505543350961812080831267271737658825376755074445910126917571016656239274519934390247263181031575215441072307539 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 0 => ((37778931862957161709567999999999999999999999999999999999915693466117353066329878157901231252592677925016422325309155065114076577457528567005755862389543133061914927097589582612365747874246366093444331832330752162624235887111925561288807048004916366896658492665940543103798960435099656194616466326179028821298502998734041943 : ℚ) / 37778931862957161709568000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 1 => ((6235275841139466494311680786444718687501370986082069267546767888117536764705605772536400258413229146437875148206803165988781390202315783838518311706933306305734764117825134509383219224037745398187013540966709283134778281111839265444080584734913838060886408167313400885378849641988955714149965554451526264276239089050481985093886675629039240627695851200993044682818083923723 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 75, 2 => ((38763846128167143484532944688708571649657074369228637517491904852482318299312930438035660227075341283424525894519199750490863096001685171933021620424741381722068815090026888558927388576511858812676959917078252982079852446461626508841593452863904887022584101713059134936800922292199326172687163281209668533713443729637717579421640652417480807753040413866001783358911973371 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 0 => ((755578637259143234191359999999999999999999999999999999999703831146470261322016861968707025390358077550582691628811061743745751016608297855891220344574465026446507138893832203717240872282227484086269937726977932347298940671424194496807579159641271196907961284735449127923645748008505092211687646203866928249221641034552689345759 : ℚ) / 755578637259143234191360000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 1 => ((623573287903049745432824621483347461944132843067408183748168328724842223243162517876001287277169873921819601517227873165230906913658887370879919783330233517926094769296090963941306079607545130363354738876774638009220920584273726465355569300031341381359692497336400365000558403831969617870628013343676878525725675741611191230991585320072284818944009387627596799271731532285173183 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 76, 2 => ((19385129928764945925334754079070666505513492376053851023426514548078034635827572298555547491879544572197988194752721802218725147600521063130446590898951235328364171654245265016439313482280126661189873854099842805222120406529577219751651012762791281956607527190172289580063059247397658248416023525262258258848284409772778165432303470819237908081079517276296869335959026999383211 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 0 => ((15111572745182864683827199999999999999999999999999999999998959558817550028024245236096067780196327926435196995692013259905778823321344950367745857070490095637906579578934032531658667184327465151595066291234873476336061178578713195267285025587819785714737667993275632786395767512753878388939658701114184518939515624954383597671651367 : ℚ) / 15111572745182864683827200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 1 => ((62361757304653908133458974523250435672538695961859583372461757946267363578706683927729640495282448003594356395178665581889480826003019245656584657953024114231723377648328692763642520237497295560145514269263814076872044169319601568787654725625587845197299301125096034611017379214114081485283051564904566356346438292459215959348728368374230693006687978434874328799937582200222841911843 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 77, 2 => ((1938828158504204025688220319529516005526816243047652542589507881536878939727735209674810454639045828638112765465930835444812989872525001008063105090727811549616005969231470022535210408900947030607899426637905508341697008207764465752195466754766464170459333126860565006554844354007544546571969932798148433466358756716279398667134660884547887968861849816603938340706443838763897411807 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 0 => ((302231454903657293676543999999999999999999999999999999999996344930126053248449173514405486111829700005566847045866042582049001006327884810641891195888631705975965814060795256283716897818542385077553467881108110522368582920347019454973972294890010907215873427660377297978608331272304374780345021017014130215034518390464749578620511252271 : ℚ) / 302231454903657293676544000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 1 => ((6236604835791745082499640795404874214926309483920346190458041140940860291189260914843297171572792306740933204360752415919948936682618600789249903409787520957448426303485583564730558924232428395413422649805052947777280121477288946517256454738365036000042337062521805836452652251055566974930059351325173880871861293071656207907388305934616355363313468943536255572915520681148484475973923703 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 78, 2 => ((193913783704974782362031316609887275131762640194645720353881746210185356010993179217640208940747382068067227092919164792703879106810475364505971342692605366992069682026540402501645072243903401147117137727625082101733661591723547025697134455055533333244965574869415622232406884309684102288710054610205133545721902605149152561307506752801452529852486533737838019354685527674288219279899843 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 0 => ((6044629098073145873530879999999999999999999999999999999999987159739532825061801946556106472710857736119556333672127407590738140535229859339784963771156763183093567904795573735324697462036539398777445332666332792265080831799179079345323564671948608317049363351370905447798851067759605268603352058832770639445416263105702665269693856029228023 : ℚ) / 6044629098073145873530880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 1 => ((623702062168876931513885194511550691929499683753945864470622119776537667756686690186325056829399831065824919132937152546000440790874842734529611593633799451692836816666505572951259472443587957465199493399439653077293353543911132631765239542160079485866554025231187449027968585623820783951930889407765207963336391591006499563015312630938477835002719854980357984379384334421946081519534496672763 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 79, 2 => ((19394420654949035784753851611385910210015124804240665299884155671453383704286553402212265511165219186621312557218488376098070116791721825195727839852292079172936081261081760446578265135795809511906164174287050091263981045374941840414123416266682366350108291037611511297967204730423540771935065208588978486490840020256482938747468839995107330802827941660584569513964414395599234289514645786519 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 0 => ((120892581961462917470617599999999999999999999999999999999999954892164978814442110238251602038633243226988001400190183582866263087700262495860664577728073709062207704049546850532195662184134362907905165453656827099227228962110516105740121682692555461017794413453365990838117363801039493308603575782679523256371747332290333463092434516230678044799 : ℚ) / 120892581961462917470617600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 1 => ((62374235015915499155969419807391215845200801357022338483745396796836160646613929446671167533879494981512912437759645695644573781219370729474443711093358155347092607381688795004701067723284119368072438060101921771715287406850709710999586812770942673582882943522829313544042899357504558729728374994638252359231186568791973319863004867118669211895779498880092259613867760744685671649722017073734903023 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 80, 2 => ((387948176762464566751271213920893914565357400471167250750245098711894244236589697481766641896463372384048743740027510697472128958673107543882923418982034370071003940218085860161583949485019758067956806938292730398322432533281948886809626155633196455997829741765566036256708644472926004536151474944798176919892012917419960258097445209073390455093216012215419434421979235542982435124841192861560607 : ℚ) / 390625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 0 => ((2417851639229258349412351999999999999999999999999999999999999841536175570575135133266977877961718583456408848918868114926609182227091022147958514661558722939935535664326058085919603361252864016895470846238696433599585255343894243079465047471298947334555511774461674725814306299033051739993124361724553165199633948378335941455843722455518371971378887 : ℚ) / 2417851639229258349412352000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 1 => ((6237813876102148206216812901656979250536576848290036509720993895640323010709846617200681714804978970345239450524388105048320210315673020168782806047440418623878427507678219343031312709981957255857124237772456150181601186047175451997705335687430851479355102103838674049957982619224009496817511950505426132307287589562486016210017829210615556608905877687321715210838945720814431453499317948010375708238483 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 81, 2 => ((194003433474422636717784911441711631665608831111902276476402048913231631030464527792293405916784885665830687873631214015188820694676226103619419778004471752680667971872882050646540195415660931967466740317293948435235634992188957438648487600719952458339368198812295876659422365311921132874458318955735731232994707515404443757869761727002387121237451904989495356771305672828098640319306096773721168472591 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 0 => ((48357032784585166988247039999999999999999999999999999999999999443316584779430449723166893285279517383682364286251983687737178057163770760805778262006055793687993536788777442055835566608081311291353789082836540571235343002023100475938160711766673201986293512863683863311785658028503110762595845882738355269346314060653094162334378996986236040735454030031 : ℚ) / 48357032784585166988247040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 1 => ((623819213338793752589584302918954661459992150291911377645925423240506165863178516052277662180235334683962273498379715567839052243232359913480618930610335567180457425927858960672885169127448896960640457057631820368294586714339814554431365023791924156452974735564474035546142352246016611356429500015367158342984302119447510224347456684426200728607409811036509449692602835125159429811373656538810333467028783143 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 82, 2 => ((19403224635919564183409517630516817249172881253703016522900389339373603452366746006830527986048871241599818558904235759405423030431967887492679230996123015554262211270839566455721196107864131517737798320848442674148207403249717238819061272121041305996748865896188572647637313823328639012194811932733995748386062075600190125934920161733053011490488009921532348465163812209270445703368917393943492784019310387 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 0 => ((967140655691703339764940799999999999999999999999999999999999998044371162330139169877485296111186944568876145737603218695020706514816326682710699034427274003225921294738975153942150345494189646566525861048004767026749759966107151971970758580436322958577849110690121411814303016654131428108999206586059842061213601295074319792280673416412647211103650007498903 : ℚ) / 967140655691703339764940800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 1 => ((62385586495675759450920360615635030876827399394685044848379589787978915620065830229646583499047956592075802954515975479503350612303120136774555660237705619160710509405642902253792719472472206152932929353608289352212109422899565280952509460716344680149229748193733618879165840448213837503331522410558748031981961734036679147895296624227603307243286740349126824952940115349893596083812229098733658829323094750721003 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 83, 2 => ((1940605318015925085116838297709696126337474740537122892634610891482273778209256537134921772967674255290400359612927660553428258024329499338098266802869538265162295593614272950478830879472965430547903830431520987929989279456575563584391603430748235029036916659226841916713440968393115417027202158535683866394885348182942430934351727289675246072057244961027339853500695222836609571565337864487813279146636891223623 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 0 => ((19342813113834066795298815999999999999999999999999999999999999993129875893265778903779605845238599736270461899976200107275607741986549755636362685707943013573332661508418019715798774163721088228388205349861640746564971906760934424877533274893072802553483983925854396519703646497505963706946914212736828225161043381349596085430282005711857629652607122476343646239 : ℚ) / 19342813113834066795298816000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 1 => ((6238913789084998387756379262212571951841067691747402105628588731703722879903394342359110310415696661774367415501682118205581703694622770138760119344837161820314888924903664474017102147665003379131843832367614623345124084156907681285827706539062591232547667624802454824983680464077868655261649493514730289378293583170686788723226657429479761624411886585954754582007293828718841875279466286931864420215124001899211916063 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 84, 2 => ((194088294784551625714220438674595313852648210200369509155016077150500354828510506954501098712883416430049986131642288218496809498918833821131501559173904224799754713251195953328214690686242262355204183700792661713628815836245603641325602223715266415348036362187236235393144662596896053686090938027297822477301060985735947665160788740010450164200657621557570424465238555500915799866524763939988320402636868402824111499 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 0 => ((386856262276681335905976319999999999999999999999999999999999999975865254013042681288977755334323200873518132654616390976859209997598749291550542114892003806683117639879072503261601093637152182946327765394063943942682746308451162634594774394699364755370389235531526494973718910145738450502504509629344477554990745398681131048116580686065755852969608821259395229237607 : ℚ) / 386856262276681335905976320000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 1 => ((623925790507180003780042124991349371845592095059556274426987733740273496592474269402373437234768372767178295686624136933440818637359630135956504500935998187777806151285678786514069362911311977901724018957330963441617541694409792294016467542634289797114889599816099858033663599804645125852337484028346208260452738879456885252469709783254845359011700532360223305140943758580378473036365360496568634519151527186200323707512323 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 85, 2 => ((3882310809797031833763494482849641402078956908334900392666082183710028700162796666614434432198774818919647419103054864937081655693123546127163541330832765692553515384180707709534069915411527116189130687122332873573650955086414811102922168120680705186224091022020056076535512446400878655505569506392795728966051616568285400693914554304542423197590974779455991008687692515040493001153778351312299828498953805788853732733043 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 0 => ((7737125245533626718119526399999999999999999999999999999999999999915214637347818939368178854489477404668669200015667381501706404721564406261217054449615609372877792268895181703958004641947315618690449439829346635070644487781588934335331442448578868385616177384422252576842674531341979176615298342327887149650682488585566813372033547950149000311482235789084255440311713391 : ℚ) / 7737125245533626718119526400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 1 => ((62395913396983713646270961743161788734350491642890764766877403448376510224885486877230749985241661642523381771637783688955561635820445065207025957976919382809700738984107048552148740105008577741800364640107171636851788238548853616528084914478873204191756468424384343439685936792265851633351011814899443271708922137993375422620526297968223965832702170867840637806620853933102944452488969988626112869860245783125497897597635533783 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 86, 2 => ((1941422742809662443188401893175155155548235476170869500858281306536641233824341733173391417123434956428607076288650562247261079958028379750875973440552650146942774330002580113406930920820973919107777265135888934042799316264623997535663329362742914158941991909530438454189190439213348268227015050407931256970736602866310228797677285118440433190593010412789780184487684814269114761083509975611950178459530837965645287834133367971 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 0 => ((154742504910672534362390527999999999999999999999999999999999999999702149021002887934000412315821534122601034899655039511215494599786855759195655512281499635726919684240628773326004470307160919768459548882120494729003174085576721926320019357321857564638669631151475373302448315628604372847449543076597867556722847582401096215375953853948873438094237094327052989361815049142583 : ℚ) / 154742504910672534362390528000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 1 => ((6239914424514133917469071109065404681203625238229543542851352884531764434001512359171971479533164291374922755504512218702045938749071421062815185928941040927503896260433503566050945431633670780664116398320582184469823967206362137674085417436936472312449080253434146374409507376831967388682250312392612386677276122715622142530687708281526020177574020968230391337092863151869278672904019421613218094578964830048646235625780862554484443 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 87, 2 => ((194168501686792472318871673130186527459233822388412975337551133612666910484457308804660317502160794717431079295913949897339299082287701055665959840419550768770708033161388386378236406294054920906821821252697489801785706007916245666018858198636788111151443625503026645770765332666866381406559898470372153072792259318719353345573929269739321939121472447531859082623360930594931129501839212685792257440391143916482339106043157469694967 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 0 => ((3094850098213450687247810559999999999999999999999999999999999999998953649510783145312143448465481049372697435602488153802900032529051224282054337814644908220308668850737328880694253704189056311146598395222889297982988150562631024127162228002271685624575646414235132986411500932803287161813090244828088308726767363556975051004615725888922392388025054912370937151628056267637894079 : ℚ) / 3094850098213450687247810560000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 1 => ((624022748077721520067083114184001451989906471083489851128124689099552505150354500986330739585083888698047579051261816064425585964012261878173149721020649273826682751202609349207376604148081676895702868026644320022733595423309338608037386091933882424101787878250776590230254407005111939500927172615829046154904709189433823822754106241122076394251537438826792141500396187901749879041202026256615864723316803248266740165085579354899392948303 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 88, 2 => ((19419422838621314387803889537201898018766672102255929381963935872332554108400122092776047358204089301203569366740815774466687179936009009332901917732400072260774403518467938932412536531137211681911826482738472443727400694162069667408949569506493058632437842321324382066921799889641385729472206202487263545648974542850045809598208158223969362570338874309965365629571188456657766755481902236299008732118299869446191414874858529851348513403 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 0 => ((61897001964269013744956211199999999999999999999999999999999999999996324170731381189481559934459234926446286091271540884309587814274556950902856888742847562577944353672640236357878913262816154821058000162418010103814237372926522787758720906971980431599134245853208022181263602776937947799449386030081074228557133748175653354179215045047784364459132017907159102213669361668211921899527 : ℚ) / 61897001964269013744956211200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 1 => ((62405308197738904408420085431973004692013977422105832614910769874989583636538236374994642907582236002002085734236958710505213763795515127982787770625132698629914885434926672683244421631325661499144907118428932092022803736931708258533389657089861668006963926633103536892125275275724629075288812798854979833057358055198226313926848742734448905826393307108321597945860290119642865279156306463235425598747904514131765311542868687464976079851189363 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 89, 2 => ((1942194601934589866367152742672563251269436387715289048954205625128191755887122616897301966560296574133131672527690481440973402825588718370503659743537640381341184830192122517668160670323435185789411517070011524949615376417588908338237203937818738004386570593757372654008789399586187569774528827939941305996228794095373119677635126004658576765857954696704602905768468306922780705806170995635320488985496514064940037131727593305901506670682479 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 0 => ((1237940039285380274899124223999999999999999999999999999999999999999987086811779342118648720049755292296605803038636923126579581991546518568521736250153623487336318514451985150325228622292273151886376754570574469494699415891090874553396386546192567256207758605682319781922779036555383010619465693123674813764921210857341070233231582453252866472344930778907849926076620467540428481633038351 : ℚ) / 1237940039285380274899124224000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 1 => ((6240824743128108881558272598016456262637386356292366757054393957806979175118411784753468365627850907886501825196569075478602487207800164254205639236084098163153872127836966938425323516598037789034428182795553623286733253805504175880318793305212548977205403492473072916536261542947912678791858294152874930555974776042099776052059928249089789003161026517497067068644439404196712450666752081955721191660415078837124679847798629036096622888625834751623 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 90, 2 => ((38848840608846938683825676088180414050025732806800982690222610586059051598236568403051090342772394747879625771492816376924712915055281884528530605652092214831507437838696758144449761041979632985533574869700688626888828695168214112683914181899320203893943329027225084752274361872809703956235152030711497165923429792803900351347007499478527799633946505816279279631617990641839023440374581304002770076763443392941442214627107028730547014021602970679 : ℚ) / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 0 => ((24758800785707605497982484479999999999999999999999999999999999999999954635969780828862812953534790341837976186074731510943674071536302919731216859446789679311012486941269823833092528150112755582576841538806428111334879048025402242306081505936774488771057855981761989393894722755419060516306182979943469620756168213741839179729342549158277319917347741826303276790307167702469525255976863727063 : ℚ) / 24758800785707605497982484480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 1 => ((624110954310141238187470381657402546024512188379305169291542556935664851787180384056449380252854146081644739059538766219297986055763548043283111792459334909672162409562008939836616536815426425145519273708574717867962285419783361653385045890699927284921950917557461715642222586594067714208982011107947544834864972758718682393795925935413676202982483629839231111118228266780040750539391550893535748952434865610126090927026095544857905502427774937560059083 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 91, 2 => ((19426846298257591415051015993209243256432293506799299669193326590641166298300138603031278680732271345517711770816906878613909354345139583349040454832225793763394649080491991178850276610728302254367645886603758327413912851854230278373493665797188269633326588185879897133685900209804792902559616710371935015210512819293717320497648006387518857899961022710068200901584794728365251184107352102112967002381413317659471018087777280295876789773382913205469351 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 0 => ((495176015714152109959649689599999999999999999999999999999999999999999840636161840051795061905767718470876810341680531797945127013307032157015764827236572143419586866624680891125654051391346110361592444325826981955119430095713238077221264330355888779052726248063929868740752161039787159593783620808541408777716418934875081038389180375193028224869642617035803411364349080138775442224246722273172319 : ℚ) / 495176015714152109959649689600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 1 => ((62413855028835445415413130101075677099591133005201153683673307596838177924227767658475285590294972231464067981289022431105567763091197234753144432411582575212273521427556089265839644930220384904946974209996396146297653872772458058630670307226874940025313571219935451544246386167097411803350437667615071564095699476123171962726796373437472671180006700406185244795050103480968875076917410771861661249131751219051971784330414143638712095019458432878963772015743 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 92, 2 => ((1942922461484051277856967872698770881539641193907617542167436201349525940263446727332794368932761016465203739433850269233445265446035709228387085755291905998736087671030866844430028206544225938478322785378089514526290841378986483133656391692482247521028242327862092299082924577628869781364687875845669927082819752495879745679138306042660153846763924168609173812338428411877343331537586969723011018311135606792114334588554798619400494255617204926900483965547 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 0 => ((9903520314283042199192993791999999999999999999999999999999999999999999440154836544101956052474961994988190234730323708206181231197747603967596381838082077939833008662452503970524422682537798885700274256916630187608334557926240605365278301592540237280812227309448585628886262341732772291652961859900405969036117779718216159687861190658053108153967054513646777384122958318527518128533778735345654356647 : ℚ) / 9903520314283042199192993792000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 1 => ((6241652896874039318971870654273828808241982423671970987333208812903232025710428389337819887098909362060868075916509751945082151388448541332217230448008969040237653581298990387169881097473940804686472977697799228075964757006267774800813383588122637901717976115374197929549855139452517889753068250415723693927593280763002418309960062757300837120052736696049783255031983317122634186447731071897407206857722439998148811992183690765521526050913891570414493056313605603 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 93, 2 => ((194315558765755670824523832612824444016325413026377021273172209002856968766417027554510545874367423757864396130367390863461152513678922213164850071288688033449122482550679814416678458659540693870575421110365012025730349791917202701405944749235766724980007985008859034211730959332135415280037788871700695196334185587024711517710284550533033116240497846180954474465464219434921040335127015863151456771441575623976751827372655938958385364609172156586208780211169183 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 0 => ((198070406285660843983859875839999999999999999999999999999999999999999998033263940779430171612344541488393512294607627186928314665197687332738166089397182339802633359431195646448452296883755287485465063464548121849068079301994883246648222673494593853567493354538092881314277439606507229060576855013830126169223881760150093368983456362781740568944886262506441128950423952572987171185539164697269283754900911 : ℚ) / 198070406285660843983859875840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 1 => ((624191199095506913851098378916516916203415128924119300788638601135071569266557314513495514444760666571492933791444979388772472654446515660328892818767890338340189152171189538395895109297403324932574165041012740725384538597183963684373855639365849365744152516748825676481324222661837851329404341006076945232512608723472981561837240250761918630655309767821027793103967306626816552116801986809598974567868308736708181763412999586051036985965724313696716395999596087492663 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 94, 2 => ((19433840713163443294153332738316798721805339515700009039056615618392442352084655855687622382091300100561932730811980151044604802650112355276046383861045585685989224466616673365273954396729827331337863882746614730368536554867217247111109320629996748460129497398609702178146218983973487434280589210802635760054973794874357681796121857895906958031884394763066593733543723388127004640397897243049972054390801988340671779828342687865567296316108992766907491793803868899459 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 0 => ((3961408125713216879677197516799999999999999999999999999999999999999999993090856223958138192874166374248726408690956594307679169418839475599909177472052301559726650991681790305973412918952632324936438767950957552055776162587908024845475206251986508207582604154492320292057056645337659895689806491663585233232483496623407278005238882202452254618703385440185127686002839345388903932374799085581506993830966900343 : ℚ) / 3961408125713216879677197516800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 1 => ((62421630427558237924516028523494823112446112332231463769215925895583894756389147116797992621980150194479773673982016131259958495825077424289731063753414779385438219722637573181400237294002115758482904474369699734094150588940718370952911177169696632092318187254380721422181945407596271339444509140454140547341441807668600229518522754260499542471323385825436437169692395774026306575027131030472245649521752117475800274529467653853181164860374195103474960440032916418249620923 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 95, 2 => ((77744319042197966882953514870673866792791257808756305920997110850794241454658034932020676929450415968059353938501111668653158272202663951835187720560814337337944409667115782705039476433095258864630934111663768670566080730573629074138492509151306093090795622962412871714893779370771732400440167729900866331753618554972905645872609433880228268505241414497629614493461498006350217887652977759324047708613375016388737056371926161730758373259374888862833992610575220054750703 : ℚ) / 78125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 0 => ((79228162514264337593543950335999999999999999999999999999999999999999999975728177914764939471566946472735775873731330515802876922168383077782480940459319735379319724933778129344884599584280597357501709391811713880371941659171320891282154399563228603333237688394731521185996439995071199213558290205214174924345714523638029767632404193177214770475504993051370353560927974620351219514432669187647834069328186720904959 : ℚ) / 79228162514264337593543950336000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 1 => ((6242406301908683021933905099812554380303578500543899913381946355578497065976724859121009481581881634897772996870855495323206860621771178163927900467444396096675404413193405914650794579562174024292821032954857808986784270235896333989886635926918683186304483040575934907779874059943513912413156700171638712637840570174570459024751435646962109200784211899674438516581986899140575504709557524940179231449084004462918360631623643699101096831534442577988102181484072056447621274814383 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 96, 2 => ((194382736599293504055944649189499372760764815812157727448637346136835608291133371089656293078232762209891517027001348470877626572678765667081662647470597884367824045290717116623283450729048160302254816526108174101786406568868808751175516638353584453216098181227823870420110339852294282886752379695535910235132085442910220858825105799794733413246815170904125312554421295160663319548828205034142380997348649595095229271984712296600347656374966027706366134862540605953198316176731 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 0 => ((1584563250285286751870879006719999999999999999999999999999999999999999999914733089014569232363614682958720780644418164102015506627577529752249855543833590230387550193692362568388579598339577738516903505093434550861746631048668850291074208405665622083509663999330691833926405493702685122837230273490917396509226495121540398573692635930631555488680449040589464052059539974841293834154201966856206841085549919950539120967 : ℚ) / 1584563250285286751870879006720000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 1 => ((624264201029743750093307668551437269233895542388701726007057074070134051698937474734900944353052992469097652081592745243456147330431138201364981689443788341413147041706262449435693821766037917459681589425670113011674283941810642967486311346635430940965186207444160752943336640370597761403852120813811887757763045695873286588532542670890692468414813451570618652480547157361668681866295559438685315991472915724212362682421093695800844147064054313595467232741051523025451585037334377043 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 97, 2 => ((19440423056810285622132401522547548997916514707487593450461213087765937316377401436438074093821884245674732414544795644480509569866593482359445790234653159025082192920569086106050800316059381421003686342310398845238413725109994037150921863874820031447898584223187087434281659274142427684098834782895296513269229086383162094862118340834665813402439471354194546821381658545104268834960084834907457534569655899599250416519498176130200092904767549150700898915244689543916523307917522127 : ℚ) / 19531250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 0 => ((31691265005705735037417580134399999999999999999999999999999999999999999999700457341708181713293378381233986102403841010490380474782679862019653742525487402479351463830441269702749080128966936595409882013393235577177315914873973671072543694129103330379369449629648720412583462499377532836527189950773592813936912677361971420189382230024308654431734417479590787214885163931617465239383711509565854632733536868786243931957071 : ℚ) / 31691265005705735037417580134400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 1 => ((62428704022978050409041139851960065639687542475295642443179802249099709073315852238940473327108755250153752089777403070086714235791511094172268729630949266780007748886285360446636000960037697153913001620948135912239666938747812777354891248632820231901272082340756805661949502833494674059981859007067389130590098322369040333603084801772929718662989442891429624142135487300471624785005371601434917600073716763181121308301104708069677247549694153710185522034991076830350310765463190225692903 : ℚ) / 62500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 98, 2 => ((1944252860012574579401192021778256722817806476708421922398574239536971265222501624634389018997211436138401344291647015056198701572845262472233262514452999966011439428276969624927160648136195500163162305998798407470353741850613614591621897122638198568449204279012019617067659311143252655734614350842362404062238236986682583142847475392592175824879011921138384818095210260650505095173323049428745480920834250872817567539268141362804550084365569710925074622867431435780804246192597658590963 : ℚ) / 1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 0 => ((633825300114114700748351602687999999999999999999999999999999999999999999998947706641420842358799638253274993177744693469852706607911554355275043597492037244909961692436340180465757518493060848259674915513050436582623910808952269506477845997475539999622724876548955954809405703760313272854720018297067631555360374235572605599125299774075396303018683008605802435485891580891772155385954978533104847324792915020046074932965190423 : ℚ) / 633825300114114700748351602688000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 1 => ((6243091705010481172434450287095522520223164115686246570174350118728765410366179150002014341649848163938560541670049775858969532992304264312896113928856318564655599830368677481413752141938639947402741936004239954886654020239470257777747477799922635889106032294187277116300827128919170961877515402004981502859438149226180734053576468338003868528110534834563439439072956726775866737890582207298573081397026766318511043644984014003109111319851162199903923644888828398170549356618629519091893825963 : ℚ) / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 99, 2 => ((194445909414007297335334892707866089781203867987242927909720690332337039495111155087750984297483348575331450609191837268683840668474191128644224271374639963584305186484294928740265850254928455807739335959291539673734643863415594638873219794712534450982877489806202062964597018387385592713879432462907084249681875748331392488568848201412585651437786715071093608875940635684137089306059831242786909126512306098601099791190132982173068377987006575619684026294756770853960788383327872178722162439 : ℚ) / 195312500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 0 => ((12676506002282294014967032053759999999999999999999999999999999999999999999996303293431311419206463129183755051033417108159592558313593290450081228157989526841368695425528863053976206162466122759936237978197346183714757798671849322776256672989131572018674632491316482269245442237309980527538631424277598589653980994689566563469727178106326867212504633409232183955861937123672795581870859839586797328651997510465421861239506713955999 : ℚ) / 12676506002282294014967032053760000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 1 => ((624330613848695583684208495018407750119543710153534547663613829104342453202809086530648597301543767143324135448939900925596729173416757338518609907146504196625516556547987275289368329083835396883995385125042853985086843016033814980846764393717455041975246649961513577640362124201790949061480711604115485284917284294445261103031625012944020993382330002548029938854436433386293435564170109280845790938266592372725590921119703645713728911628811108293251979451024855923574849407868860099667249385120223 : ℚ) / 625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
  | 100, 2 => ((3889322146793133551266150288333931663980235382342691332009441594391764004744761972186582953125796363091471322154049418448941894022545747447892335610043235362447285706625600626182786756813919145768955332980784860770039498350549214626540202115011646768736036476959584194659754585033854794981236096384065608246908106597051627555112806550572054905788500684496267990246644127549481295795071976441808387123609601612589547320144514959788643470290910376927116801082193684657585567756588913196275270561551 : ℚ) / 3906250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
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

end LinuxArenaSplitCertificate
