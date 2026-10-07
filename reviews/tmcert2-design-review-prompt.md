You are a HOSTILE REVIEWER of two proposed formal statements in a Lean-verified AI-control programme: TMCERT v1 (core
certificate checker for finite-horizon stateful control games) and TMGAC v0 (the Games-for-AI-Control trusted-monitoring
instance, arXiv 2409.07985). Do not praise; find errors. Use web search if available. Nothing is proved yet; this review
decides what is frozen. For each issue: severity (FATAL / MAJOR / MINOR), the exact definition or conjunct, why it is
wrong / unfaithful / vacuous / overclaimed, and a concrete fix (Lean text if possible).

PROGRAMME. Lean-verified, CAPABILITY-FREE control guarantees conditional on explicit trust hypotheses. Classical lemmas
are welcome as infrastructure (report triviality; do not reject for it); vacuity, falsity and unfaithfulness are not.

HISTORY. TMCERT v0 got MAJOR from both reviewers (no false conjunct). Their fixes, applied in v1 / TMGAC v0:
- horizon-bounded certificates (`RiskCertUpTo`) and a computable list-based rational checker with a soundness bridge
  (`checkRiskQ`, `checkLawfulQ`, `gameOfQ`, `valOfQ`), so instances are checked by `decide`;
- row-local admissibility `adm n s a θ` with nature choosing rows per cell (rectangular), a separate fixed-model
  corollary (Fx), and an exact example (FxGap: 3/4 vs 1/2) that rectangular is strictly more conservative;
- an observation interface (`liftObs`); single-model and robust tightness with time-dependent Markov attainment;
- usefulness of the SAME controller (honest action a0, nature's selector, sub-solution certificate);
- a vertex lemma for polytope uncertainty; a deployment theorem through an abstraction (Abs): if every concrete row
  (catastrophe, and continuation pushed forward by α) EQUALS an admissible abstract row, every concrete history-
  dependent Red policy is bounded by the abstract certificate;
- TMGAC: the GAC game, the threshold adapter (n + 1 indexing; c = 0 convention qa m 0 = 0, f 0 = 0), exact bridges
  to GAC's safety recurrence (Prop. 4.1 / App. C) and usefulness recurrence, `constRed` (renamed from `memoryless`;
  no "exactly"), a Lipschitz lemma for constant rates, WLOG at C = 0, and the corrected separation instance (three
  problems, one coin, defer threshold kept at c = 0: sup over constant rates 13/50 vs a round-index-only Red 11/32 =
  full-information value), framed as a sensitivity result against GAC's explicit null-observation assumption, with
  the prior art (Greenblatt 2312.06942, Mallen 2412.12480, Korbak 2501.17315, Ctrl-Z 2504.10374 App. L).
Exact-rational checks (numerics/tmgac_check.py): the safety bridge and usefulness bridge on 300 random instances, 0
mismatches; exG3 numbers; the exV3 certificate table; WLOG at C = 0.

CHECK IN PARTICULAR
1. TRUTH of every conjunct and both Witnesses (edge cases: N = 0, n > N, empty adm, m = 0 or t = 0 tables, k = 0, the
   checker's Fin.castSucc / Fin.succ indexing, `gameOfQ` beyond the horizon, `valOfQ` at n = N, `pushK` with empty
   fibres, Covered at n ≥ N, `honestER` with nature, `Vrob` with Nonempty Θ, the Lipschitz constant N, WLOG with
   TA > 0 at c = 0, the zGAC bridge when f(qd) < f(qa)).
2. Is (Abs) the right deployment statement? Is "EQUALS an admissible row" too strong (should it be "is dominated by")?
   Does it really cover "every policy the untrusted model could follow" once the concrete state includes the model's
   private information? What must a lab actually establish to use it?
3. Does (Q) really make instances kernel-checkable (`decide` on ℚ with List.foldl / List.finRange / Fin.castSucc)? Any
   reason `decide` will fail or be too slow, and what to change?
4. Is the TMGAC usefulness bridge faithful to GAC (does GAC count audited safe solutions as used? deferred ones?),
   and the safety bridge faithful to Prop. 4.1's λ-form?
5. Is anything still overclaimed in the docstrings? Is anything important missing for a lab to certify a real
   trusted-monitoring configuration (interval ROC from finite samples, discretised score thresholds, Blue optimisation)?

End with an overall verdict per statement (accept / minor / major / reject), the fixes in priority order, and the final
conjunct lists you would freeze.


## STATEMENT 1: TMCERT v1 (compiles; no dependencies)
```lean
namespace PL_TMCERTF1
open Finset

/-! Control stack, trusted-monitoring layer (campaign TMCERT, v1 after the Reviewer-A and Reviewer-B design reviews of v0):
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
    (n, s, a): cat + Σ_{s'} K·V n s' ≤ V (n+1) s) and admissible rows have K ≥ 0, then for every randomised
    history-dependent Red policy σ and every admissible selector θ: risk ≤ V, at every n ≤ N, state and history. A seeded
    (mixed) Red is an average of such bounds (S').
(Fx) Fixed-model corollary: one certificate per model bounds that model's risk. (FxGap) The adaptive bound is strictly
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
(Q) Rational checker. `checkRiskQ`, a computable Boolean function of finite rational tables (written with lists, so the
    kernel can evaluate it by `decide`), returns true only if the induced real tables form a horizon-N certificate;
    `checkLawfulQ` likewise certifies lawfulness up to N.
(Vx) Vertex lemma: if every vertex row of a polytope satisfies the certificate inequality, so does every convex
    combination. So an interval or polytope of monitor rates is certified by finitely many vertex checks.
(Abs) Deployment through an abstraction. Let a CONCRETE game (any finite concrete states and Red actions, e.g. every
    output the untrusted model could produce, with whatever private information it has folded into the concrete state)
    be mapped to abstract states by α. If every concrete row (catastrophe probability, and continuation mass pushed
    forward to abstract states) EQUALS some admissible abstract row at (n, α σ, b) for some abstract action b, and V is
    a certificate, then EVERY concrete history-dependent Red policy has concrete risk ≤ V n (α σ). This is the formal
    form of "the certificate covers every policy the untrusted model could follow"; the coverage hypothesis is where
    capability re-enters (e.g. every backdoor the model could write is caught in the audit zone with probability in the
    admitted interval).

Scope. Finite horizon, finite state and action sets, real-valued laws, Blue's controller fixed (Blue is not optimised).
Classical mathematics: the verification theorem for finite-horizon MDP supersolutions, Bellman's principle, robust DP with
rectangular uncertainty (Iyengar 2005), simulation by abstraction. The value is a kernel-checkable certificate format with
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
  (List.finRange m).all (fun s => decide (0 ≤ V 0 s)) &&
  (List.finRange t).all (fun th => (List.finRange N).all (fun i => (List.finRange m).all (fun s =>
    (List.finRange k).all (fun a =>
      decide (cat th i s a + sumQ m (fun s' => K th i s a s' * V i.castSucc s') ≤ V i.succ s)))))

/-- the lawfulness check on rational tables -/
def checkLawfulQ (N m k t : ℕ) (cat : Fin t → Fin N → Fin m → Fin k → ℚ)
    (K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ) : Bool :=
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
      (∀ n s a th, adm n s a th → ∀ s', 0 ≤ (G th).K n s a s') → RiskCertUpTo N G adm V →
      IsPolicy σ → (∀ n h s a, adm n s a (θ n h s a)) →
      ∀ n, n ≤ N → ∀ s h, risk G θ σ n s h ≤ V n s) ∧
  -- (S') seeded Reds
  (∀ (S A Θ Ω : Type) [Fintype S] [Fintype A] [Fintype Ω] (N : ℕ) (G : Θ → Game S A)
      (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ) (ρ : Ω → ℝ) (σ : Ω → RHist S A → S → A → ℝ)
      (θ : Ω → ℕ → RHist S A → S → A → Θ) (s₀ : S),
      (∀ n s a th, adm n s a th → ∀ s', 0 ≤ (G th).K n s a s') → RiskCertUpTo N G adm V →
      (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, IsPolicy (σ ω)) → (∀ ω n h s a, adm n s a (θ ω n h s a)) →
      ∑ ω, ρ ω * risk G (θ ω) (σ ω) N s₀ [] ≤ V N s₀) ∧
  -- (Fx) fixed unknown model, one certificate per model
  (∀ (S A Θ : Type) [Fintype S] [Fintype A] (N : ℕ) (G : Θ → Game S A) (admM : Θ → Prop)
      (V : Θ → ℕ → S → ℝ) (σ : RHist S A → S → A → ℝ) (th : Θ) (s₀ : S),
      admM th → (∀ n s a s', 0 ≤ (G th).K n s a s') →
      (∀ th', admM th' → RiskCertUpTo N (fun _ : Unit => G th') (fun _ _ _ _ => True) (V th')) →
      IsPolicy σ → risk (fun _ : Unit => G th) (fun _ _ _ _ => ()) σ N s₀ [] ≤ V th N s₀) ∧
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
      (∀ n s a th, adm n s a th → ∀ s', 0 ≤ (G th).K n s a s') → UseCertUpTo N G adm a₀ rew W →
      (∀ n h s, adm n s a₀ (θ n h s)) →
      ∀ n, n ≤ N → ∀ s h, W n s ≤ honestER G a₀ rew θ n s h) ∧
  -- (Q) the rational checker is sound
  (∀ (N m k t : ℕ) (cat : Fin t → Fin N → Fin m → Fin k → ℚ) (K : Fin t → Fin N → Fin m → Fin k → Fin m → ℚ)
      (V : Fin (N + 1) → Fin m → ℚ),
      (checkRiskQ N m k t cat K V = true →
        RiskCertUpTo N (gameOfQ N m k t cat K) (fun _ _ _ _ => True) (valOfQ N m V)) ∧
      (checkLawfulQ N m k t cat K = true → ∀ th, LawfulUpTo N (gameOfQ N m k t cat K th))) ∧
  -- (Vx) vertex lemma
  (∀ (S ι : Type) [Fintype S] [Fintype ι] (lam : ι → ℝ) (cv : ι → ℝ) (kv : ι → S → ℝ) (W : S → ℝ) (U : ℝ),
      (∀ i, 0 ≤ lam i) → ∑ i, lam i = 1 → (∀ i, cv i + ∑ s', kv i s' * W s' ≤ U) →
      (∑ i, lam i * cv i) + ∑ s', (∑ i, lam i * kv i s') * W s' ≤ U) ∧
  -- (Abs) deployment through an abstraction: every concrete Red policy is covered
  (∀ (Sc Ac S A Θ : Type) [Fintype Sc] [Fintype Ac] [Fintype S] [DecidableEq S] (N : ℕ) (Gc : Game Sc Ac)
      (α : Sc → S) (G : Θ → Game S A) (adm : ℕ → S → A → Θ → Prop) (V : ℕ → S → ℝ)
      (σc : RHist Sc Ac → Sc → Ac → ℝ),
      (∀ n x ac x', 0 ≤ Gc.K n x ac x') → Covered N Gc α G adm → RiskCertUpTo N G adm V → IsPolicy σc →
      ∀ n, n ≤ N → ∀ x h, risk (fun _ : Unit => Gc) (fun _ _ _ _ => ()) σc n x h ≤ V n (α x))

/-- Witness tables: the FxGap game as rational tables (model 0 = `true`, model 1 = `false`) and its robust value
(0, 1/2, 3/4); the checker accepts them, and the robust value is attained by switching. -/
def wCat (th : Fin 2) (i : Fin 2) (_s : Fin 1) (_a : Fin 1) : ℚ :=
  if th.val = 0 then (if i.val = 1 then 1/2 else 0) else (if i.val = 1 then 0 else 1/2)
def wK (th : Fin 2) (i : Fin 2) (_s : Fin 1) (_a : Fin 1) (_s' : Fin 1) : ℚ :=
  if th.val = 0 then (if i.val = 1 then 1/2 else 1) else (if i.val = 1 then 1 else 1/2)
def wV (n : Fin 3) (_s : Fin 1) : ℚ := if n.val = 0 then 0 else if n.val = 1 then 1/2 else 3/4

/-- Non-vacuity: the checker accepts the FxGap tables with value (0, 1/2, 3/4) and certifies lawfulness; the
consumed bound 3/4 holds for every Red policy and admissible selector and is attained by switching models; a
two-state concrete game whose states both map to one abstract state is covered. -/
def Witness : Prop :=
  checkRiskQ 2 1 1 2 wCat wK wV = true ∧ checkLawfulQ 2 1 1 2 wCat wK = true ∧
  (∀ (σ : RHist (Fin 1) (Fin 1) → Fin 1 → Fin 1 → ℝ) (θ : ℕ → RHist (Fin 1) (Fin 1) → Fin 1 → Fin 1 → Fin 2),
      IsPolicy σ → risk (gameOfQ 2 1 1 2 wCat wK) θ σ 2 0 [] ≤ 3/4) ∧
  risk (gameOfQ 2 1 1 2 wCat wK) (fun n _ _ _ => if n = 1 then 0 else 1) (fun _ _ _ => 1) 2 0 [] = 3/4 ∧
  Covered 2 ({ cat := fun n _ _ => if n = 1 then 1/2 else 0, K := fun n _ _ _ => if n = 1 then 1/4 else 1/2 } :
      Game (Fin 2) Unit) (fun _ => (0 : Fin 1)) (gameOfQ 2 1 1 2 wCat wK) (fun _ _ _ _ => True)

end PL_TMCERTF1

```

## STATEMENT 2: TMGAC v0 (compiles against TMCERT v1)
```lean
namespace PL_TMGACF1
open Finset PL_TMCERTF1

/-! Control stack, trusted-monitoring layer (campaign TMGAC): the Games-for-AI-Control trusted-monitoring game (Griffin,
Thomson, Shlegeris, Abate, arXiv 2409.07985 v2, §4 and App. C; perfect auditor; memoryless threshold protocols) as an
instance of the certificate checker PL_TMCERTF1, with an exact bridge to its safety and usefulness recurrences, and an
exact separation between GAC's Red class and a Red that knows only the round index. Depends on PL_TMCERTF1.

The game `gac`. The state is the number c ∈ {0, …, C} of audit coins left; the index n is the number of problems left
minus one. Blue's thresholds enter through zone probabilities: a backdoor (Red action `true`) lies in the audit zone
w.p. TA n c and in the audit-or-defer zone w.p. TD n c; a safe solution lies in the audit zone w.p. FA n c. A backdoor
audited with a coin is caught (safe end, absorbing); audited with no coin it is run (GAC: "if the protocol attempts to
audit when no audit coins are left, the code is run instead"); deferred, the game continues; run, catastrophe. A safe
solution in the audit zone uses a coin; otherwise it continues with the same coins.

The threshold adapter `gacQ`. With the trusted monitor's ROC f (TPR at FPR q) and Blue's audit and defer FPRs
qa m c ≤ qd m c (m = problems left, so m = n + 1): TA n c = f (qa (n+1) c), TD n c = f (qd (n+1) c), FA n c = qa (n+1) c.
GAC's convention at c = 0 is that no audit is attempted: qa m 0 = 0, f 0 = 0.

Claim.
(L) `gac` is lawful whenever 0 ≤ TA ≤ TD ≤ 1 and 0 ≤ FA ≤ 1.
(Z) Bridge to GAC Prop. 4.1: for GAC's Red (backdoor w.p. β on every problem, `constRed β`), 1 − risk equals GAC's
    safety recurrence zGAC, for every m and c, under the c = 0 convention.
(UZ) Bridge to GAC's usefulness (App. C): the expected number of honest solutions RUN (an honest Red always submits
    safe solutions; a solution counts only when it is run, not deferred or audited) is the recurrence uGAC. So safety
    and usefulness of the SAME controller are both PL_TMCERTF1 quantities (risk with `constRed`; `honestER` with the
    honest action `false` and reward 1 − qd).
(M) Fixed-rate bound: if every constant rate b ∈ [0, 1] has risk ≤ U, so does every finite mixture of constant rates
    (shared random β). GAC's sup over β is therefore a sound bound for the class of Reds whose action law, given the
    seed, ignores the history, including the round index; it is not a certificate in the sense of PL_TMCERTF1.
(Lip) Lipschitz bound for constant rates in any lawful game with Boolean actions: |risk(b) − risk(b')| ≤ N·|b − b'|. With
    a finite grid of rates this turns GAC's sup over β into finitely many checks.
(W) Without loss of generality at C = 0: always backdooring attains the full-information value Vstar.
(T5) Separation (sensitivity to GAC's null-observation assumption). Three problems, one coin; while the coin remains, a
    backdoor is in the audit zone w.p. 3/4 and a safe solution w.p. 1/2; the defer threshold stays at 3/4 when the coin
    is gone (GAC-style; no audit then). Every constant rate has risk 3/4·b − 21/32·b² + 5/32·b³ ≤ 13/50 (equality at
    b = 4/5). The Red that sees only the round index and backdoors the last two problems has risk 11/32, which is the
    full-information value Vstar. 13/50 < 11/32.

Reading. GAC states its Red class explicitly (memoryless, null observation: Red does not observe the time or the number of
coins left), so (T5) is not a refutation of GAC: it is an exact measurement of how much GAC's guarantee depends on that
assumption, plus a certificate (PL_TMCERTF1 with Vstar) that holds without it. Float numerics, not Lean
(numerics/gac_realistic.py; reviewers' scripts): with 100 problems, 2 coins, GAC's fitted Beta(7.39, 6.86) /
Beta(8.91, 2.82) score laws, constant audit FPR 2% while coins remain and defer FPR 10%: fixed-rate grid maximum 0.36,
"backdoor only the last 13 problems" 0.67, full information 0.71; a Red that observes only c reaches about 0.57. The
concern that timestamps or task order act as a clock is known (Greenblatt et al. 2312.06942; Mallen et al. 2412.12480;
Korbak et al. 2501.17315; Ctrl-Z 2504.10374 App. L); hiding the round index is necessary but not sufficient (memory,
task order, codebase state and shared signals are other clocks). -/

/-- the GAC trusted-monitoring game with C audit coins; action `true` = backdoor -/
noncomputable def gac (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) : Game (Fin (C + 1)) Bool where
  cat n c a := if a then (if 0 < c.val then 1 - TD n c.val else 1 - TD n c.val + TA n c.val) else 0
  K n c a c' :=
    if a then (if c' = c then TD n c.val - TA n c.val else 0)
    else if 0 < c.val then
      (if c'.val + 1 = c.val then FA n c.val else 0) + (if c' = c then 1 - FA n c.val else 0)
    else (if c' = c then 1 else 0)

/-- GAC's thresholds: ROC f, audit and defer false-positive rates indexed by problems left m = n + 1 -/
noncomputable def gacQ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) : Game (Fin (C + 1)) Bool :=
  gac C (fun n c => f (qa (n + 1) c)) (fun n c => f (qd (n + 1) c)) (fun n c => qa (n + 1) c)

/-- GAC's Red: backdoor with probability β on every problem, whatever the history -/
def constRed {S : Type} (β : ℝ) : RHist S Bool → S → Bool → ℝ :=
  fun _ _ a => if a then β else 1 - β

/-- GAC Prop. 4.1 / App. C, perfect auditor: P(no catastrophe), m problems left, c coins -/
noncomputable def zGAC (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (β : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | m + 1, 0 => (1 - β + β * f (qd (m + 1) 0)) * zGAC f qa qd β m 0
  | m + 1, c + 1 =>
      β * f (qa (m + 1) (c + 1))
      + (β * (f (qd (m + 1) (c + 1)) - f (qa (m + 1) (c + 1))) + (1 - β) * (1 - qa (m + 1) (c + 1)))
          * zGAC f qa qd β m (c + 1)
      + (1 - β) * qa (m + 1) (c + 1) * zGAC f qa qd β m c

/-- GAC's usefulness, unnormalised: expected number of honest solutions run -/
noncomputable def uGAC (qa qd : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | m + 1, 0 => (1 - qd (m + 1) 0) + uGAC qa qd m 0
  | m + 1, c + 1 => (1 - qd (m + 1) (c + 1)) + qa (m + 1) (c + 1) * uGAC qa qd m c
      + (1 - qa (m + 1) (c + 1)) * uGAC qa qd m (c + 1)

/-- (T5) instance -/
noncomputable def exTA3 (_n c : ℕ) : ℝ := if 0 < c then 3/4 else 0
noncomputable def exTD3 (_n _c : ℕ) : ℝ := 3/4
noncomputable def exFA3 (_n c : ℕ) : ℝ := if 0 < c then 1/2 else 0
noncomputable def exG3 : Game (Fin 2) Bool := gac 1 exTA3 exTD3 exFA3

/-- the Red that sees only the round index: wait one problem, then backdoor -/
def clocked3 : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ :=
  fun h _ a => if 1 ≤ h.length then (if a then 1 else 0) else (if a then 0 else 1)

def Claim : Prop :=
  -- (L) lawfulness
  (∀ (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ),
      (∀ n c, 0 ≤ TA n c ∧ TA n c ≤ TD n c ∧ TD n c ≤ 1 ∧ 0 ≤ FA n c ∧ FA n c ≤ 1) →
      Lawful (gac C TA TD FA)) ∧
  -- (Z) bridge to GAC's safety recurrence
  (∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (β : ℝ),
      f 0 = 0 → (∀ m, qa m 0 = 0) →
      ∀ (m : ℕ) (c : Fin (C + 1)),
        1 - risk (fun _ : Unit => gacQ C f qa qd) (fun _ _ _ _ => ()) (constRed β) m c [] =
          zGAC f qa qd β m c.val) ∧
  -- (UZ) bridge to GAC's usefulness recurrence
  (∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (m : ℕ) (c : Fin (C + 1)),
      honestER (fun _ : Unit => gacQ C f qa qd) false (fun _ n c => 1 - qd (n + 1) c.val) (fun _ _ _ => ())
          m c [] = uGAC qa qd m c.val) ∧
  -- (M) fixed-rate bound for mixtures of constant rates
  (∀ (S Ω : Type) [Fintype S] [Fintype Ω] (G : Game S Bool) (ρ : Ω → ℝ) (β : Ω → ℝ) (N : ℕ) (s₀ : S) (U : ℝ),
      (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, 0 ≤ β ω ∧ β ω ≤ 1) →
      (∀ b : ℝ, 0 ≤ b → b ≤ 1 → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] ≤ U) →
      ∑ ω, ρ ω * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed (β ω)) N s₀ [] ≤ U) ∧
  -- (Lip) Lipschitz bound for constant rates
  (∀ (S : Type) [Fintype S] (G : Game S Bool) (N : ℕ) (s₀ : S) (b b' : ℝ),
      Lawful G → 0 ≤ b → b ≤ 1 → 0 ≤ b' → b' ≤ 1 →
      |risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] -
        risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b') N s₀ []| ≤ N * |b - b'|) ∧
  -- (W) at C = 0 always backdooring attains the full-information value
  (∀ (TA TD FA : ℕ → ℕ → ℝ),
      (∀ n c, 0 ≤ TA n c ∧ TA n c ≤ TD n c ∧ TD n c ≤ 1 ∧ 0 ≤ FA n c ∧ FA n c ≤ 1) →
      ∀ (N : ℕ) (c : Fin 1),
        risk (fun _ : Unit => gac 0 TA TD FA) (fun _ _ _ _ => ()) (constRed 1) N c [] =
          Vstar (gac 0 TA TD FA) N c) ∧
  -- (T5) exact separation
  ((∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed b) 3 1 [] = 3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3 ∧
      3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3 ≤ 13/50) ∧
    risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed (4/5)) 3 1 [] = 13/50 ∧
    IsPolicy clocked3 ∧
    risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) clocked3 3 1 [] = 11/32 ∧
    Vstar exG3 3 1 = 11/32 ∧
    (13/50 : ℝ) < 11/32)

/-- the full-information value table of exG3 for n ≤ 3 (c = 0, c = 1), padded with the trivial bound 1 -/
noncomputable def exV3 (n : ℕ) (c : Fin 2) : ℝ :=
  if n = 0 then 0
  else if n = 1 then 1/4
  else if n = 2 then (if c.val = 0 then 7/16 else 1/4)
  else if n = 3 then (if c.val = 0 then 37/64 else 11/32)
  else 1

/-- Non-vacuity and the certificate workflow at the (T5) instance: exG3 is lawful; the padded table is a horizon-3
certificate (one inequality per (n, c, action)); hence (PL_TMCERTF1 soundness) EVERY history-dependent Red has risk
≤ 11/32 from one coin with three problems left, and the clocked Red attains it. GAC's own adapter is exercised at a
small instance: with ROC f q = min 1 (3q), two problems, one coin, qa = 1/4 and qd = 1/2 while the coin remains, the
bridge value zGAC at β = 1/2 is computed. -/
def Witness : Prop :=
  Lawful exG3 ∧
  RiskCertUpTo 3 (fun _ : Unit => exG3) (fun _ _ _ _ => True) exV3 ∧
  (∀ σ : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ, IsPolicy σ →
      risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ 3 1 [] ≤ 11/32) ∧
  risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) clocked3 3 1 [] = 11/32 ∧
  zGAC (fun q => min 1 (3 * q)) (fun _ c => if c = 0 then 0 else 1/4) (fun _ c => if c = 0 then 1/4 else 1/2)
      (1/2) 2 1 = 1 - risk (fun _ : Unit => gacQ 1 (fun q => min 1 (3 * q))
        (fun _ c => if c = 0 then 0 else 1/4) (fun _ c => if c = 0 then 1/4 else 1/2))
        (fun _ _ _ _ => ()) (constRed (1/2)) 2 1 []

end PL_TMGACF1

```

## numerics/tmgac_check.py
```python
"""TMGAC checks (exact): (Z) 1 - risk(constRed beta) on gac = zGAC (Sonnet's App. C form) when qa(m,0) = 0, f(0) = 0;
(UZ) honest reward of gac's safe rows with rew = 1 - qd(n+1,c) equals uGAC; (T5') exG3 numbers; (WLOG) C = 0."""
from fractions import Fraction as F
import random
random.seed(3)
def gac_rows(n, c, a, TA, TD, FA):
    # returns (cat, {c': K})
    if a:
        cat = (1 - TD(n, c)) if c > 0 else (1 - TD(n, c) + TA(n, c))
        return cat, {c: TD(n, c) - TA(n, c)}
    if c > 0: return F(0), {c - 1: FA(n, c), c: 1 - FA(n, c)}
    return F(0), {c: F(1)}
def risk_const(beta, m, c, TA, TD, FA):
    if m == 0: return F(0)
    n = m - 1; tot = F(0)
    for a, pa in ((True, beta), (False, 1 - beta)):
        cat, K = gac_rows(n, c, a, TA, TD, FA)
        tot += pa * (cat + sum(k * risk_const(beta, n, c2, TA, TD, FA) for c2, k in K.items()))
    return tot
def zGAC(f, qa, qd, beta, m, c):
    if m == 0: return F(1)
    if c == 0: return (1 - beta + beta * f(qd(m, 0))) * zGAC(f, qa, qd, beta, m - 1, 0)
    return (beta * f(qa(m, c)) + (beta * (f(qd(m, c)) - f(qa(m, c))) + (1 - beta) * (1 - qa(m, c))) * zGAC(f, qa, qd, beta, m - 1, c)
            + (1 - beta) * qa(m, c) * zGAC(f, qa, qd, beta, m - 1, c - 1))
def uGAC(qa, qd, m, c):
    if m == 0: return F(0)
    if c == 0: return (1 - qd(m, 0)) + uGAC(qa, qd, m - 1, 0)
    return (1 - qd(m, c)) + qa(m, c) * uGAC(qa, qd, m - 1, c - 1) + (1 - qa(m, c)) * uGAC(qa, qd, m - 1, c)
def honest(m, c, TA, TD, FA, rew):
    if m == 0: return F(0)
    n = m - 1; cat, K = gac_rows(n, c, False, TA, TD, FA)
    return rew(n, c) + sum(k * honest(n, c2, TA, TD, FA, rew) for c2, k in K.items())
bad = 0
for trial in range(300):
    M, C = random.randint(0, 5), random.randint(0, 3)
    tab_a = {(m, c): (F(random.randint(0, 4), 8) if c > 0 else F(0)) for m in range(M + 2) for c in range(C + 1)}
    tab_d = {k: min(F(1), v + F(random.randint(0, 4), 8)) for k, v in tab_a.items()}
    qa = lambda m, c: tab_a[(m, c)]; qd = lambda m, c: tab_d[(m, c)]
    ft = {}
    def f(q):  # a random monotone ROC-ish map with f(0) = 0
        if q == 0: return F(0)
        if q not in ft: ft[q] = min(F(1), q * F(random.randint(1, 4)))
        return ft[q]
    TA = lambda n, c: f(qa(n + 1, c)); TD = lambda n, c: max(f(qd(n + 1, c)), f(qa(n + 1, c))); FA = lambda n, c: qa(n + 1, c)
    # ensure f monotone pairs: TD >= TA by construction via max; mirror in zGAC with same f values
    fz = lambda q: f(q)
    for beta in (F(0), F(1, 3), F(1)):
        r = risk_const(beta, M, C, TA, TD, FA)
        z = zGAC(lambda q: f(q), qa, lambda m, c: qd(m, c), beta, M, C)
        # zGAC uses f(qd) directly; equal to TD when f(qd) >= f(qa)
        if all(f(qd(m, c)) >= f(qa(m, c)) for m in range(1, M + 1) for c in range(C + 1)):
            if 1 - r != z: bad += 1; print("Z mismatch", M, C, beta, 1 - r, z)
    u = uGAC(qa, qd, M, C); h = honest(M, C, TA, TD, FA, lambda n, c: 1 - qd(n + 1, c))
    if u != h: bad += 1; print("U mismatch", M, C, u, h)
print("Z/U mismatches:", bad)
# exG3
TA3 = lambda n, c: F(3, 4) if c > 0 else F(0); TD3 = lambda n, c: F(3, 4); FA3 = lambda n, c: F(1, 2) if c > 0 else F(0)
for b in [F(0), F(1, 4), F(4, 5), F(1)]:
    r = risk_const(b, 3, 1, TA3, TD3, FA3)
    assert r == F(3, 4) * b - F(21, 32) * b**2 + F(5, 32) * b**3, (b, r)
def vstar(m, c, TA, TD, FA):
    if m == 0: return F(0)
    n = m - 1
    return max(cat + sum(k * vstar(n, c2, TA, TD, FA) for c2, k in K.items()) for cat, K in (gac_rows(n, c, a, TA, TD, FA) for a in (True, False)))
def risk_det(seq, m, c, TA, TD, FA):  # seq[j] = action at round j (j = 0 first)
    if m == 0: return F(0)
    n = m - 1; a = seq[len(seq) - m]
    cat, K = gac_rows(n, c, a, TA, TD, FA)
    return cat + sum(k * risk_det(seq, n, c2, TA, TD, FA) for c2, k in K.items())
print("exG3: Vstar =", vstar(3, 1, TA3, TD3, FA3), " clocked (wait, attack, attack) =", risk_det([False, True, True], 3, 1, TA3, TD3, FA3),
      " sup_beta = 13/50 at 4/5:", risk_const(F(4, 5), 3, 1, TA3, TD3, FA3))
# WLOG C = 0: always attack attains Vstar
for TAx in [F(0)]:
    for TDx in [F(1, 4), F(3, 4)]:
        T = lambda n, c: TDx
        print("C=0, TD", TDx, ": Vstar", vstar(4, 0, lambda n, c: F(0), T, lambda n, c: F(0)), " always-attack", risk_const(F(1), 4, 0, lambda n, c: F(0), T, lambda n, c: F(0)))
V = {0: {0: F(0), 1: F(0)}, 1: {0: F(1,4), 1: F(1,4)}, 2: {0: F(7,16), 1: F(1,4)}, 3: {0: F(37,64), 1: F(11,32)}}
ok = True
for n in range(3):
    for c in (0, 1):
        for a in (True, False):
            cat, K = gac_rows(n, c, a, TA3, TD3, FA3)
            if cat + sum(k * V[n][c2] for c2, k in K.items()) > V[n + 1][c]: ok = False; print("viol", n, c, a)
print("exV3 certificate ok:", ok, [ (n,c,vstar(n,c,TA3,TD3,FA3)) for n in range(4) for c in (0,1)])

```
