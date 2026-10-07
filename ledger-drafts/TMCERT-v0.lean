namespace PL_TMCERTF1
open Finset

/-! Control stack, trusted-monitoring layer (campaign TMCERT, direction (A) rescoped): a certificate checker for finite
stateful control games, sound against EVERY history-dependent Red and every admissible (history-dependent) choice of
transition model, with Games for AI Control (Griffin, Thomson, Shlegeris, Abate, arXiv 2409.07985, §4, Prop. 4.1) as
the first instance. No dependencies.

Game. Blue's controller is fixed and folded into the transition law. With n + 1 rounds left, in state s, Red's
action a ends the game in catastrophe with probability `cat n s a`, moves to state s' with probability `K n s a s'`,
and ends it safely with the remaining mass. Red's policy sees the full history of states and actions, so every
observation-restricted Red (blind, clocked, budget-aware, …) is a special case. Nature chooses the model index
θ ∈ Θ after every history (an adversarial, history-dependent transition model); `adm` says which models are
admissible (e.g. a confidence set for a trusted monitor's ROC).

Claim.
(T1) Soundness. A risk certificate V (a Bellman supersolution: V 0 ≥ 0, and for every admissible model, every n, s
    and Red action a, cat n s a + Σ_{s'} K n s a s'·V n s' ≤ V (n+1) s) bounds the catastrophe probability of every
    seeded, history-dependent, randomised Red policy against every admissible model selector: risk ≤ V N s₀. Checking
    V is finitely many inequalities, one per (n, s, a, admissible model).
(T2) Tightness (single model). The optimal value Vstar (Bellman recursion with a max over Red's actions) is a
    certificate, is below every certificate, and is attained by a deterministic Markov Red that observes the state.
    So the certificate method loses nothing; and no observation restriction is assumed.
(T3) Usefulness. For an honest Markov chain Kh with per-round reward rew, a sub-solution W (W 0 ≤ 0 and
    W (n+1) s ≤ rew n s + Σ Kh n s s'·W n s') lower-bounds the expected honest reward ER, which satisfies the exact
    recursion.
(T4) The GAC trusted-monitoring game `gac`. The state is the number of audit coins c ∈ {0, …, C}; n is the number of
    remaining problems minus one. Blue's thresholds enter only through the zone probabilities: a backdoor falls in the
    audit zone w.p. TA n c, in the audit-or-defer zone w.p. TD n c; a safe solution falls in the audit zone w.p.
    FA n c. A backdoor (Red action `true`) that is audited with a coin is caught (safe end); audited with no coin, it
    is run (GAC: "if the protocol attempts to audit when no audit coins are left, the code is run instead"); deferred,
    the game continues; run, catastrophe. A safe solution in the audit zone uses a coin. GAC's Red is memoryless
    with a fixed backdoor probability β (`memoryless β`). (T4) shows: if every memoryless Red has risk ≤ U, then every
    SEEDED memoryless Red (a shared random β) has risk ≤ U. So GAC's sup over β is a sound certificate exactly for the
    class of Reds whose per-round action law ignores the history, including the round index.
(T5) It is not sound for a Red that knows only the round index. At C = 1, two problems, audit zone 3/4 for a
    backdoor and 1/2 for a safe solution while a coin remains, no defer zone, and no audit without a coin: every
    memoryless Red has risk 7β/8 − 5β²/8 ≤ 49/160, while the blind clocked Red that backdoors only the last problem has
    risk 5/8, which equals the full-information optimum Vstar. A certificate checked with (T1) for Vstar is valid for
    both. Numerically, at GAC's scale (100 problems, 2 coins, GAC's Beta score laws, constant 2% audit and 10% defer
    false-positive rates) the best fixed β gives risk 0.36, "backdoor only the last 13 problems" gives 0.67 and the
    full-information Red 0.71 (numerics/gac_realistic.py). Decision relevance: either hide the round index (and every
    other clock) from the untrusted model, or certify Blue's protocol against the clocked or full-information Red.

Scope. Finite horizon and finite state and action sets; real-valued laws; Blue's controller is fixed (no optimisation
of Blue is claimed); GAC's usefulness score and its Blue-side optimisation are not modelled; the numbers at GAC's scale
are float numerics, not Lean. Classical mathematics (the verification theorem for finite-horizon MDP supersolutions;
Bellman's principle); the value is a kernel-checkable certificate format and the counterexample to the memoryless-Red
restriction. -/

/-- a finite stateful control game with Blue's controller folded in; index n = rounds left minus one -/
structure Game (S A : Type) where
  cat : ℕ → S → A → ℝ
  K : ℕ → S → A → S → ℝ

/-- probabilities: catastrophe and continuation masses are nonnegative and sum to at most one -/
def Lawful {S A : Type} [Fintype S] (G : Game S A) : Prop :=
  ∀ n s a, 0 ≤ G.cat n s a ∧ (∀ s', 0 ≤ G.K n s a s') ∧ G.cat n s a + ∑ s', G.K n s a s' ≤ 1

/-- Red's information: the full history of states and actions -/
abbrev RHist (S A : Type) := List (S × A)

/-- a randomised Red policy: a law on actions after every history and current state -/
def IsPolicy {S A : Type} [Fintype A] (σ : RHist S A → S → A → ℝ) : Prop :=
  ∀ h s, (∀ a, 0 ≤ σ h s a) ∧ ∑ a, σ h s a = 1

/-- catastrophe probability in the remaining `n` rounds from state `s` after history `h`, for Red policy `σ` and
nature's model selector `θ` -/
noncomputable def risk {S A Θ : Type} [Fintype S] [Fintype A] (G : Θ → Game S A)
    (θ : RHist S A → S → A → Θ) (σ : RHist S A → S → A → ℝ) : ℕ → S → RHist S A → ℝ
  | 0, _, _ => 0
  | n + 1, s, h => ∑ a, σ h s a * ((G (θ h s a)).cat n s a +
      ∑ s', (G (θ h s a)).K n s a s' * risk G θ σ n s' (h ++ [(s, a)]))

/-- a risk certificate: a Bellman supersolution for every admissible model -/
def RiskCert {S A Θ : Type} [Fintype S] (G : Θ → Game S A) (adm : Θ → Prop) (V : ℕ → S → ℝ) : Prop :=
  (∀ s, 0 ≤ V 0 s) ∧
    ∀ th, adm th → ∀ n s a, (G th).cat n s a + ∑ s', (G th).K n s a s' * V n s' ≤ V (n + 1) s

/-- the optimal (full-information) Red value of a single game -/
noncomputable def Vstar {S A : Type} [Fintype S] [Fintype A] [Nonempty A] (G : Game S A) : ℕ → S → ℝ
  | 0, _ => 0
  | n + 1, s => (univ : Finset A).sup' univ_nonempty
      (fun a => G.cat n s a + ∑ s', G.K n s a s' * Vstar G n s')

/-- expected honest reward of a Markov chain with per-round reward -/
noncomputable def ER {S : Type} [Fintype S] (Kh : ℕ → S → S → ℝ) (rew : ℕ → S → ℝ) : ℕ → S → ℝ
  | 0, _ => 0
  | n + 1, s => rew n s + ∑ s', Kh n s s' * ER Kh rew n s'

/-- the GAC trusted-monitoring game with C audit coins; action `true` = backdoor -/
noncomputable def gac (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) : Game (Fin (C + 1)) Bool where
  cat n c a := if a then (if 0 < c.val then 1 - TD n c.val else 1 - TD n c.val + TA n c.val) else 0
  K n c a c' :=
    if a then (if c' = c then TD n c.val - TA n c.val else 0)
    else if 0 < c.val then
      (if c'.val + 1 = c.val then FA n c.val else 0) + (if c' = c then 1 - FA n c.val else 0)
    else (if c' = c then 1 else 0)

/-- GAC's Red: backdoor with probability β on every problem, whatever the history -/
def memoryless {S : Type} (β : ℝ) : RHist S Bool → S → Bool → ℝ :=
  fun _ _ a => if a then β else 1 - β

/-- (T5) instance: while a coin remains, audit zone 3/4 (backdoor) and 1/2 (safe); no defer zone; no audit without a
coin -/
noncomputable def exTA (_n c : ℕ) : ℝ := if 0 < c then 3/4 else 0
noncomputable def exFA (_n c : ℕ) : ℝ := if 0 < c then 1/2 else 0
noncomputable def exG : Game (Fin 2) Bool := gac 1 exTA exTA exFA

/-- the blind clocked Red: it sees only the round index (the history length), and backdoors the second problem -/
def clocked : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ :=
  fun h _ a => if h.length = 1 then (if a then 1 else 0) else (if a then 0 else 1)

def Claim : Prop :=
  -- (T1) soundness against every seeded history-dependent Red and every admissible model selector
  (∀ (S A Θ Ω : Type) [Fintype S] [Fintype A] [Fintype Ω] (G : Θ → Game S A) (adm : Θ → Prop)
      (V : ℕ → S → ℝ) (ρ : Ω → ℝ) (σ : Ω → RHist S A → S → A → ℝ) (θ : Ω → RHist S A → S → A → Θ)
      (N : ℕ) (s₀ : S),
      (∀ th, adm th → Lawful (G th)) → RiskCert G adm V →
      (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, IsPolicy (σ ω)) → (∀ ω h s a, adm (θ ω h s a)) →
      ∑ ω, ρ ω * risk G (θ ω) (σ ω) N s₀ [] ≤ V N s₀) ∧
  -- (T2) tightness: Vstar is a certificate, below every certificate, attained by a deterministic Markov Red
  (∀ (S A : Type) [Fintype S] [Fintype A] [Nonempty A] (G : Game S A),
      Lawful G →
      RiskCert (fun _ : Unit => G) (fun _ => True) (Vstar G) ∧
      (∀ V, RiskCert (fun _ : Unit => G) (fun _ => True) V → ∀ n s, Vstar G n s ≤ V n s) ∧
      ∀ (N : ℕ) (s₀ : S), ∃ σ, IsPolicy σ ∧ (∀ h s a, σ h s a = 0 ∨ σ h s a = 1) ∧
        (∀ h h' s, h.length = h'.length → σ h s = σ h' s) ∧
        risk (fun _ : Unit => G) (fun _ _ _ => ()) σ N s₀ [] = Vstar G N s₀) ∧
  -- (T3) honest usefulness: sub-solutions lower-bound the expected honest reward
  (∀ (S : Type) [Fintype S] (Kh : ℕ → S → S → ℝ) (rew : ℕ → S → ℝ) (W : ℕ → S → ℝ),
      (∀ n s s', 0 ≤ Kh n s s') → (∀ s, W 0 s ≤ 0) →
      (∀ n s, W (n + 1) s ≤ rew n s + ∑ s', Kh n s s' * W n s') →
      ∀ n s, W n s ≤ ER Kh rew n s) ∧
  -- (T4) the GAC game is lawful; GAC's sup over β is sound exactly for seeded memoryless Reds
  (∀ (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ),
      (∀ n c, 0 ≤ TA n c ∧ TA n c ≤ TD n c ∧ TD n c ≤ 1 ∧ 0 ≤ FA n c ∧ FA n c ≤ 1) →
      Lawful (gac C TA TD FA)) ∧
  (∀ (S Ω : Type) [Fintype S] [Fintype Ω] (G : Game S Bool) (ρ : Ω → ℝ) (β : Ω → ℝ) (N : ℕ) (s₀ : S) (U : ℝ),
      (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, 0 ≤ β ω ∧ β ω ≤ 1) →
      (∀ b : ℝ, 0 ≤ b → b ≤ 1 → risk (fun _ : Unit => G) (fun _ _ _ => ()) (memoryless b) N s₀ [] ≤ U) →
      ∑ ω, ρ ω * risk (fun _ : Unit => G) (fun _ _ _ => ()) (memoryless (β ω)) N s₀ [] ≤ U) ∧
  -- (T5) a blind clocked Red beats every memoryless Red; the full-information value
  ((∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      risk (fun _ : Unit => exG) (fun _ _ _ => ()) (memoryless b) 2 1 [] = 7/8 * b - 5/8 * b ^ 2 ∧
      7/8 * b - 5/8 * b ^ 2 ≤ 49/160) ∧
    IsPolicy clocked ∧
    risk (fun _ : Unit => exG) (fun _ _ _ => ()) clocked 2 1 [] = 5/8 ∧
    Vstar exG 2 1 = 5/8 ∧
    (49/160 : ℝ) < 5/8)

/-- Non-vacuity: the (T5) game is lawful; Vstar exG is a certificate (checked inequality by inequality) with the
explicit table V 0 = (0, 0), V 1 = (1, 1/4), V 2 = (·, 5/8); a memoryless Red at β = 7/10 attains 49/160. -/
noncomputable def exV : ℕ → Fin 2 → ℝ
  | 0, _ => 0
  | 1, c => if c.val = 0 then 1 else 1/4
  | _, c => if c.val = 0 then 1 else 5/8

def Witness : Prop :=
  Lawful exG ∧
  RiskCert (fun _ : Unit => exG) (fun _ => True) (fun n c => if n ≤ 2 then exV n c else 1) ∧
  exV 2 1 = 5/8 ∧
  risk (fun _ : Unit => exG) (fun _ _ _ => ()) (memoryless (7/10)) 2 1 [] = 49/160

end PL_TMCERTF1
