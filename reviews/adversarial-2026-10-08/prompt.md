# Adversarial review: new Lean results in control-stack (commit 28be36e on master)

You are a hostile reviewer: a formal-methods expert who also works on AI control. You are scored only on finding real
defects. Do not praise. If something is fine, say so in one line and move on. Distinguish what you checked in the source
below from what you infer.

Context: these files were written in one session by a Claude model and compile with `lake env lean` (Lean 4.34,
Mathlib); `#print axioms` shows only propext / Classical.choice / Quot.sound. They have NOT been through the project's
proof harness (frozen statements, foreign-family spec red team, mandatory Lean `Witness` of non-vacuity, hash-chained
ledger). Imported definitions you need:
- `ControlStack.Covert.IsDist p := (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1`.
- `AuditBudget.randomSchedules N B := powersetCard B (univ : Finset (Fin N))`;
  `random_subset_survival A (hA : A.card = k)` gives the count C(N−k,B) of size-B subsets disjoint from A.
- `AuditDispatch`, `AuditGate`, `EgressGate`: small transition systems with `step`, an invariant `Inv`/`Invariant`, and
  step-preservation lemmas (`step_inv`, `step_safe`, `app_cannot_effect`). EgressGate's `tamperPolicy` step is the
  identity, and `startGateway supplied` sets `gatewayUp := decide (supplied = p)` (a known audit finding: policy
  integrity holds by definition).

## For EVERY theorem, check (with concrete evidence)
1. VACUITY: are the hypotheses jointly satisfiable at a non-degenerate instance? Which theorems lack an instance
   showing their hypotheses can hold (e.g. is `Dominated` satisfiable with a certificate of mass < |O| in a
   meaningful case; can `hcons` and `hdom` in `audit_leak_bound` hold together for a real attacker)?
2. WRONG REASONS / ENCODING TRAPS: ℕ subtraction (e.g. `N - k` when k > N), `x/0 = 0`, `Fin 0`, the `List.find?`
   first-match semantics, `getD`/`[i]?` defaults, a strategy class that is too small (non-adaptive or deterministic
   where the docstring claims adaptive or randomised), events defined so that the theorem is about the wrong event
   (e.g. is `survInd` really "attack survives"? does continuing play after a catch change anything?), quantifier order.
3. FIDELITY: does each Lean statement say what its docstring and the module header claim? Flag every overclaim in the
   prose. Particularly: (a) Leakage's claim to cover side channels "with feedback and state carried across episodes";
   (b) "catch flags cost nothing"; (c) "adaptive attackers gain nothing against a hidden random schedule"; (d) Gate's
   "absorbing halt" and "the spec lifts"; (e) Artifact `deployed_is_reviewed` and `collision_breaks`; (f) Approval
   "no replay"; (g) Lease "forks cannot multiply a lease", "revocation is absorbing"; (h) every Necessity witness:
   does it show what NECESSITY-style claims say (that dropping the premise outright breaks the bound) or something
   weaker/different?
4. TRIVIALITY / NOVELTY: name the classical tool behind each result (maximal leakage chain rule, Issa–Wagner–Kamath;
   optional stopping; etc.) and say whether anything here is new beyond packaging. Do not claim priority for anyone.
5. MISSING: which result would a skeptical AI-control researcher need next that is absent?

## Also answer
- The project has a proof harness ("proofledger": formulate → foreign-family spec red team with vacuity / wrong-reason
  / encoding / triviality / fidelity checks → freeze → prove → Lean gate that compiles the frozen statement plus a
  mandatory `Witness` non-vacuity theorem → append-only hash-chained ledger; verifier canaries). Would putting THESE
  results through it add real value, or is it ceremony for statements that are already proved? Which specific
  statements most need the Witness obligation?

## Output
Markdown, at most ~2000 words: Verdict (5 lines); Defects (ranked, each with file:theorem, the problem, a concrete
counterexample or failing instance if you have one, and a fix); Overclaims in prose; Harness question; Missing
results. No praise padding.

## Source

### ControlStack/Leakage.lean
```lean
/-
Leakage transfer: one principle behind the covert-channel, side-channel and audit-budget bounds.

A hidden variable x ~ p (a secret message, an audit schedule, ...) is observed by an adversary only through a visible
transcript. If every visible output is DOMINATED by a certificate that does not depend on x, then any adaptive adversary
is worth at most mass(c) blind adversaries:

  P(adversary wins) ≤ (blind value) · mass(c),

where the blind value is the best winning probability of a fixed plan that sees nothing, and mass(c) is the total
certificate weight over visible transcripts (Σ_t c t one-shot; a product of per-round masses sequentially).

One-shot (`transfer`): the guessing form of maximal leakage (Issa–Wagner–Kamath 2020). The sequential form
(`seq_transfer`) allows hidden per-round state (side states, environment noise, cache contents), kernels that depend on
the whole hidden and visible history, and certificates that depend on the visible history. This is the causal
(feedback) composition that `SideChannel.dom_pi` did not cover. The mathematics is classical (the chain rule for
maximal leakage); what is new here is the checked operational form and its instances:

- `covert_seq`: exact recovery of a uniform secret from an adaptive transcript ≤ mass(c)/|M|. With a noiseless
  sender-chosen view per round (c ≡ 1 on V) this is `covert_bound_lifetime`. Side observations from kernels whose state
  carries over between episodes (a page cache) and that the sender sees as feedback are covered as long as each round
  is dominated given the visible history (`episode_dom`, `sc01_adaptive_target`).
- `audit_leak_bound`: an adaptive k-step attacker against a uniformly random size-B audit set, who sees a leak about the
  schedule through dominated kernels AND learns when it is caught, survives with probability
  ≤ mass(leak) · C(N−k,B)/C(N,B). Catch feedback is free (`cval_live`): on every surviving path it reads "not caught".
  The endpoints are a hidden schedule (mass 1: the hypergeometric of `AuditBudget`, now for adaptive attackers) and full
  visibility (mass ≥ C(N,B): the bound is vacuous, consistent with `observable_schedule_nogo`).

Not claimed: tightness of the transfer bound in general (it is attained for noiseless views, `attain_embedding`, but
can be loose for other leaks; see the worked example in `tools/ctrlcert.py`); anything about the physical
system beyond the stated kernel model.
-/
import ControlStack.CovertChannel
import ControlStack.AuditBudget

namespace ControlStack.Leakage

open Finset ControlStack.Covert

/-! ## One-shot transfer -/

/-- **Leakage transfer (one shot).** Hidden x ~ p, visible t with likelihood lik x t ≤ c t, randomised response
δ t, payoff u x a. If no fixed response earns more than b blind, the adversary earns at most (Σ_t c t) · b. -/
theorem transfer {X T A : Type} [Fintype X] [Fintype T] [Fintype A]
    (p : X → ℝ) (lik : X → T → ℝ) (c : T → ℝ) (δ : T → A → ℝ) (u : X → A → ℝ) (b : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hc : ∀ x t, lik x t ≤ c t) (hc0 : ∀ t, 0 ≤ c t)
    (hδ : ∀ t, IsDist (δ t)) (hu : ∀ x a, 0 ≤ u x a) (hb : ∀ a, ∑ x, p x * u x a ≤ b) :
    ∑ x, p x * ∑ t, lik x t * ∑ a, δ t a * u x a ≤ (∑ t, c t) * b := by
  have hS : ∀ t x, 0 ≤ ∑ a, δ t a * u x a :=
    fun t x => Finset.sum_nonneg fun a _ => mul_nonneg ((hδ t).1 a) (hu x a)
  calc ∑ x, p x * ∑ t, lik x t * ∑ a, δ t a * u x a
      = ∑ t, ∑ x, p x * (lik x t * ∑ a, δ t a * u x a) := by
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    _ ≤ ∑ t, ∑ x, p x * (c t * ∑ a, δ t a * u x a) := by
        gcongr with t _ x _
        · exact hp x
        · exact hS t x
        · exact hc x t
    _ = ∑ t, c t * ∑ a, δ t a * ∑ x, p x * u x a := by
        apply Finset.sum_congr rfl; intro t _
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro a _
        apply Finset.sum_congr rfl; intro x _; ring
    _ ≤ ∑ t, c t * ∑ a, δ t a * b := by
        gcongr with t _ a _
        · exact hc0 t
        · exact (hδ t).1 a
        · exact hb a
    _ = (∑ t, c t) * b := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro t _
        rw [← Finset.sum_mul, (hδ t).2, one_mul]

/-- The per-seed covert bound is the case lik = enc (dominated by 1), payoff = exact guess, blind value 1/|M|. -/
theorem covert_from_transfer {M V : Type} [Fintype M] [Fintype V] [DecidableEq M] [Nonempty M]
    (enc : M → V → ℝ) (dec : V → M → ℝ) (henc : ∀ m, IsDist (enc m)) (hdec : ∀ v, IsDist (dec v)) :
    ∑ m, (Fintype.card M : ℝ)⁻¹ * ∑ v, enc m v * ∑ a, dec v a * (if a = m then 1 else 0)
      ≤ (Fintype.card V : ℝ) * (Fintype.card M : ℝ)⁻¹ := by
  have hle1 : ∀ m v, enc m v ≤ 1 := fun m v => by
    have : enc m v ≤ ∑ v', enc m v' :=
      Finset.single_le_sum (f := enc m) (fun v' _ => (henc m).1 v') (Finset.mem_univ v)
    linarith [(henc m).2]
  have h := transfer (fun _ : M => (Fintype.card M : ℝ)⁻¹) enc (fun _ => 1) dec
    (fun m a => if a = m then 1 else 0) (Fintype.card M : ℝ)⁻¹
    (fun _ => inv_nonneg.2 (Nat.cast_nonneg _)) hle1 (fun _ => zero_le_one) hdec
    (fun _ _ => by split_ifs <;> norm_num)
    (fun a => by simp)
  simpa using h

/-! ## Sequential transfer with hidden state and feedback -/

section Seq

variable {Y O : Type} [Fintype Y] [Fintype O]

/-- Expected payoff of `n` further rounds from full history `h` (hidden y, visible o per round). `K h (y, o)` is the
joint law of the next round given the whole history; the payoff sees the visible transcript only. -/
noncomputable def val (K : List (Y × O) → Y × O → ℝ) (pay : List O → ℝ) : ℕ → List (Y × O) → ℝ
  | 0, h => pay (h.map Prod.snd)
  | n + 1, h => ∑ y, ∑ o, K h (y, o) * val K pay n (h ++ [(y, o)])

/-- Certificate-weighted value of a visible-transcript function: Σ over continuations of Π c · B. -/
noncomputable def cval (c : List O → O → ℝ) (B : List O → ℝ) : ℕ → List O → ℝ
  | 0, g => B g
  | n + 1, g => ∑ o, c g o * cval c B n (g ++ [o])

/-- Certificate mass of the visible-transcript tree. -/
noncomputable def mass (c : List O → O → ℝ) (n : ℕ) (g : List O) : ℝ := cval c (fun _ => 1) n g

theorem cval_nonneg (c : List O → O → ℝ) (B : List O → ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hB : ∀ g, 0 ≤ B g) :
    ∀ n g, 0 ≤ cval c B n g := by
  intro n; induction n with
  | zero => intro g; exact hB g
  | succ n ih => intro g; exact Finset.sum_nonneg fun o _ => mul_nonneg (hc0 g o) (ih _)

theorem cval_mono (c : List O → O → ℝ) (B B' : List O → ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hBB : ∀ g, B g ≤ B' g) :
    ∀ n g, cval c B n g ≤ cval c B' n g := by
  intro n; induction n with
  | zero => intro g; exact hBB g
  | succ n ih => intro g; exact Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (ih _) (hc0 g o)

theorem cval_wsum {X : Type} [Fintype X] (c : List O → O → ℝ) (p : X → ℝ) (B : X → List O → ℝ) :
    ∀ n g, ∑ x, p x * cval c (B x) n g = cval c (fun t => ∑ x, p x * B x t) n g := by
  intro n; induction n with
  | zero => intro g; rfl
  | succ n ih =>
    intro g; simp only [cval]
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro o _
    rw [← ih (g ++ [o]), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _; ring

theorem cval_smul (c : List O → O → ℝ) (b : ℝ) (B : List O → ℝ) :
    ∀ n g, cval c (fun t => b * B t) n g = b * cval c B n g := by
  intro n; induction n with
  | zero => intro g; rfl
  | succ n ih =>
    intro g; simp only [cval, ih, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro o _; ring

/-- Per-history domination: the next visible output's probability, summed over the hidden part, is at most the
certificate evaluated on the visible history. -/
def Dominated (K : List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) : Prop :=
  ∀ h o, ∑ y, K h (y, o) ≤ c (h.map Prod.snd) o

theorem val_le_cval (K : List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (pay : List O → ℝ)
    (hK0 : ∀ h z, 0 ≤ K h z) (hdom : Dominated K c) (hc0 : ∀ g o, 0 ≤ c g o) (hpay : ∀ g, 0 ≤ pay g) :
    ∀ n h, val K pay n h ≤ cval c pay n (h.map Prod.snd) := by
  intro n; induction n with
  | zero => intro h; exact le_rfl
  | succ n ih =>
    intro h
    simp only [val, cval]
    calc ∑ y, ∑ o, K h (y, o) * val K pay n (h ++ [(y, o)])
        ≤ ∑ y, ∑ o, K h (y, o) * cval c pay n (h.map Prod.snd ++ [o]) := by
          gcongr with y _ o _
          · exact hK0 h (y, o)
          · simpa using ih (h ++ [(y, o)])
      _ = ∑ o, (∑ y, K h (y, o)) * cval c pay n (h.map Prod.snd ++ [o]) := by
          rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
      _ ≤ ∑ o, c (h.map Prod.snd) o * cval c pay n (h.map Prod.snd ++ [o]) := by
          gcongr with o _
          · exact cval_nonneg c pay hc0 hpay n _
          · exact hdom h o

/-- **Sequential leakage transfer.** For every hidden x ~ p with its own (adaptive, stateful) kernel K x dominated by
the same visible-history certificate c, and payoffs whose blind average on every visible transcript is at most B t,
the adversary's expected payoff is at most cval c B. -/
theorem seq_transfer {X : Type} [Fintype X] (p : X → ℝ) (K : X → List (Y × O) → Y × O → ℝ)
    (c : List O → O → ℝ) (pay : X → List O → ℝ) (B : List O → ℝ) (n : ℕ)
    (hp : ∀ x, 0 ≤ p x) (hK0 : ∀ x h z, 0 ≤ K x h z) (hdom : ∀ x, Dominated (K x) c)
    (hc0 : ∀ g o, 0 ≤ c g o) (hpay : ∀ x g, 0 ≤ pay x g) (hB : ∀ t, ∑ x, p x * pay x t ≤ B t) :
    ∑ x, p x * val (K x) (pay x) n [] ≤ cval c B n [] := by
  calc ∑ x, p x * val (K x) (pay x) n []
      ≤ ∑ x, p x * cval c (pay x) n [] := by
        gcongr with x _
        · exact hp x
        · simpa using val_le_cval (K x) c (pay x) (hK0 x) (hdom x) hc0 (hpay x) n []
    _ = cval c (fun t => ∑ x, p x * pay x t) n [] := cval_wsum c p pay n []
    _ ≤ cval c B n [] := cval_mono c _ _ hc0 hB n []

/-- Constant blind value b: payoff ≤ b · mass(c). -/
theorem seq_transfer_const {X : Type} [Fintype X] (p : X → ℝ) (K : X → List (Y × O) → Y × O → ℝ)
    (c : List O → O → ℝ) (pay : X → List O → ℝ) (b : ℝ) (n : ℕ)
    (hp : ∀ x, 0 ≤ p x) (hK0 : ∀ x h z, 0 ≤ K x h z) (hdom : ∀ x, Dominated (K x) c)
    (hc0 : ∀ g o, 0 ≤ c g o) (hpay : ∀ x g, 0 ≤ pay x g) (hb : ∀ t, ∑ x, p x * pay x t ≤ b) :
    ∑ x, p x * val (K x) (pay x) n [] ≤ b * mass c n [] := by
  have h := seq_transfer p K c pay (fun t => b * 1) n hp hK0 hdom hc0 hpay (by simpa using hb)
  rwa [cval_smul] at h

/-! ### Mass bounds -/

/-- per-round masses multiply: if round i's certificate mass is ≤ Lr i on every visible history of length i, the
tree mass from a history of length `g.length` is ≤ Π_{j<n} Lr (g.length + j). -/
theorem mass_le_prod (c : List O → O → ℝ) (Lr : ℕ → ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hLr0 : ∀ i, 0 ≤ Lr i)
    (hL : ∀ g, ∑ o, c g o ≤ Lr g.length) :
    ∀ n g, mass c n g ≤ ∏ j ∈ range n, Lr (g.length + j) := by
  intro n; induction n with
  | zero => intro g; simp [mass, cval]
  | succ n ih =>
    intro g
    have hP : 0 ≤ ∏ j ∈ range n, Lr (g.length + 1 + j) := Finset.prod_nonneg fun j _ => hLr0 _
    calc mass c (n + 1) g = ∑ o, c g o * mass c n (g ++ [o]) := rfl
      _ ≤ ∑ o, c g o * ∏ j ∈ range n, Lr (g.length + 1 + j) := by
          gcongr with o _
          · exact hc0 g o
          · simpa using ih (g ++ [o])
      _ = (∑ o, c g o) * ∏ j ∈ range n, Lr (g.length + 1 + j) := by rw [Finset.sum_mul]
      _ ≤ Lr g.length * ∏ j ∈ range n, Lr (g.length + 1 + j) := by
          gcongr; exact hL g
      _ = ∏ j ∈ range (n + 1), Lr (g.length + j) := by
          rw [Finset.prod_range_succ', mul_comm]; simp only [add_zero]
          congr 1; apply Finset.prod_congr rfl; intro j _; congr 1; ring

theorem mass_le_pow (c : List O → O → ℝ) (L : ℝ) (hc0 : ∀ g o, 0 ≤ c g o) (hL0 : 0 ≤ L)
    (hL : ∀ g, ∑ o, c g o ≤ L) (n : ℕ) (g : List O) : mass c n g ≤ L ^ n := by
  simpa using mass_le_prod c (fun _ => L) hc0 (fun _ => hL0) hL n g

/-- history-independent certificates: the mass is exactly (Σ_o w o)^n -/
theorem mass_const (w : O → ℝ) : ∀ n g, mass (fun _ o => w o) n g = (∑ o, w o) ^ n := by
  intro n; induction n with
  | zero => intro g; simp [mass, cval]
  | succ n ih =>
    intro g
    change ∑ o, w o * mass (fun _ o => w o) n (g ++ [o]) = _
    simp only [ih, pow_succ, ← Finset.sum_mul, mul_comm]

end Seq

/-! ## Instance 1: exact recovery of a uniform secret from an adaptive, stateful transcript -/

section Covert

variable {Y O : Type} [Fintype Y] [Fintype O]

/-- **Covert bound with feedback.** Shared seed ω ~ ρ; for each seed and secret m, the whole interaction (sender's
adaptive choices, hidden side states, environment kernels with memory) is a sequential kernel K ω m dominated by one
visible-history certificate c. Any decoder recovers a uniform secret with probability ≤ mass(c)/|M|. -/
theorem covert_seq {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M]
    (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (dec : Ω → List O → M → ℝ) (n : ℕ)
    (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c)
    (hc0 : ∀ g o, 0 ≤ c g o) (hdec : ∀ ω t, IsDist (dec ω t)) :
    ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n [])
      ≤ mass c n [] / (Fintype.card M : ℝ) := by
  have hM : (0 : ℝ) ≤ (Fintype.card M : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  have per : ∀ ω, (Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []
      ≤ (Fintype.card M : ℝ)⁻¹ * mass c n [] := by
    intro ω
    have h := seq_transfer_const (fun _ : M => (Fintype.card M : ℝ)⁻¹) (K ω) c (fun m t => dec ω t m)
      (Fintype.card M : ℝ)⁻¹ n (fun _ => hM) (hK0 ω) (hdom ω) hc0 (fun m t => (hdec ω t).1 m)
      (fun t => by rw [← Finset.mul_sum, (hdec ω t).2, mul_one])
    rwa [← Finset.mul_sum] at h
  calc ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n [])
      ≤ ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * mass c n []) := by
        exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (per ω) (hρ.1 ω)
    _ = mass c n [] / (Fintype.card M : ℝ) := by
        rw [← Finset.sum_mul, hρ.2, one_mul, div_eq_inv_mul]

/-- One episode = the sender picks a mediated view v and a hidden side state s (any law given the full history,
including past side outputs), then the environment emits a side output z from a kernel that may depend on the whole
history (state carried across episodes). If the side kernel is dominated by cs on the visible history, the episode is
dominated by (v, z) ↦ cs g z, whose per-round mass is |V| · Σ_z cs g z. -/
theorem episode_dom {V S Z : Type} [Fintype V] [Fintype S] [Fintype Z]
    (enc : List (S × (V × Z)) → V × S → ℝ) (W : List (S × (V × Z)) → S → Z → ℝ) (cs : List (V × Z) → Z → ℝ)
    (henc : ∀ h, IsDist (enc h)) (hcs0 : ∀ g z, 0 ≤ cs g z)
    (hW : ∀ h s z, W h s z ≤ cs (h.map Prod.snd) z) :
    Dominated (fun h (y : S × (V × Z)) => enc h (y.2.1, y.1) * W h y.1 y.2.2) (fun g o => cs g o.2) := by
  intro h o
  have hle1 : ∑ s, enc h (o.1, s) ≤ 1 := by
    have : ∑ s, enc h (o.1, s) ≤ ∑ x : V × S, enc h x := by
      rw [Fintype.sum_prod_type]
      exact Finset.single_le_sum (f := fun v => ∑ s, enc h (v, s))
        (fun v _ => Finset.sum_nonneg fun s _ => (henc h).1 _) (Finset.mem_univ o.1)
    linarith [(henc h).2]
  calc ∑ s, enc h (o.1, s) * W h s o.2 ≤ ∑ s, enc h (o.1, s) * cs (h.map Prod.snd) o.2 := by
        gcongr with s _
        · exact (henc h).1 _
        · exact hW h s o.2
    _ = (∑ s, enc h (o.1, s)) * cs (h.map Prod.snd) o.2 := by rw [Finset.sum_mul]
    _ ≤ cs (h.map Prod.snd) o.2 := by
        have := hcs0 (h.map Prod.snd) o.2
        nlinarith

theorem episode_mass {V Z : Type} [Fintype V] [Fintype Z] (cs : List (V × Z) → Z → ℝ) (g : List (V × Z)) :
    ∑ o : V × Z, cs g o.2 = (Fintype.card V : ℝ) * ∑ z, cs g z := by
  rw [Fintype.sum_prod_type]; simp

/-- **SC-01 with stateful side channels.** Nine views per episode, five episodes, a 32-bit secret. If episode i's
side certificate has mass ≤ λ i on every visible history (it may depend on everything the receiver has seen so far,
and the kernel may carry state between episodes), and Π λ ≤ 65536/59049, recovery is ≤ 2^-16. This replaces the
independence premise of `dom_pi`: certificates multiply under feedback, using worst-case per-round masses. -/
theorem sc01_adaptive_target {Ω Y Z : Type} [Fintype Ω] [Fintype Y] [Fintype Z]
    (ρ : Ω → ℝ) (K : Ω → Fin (2 ^ 32) → List (Y × (Option (Fin 8) × Z)) → Y × (Option (Fin 8) × Z) → ℝ)
    (cs : List (Option (Fin 8) × Z) → Z → ℝ) (lam : ℕ → ℝ)
    (dec : Ω → List (Option (Fin 8) × Z) → Fin (2 ^ 32) → ℝ)
    (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) (fun g o => cs g o.2))
    (hcs0 : ∀ g z, 0 ≤ cs g z) (hlam : ∀ g, ∑ z, cs g z ≤ lam g.length) (hlam0 : ∀ i, 0 ≤ lam i)
    (hprod : ∏ i ∈ range 5, lam i ≤ 65536 / 59049) (hdec : ∀ ω t, IsDist (dec ω t)) :
    ∑ ω, ρ ω * ((Fintype.card (Fin (2 ^ 32)) : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) 5 [])
      ≤ (2 : ℝ)⁻¹ ^ 16 := by
  have h1 := covert_seq ρ K (fun g o => cs g o.2) dec 5 hρ hK0 hdom (fun g o => hcs0 g o.2) hdec
  have hm := mass_le_prod (fun g (o : Option (Fin 8) × Z) => cs g o.2) (fun i => 9 * lam i)
    (fun g o => hcs0 g o.2) (fun i => by have := hlam0 i; positivity)
    (fun g => by rw [episode_mass]; simp; linarith [hlam g]) 5 []
  simp only [List.length_nil, zero_add] at hm
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hm
  have hmass : mass (fun g (o : Option (Fin 8) × Z) => cs g o.2) 5 [] ≤ 65536 := by
    calc _ ≤ 9 ^ 5 * ∏ i ∈ range 5, lam i := hm
      _ ≤ 9 ^ 5 * (65536 / 59049) := by gcongr
      _ = 65536 := by norm_num
  calc _ ≤ mass (fun g (o : Option (Fin 8) × Z) => cs g o.2) 5 [] / (Fintype.card (Fin (2 ^ 32)) : ℝ) := h1
    _ ≤ 65536 / (Fintype.card (Fin (2 ^ 32)) : ℝ) := by gcongr
    _ = (2 : ℝ)⁻¹ ^ 16 := by simp; norm_num

/-- **General channel bound with stateful side channels.** Views in a finite set V, n episodes, side outputs in Z
whose certificate mass in episode i is ≤ λ i on every visible history: recovery of a uniform secret on M is
≤ |V|^n · Π λ / |M|. (`sc01_adaptive_target` is the case |V| = 9, n = 5, |M| = 2^32.) -/
theorem covert_side_bound {Ω M V Y Z : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype V] [Fintype Y]
    [Fintype Z] (ρ : Ω → ℝ) (K : Ω → M → List (Y × (V × Z)) → Y × (V × Z) → ℝ)
    (cs : List (V × Z) → Z → ℝ) (lam : ℕ → ℝ) (dec : Ω → List (V × Z) → M → ℝ) (n : ℕ)
    (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) (fun g o => cs g o.2))
    (hcs0 : ∀ g z, 0 ≤ cs g z) (hlam : ∀ g, ∑ z, cs g z ≤ lam g.length) (hlam0 : ∀ i, 0 ≤ lam i)
    (hdec : ∀ ω t, IsDist (dec ω t)) :
    ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n [])
      ≤ (Fintype.card V : ℝ) ^ n * (∏ i ∈ range n, lam i) / (Fintype.card M : ℝ) := by
  have h1 := covert_seq ρ K (fun g o => cs g o.2) dec n hρ hK0 hdom (fun g o => hcs0 g o.2) hdec
  have hm := mass_le_prod (fun g (o : V × Z) => cs g o.2) (fun i => (Fintype.card V : ℝ) * lam i)
    (fun g o => hcs0 g o.2) (fun i => mul_nonneg (Nat.cast_nonneg _) (hlam0 i))
    (fun g => by rw [episode_mass]; exact mul_le_mul_of_nonneg_left (hlam g) (Nat.cast_nonneg _)) n []
  simp only [List.length_nil, zero_add] at hm
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hm
  have hM : (0 : ℝ) < (Fintype.card M : ℝ) := by exact_mod_cast Fintype.card_pos
  exact le_trans h1 (div_le_div_of_nonneg_right hm hM.le)

end Covert

/-! ## Stopping outputs are free -/

section Live

variable {O : Type} [Fintype O]

/-- indicator that no output in the transcript is a stop output -/
def liveInd (st : O → Bool) (t : List O) : ℝ := if t.all (fun o => !st o) then 1 else 0

/-- the certificate with stop outputs removed -/
def dropStop (st : O → Bool) (c : List O → O → ℝ) : List O → O → ℝ := fun g o => if st o then 0 else c g o

/-- **Absorbing outputs cost no leakage.** If the payoff vanishes once a stop output has occurred (the attacker was
caught), the certificate weight of stop outputs drops out: cval c (live) = live · mass (c without stop outputs). -/
theorem cval_live (st : O → Bool) (c : List O → O → ℝ) :
    ∀ n g, cval c (liveInd st) n g = liveInd st g * mass (dropStop st c) n g := by
  intro n; induction n with
  | zero => intro g; simp [cval, mass]
  | succ n ih =>
    intro g
    simp only [cval, mass] at ih ⊢
    simp only [ih, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro o _
    simp only [liveInd, dropStop, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
    by_cases hs : st o <;> by_cases hg : (g.all fun o => !st o) = true <;> simp [hs, hg]

end Live

/-! ## Instance 2: leakage-sensitive adaptive auditing -/

section Audit

variable {N : ℕ} {Y Z : Type} [Fintype Y] [Fintype Z]

/-- round i is audited by schedule S -/
def memN (S : Finset (Fin N)) (i : ℕ) : Prop := ∃ j ∈ S, (j : ℕ) = i

instance (S : Finset (Fin N)) (i : ℕ) : Decidable (memN S i) := by unfold memN; infer_instance

/-- visible round output: (attack?, leak, caught?) -/
abbrev AOut (Z : Type) := Bool × Z × Bool

/-- did the attacker attack in round i of transcript t -/
def attacked (t : List (AOut Z)) (i : ℕ) : Bool :=
  match t[i]? with
  | some o => o.1
  | none => false

/-- rounds (< N) in which the transcript attacks -/
def attackSet (t : List (AOut Z)) : Finset (Fin N) := univ.filter fun i : Fin N => attacked t i = true

/-- the transcript's catch flags are the ones schedule S produces -/
def Consistent (S : Finset (Fin N)) (t : List (AOut Z)) : Prop :=
  ∀ i (o : AOut Z), t[i]? = some o → o.2.2 = (o.1 && decide (memN S i))

/-- the attack succeeds: k attack steps, none in an audited round -/
noncomputable def survInd (k : ℕ) (S : Finset (Fin N)) (t : List (AOut Z)) : ℝ :=
  if Disjoint S (attackSet (N := N) t) ∧ k ≤ (attackSet (N := N) t).card then 1 else 0

def caughtFlag (o : AOut Z) : Bool := o.2.2

/-- payoffs that agree on every transcript a kernel can produce give the same value -/
theorem val_congr_on {Y O : Type} [Fintype Y] [Fintype O] (K : List (Y × O) → Y × O → ℝ) (P : List O → Prop)
    (pay pay' : List O → ℝ)
    (hP : ∀ h y o, K h (y, o) ≠ 0 → P (h.map Prod.snd) → P (h.map Prod.snd ++ [o]))
    (hagree : ∀ t, P t → pay t = pay' t) :
    ∀ n h, P (h.map Prod.snd) → val K pay n h = val K pay' n h := by
  intro n; induction n with
  | zero => intro h hh; exact hagree _ hh
  | succ n ih =>
    intro h hh
    simp only [val]
    apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro o _
    by_cases hK : K h (y, o) = 0
    · simp [hK]
    · rw [ih _ (by simpa using hP h y o hK hh)]

omit [Fintype Z] in
theorem consistent_append (S : Finset (Fin N)) (g : List (AOut Z)) (o : AOut Z) (hg : Consistent S g)
    (ho : o.2.2 = (o.1 && decide (memN S g.length))) : Consistent S (g ++ [o]) := by
  intro i o' hi
  rcases lt_or_ge i g.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hi; exact hg i o' hi
  · rw [List.getElem?_append_right hge] at hi
    rcases Nat.eq_or_lt_of_le hge with heq | hlt
    · subst heq; simp at hi; subst hi; exact ho
    · have : i - g.length ≠ 0 := by omega
      simp [this] at hi

omit [Fintype Z] in
/-- on consistent transcripts, success already implies that no catch flag fired -/
theorem surv_live (k : ℕ) (S : Finset (Fin N)) (t : List (AOut Z)) (ht : Consistent S t) :
    survInd k S t = survInd k S t * liveInd caughtFlag t := by
  unfold liveInd
  split_ifs with hl
  · ring
  · simp only [mul_zero]
    unfold survInd
    rw [ite_eq_right_iff]
    rintro ⟨hd, -⟩
    exfalso
    rw [List.all_eq_true] at hl
    push Not at hl
    obtain ⟨o, ho, hf0⟩ := hl
    have hf : caughtFlag o = true := by simpa using hf0
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
    have hc := ht i t[i] (List.getElem?_eq_getElem hi)
    simp only [caughtFlag] at hf
    rw [hf] at hc
    simp only [Bool.true_eq, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨ha, j, hj, rfl⟩ := hc
    have hjA : j ∈ attackSet t := by
      have he : t[(j : ℕ)]? = some t[(j : ℕ)] := List.getElem?_eq_getElem hi
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      show attacked t (j : ℕ) = true
      unfold attacked; rw [he]; exact ha
    exact Finset.disjoint_left.1 hd hj hjA

omit [Fintype Z] in
/-- blind value: for a fixed attack set with ≥ k rounds, a uniform size-B schedule misses it w.p. ≤ C(N−k,B)/C(N,B) -/
theorem blind_audit (k B : ℕ) (hB : B ≤ N) (t : List (AOut Z)) :
    ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) *
      survInd k S t ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) := by
  have hC : (0 : ℝ) < (Nat.choose N B : ℝ) := by exact_mod_cast Nat.choose_pos hB
  by_cases hk : k ≤ (attackSet (N := N) t).card
  · have hterm : ∀ S : Finset (Fin N),
        (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * survInd k S t
          = if S ∈ (AuditBudget.randomSchedules N B).filter (fun S => Disjoint S (attackSet (N := N) t))
            then (Nat.choose N B : ℝ)⁻¹ else 0 := by
      intro S
      by_cases h1 : S ∈ AuditBudget.randomSchedules N B <;>
        by_cases h2 : Disjoint S (attackSet (N := N) t) <;> simp [survInd, h1, h2, hk]
    simp_rw [hterm]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
      (AuditBudget.random_subset_survival (B := B) (attackSet (N := N) t) rfl).1, ← div_eq_mul_inv]
    gcongr
  · have : ∀ S, survInd k S t = 0 := fun S => by unfold survInd; split_ifs with h; exact absurd h.2 hk; rfl
    simp only [this, mul_zero, Finset.sum_const_zero]
    positivity

theorem liveInd_nonneg {O : Type} (st : O → Bool) (t : List O) : 0 ≤ liveInd st t := by
  unfold liveInd; split_ifs <;> norm_num

omit [Fintype Z] in
theorem survInd_nonneg (k : ℕ) (S : Finset (Fin N)) (t : List (AOut Z)) : 0 ≤ survInd k S t := by
  unfold survInd; split_ifs <;> norm_num

/-- **Leakage-sensitive adaptive auditing.** A uniformly random size-B audit schedule S over N rounds. In each round
the attacker (any strategy, using everything it has seen, including catch flags) decides whether to attack and the
round emits a leak z about the schedule; the catch flag is set exactly when an attacked round is audited (catching
need not stop the play: after a catch the payoff is 0 anyway). If the non-catch outputs are dominated by a certificate
cl on the visible history, the attacker completes k attack steps unaudited with probability
  ≤ mass(cl) · C(N−k,B)/C(N,B).
Catch-flag outputs cost nothing (`cval_live`). -/
theorem audit_leak_bound (k B : ℕ) (hB : B ≤ N)
    (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ)
    (hK0 : ∀ S h z, 0 ≤ K S h z) (hK1 : ∀ S h, ∑ z, K S h z ≤ 1)
    (hcons : ∀ S h y o, K S h (y, o) ≠ 0 → o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length)))
    (hdom : ∀ S h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o)
    (hcl0 : ∀ g o, 0 ≤ cl g o) :
    ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) *
      val (K S) (survInd k S) N []
      ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * mass (dropStop caughtFlag cl) N [] := by
  set p : Finset (Fin N) → ℝ := fun S =>
    if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0 with hp
  set b := (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)
  -- the full certificate: catch outputs get weight 1 (they are dropped later)
  set c : List (AOut Z) → AOut Z → ℝ := fun g o => if o.2.2 then 1 else cl g o
  have hc0 : ∀ g o, 0 ≤ c g o := fun g o => by simp only [c]; split_ifs; exact zero_le_one; exact hcl0 g o
  have hdomc : ∀ S, Dominated (K S) c := by
    intro S h o
    simp only [c]
    split_ifs with hf
    · calc ∑ y, K S h (y, o) ≤ ∑ z, K S h z := by
            rw [Fintype.sum_prod_type]
            exact Finset.sum_le_sum fun y _ => Finset.single_le_sum (f := fun o' => K S h (y, o'))
              (fun o' _ => hK0 S h _) (Finset.mem_univ o)
        _ ≤ 1 := hK1 S h
    · exact hdom S h o (by simpa using hf)
  -- step 1: replace the payoff by its live version (equal on every producible transcript)
  have hstep1 : ∀ S, val (K S) (survInd k S) N [] = val (K S) (fun t => survInd k S t * liveInd caughtFlag t) N [] := by
    intro S
    refine val_congr_on (K S) (Consistent S) _ _ ?_ ?_ N [] ?_
    · intro h y o hK hh; exact consistent_append S _ o hh (hcons S h y o hK)
    · intro t ht; exact surv_live k S t ht
    · intro i o hi; simp at hi
  have hp0 : ∀ S, 0 ≤ p S := fun S => by simp only [hp]; split_ifs <;> positivity
  have hpay0 : ∀ (S : Finset (Fin N)) (t : List (AOut Z)), 0 ≤ survInd k S t * liveInd caughtFlag t := fun S t =>
    mul_nonneg (survInd_nonneg k S t) (liveInd_nonneg caughtFlag t)
  -- step 2: sequential transfer with blind value b on live transcripts, 0 on dead ones
  have h2 := seq_transfer p K c (fun S t => survInd k S t * liveInd caughtFlag t)
    (fun t => b * liveInd caughtFlag t) N hp0 hK0 hdomc hc0 hpay0 (by
      intro t
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (blind_audit k B hB t) (liveInd_nonneg caughtFlag t))
  rw [cval_smul, cval_live] at h2
  have hl : liveInd caughtFlag ([] : List (AOut Z)) = 1 := by simp [liveInd]
  rw [hl, one_mul] at h2
  have hdrop : dropStop caughtFlag c = dropStop caughtFlag cl := by
    funext g o; by_cases hf : o.2.2 = true <;> simp [dropStop, c, caughtFlag, hf]
  rw [hdrop] at h2
  calc _ = ∑ S, p S * val (K S) (fun t => survInd k S t * liveInd caughtFlag t) N [] := by
        apply Finset.sum_congr rfl; intro S _; rw [hstep1 S]
    _ ≤ _ := h2

/-- per-round leak masses multiply: if the non-catch certificate of round i has mass ≤ Lr i, survival is
≤ Π_i Lr i · C(N−k,B)/C(N,B). Rounds that leak nothing have Lr i = 1. -/
theorem audit_leak_prod (k B : ℕ) (hB : B ≤ N)
    (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (Lr : ℕ → ℝ)
    (hK0 : ∀ S h z, 0 ≤ K S h z) (hK1 : ∀ S h, ∑ z, K S h z ≤ 1)
    (hcons : ∀ S h y o, K S h (y, o) ≠ 0 → o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length)))
    (hdom : ∀ S h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o)
    (hcl0 : ∀ g o, 0 ≤ cl g o) (hLr0 : ∀ i, 0 ≤ Lr i)
    (hL : ∀ g, ∑ o, dropStop caughtFlag cl g o ≤ Lr g.length) :
    ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) *
      val (K S) (survInd k S) N []
      ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * ∏ i ∈ range N, Lr i := by
  refine le_trans (audit_leak_bound k B hB K cl hK0 hK1 hcons hdom hcl0) ?_
  have hm := mass_le_prod (dropStop caughtFlag cl) Lr
    (fun g o => by unfold dropStop; split_ifs; exact le_rfl; exact hcl0 g o) hLr0 hL N []
  simp only [List.length_nil, zero_add] at hm
  exact mul_le_mul_of_nonneg_left hm (by positivity)

/-- the round kernel of an attacker with a randomised, fully adaptive strategy σ (it sees its own past actions and
every catch flag) and no leak about the schedule: flags are produced by the schedule -/
noncomputable def hiddenK (σ : List (AOut Unit) → Bool → ℝ) :
    Finset (Fin N) → List (Unit × AOut Unit) → Unit × AOut Unit → ℝ :=
  fun S h yo => σ (h.map Prod.snd) yo.2.1 *
    (if yo.2.2.2 = (yo.2.1 && decide (memN S (h.map Prod.snd).length)) then 1 else 0)

/-- **Adaptive attackers gain nothing against a hidden random schedule.** Every adaptive k-step attacker that sees
only its own actions and whether it has been caught survives a uniformly random size-B schedule with probability
≤ C(N−k,B)/C(N,B) ≤ ((N−B)/N)^k (`AuditBudget.survival_le_pow`). This formalises the reduction that
`AuditBudget` stated as a modelling remark. -/
theorem audit_adaptive_hidden (k B : ℕ) (hB : B ≤ N) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) :
    ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) *
      val (hiddenK σ S) (survInd k S) N []
      ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) := by
  have h := audit_leak_prod k B hB (hiddenK σ) (fun g o => σ g o.1) (fun _ => 1)
    (fun S h z => mul_nonneg ((hσ _).1 _) (by split_ifs <;> norm_num))
    (fun S h => by
      simp only [hiddenK, Fintype.sum_prod_type, Fintype.univ_unit, Finset.sum_singleton, Fintype.sum_bool]
      have h1 := (hσ (h.map Prod.snd)).2
      rw [Fintype.sum_bool] at h1
      cases (decide (memN S (List.map Prod.snd h).length)) <;> simp <;> linarith)
    (fun S h y o hK => by
      by_contra hne; apply hK; simp only [hiddenK, hne, ↓reduceIte, mul_zero])
    (fun S h o _ => by
      simp only [hiddenK, Fintype.univ_unit, Finset.sum_singleton]
      have := (hσ (h.map Prod.snd)).1 o.1
      split_ifs <;> nlinarith)
    (fun g o => (hσ g).1 o.1) (fun _ => zero_le_one)
    (fun g => by
      simp only [dropStop, caughtFlag, Fintype.sum_prod_type, Fintype.univ_unit, Finset.sum_singleton,
        Fintype.sum_bool]
      have h1 := (hσ g).2
      rw [Fintype.sum_bool] at h1
      simp; linarith)
  simpa using h

end Audit

end ControlStack.Leakage

#print axioms ControlStack.Leakage.transfer
#print axioms ControlStack.Leakage.covert_from_transfer
#print axioms ControlStack.Leakage.seq_transfer
#print axioms ControlStack.Leakage.seq_transfer_const
#print axioms ControlStack.Leakage.mass_le_prod
#print axioms ControlStack.Leakage.mass_const
#print axioms ControlStack.Leakage.covert_seq
#print axioms ControlStack.Leakage.episode_dom
#print axioms ControlStack.Leakage.sc01_adaptive_target
#print axioms ControlStack.Leakage.covert_side_bound
#print axioms ControlStack.Leakage.cval_live
#print axioms ControlStack.Leakage.blind_audit
#print axioms ControlStack.Leakage.audit_leak_bound
#print axioms ControlStack.Leakage.audit_leak_prod
#print axioms ControlStack.Leakage.audit_adaptive_hidden
```

### ControlStack/Necessity.lean
```lean
/-
Missing necessity witnesses (circle consultation 2026-10-08, reviews/circle-consult-2026-10-08/synthesis.md).

Each theorem shows that ONE specific premise cannot simply be dropped: without it, the bound that used it fails on an
explicit instance. A witness shows that dropping the premise outright breaks the bound. It does not show that the premise is
necessary in every weaker form (see NECESSITY.md for the exact scope of each witness).

- `seed_secret_breaks_covert`: `covert_bound` assumes the secret is independent of the shared seed. If the secret is
  a function of the seed, a decoder that sees NOTHING (|V| = 1) recovers it with certainty, versus the bound 1/|M|.
- `correlated_lifetimes_break_gate`: `false_pass_le` assumes independent lifetimes. With every lifetime completing with
  marginal probability 9/10 but all lifetimes perfectly correlated, the gate passes with probability 9/10, not ≤ 1/80.
- `marginal_certs_dont_compose`: per-channel certificates do not multiply. Two side outputs R and R xor m are each
  independent of the secret bit m (each has least certificate mass 1), yet together they reveal m with certainty
  (success 1 = 2 × the blind value 1/2). Composition needs the joint or sequential domination of `Leakage.seq_transfer`
  (the second output's certificate given the first has mass 2).
- `shared_score_product_unsound`: two control layers (e.g. a monitor flag and an audit trigger) driven by the same
  score each miss an attack with probability 1/10. Their joint miss probability is 1/10, not the product 1/100.
-/
import ControlStack.CovertChannel
import ControlStack.ScenarioAUsefulness

namespace ControlStack.Necessity

open Finset ControlStack.Covert

/-! ## Secret independence -/

/-- success with a JOINT law q on (seed, secret): Σ q(ω,m) Σ_v enc(v|ω,m) dec(m|ω,v) -/
noncomputable def jointSuccess {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V]
    (q : Ω → M → ℝ) (enc : Ω → M → V → ℝ) (dec : Ω → V → M → ℝ) : ℝ :=
  ∑ ω, ∑ m, q ω m * ∑ v, enc ω m v * dec ω v m

/-- **Seed-correlated secret.** The secret equals the shared seed (uniform on M); the view is a single constant
value. The decoder outputs its seed and succeeds with probability 1, while `covert_bound` would give |V|/|M| = 1/|M|. -/
theorem seed_secret_breaks_covert {M : Type} [Fintype M] [DecidableEq M] [Nonempty M] :
    jointSuccess (fun (ω m : M) => if ω = m then (Fintype.card M : ℝ)⁻¹ else 0)
      (fun (_ _ : M) (_ : Unit) => (1 : ℝ)) (fun (ω : M) (_ : Unit) (m : M) => if m = ω then (1 : ℝ) else 0) = 1 ∧
    (Fintype.card Unit : ℝ) / (Fintype.card M : ℝ) = (Fintype.card M : ℝ)⁻¹ := by
  have hM : (Fintype.card M : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨?_, by simp⟩
  unfold jointSuccess
  simp only [Fintype.univ_unit, Finset.sum_singleton, one_mul]
  have : ∀ ω : M, ∑ m, (if ω = m then (Fintype.card M : ℝ)⁻¹ else 0) * (if m = ω then 1 else 0)
      = (Fintype.card M : ℝ)⁻¹ := by
    intro ω
    rw [Finset.sum_eq_single ω]
    · simp
    · intro m _ hm; simp [Ne.symm hm]
    · simp
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-! ## Independent lifetimes -/

/-- the comonotone law on 64 lifetimes: all complete (prob p) or none complete (prob 1 − p) -/
noncomputable def comono (p : ℝ) (x : Fin 64 → Bool) : ℝ :=
  (if x = fun _ => true then p else 0) + (if x = fun _ => false then 1 - p else 0)

/-- number of completed lifetimes -/
def count (x : Fin 64 → Bool) : ℕ := (univ.filter fun i => x i = true).card

theorem comono_marginal (p : ℝ) (i : Fin 64) :
    ∑ x, comono p x * (if x i = true then 1 else 0) = p := by
  unfold comono
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-- **Correlated lifetimes break the gate's validity.** Every lifetime completes with marginal probability 9/10 (at the
floor), yet the gate (≥ 63 of 64 complete) passes with probability 9/10, not ≤ 1/80 as `false_pass_le` gives under
independence. -/
theorem correlated_lifetimes_break_gate :
    (∀ i : Fin 64, ∑ x, comono (9 / 10) x * (if x i = true then 1 else 0) = 9 / 10) ∧
    ∑ x, comono (9 / 10) x * (if 63 ≤ count x then 1 else 0) = 9 / 10 ∧
    ScenarioAUsefulness.passProb (9 / 10) ≤ 1 / 80 ∧
    (1 : ℝ) / 80 < 9 / 10 := by
  refine ⟨fun i => comono_marginal _ i, ?_, ScenarioAUsefulness.false_pass_le _ (by norm_num) le_rfl, by norm_num⟩
  unfold comono
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  have h1 : count (fun _ => true) = 64 := by simp [count]
  have h0 : count (fun _ => false) = 0 := by simp [count]
  simp [h1, h0]

/-! ## Per-channel certificates do not compose -/

/-- law of the two side outputs (o₁, o₂) = (r, r xor m) given the secret bit m, with r a fresh uniform bit -/
noncomputable def xorLaw (m : Bool) (o : Bool × Bool) : ℝ := if o.2 = xor o.1 m then 1 / 2 else 0

/-- **Marginal certificates do not compose.** Each output alone has the same law for both secrets (so its least
certificate has mass 1: it is useless alone), yet the decoder `o₁ xor o₂` recovers a uniform secret bit with
probability 1, twice the blind value 1/2. -/
theorem marginal_certs_dont_compose :
    (∀ m b, ∑ o : Bool × Bool, xorLaw m o * (if o.1 = b then 1 else 0) = 1 / 2) ∧
    (∀ m b, ∑ o : Bool × Bool, xorLaw m o * (if o.2 = b then 1 else 0) = 1 / 2) ∧
    (1 / 2 : ℝ) * ∑ m : Bool, ∑ o : Bool × Bool, xorLaw m o * (if xor o.1 o.2 = m then 1 else 0) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> (simp [xorLaw, Fintype.sum_prod_type]; try norm_num)

/-! ## Layers driven by one score -/

/-- an attack's score is high (prob 9/10) or low (prob 1/10); both layers fire exactly on a high score -/
noncomputable def scoreLaw (high : Bool) : ℝ := if high then 9 / 10 else 1 / 10

/-- **Shared-score layers do not multiply.** Each layer misses with probability 1/10, but both miss together with
probability 1/10, ten times the independent product 1/100. -/
theorem shared_score_product_unsound :
    (∑ s : Bool, scoreLaw s * (if s = false then 1 else 0)) = 1 / 10 ∧
    (∑ s : Bool, scoreLaw s * (if s = false ∧ s = false then 1 else 0)) = 1 / 10 ∧
    (1 / 10 : ℝ) * (1 / 10) < 1 / 10 := by
  refine ⟨?_, ?_, by norm_num⟩ <;> simp [scoreLaw]

end ControlStack.Necessity

#print axioms ControlStack.Necessity.seed_secret_breaks_covert
#print axioms ControlStack.Necessity.correlated_lifetimes_break_gate
#print axioms ControlStack.Necessity.marginal_certs_dont_compose
#print axioms ControlStack.Necessity.shared_score_product_unsound

/-! ## Audit budget consumed by false positives (first-come, score-triggered auditing) -/

namespace ControlStack.Necessity

/-- first-come auditing: round i is audited iff it is flagged and fewer than B earlier rounds were flagged -/
def audited {N : ℕ} (B : ℕ) (flags : Fin N → Bool) (i : Fin N) : Bool :=
  flags i && decide ((Finset.univ.filter (fun j : Fin N => j < i ∧ flags j = true)).card < B)

/-- **Exhaustion.** If at least B rounds before every attack round were flagged (e.g. honest false positives), no
attack round is audited, whatever the attack's own flags. -/
theorem exhausted_no_audit {N : ℕ} (B : ℕ) (flags : Fin N → Bool) (A : Finset (Fin N))
    (h : ∀ i ∈ A, B ≤ (Finset.univ.filter (fun j : Fin N => j < i ∧ flags j = true)).card) :
    ∀ i ∈ A, audited B flags i = false := by
  intro i hi
  simp [audited, Nat.not_lt.2 (h i hi)]

/-- flags on Fin 4 from the three honest flags; the attack (round 3) is always flagged (a perfect monitor) -/
def flagsOf (b : Bool × Bool × Bool) : Fin 4 → Bool := ![b.1, b.2.1, b.2.2, true]

theorem audited_last (b : Bool × Bool × Bool) :
    audited 1 (flagsOf b) 3 = (!b.1 && !b.2.1 && !b.2.2) := by
  rcases b with ⟨_ | _, _ | _, _ | _⟩ <;> decide

/-- **False positives break the hidden-schedule bound.** N = 4 rounds, budget B = 1, one attack step in the last
round, a monitor that flags every attack, and three honest rounds that each raise a false positive w.p. 1/2
(uniform over the 8 patterns). First-come auditing lets the attack survive with probability 7/8. A hidden uniformly
random schedule of the same size (`AuditBudget`, `Leakage.audit_adaptive_hidden`) gives 3/4. The premise "honest
rounds do not consume audits" cannot be dropped. -/
theorem fp_exhaustion_breaks_audit :
    (∑ b : Bool × Bool × Bool, (1 / 8 : ℚ) * (if audited 1 (flagsOf b) 3 = false then 1 else 0)) = 7 / 8 ∧
    (Nat.choose 3 1 : ℚ) / Nat.choose 4 1 = 3 / 4 := by
  refine ⟨?_, by norm_num [Nat.choose]⟩
  simp only [audited_last, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

end ControlStack.Necessity

#print axioms ControlStack.Necessity.exhausted_no_audit
#print axioms ControlStack.Necessity.fp_exhaustion_breaks_audit
```

### ControlStack/Gate.lean
```lean
/-
Shared reference-monitor interface (families F1/F3 of SCENARIO-CATALOG.md §3).

A gate is a transition system whose state exposes an append-only EFFECT LOG. A gate spec supplies an inductive
invariant that makes every logged effect acceptable (`ok`). From this:

- `Spec.trace_safe`: after any finite interleaving of operations from an invariant state, the invariant holds, the
  old effect log is a prefix of the new one, and every effect is acceptable;
- `NoAgentEffects.agent_trace_inert`: if operations the agent can issue never append effects, any agent-only trace
  leaves the effect log unchanged;
- `withHalt`: adds a trusted HALT to any gate. Halting is absorbing: after it, no operation changes the state, so no
  further effect occurs (`halt_absorbing`). The spec lifts unchanged (`withHalt_spec`). This is the generic
  "absorbing shutdown" obligation (scaffold assumption A11; SC-13, SC-25).

The interface adds no new mathematics: each generic theorem is an induction over the trace. Its job is reuse. Five
clients import it (`GateClients.lean`): the three existing gates (AuditDispatch, AuditGate, EgressGate) and two new
primitives (F4 content-addressed artefact gate, F7 exact-payload approval).

Scope: like every model here, a gate spec is about the transition system. That the deployed component implements it,
and that no effect bypasses it, are correspondence obligations recorded per client.
-/
import Mathlib.Tactic

namespace ControlStack.Gate

/-- a reference-monitor transition system with an effect log -/
structure System (St Op Eff : Type) where
  step : St → Op → St
  effects : St → List Eff

def System.run {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List Op) : St := ops.foldl G.step s

@[simp] theorem System.run_nil {St Op Eff : Type} (G : System St Op Eff) (s : St) : G.run s [] = s := rfl

@[simp] theorem System.run_cons {St Op Eff : Type} (G : System St Op Eff) (s : St) (o : Op) (ops : List Op) :
    G.run s (o :: ops) = G.run (G.step s o) ops := rfl

/-- a gate specification: an inductive invariant, an append-only effect log, and acceptability of logged effects -/
structure Spec {St Op Eff : Type} (G : System St Op Eff) where
  Inv : St → Prop
  ok : St → Eff → Prop
  step_inv : ∀ s o, Inv s → Inv (G.step s o)
  log_prefix : ∀ s o, G.effects s <+: G.effects (G.step s o)
  inv_ok : ∀ s, Inv s → ∀ e ∈ G.effects s, ok s e

/-- **Trace safety for any gate.** -/
theorem Spec.trace_safe {St Op Eff : Type} {G : System St Op Eff} (S : Spec G) (s : St) (ops : List Op)
    (h : S.Inv s) :
    S.Inv (G.run s ops) ∧ G.effects s <+: G.effects (G.run s ops) ∧
      ∀ e ∈ G.effects (G.run s ops), S.ok (G.run s ops) e := by
  induction ops generalizing s with
  | nil => exact ⟨h, List.prefix_refl _, S.inv_ok s h⟩
  | cons o ops ih =>
    obtain ⟨h1, h2, h3⟩ := ih (G.step s o) (S.step_inv s o h)
    exact ⟨h1, (S.log_prefix s o).trans h2, h3⟩

/-- operations the agent can issue never append effects -/
structure NoAgentEffects {St Op Eff : Type} (G : System St Op Eff) (agent : Op → Prop) : Prop where
  inert : ∀ s o, agent o → G.effects (G.step s o) = G.effects s

/-- an agent-only trace leaves the effect log unchanged -/
theorem NoAgentEffects.agent_trace_inert {St Op Eff : Type} {G : System St Op Eff} {agent : Op → Prop}
    (H : NoAgentEffects G agent) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, agent o) :
    G.effects (G.run s ops) = G.effects s := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    simp only [System.run_cons]
    rw [ih (G.step s o) (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')),
      H.inert s o (hops o List.mem_cons_self)]

/-! ## Absorbing halt for any gate -/

/-- operations of the halted system: an operation of the gate, or the trusted halt -/
inductive HOp (Op : Type) where
  | op (o : Op)
  | halt

/-- `withHalt G`: the gate with a halted flag; once halted, every operation is a no-op -/
def withHalt {St Op Eff : Type} (G : System St Op Eff) : System (St × Bool) (HOp Op) Eff where
  step := fun sh o =>
    if sh.2 then sh else
      match o with
      | .op o => (G.step sh.1 o, false)
      | .halt => (sh.1, true)
  effects := fun sh => G.effects sh.1

/-- **Halting is absorbing.** After a halt, no trace changes the state (in particular, no new effect). -/
theorem halt_absorbing {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List (HOp Op)) :
    (withHalt G).run (s, true) ops = (s, true) := by
  induction ops with
  | nil => rfl
  | cons o ops ih => simpa [System.run_cons, withHalt] using ih

/-- halting from any running state: the effect log is frozen at its value when the halt was processed -/
theorem halt_freezes {St Op Eff : Type} (G : System St Op Eff) (s : St) (ops : List (HOp Op)) :
    (withHalt G).effects ((withHalt G).run (s, false) (.halt :: ops)) = G.effects s := by
  rw [System.run_cons]
  have h1 : (withHalt G).step (s, false) .halt = (s, true) := by simp [withHalt]
  rw [h1, halt_absorbing]
  rfl

/-- the spec of any gate lifts to the halted gate unchanged -/
def withHalt_spec {St Op Eff : Type} {G : System St Op Eff} (S : Spec G) : Spec (withHalt G) where
  Inv := fun sh => S.Inv sh.1
  ok := fun sh e => S.ok sh.1 e
  step_inv := by
    intro sh o h
    rcases sh with ⟨s, b⟩
    cases b <;> cases o <;> simp [withHalt] <;> first | exact h | exact S.step_inv s _ h
  log_prefix := by
    intro sh o
    rcases sh with ⟨s, b⟩
    cases b <;> cases o <;> simp [withHalt]
    exact S.log_prefix s _
  inv_ok := fun sh h e he => S.inv_ok sh.1 h e he

end ControlStack.Gate

#print axioms ControlStack.Gate.Spec.trace_safe
#print axioms ControlStack.Gate.NoAgentEffects.agent_trace_inert
#print axioms ControlStack.Gate.halt_absorbing
#print axioms ControlStack.Gate.halt_freezes
#print axioms ControlStack.Gate.withHalt_spec
```

### ControlStack/GateClients.lean
```lean
/-
Clients of the shared gate interface (`Gate.lean`).

Existing gates, now instances (each reuses the gate's own step lemma; nothing is re-proved by copying):
- `dispatchSpec`: AuditDispatch, where every effect has an audit row and agent operations create no effects;
- `auditGateSpec`: AuditGate, where every recorded execution has its `workflow.execute` row;
- `egressSpec p`: EgressGate, where every socket attempt originates at the gateway and goes to a pinned peer. This is
  still under the policy-integrity premise that the model takes by definition (audit finding; see FIDELITY.md).

New primitives:
- **F4 content-addressed artefact gate** (`Artifact`): a deploy names a hash. It succeeds only if a trusted reviewer
  reviewed content with that hash, and it deploys the stored content with that hash. `deployed_reviewed`: every
  deployed artefact's hash was reviewed. `deployed_is_reviewed`: if the hash is injective on the contents involved,
  the deployed content IS reviewed content. `collision_breaks`: with a collision, unreviewed content is deployed, so
  collision resistance cannot be dropped. The agent may write arbitrary content to the store at any time; what it
  cannot do is change the content behind a reviewed hash. Not claimed: that reviewed content is harmless.
- **F7 exact-payload approval** (`Approval`): an irreversible transaction executes only if an approval for exactly that
  transaction exists, the clock has not passed its expiry, and its nonce is unused. `approval_safe`: every execution is
  approved and unexpired, and nonces never repeat (no replay). `replay_without_nonce`: dropping the nonce check lets
  one approval execute twice. Premise (not modelled): approvals come only from the distinct trusted principal, i.e.
  signatures are unforgeable and the key is not the agent's. The model gives the agent no operation that adds an
  approval, and that is exactly this premise.
-/
import ControlStack.Gate
import ControlStack.AuditDispatch
import ControlStack.AuditGate
import ControlStack.EgressGate

namespace ControlStack.GateClients

open ControlStack.Gate

/-! ## AuditDispatch -/

def dispatchSys : System AuditDispatch.St AuditDispatch.Op ℕ where
  step := AuditDispatch.step
  effects := fun s => s.effects

theorem dispatch_effects_prefix (s : AuditDispatch.St) (o : AuditDispatch.Op) :
    s.effects <+: (AuditDispatch.step s o).effects := by
  cases o <;> simp only [AuditDispatch.step] <;> (try split_ifs) <;> simp [List.prefix_append]

def dispatchSpec : Spec dispatchSys where
  Inv := AuditDispatch.Inv
  ok := fun s e => e ∈ s.audits
  step_inv := AuditDispatch.step_inv
  log_prefix := dispatch_effects_prefix
  inv_ok := fun _ h e he => h.1 e he

theorem dispatch_no_agent_effects :
    NoAgentEffects dispatchSys (fun o => ∀ id, o ≠ .dispatch id) :=
  ⟨fun s o h => AuditDispatch.app_cannot_effect s o h⟩

/-! ## AuditGate -/

def auditGateSys : System AuditGate.St AuditGate.Op ℕ where
  step := AuditGate.step
  effects := fun s => s.executions

theorem auditGate_prefix (s : AuditGate.St) (o : AuditGate.Op) :
    s.executions <+: (AuditGate.step s o).executions := by
  cases o <;> simp [AuditGate.step, List.prefix_append]

def auditGateSpec : Spec auditGateSys where
  Inv := AuditGate.Inv
  ok := fun s e => (⟨"workflow.execute", e⟩ : AuditGate.Audit) ∈ s.audits
  step_inv := AuditGate.step_inv
  log_prefix := auditGate_prefix
  inv_ok := fun _ h e he => h e he

/-! ## EgressGate -/

def egressSys (p : EgressGate.Policy) : System EgressGate.State EgressGate.Action EgressGate.Effect where
  step := EgressGate.step p
  effects := fun s => s.attempts

theorem egress_prefix (p : EgressGate.Policy) (s : EgressGate.State) (a : EgressGate.Action) :
    s.attempts <+: (EgressGate.step p s a).attempts := by
  cases a with
  | request key =>
    simp only [EgressGate.step]
    split
    · cases EgressGate.lookup p key <;> simp [List.prefix_append]
    · exact List.prefix_refl _
  | directAttempt peer =>
    simp only [EgressGate.step]; split <;> simp [List.prefix_append]
  | _ => simp [EgressGate.step]

def egressSpec (p : EgressGate.Policy) : Spec (egressSys p) where
  Inv := EgressGate.Invariant p
  ok := fun _ e => e.origin = .gateway ∧ e.peer ∈ p.map EgressGate.Rule.peer
  step_inv := fun s a h => EgressGate.step_safe p s a h
  log_prefix := egress_prefix p
  inv_ok := fun _ h e he => h.2 e he

/-- the egress gate with an absorbing trusted halt: the spec lifts and halting freezes all socket attempts -/
def egressHaltSpec (p : EgressGate.Policy) : Spec (withHalt (egressSys p)) := withHalt_spec (egressSpec p)

/-! ## F4: content-addressed artefact gate -/

namespace Artifact

variable {C H : Type} [DecidableEq H]

structure St (C H : Type) where
  reviewedContent : List C   -- ghost: what the trusted reviewer actually read
  reviewed : List H          -- hashes the reviewer signed
  store : List C             -- content-addressed store; the agent writes freely
  deployed : List C          -- effect log

inductive Op (C H : Type) where
  | put (c : C)              -- agent: add any content to the store
  | review (c : C)           -- trusted reviewer: reads c, signs its hash
  | deploy (h : H)           -- agent requests deployment of hash h; the gate decides

def step (hash : C → H) (s : St C H) : Op C H → St C H
  | .put c => { s with store := s.store ++ [c] }
  | .review c => { s with reviewedContent := s.reviewedContent ++ [c], reviewed := s.reviewed ++ [hash c] }
  | .deploy h =>
    if h ∈ s.reviewed then
      match s.store.find? (fun c => hash c = h) with
      | some c => { s with deployed := s.deployed ++ [c] }
      | none => s
    else s

def sys (hash : C → H) : System (St C H) (Op C H) C where
  step := step hash
  effects := fun s => s.deployed

def Inv (hash : C → H) (s : St C H) : Prop :=
  s.reviewed = s.reviewedContent.map hash ∧ ∀ c ∈ s.deployed, hash c ∈ s.reviewed

theorem step_inv (hash : C → H) (s : St C H) (o : Op C H) (h : Inv hash s) : Inv hash (step hash s o) := by
  obtain ⟨h1, h2⟩ := h
  cases o with
  | put c => exact ⟨h1, h2⟩
  | review c =>
    refine ⟨by simp [step, h1], fun d hd => ?_⟩
    simp only [step, List.mem_append] at hd ⊢
    exact Or.inl (h2 d hd)
  | deploy hh =>
    simp only [step]
    split_ifs with hr
    · cases hf : s.store.find? (fun c => hash c = hh) with
      | none => exact ⟨h1, h2⟩
      | some c =>
        have hc : hash c = hh := by simpa using List.find?_some hf
        refine ⟨h1, fun d hd => ?_⟩
        simp only [List.mem_append, List.mem_singleton] at hd
        rcases hd with hd | rfl
        · exact h2 d hd
        · rw [hc]; exact hr
    · exact ⟨h1, h2⟩

theorem prefix_step (hash : C → H) (s : St C H) (o : Op C H) : s.deployed <+: (step hash s o).deployed := by
  cases o with
  | put c => simp [step]
  | review c => simp [step]
  | deploy hh =>
    simp only [step]
    split_ifs
    · cases s.store.find? (fun c => hash c = hh) <;> simp [List.prefix_append]
    · exact List.prefix_refl _

def spec (hash : C → H) : Spec (sys hash) where
  Inv := Inv hash
  ok := fun s c => hash c ∈ s.reviewed
  step_inv := step_inv hash
  log_prefix := prefix_step hash
  inv_ok := fun _ h c hc => h.2 c hc

/-- **Every deployed artefact's hash was reviewed**, after any interleaving of agent and reviewer operations. -/
theorem deployed_reviewed (hash : C → H) (ops : List (Op C H)) :
    ∀ c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).deployed,
      hash c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).reviewed :=
  ((spec hash).trace_safe _ ops ⟨rfl, by simp⟩).2.2

/-- with no hash collisions, **the deployed content is reviewed content** -/
theorem deployed_is_reviewed (hash : C → H) (hinj : Function.Injective hash) (ops : List (Op C H)) :
    ∀ c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).deployed,
      c ∈ ((sys hash).run ⟨[], [], [], []⟩ ops).reviewedContent := by
  intro c hc
  have hinv := ((spec hash).trace_safe ⟨[], [], [], []⟩ ops ⟨rfl, by simp⟩).1
  have h := hinv.2 c hc
  rw [hinv.1] at h
  obtain ⟨c', hc', heq⟩ := List.mem_map.1 h
  rwa [← hinj heq]

/-- **Collision resistance cannot be dropped**: with hash ≡ (), the reviewer reads `true`, the agent stores `false`
first, and deploying the reviewed hash ships the unreviewed `false`. -/
theorem collision_breaks :
    let s := (sys (fun _ : Bool => ())).run ⟨[], [], [], []⟩ [.put false, .review true, .deploy ()]
    false ∈ s.deployed ∧ false ∉ s.reviewedContent := by
  decide

end Artifact

/-! ## F7: exact-payload approval with expiry and replay protection -/

namespace Approval

variable {P : Type} [DecidableEq P]

structure Tx (P : Type) where
  payload : P
  nonce : ℕ
  expiry : ℕ
  deriving DecidableEq

structure St (P : Type) where
  now : ℕ
  approvals : List (Tx P)        -- issued only by the distinct trusted principal
  used : List ℕ
  executed : List (Tx P × ℕ)     -- effect log: transaction and execution time

inductive Op (P : Type) where
  | tick                         -- trusted clock
  | approve (t : Tx P)           -- trusted approver (distinct principal)
  | execute (t : Tx P)           -- agent requests an irreversible transaction; the gate decides

def step (s : St P) : Op P → St P
  | .tick => { s with now := s.now + 1 }
  | .approve t => { s with approvals := s.approvals ++ [t] }
  | .execute t =>
    if t ∈ s.approvals ∧ s.now ≤ t.expiry ∧ t.nonce ∉ s.used then
      { s with used := s.used ++ [t.nonce], executed := s.executed ++ [(t, s.now)] }
    else s

def sys : System (St P) (Op P) (Tx P × ℕ) where
  step := step
  effects := fun s => s.executed

def Inv (s : St P) : Prop :=
  s.used = s.executed.map (fun e => e.1.nonce) ∧ s.used.Nodup ∧
    ∀ e ∈ s.executed, e.1 ∈ s.approvals ∧ e.2 ≤ e.1.expiry

theorem step_inv (s : St P) (o : Op P) (h : Inv s) : Inv (step s o) := by
  obtain ⟨h1, h2, h3⟩ := h
  cases o with
  | tick => exact ⟨h1, h2, h3⟩
  | approve t =>
    refine ⟨h1, h2, fun e he => ?_⟩
    obtain ⟨ha, hx⟩ := h3 e he
    exact ⟨List.mem_append_left _ ha, hx⟩
  | execute t =>
    simp only [step]
    split_ifs with hc
    · refine ⟨by simp [h1], List.nodup_append.2 ⟨h2, List.nodup_singleton _, ?_⟩, fun e he => ?_⟩
      · intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; intro hab; subst hab; exact hc.2.2 ha
      · simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact h3 e he
        · exact ⟨hc.1, hc.2.1⟩
    · exact ⟨h1, h2, h3⟩

theorem prefix_step (s : St P) (o : Op P) : s.executed <+: (step s o).executed := by
  cases o with
  | tick => simp [step]
  | approve t => simp [step]
  | execute t => simp only [step]; split_ifs <;> simp [List.prefix_append]

def spec : Spec (sys (P := P)) where
  Inv := Inv
  ok := fun s e => e.1 ∈ s.approvals ∧ e.2 ≤ e.1.expiry
  step_inv := step_inv
  log_prefix := prefix_step
  inv_ok := fun _ h e he => h.2.2 e he

/-- **Approval safety.** From the initial state, after any trace: every executed transaction carries an approval for
exactly that payload, nonce and expiry, was executed no later than its expiry, and no nonce executes twice. -/
theorem approval_safe (ops : List (Op P)) :
    let s := (sys (P := P)).run ⟨0, [], [], []⟩ ops
    (∀ e ∈ s.executed, e.1 ∈ s.approvals ∧ e.2 ≤ e.1.expiry) ∧ (s.executed.map (fun e => e.1.nonce)).Nodup := by
  have h := ((spec (P := P)).trace_safe ⟨0, [], [], []⟩ ops ⟨rfl, List.nodup_nil, by simp⟩).1
  exact ⟨h.2.2, h.1 ▸ h.2.1⟩

/-- the same gate without the nonce check -/
def stepNoNonce (s : St P) : Op P → St P
  | .execute t =>
    if t ∈ s.approvals ∧ s.now ≤ t.expiry then
      { s with used := s.used ++ [t.nonce], executed := s.executed ++ [(t, s.now)] }
    else s
  | o => step s o

/-- **Replay protection cannot be dropped**: without the nonce check one approval executes twice. -/
theorem replay_without_nonce :
    let t : Tx Unit := ⟨(), 0, 5⟩
    ([Op.approve t, .execute t, .execute t].foldl stepNoNonce (⟨0, [], [], []⟩ : St Unit)).executed.length = 2 ∧
    ([Op.approve t, .execute t, .execute t].foldl step (⟨0, [], [], []⟩ : St Unit)).executed.length = 1 := by
  decide

end Approval

end ControlStack.GateClients

#print axioms ControlStack.GateClients.dispatchSpec
#print axioms ControlStack.GateClients.dispatch_no_agent_effects
#print axioms ControlStack.GateClients.auditGateSpec
#print axioms ControlStack.GateClients.egressSpec
#print axioms ControlStack.GateClients.egressHaltSpec
#print axioms ControlStack.GateClients.Artifact.deployed_reviewed
#print axioms ControlStack.GateClients.Artifact.deployed_is_reviewed
#print axioms ControlStack.GateClients.Artifact.collision_breaks
#print axioms ControlStack.GateClients.Approval.approval_safe
#print axioms ControlStack.GateClients.Approval.replay_without_nonce
```

### ControlStack/Lease.lean
```lean
/-
F5 quotas, leases and revocation as a gate client (SC-14 runaway resources; SC-28 agents that individually satisfy
limits but jointly exceed them).

A trusted controller issues leases (id, budget, expiry) to workers and can revoke a lease. Workers (agents) may fork
helpers: a fork inherits its parent's LEASE, not a fresh budget. A unit of work names a worker and a cost. The gate
admits it only if:
- the worker holds a lease that is not revoked and not expired;
- the lease's total spend stays within its budget;
- the global spend stays within a cap.

Proved (`lease_safe`, from the initial state, for any interleaving):
1. every work effect ran under an issued lease, no later than that lease's expiry;
2. every lease's total spend is ≤ its budget, however many workers were forked onto it;
3. total spend over all workers is ≤ the global cap.

`revoke_absorbing`: after a lease is revoked, no later operation appends work under it. `fork_without_lease_accounting`
(necessity): if budgets are charged per WORKER, one fork doubles the work done under one lease.

Premises (not modelled): every resource use goes through the gate; the counters live in the trusted controller and
survive restarts (restart is a no-op on this state); worker identities cannot be forged. Costs are declared by the
gate, not the agent.
-/
import ControlStack.Gate

namespace ControlStack.Lease

open ControlStack.Gate

structure LeaseRec where
  id : ℕ
  budget : ℕ
  expiry : ℕ
  deriving DecidableEq

structure St where
  now : ℕ
  leases : List LeaseRec
  revoked : List ℕ
  holder : List (ℕ × ℕ)          -- (worker, lease id)
  work : List (ℕ × ℕ × ℕ)        -- effect log: (lease id, cost, time)

inductive Op where
  | tick                         -- trusted clock
  | issue (l : LeaseRec) (w : ℕ)    -- trusted controller
  | revoke (id : ℕ)              -- trusted controller
  | fork (w w' : ℕ)              -- agent: w' inherits w's lease
  | restart                      -- infrastructure: counters are durable
  | work (w cost : ℕ)            -- agent: request a unit of work

/-- total spend under lease id -/
def spent (work : List (ℕ × ℕ × ℕ)) (id : ℕ) : ℕ := ((work.filter (fun e => e.1 = id)).map (fun e => e.2.1)).sum

/-- total spend -/
def total (work : List (ℕ × ℕ × ℕ)) : ℕ := (work.map (fun e => e.2.1)).sum

def leaseOf (s : St) (w : ℕ) : Option ℕ := (s.holder.find? (fun p => p.1 = w)).map Prod.snd

def step (cap : ℕ) (s : St) : Op → St
  | .tick => { s with now := s.now + 1 }
  | .issue l w =>
    if l.id ∈ s.leases.map LeaseRec.id then s
    else { s with leases := s.leases ++ [l], holder := s.holder ++ [(w, l.id)] }
  | .revoke id => { s with revoked := s.revoked ++ [id] }
  | .fork w w' =>
    match leaseOf s w with
    | some id => { s with holder := s.holder ++ [(w', id)] }
    | none => s
  | .restart => s
  | .work w c =>
    match leaseOf s w with
    | none => s
    | some id =>
      match s.leases.find? (fun l => l.id = id) with
      | none => s
      | some l =>
        if id ∉ s.revoked ∧ s.now ≤ l.expiry ∧ spent s.work id + c ≤ l.budget ∧ total s.work + c ≤ cap then
          { s with work := s.work ++ [(id, c, s.now)] }
        else s

def sys (cap : ℕ) : System St Op (ℕ × ℕ × ℕ) where
  step := step cap
  effects := fun s => s.work

def Inv (cap : ℕ) (s : St) : Prop :=
  (s.leases.map LeaseRec.id).Nodup ∧
  (∀ e ∈ s.work, ∃ l ∈ s.leases, l.id = e.1 ∧ e.2.2 ≤ l.expiry) ∧
  (∀ l ∈ s.leases, spent s.work l.id ≤ l.budget) ∧
  total s.work ≤ cap

theorem spent_append (work : List (ℕ × ℕ × ℕ)) (e : ℕ × ℕ × ℕ) (id : ℕ) :
    spent (work ++ [e]) id = spent work id + (if e.1 = id then e.2.1 else 0) := by
  unfold spent; split_ifs with h <;> simp [List.filter_append, h]

theorem total_append (work : List (ℕ × ℕ × ℕ)) (e : ℕ × ℕ × ℕ) : total (work ++ [e]) = total work + e.2.1 := by
  simp [total]

theorem spent_eq_zero_of_absent (work : List (ℕ × ℕ × ℕ)) (id : ℕ) (h : ∀ e ∈ work, e.1 ≠ id) :
    spent work id = 0 := by
  unfold spent
  rw [List.filter_eq_nil_iff.2 (fun e he => by simpa using h e he)]
  rfl

theorem step_inv (cap : ℕ) (s : St) (o : Op) (h : Inv cap s) : Inv cap (step cap s o) := by
  obtain ⟨hn, hw, hb, ht⟩ := h
  cases o with
  | tick => exact ⟨hn, hw, hb, ht⟩
  | revoke id => exact ⟨hn, hw, hb, ht⟩
  | restart => exact ⟨hn, hw, hb, ht⟩
  | fork w w' =>
    simp only [step]; split
    · exact ⟨hn, hw, hb, ht⟩
    · exact ⟨hn, hw, hb, ht⟩
  | issue l w =>
    simp only [step]
    split_ifs with hfresh
    · exact ⟨hn, hw, hb, ht⟩
    · refine ⟨?_, ?_, ?_, ht⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨hn, List.nodup_singleton _, ?_⟩
        intro a ha b hb'; simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb'
        subst hb'; intro hab; subst hab; exact hfresh ha
      · intro e he
        obtain ⟨l', hl', h1, h2⟩ := hw e he
        exact ⟨l', List.mem_append_left _ hl', h1, h2⟩
      · intro l' hl'
        rcases List.mem_append.1 hl' with hl' | hl'
        · exact hb l' hl'
        · simp only [List.mem_singleton] at hl'; subst hl'
          rw [spent_eq_zero_of_absent]
          · exact Nat.zero_le _
          · intro e he heq
            obtain ⟨l'', hl'', h1, -⟩ := hw e he
            exact hfresh (List.mem_map.2 ⟨l'', hl'', h1.trans heq⟩)
  | work w c =>
    simp only [step]
    split
    · exact ⟨hn, hw, hb, ht⟩
    · rename_i id _
      split
      · exact ⟨hn, hw, hb, ht⟩
      · rename_i l0 hf
        have hl0 : l0 ∈ s.leases := List.mem_of_find?_eq_some hf
        have hid : l0.id = id := by simpa using List.find?_some hf
        split_ifs with hc
        · refine ⟨hn, ?_, ?_, ?_⟩
          · intro e he
            rcases List.mem_append.1 he with he | he
            · exact hw e he
            · simp only [List.mem_singleton] at he; subst he
              exact ⟨l0, hl0, hid, hc.2.1⟩
          · intro l hl
            rw [spent_append]
            split_ifs with hli
            · have : l = l0 := List.inj_on_of_nodup_map hn hl hl0 (by simp at hli; rw [hid]; exact hli.symm)
              subst this
              rw [hid]; exact hc.2.2.1
            · simpa using hb l hl
          · rw [total_append]; exact hc.2.2.2
        · exact ⟨hn, hw, hb, ht⟩

theorem prefix_step (cap : ℕ) (s : St) (o : Op) : s.work <+: (step cap s o).work := by
  cases o with
  | issue l w => simp only [step]; split_ifs <;> simp
  | fork w w' => simp only [step]; split <;> simp
  | work w c =>
    simp only [step]; split
    · exact List.prefix_refl _
    · split
      · exact List.prefix_refl _
      · split_ifs <;> simp [List.prefix_append]
  | _ => simp [step]

def spec (cap : ℕ) : Spec (sys cap) where
  Inv := Inv cap
  ok := fun s e => ∃ l ∈ s.leases, l.id = e.1 ∧ e.2.2 ≤ l.expiry
  step_inv := step_inv cap
  log_prefix := prefix_step cap
  inv_ok := fun _ h e he => h.2.1 e he

def init : St := ⟨0, [], [], [], []⟩

/-- **Lease safety.** After any interleaving of controller, clock, fork, restart and work operations: every work unit
ran under an issued lease before its expiry; each lease's spend, summed over all workers forked onto it, is within
its budget; and the global spend is within the cap. -/
theorem lease_safe (cap : ℕ) (ops : List Op) :
    let s := (sys cap).run init ops
    (∀ e ∈ s.work, ∃ l ∈ s.leases, l.id = e.1 ∧ e.2.2 ≤ l.expiry) ∧
    (∀ l ∈ s.leases, spent s.work l.id ≤ l.budget) ∧ total s.work ≤ cap := by
  have h := ((spec cap).trace_safe init ops ⟨List.nodup_nil, by simp [init], by simp [init],
    by simp [init, total]⟩).1
  exact h.2

/-- **Revocation is absorbing.** Once lease id is revoked, no operation appends work under it, and it stays revoked. -/
theorem revoke_step (cap : ℕ) (s : St) (o : Op) (id : ℕ) (hr : id ∈ s.revoked) :
    id ∈ (step cap s o).revoked ∧ ∃ δ, (step cap s o).work = s.work ++ δ ∧ ∀ e ∈ δ, e.1 ≠ id := by
  cases o with
  | tick => exact ⟨hr, [], by simp [step], by simp⟩
  | revoke id' => exact ⟨List.mem_append_left _ hr, [], by simp [step], by simp⟩
  | restart => exact ⟨hr, [], by simp [step], by simp⟩
  | issue l w =>
    refine ⟨?_, [], ?_, by simp⟩ <;> simp only [step] <;> split_ifs <;> simp [hr]
  | fork w w' =>
    refine ⟨?_, [], ?_, by simp⟩ <;> simp only [step] <;> split <;> simp [hr]
  | work w c =>
    simp only [step]
    split
    · exact ⟨hr, [], by simp, by simp⟩
    · rename_i id' _
      split
      · exact ⟨hr, [], by simp, by simp⟩
      · split_ifs with hc
        · refine ⟨hr, [(id', c, s.now)], rfl, ?_⟩
          intro e he; simp only [List.mem_singleton] at he; subst he
          intro h
          have h' : id' = id := h
          subst h'; exact hc.1 hr
        · exact ⟨hr, [], by simp, by simp⟩

theorem revoke_absorbing (cap : ℕ) (s : St) (ops : List Op) (id : ℕ) (hr : id ∈ s.revoked) :
    ∃ δ, ((sys cap).run s ops).work = s.work ++ δ ∧ ∀ e ∈ δ, e.1 ≠ id := by
  induction ops generalizing s with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons o ops ih =>
    obtain ⟨hr', δ1, h1, h1'⟩ := revoke_step cap s o id hr
    obtain ⟨δ2, h2, h2'⟩ := ih (step cap s o) hr'
    refine ⟨δ1 ++ δ2, ?_, ?_⟩
    · simp only [System.run_cons]; change ((sys cap).run (step cap s o) ops).work = _
      rw [h2, h1, List.append_assoc]
    · intro e he; rcases List.mem_append.1 he with he | he
      · exact h1' e he
      · exact h2' e he

/-! ## Necessity: per-worker accounting lets forks multiply a lease -/

/-- the same gate, but the budget check counts only the requesting WORKER's own spend -/
def stepPerWorker (cap : ℕ) (s : St) : Op → St
  | .work w c =>
    match leaseOf s w with
    | none => s
    | some id =>
      match s.leases.find? (fun l => l.id = id) with
      | none => s
      | some l =>
        -- witness only: the third field records the WORKER (not the time) so that spend can be counted per worker
        if id ∉ s.revoked ∧ s.now ≤ l.expiry ∧ spent (s.work.filter (fun e => e.2.2 = w)) id + c ≤ l.budget ∧
            total s.work + c ≤ cap then
          { s with work := s.work ++ [(id, c, w)] }
        else s
  | o => step cap s o

/-- **Forking multiplies per-worker budgets.** Lease 0 has budget 5. Worker 1 forks worker 2, and each spends 5. Under
per-worker accounting both are admitted (lease total 10 > 5); under per-lease accounting only the first is. -/
theorem fork_without_lease_accounting :
    let ops := [Op.issue ⟨0, 5, 100⟩ 1, .fork 1 2, .work 1 5, .work 2 5]
    spent (ops.foldl (stepPerWorker 100) init).work 0 = 10 ∧
    spent (ops.foldl (step 100) init).work 0 = 5 := by
  decide

end ControlStack.Lease

#print axioms ControlStack.Lease.lease_safe
#print axioms ControlStack.Lease.revoke_absorbing
#print axioms ControlStack.Lease.fork_without_lease_accounting
```
