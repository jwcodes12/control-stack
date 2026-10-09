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
  is dominated given the visible history (`episode_dom`, `sc01_adaptive_target`). Domination is worst-case over the
  hidden history, so a cache written once and read out over later episodes pays its full capacity in every round.
  At the SC-01 design point the condition allows only about 0.15 bits of maximal leakage over five episodes (for a
  binary symmetric side bit, crossover ≥ about 0.49). The bound is therefore informative only near "no side
  channel". `covert_seq_seed` lets the certificate depend on the shared seed.
- `audit_leak_bound`: an adaptive attacker against a uniformly random size-B audit set sees a leak about the schedule
  through kernels dominated on the support, AND learns when it is caught. It attacks in ≥ k rounds with no attacked
  round audited with probability ≤ mass(leak) · C(N−k,B)/C(N,B). The success event `survInd` requires EVERY attack
  to go unaudited. Catch feedback is free (`cval_live`): on every surviving path it reads "not caught".
  The endpoints are a hidden schedule (mass 1: the hypergeometric of `AuditBudget`, now for adaptive attackers) and full
  visibility (mass ≥ C(N,B): the bound is vacuous, consistent with `observable_schedule_nogo`).

Not claimed:
- tightness of the transfer bound in general. It is attained for noiseless views (`attain_embedding`) but can be loose
  for other leaks; see the worked example in `tools/ctrlcert.py`.
- that a leaky instance of `audit_leak_bound` has been exhibited in Lean. The only Lean instance is the no-leak
  `audit_adaptive_hidden` (adversarial review D5).
- anything about the physical system beyond the stated kernel model.

Adversarial review 2026-10-08: reviews/adversarial-2026-10-08/ (Gemini 3.1 Pro, Opus 5.5).
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

/-- **Seed-dependent certificates** (adversarial review D7): the decoder knows the shared seed, so the certificate may
depend on it; the bound is the seed-average of the masses. -/
theorem covert_seq_seed {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M]
    (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : Ω → List O → O → ℝ) (dec : Ω → List O → M → ℝ)
    (n : ℕ) (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) (c ω))
    (hc0 : ∀ ω g o, 0 ≤ c ω g o) (hdec : ∀ ω t, IsDist (dec ω t)) :
    ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n [])
      ≤ (∑ ω, ρ ω * mass (c ω) n []) / (Fintype.card M : ℝ) := by
  have hM : (0 : ℝ) ≤ (Fintype.card M : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg _)
  have per : ∀ ω, (Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n []
      ≤ (Fintype.card M : ℝ)⁻¹ * mass (c ω) n [] := by
    intro ω
    have h := seq_transfer_const (fun _ : M => (Fintype.card M : ℝ)⁻¹) (K ω) (c ω) (fun m t => dec ω t m)
      (Fintype.card M : ℝ)⁻¹ n (fun _ => hM) (hK0 ω) (hdom ω) (hc0 ω) (fun m t => (hdec ω t).1 m)
      (fun t => by rw [← Finset.mul_sum, (hdec ω t).2, mul_one])
    rwa [← Finset.mul_sum] at h
  calc _ ≤ ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * mass (c ω) n []) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (per ω) (hρ.1 ω)
    _ = (∑ ω, ρ ω * mass (c ω) n []) / (Fintype.card M : ℝ) := by
        rw [div_eq_inv_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro ω _; ring

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

/-- the attack succeeds: it attacks in at least k rounds and NO attacked round is audited. Attacking again after k
unaudited steps therefore risks the whole attack (adversarial review D6). For `audit_adaptive_hidden` this costs
nothing: an attacker can stop after k steps within the same strategy class. For leaky kernels, "the first k
attacks unaudited" would need a truncation lemma that is not proved here. -/
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
cl on the visible history, the attacker attacks in ≥ k rounds with no attacked round audited with probability
  ≤ mass(cl) · C(N−k,B)/C(N,B).
Catch-flag outputs cost nothing (`cval_live`). -/
theorem audit_leak_bound_all (k B : ℕ) (hB : B ≤ N)
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

/-- **Leakage-sensitive adaptive auditing** (support form). The kernel, its consistency and the leak certificate are
only required on schedules the protocol can actually draw (size-B subsets): a leak that is uninformative on the
support costs nothing extra (adversarial review D7). -/
theorem audit_leak_bound (k B : ℕ) (hB : B ≤ N)
    (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ)
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1)
    (hcons : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h y o, K S h (y, o) ≠ 0 →
      o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length)))
    (hdom : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o)
    (hcl0 : ∀ g o, 0 ≤ cl g o) :
    ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) *
      val (K S) (survInd k S) N []
      ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) * mass (dropStop caughtFlag cl) N [] := by
  classical
  -- off the support, replace the kernel by 0 (it has weight 0 anyway)
  set K' : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ :=
    fun S => if S ∈ AuditBudget.randomSchedules N B then K S else fun _ _ => 0 with hK'
  have hsame : ∀ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (K S) (survInd k S) N []
      = (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (K' S) (survInd k S) N [] := by
    intro S
    by_cases hS : S ∈ AuditBudget.randomSchedules N B
    · simp only [hK', if_pos hS]
    · simp only [if_neg hS, zero_mul]
  rw [Finset.sum_congr rfl (fun S _ => hsame S)]
  refine audit_leak_bound_all k B hB K' cl ?_ ?_ ?_ ?_ hcl0
  · intro S h z; by_cases hS : S ∈ AuditBudget.randomSchedules N B
    · simp only [hK', if_pos hS]; exact hK0 S hS h z
    · simp [hK', hS]
  · intro S h; by_cases hS : S ∈ AuditBudget.randomSchedules N B
    · simp only [hK', if_pos hS]; exact hK1 S hS h
    · simp [hK', hS]
  · intro S h y o hne; by_cases hS : S ∈ AuditBudget.randomSchedules N B
    · simp only [hK', if_pos hS] at hne; exact hcons S hS h y o hne
    · simp [hK', hS] at hne
  · intro S h o hf; by_cases hS : S ∈ AuditBudget.randomSchedules N B
    · simp only [hK', if_pos hS]; exact hdom S hS h o hf
    · simp only [hK', if_neg hS, Finset.sum_const_zero]; exact hcl0 _ _

/-- per-round leak masses multiply: if the non-catch certificate of round i has mass ≤ Lr i, survival is
≤ Π_i Lr i · C(N−k,B)/C(N,B). Rounds that leak nothing have Lr i = 1. -/
theorem audit_leak_prod (k B : ℕ) (hB : B ≤ N)
    (K : Finset (Fin N) → List (Y × AOut Z) → Y × AOut Z → ℝ) (cl : List (AOut Z) → AOut Z → ℝ) (Lr : ℕ → ℝ)
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z) (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1)
    (hcons : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h y o, K S h (y, o) ≠ 0 →
      o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length)))
    (hdom : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h o, o.2.2 = false → ∑ y, K S h (y, o) ≤ cl (h.map Prod.snd) o)
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
≤ C(N−k,B)/C(N,B), and ≤ ((N−B)/N)^k when 0 < N and k ≤ N (`AuditBudget.survival_le_pow`). This formalises the reduction that
`AuditBudget` stated as a modelling remark. -/
theorem audit_adaptive_hidden (k B : ℕ) (hB : B ≤ N) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) :
    ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) *
      val (hiddenK σ S) (survInd k S) N []
      ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) := by
  have h := audit_leak_prod k B hB (hiddenK σ) (fun g o => σ g o.1) (fun _ => 1)
    (fun S _ h z => mul_nonneg ((hσ _).1 _) (by split_ifs <;> norm_num))
    (fun S _ h => by
      simp only [hiddenK, Fintype.sum_prod_type, Fintype.univ_unit, Finset.sum_singleton, Fintype.sum_bool]
      have h1 := (hσ (h.map Prod.snd)).2
      rw [Fintype.sum_bool] at h1
      cases (decide (memN S (List.map Prod.snd h).length)) <;> simp <;> linarith)
    (fun S _ h y o hK => by
      by_contra hne; apply hK; simp only [hiddenK, hne, ↓reduceIte, mul_zero])
    (fun S _ h o _ => by
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
#print axioms ControlStack.Leakage.covert_seq_seed
#print axioms ControlStack.Leakage.episode_dom
#print axioms ControlStack.Leakage.sc01_adaptive_target
#print axioms ControlStack.Leakage.covert_side_bound
#print axioms ControlStack.Leakage.cval_live
#print axioms ControlStack.Leakage.blind_audit
#print axioms ControlStack.Leakage.audit_leak_bound
#print axioms ControlStack.Leakage.audit_leak_bound_all
#print axioms ControlStack.Leakage.audit_leak_prod
#print axioms ControlStack.Leakage.audit_adaptive_hidden
