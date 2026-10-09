/-
F2 channel instances: the leakage machinery (`Core/Leakage.lean`: `covert_seq`, `mass_le_prod`) applied to concrete
scenario shapes, including a datacenter (GPU) side channel. Every result is a bound on recovering a uniform secret
from an adaptive transcript. Adversary class SHARED_SEED + ADAPTIVE_FEEDBACK throughout: the sender and receiver
share a seed, the sender adapts to the full hidden and visible history, and hidden per-round state is allowed.

Results.
0. `covert_rounds`: per-round certificate masses Lr i give recovery ≤ Π_{i<n} Lr i / |M|.
   `covert_alphabet`: any sub-distribution kernel over a visible alphabet O gives ≤ |O|^n / |M|.
1. SC-02 accumulated cross-episode leakage (persistent receiver):
   - `sc02_accumulated`: E episodes with episode masses L_e give recovery of a k-bit secret ≤ Π L_e / 2^k;
   - `rekey_epoch`: re-keying every epoch. Secret m_j is fresh for epoch j and the decoder sees ALL rounds.
     Recovery of m_j is ≤ L^E / |M|, where E is the epoch length and L the per-round mass in the epoch. The
     required independence: every round OUTSIDE epoch j is dominated by a certificate of mass ≤ 1 that does not
     depend on m_j (e.g. a kernel that does not read m_j and has no hidden state correlated with it). Other secrets
     and shared randomness can be folded into the seed. If an earlier epoch's hidden state (a persistent cache)
     carries m_j-dependent content into later rounds, the premise fails and those rounds must be charged their own
     masses.
   - `sc02_example`: L = 21/20 per episode, E = 20, a 16-bit secret: per-epoch recovery ≤ 1/20000. Without
     re-keying, 200 episodes give a bound ≥ 1/4 (`sc02_no_rekey`).
2. `canonical_seq`: the sequential canonical channel. m items canonicalised to K classes give recovery ≤ K^m / |M|.
   This closes the gap noted in `MonitorCollusion` (one-shot `canon_channel` only).
3. SC-04 structured-log channel:
   - `log_channel`: a trusted canonicaliser maps each record to one of K templates with f numeric fields quantised
     to Q levels. Over m records, recovery ≤ K^m · Q^{fm} / |M|, i.e. ≤ log₂(K·Q^f) bits per record.
   - `log_example`: K = 8, f = 2, Q = 4 (7 bits/record), 4 records, 64-bit secret gives ≤ 2^-36.
   - `free_text_leaks`: an uncanonicalised free-text field large enough to hold the secret leaks an n-bit secret
     with probability 1 in ONE record.
4. GPU time-slicing contention channel (datacenter). Per scheduler quantum, the sender sets its occupancy
   s ∈ {busy, idle} (adaptively); the receiver observes its own completion time quantised to J levels with law W s ·.
   - `gpu_bound`: over m quanta, recovery ≤ (Σ_o max_s W s o)^m / |M|, i.e. per-quantum maximal leakage
     log₂ Σ_o max_s W s o;
   - `gpu_partition`: partitioning (MIG-style; the receiver's view does not depend on s) gives Σ = 1, the blind
     bound;
   - `gpu_jitter`: jitter making W busy and W idle (1+δ)-close in max-ratio gives Σ ≤ 1 + δ;
   - `gpu_example`: J = 4 with the matrix idle = (.4,.3,.2,.1), busy = (.1,.2,.3,.4): Σ = 1.4 (≈ 0.49 bits per
     quantum), and 10 quanta with a 16-bit secret give ≤ 1/2000. `gpu_jitter_example`: a jittered matrix
     (.26/.25/.25/.24 vs .24/.25/.25/.26) has exact Σ = 1.02. Its max-ratio closeness δ = 1/12 gives the looser
     `gpu_jitter` bound 1 + 1/12.

Limits (what is NOT claimed).
- These are models of the channel STRUCTURE, not measurements of any GPU, log pipeline or host. W, L_e, K, Q, f
  must be measured or enforced (STACK-MAP top-10 item 9). The bounds are only as good as the stated kernels and
  certificates.
- Domination is worst case over the hidden history. A persistent hidden state pays its capacity in every round
  it can influence.
- The GPU model has one sender bit per quantum and a stationary W. Multi-level occupancy, correlated jitter and
  other shared resources (memory bandwidth, L2, NVLink, power/thermal) are further channels with their own
  certificates.
- Re-keying needs the cross-epoch independence premise stated above. It is not automatic.
- Classical (maximal leakage, covert-channel counting); no novelty is claimed.
-/
import ControlStack.Core.Leakage

namespace ControlStack.ChannelInstances

open Finset ControlStack.Covert ControlStack.Leakage

section General

variable {Ω M Y O : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] [Fintype O]

/-- **Per-round masses multiply.** Adversary class: SHARED_SEED, ADAPTIVE_FEEDBACK. -/
theorem covert_rounds (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (Lr : ℕ → ℝ)
    (dec : Ω → List O → M → ℝ) (n : ℕ)
    (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c)
    (hc0 : ∀ g o, 0 ≤ c g o) (hLr0 : ∀ i, 0 ≤ Lr i) (hL : ∀ g, ∑ o, c g o ≤ Lr g.length)
    (hdec : ∀ ω t, IsDist (dec ω t)) :
    ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n [])
      ≤ (∏ i ∈ range n, Lr i) / (Fintype.card M : ℝ) := by
  have h1 := covert_seq ρ K c dec n hρ hK0 hdom hc0 hdec
  have hm := mass_le_prod c Lr hc0 hLr0 hL n []
  simp only [List.length_nil, zero_add] at hm
  have hM : (0 : ℝ) < (Fintype.card M : ℝ) := by exact_mod_cast Fintype.card_pos
  exact h1.trans (div_le_div_of_nonneg_right hm hM.le)

/-- **Finite visible alphabet.** Any sub-distribution kernel (hidden state allowed) whose visible output lies in O:
recovery ≤ |O|^n / |M|. Adversary class: SHARED_SEED, ADAPTIVE_FEEDBACK. -/
theorem covert_alphabet (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (dec : Ω → List O → M → ℝ) (n : ℕ)
    (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hK1 : ∀ ω m h, ∑ z, K ω m h z ≤ 1)
    (hdec : ∀ ω t, IsDist (dec ω t)) :
    ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n [])
      ≤ (Fintype.card O : ℝ) ^ n / (Fintype.card M : ℝ) := by
  have h := covert_rounds ρ K (fun _ _ => 1) (fun _ => (Fintype.card O : ℝ)) dec n hρ hK0
    (fun ω m h o => by
      calc ∑ y, K ω m h (y, o) ≤ ∑ z, K ω m h z := by
            rw [Fintype.sum_prod_type]
            exact Finset.sum_le_sum fun y _ => Finset.single_le_sum (f := fun o' => K ω m h (y, o'))
              (fun o' _ => hK0 ω m h _) (Finset.mem_univ o)
        _ ≤ 1 := hK1 ω m h)
    (fun _ _ => zero_le_one) (fun _ => Nat.cast_nonneg _) (fun g => by simp) hdec
  simpa [Finset.prod_const, card_range] using h

end General

/-! ## 1. SC-02: accumulated cross-episode leakage and re-keying -/

section SC02

variable {Ω Y O : Type} [Fintype Ω] [Fintype Y] [Fintype O]

/-- **SC-02 accumulated leakage.** A persistent receiver across E episodes; episode e's visible output is dominated
by a certificate of mass ≤ L e (state may persist across episodes; worst case over the hidden history). Recovery of
a uniform k-bit secret ≤ Π_e L e / 2^k. -/
theorem sc02_accumulated (k E : ℕ) (ρ : Ω → ℝ) (K : Ω → Fin (2 ^ k) → List (Y × O) → Y × O → ℝ)
    (c : List O → O → ℝ) (L : ℕ → ℝ) (dec : Ω → List O → Fin (2 ^ k) → ℝ)
    (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c)
    (hc0 : ∀ g o, 0 ≤ c g o) (hL0 : ∀ i, 0 ≤ L i) (hL : ∀ g, ∑ o, c g o ≤ L g.length)
    (hdec : ∀ ω t, IsDist (dec ω t)) :
    ∑ ω, ρ ω * (((2 : ℝ) ^ k)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) E [])
      ≤ (∏ e ∈ range E, L e) / 2 ^ k := by
  have h := covert_rounds ρ K c L dec E hρ hK0 hdom hc0 hL0 hL hdec
  simpa [Fintype.card_fin] using h

/-- product of an epoch-indicator mass: L inside the epoch window [a, a+E), 1 outside -/
theorem prod_epoch (n a E : ℕ) (L : ℝ) (h : a + E ≤ n) :
    ∏ i ∈ range n, (if a ≤ i ∧ i < a + E then L else 1) = L ^ E := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  have : (range n).filter (fun i => a ≤ i ∧ i < a + E) = Ico a (a + E) := by
    ext i; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Nat.card_Ico]; omega

/-- **Re-keying every epoch.** Adversary class: SHARED_SEED, ADAPTIVE_FEEDBACK. Secret m (for epoch j, occupying
rounds [a, a+E)) is uniform and fresh; other secrets and shared randomness are folded into the seed ω. The decoder
sees ALL n rounds. Premise (the precise independence): the certificate has mass ≤ L inside the epoch and ≤ 1 at
every round outside it. For instance, rounds outside the epoch do not read m and have no hidden state correlated
with m, so their visible law is a sub-distribution that does not depend on m. Then recovery of m ≤ L^E / |M|,
whatever happens in other epochs. -/
theorem rekey_epoch {M : Type} [Fintype M] [Nonempty M] (n a E : ℕ) (hE : a + E ≤ n) (L : ℝ) (hL0 : 0 ≤ L)
    (ρ : Ω → ℝ) (K : Ω → M → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (dec : Ω → List O → M → ℝ)
    (hρ : IsDist ρ) (hK0 : ∀ ω m h z, 0 ≤ K ω m h z) (hdom : ∀ ω m, Dominated (K ω m) c)
    (hc0 : ∀ g o, 0 ≤ c g o)
    (hin : ∀ g, a ≤ g.length ∧ g.length < a + E → ∑ o, c g o ≤ L)
    (hout : ∀ g, ¬(a ≤ g.length ∧ g.length < a + E) → ∑ o, c g o ≤ 1)
    (hdec : ∀ ω t, IsDist (dec ω t)) :
    ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, val (K ω m) (fun t => dec ω t m) n [])
      ≤ L ^ E / (Fintype.card M : ℝ) := by
  have h := covert_rounds ρ K c (fun i => if a ≤ i ∧ i < a + E then L else 1) dec n hρ hK0 hdom hc0
    (fun i => by split_ifs <;> linarith)
    (fun g => by
      by_cases hg : a ≤ g.length ∧ g.length < a + E
      · rw [if_pos hg]; exact hin g hg
      · rw [if_neg hg]; exact hout g hg)
    hdec
  rwa [prod_epoch n a E L hE] at h

/-- **SC-02 numbers.** Per-episode mass 21/20 (≈ 0.07 bits), epochs of 20 episodes, 16-bit secrets: per-epoch recovery
≤ (21/20)^20 / 2^16 ≤ 1/20000. -/
theorem sc02_example : ((21 : ℝ) / 20) ^ 20 / 2 ^ 16 ≤ 1 / 20000 := by norm_num

/-- without re-keying, the same leak over 200 episodes gives a bound ≥ 1/4: accumulated leakage is the threat -/
theorem sc02_no_rekey : (1 : ℝ) / 4 ≤ ((21 : ℝ) / 20) ^ 200 / 2 ^ 16 := by norm_num

end SC02

/-! ## 2. Sequential canonical channel -/

/-- **Sequential canonical channel** (closes the one-shot gap of `MonitorCollusion.canon_channel`). Each of m items
reaches the monitor only as one of K canonical classes; the generator and monitor share a codebook (seed). Any
adaptive generator/decoder pair recovers a uniform message with probability ≤ K^m / |M|. -/
theorem canonical_seq {Ω M Y : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] (Kc m : ℕ)
    (ρ : Ω → ℝ) (K : Ω → M → List (Y × Fin Kc) → Y × Fin Kc → ℝ) (dec : Ω → List (Fin Kc) → M → ℝ)
    (hρ : IsDist ρ) (hK0 : ∀ ω x h z, 0 ≤ K ω x h z) (hK1 : ∀ ω x h, ∑ z, K ω x h z ≤ 1)
    (hdec : ∀ ω t, IsDist (dec ω t)) :
    ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ x, val (K ω x) (fun t => dec ω t x) m [])
      ≤ (Kc : ℝ) ^ m / (Fintype.card M : ℝ) := by
  simpa [Fintype.card_fin] using covert_alphabet ρ K dec m hρ hK0 hK1 hdec

/-! ## 3. SC-04 structured-log channel -/

section SC04

/-- **Canonicalised structured logs.** Each record reaches the reader as (template ∈ Fin K, f fields each quantised
to Fin Q). Over m records, recovery ≤ K^m · Q^{fm} / |M|: at most log₂(K·Q^f) bits per record. -/
theorem log_channel {Ω M Y : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype Y] (Kt f Q m : ℕ)
    (ρ : Ω → ℝ) (K : Ω → M → List (Y × (Fin Kt × (Fin f → Fin Q))) → Y × (Fin Kt × (Fin f → Fin Q)) → ℝ)
    (dec : Ω → List (Fin Kt × (Fin f → Fin Q)) → M → ℝ)
    (hρ : IsDist ρ) (hK0 : ∀ ω x h z, 0 ≤ K ω x h z) (hK1 : ∀ ω x h, ∑ z, K ω x h z ≤ 1)
    (hdec : ∀ ω t, IsDist (dec ω t)) :
    ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ x, val (K ω x) (fun t => dec ω t x) m [])
      ≤ (Kt : ℝ) ^ m * (Q : ℝ) ^ (f * m) / (Fintype.card M : ℝ) := by
  have h := covert_alphabet ρ K dec m hρ hK0 hK1 hdec
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Nat.cast_mul, Nat.cast_pow] at h
  rwa [mul_pow, ← pow_mul] at h

/-- **SC-04 numbers.** 8 templates, 2 fields at 4 levels (7 bits/record), 4 records, a 64-bit secret: ≤ 2^-36. -/
theorem log_example : ((8 : ℝ) ^ 4 * (4 : ℝ) ^ (2 * 4)) / 2 ^ 64 = 1 / 2 ^ 36 := by norm_num

/-- **Free text leaks everything.** A free-text field large enough to carry the n-bit secret (the record IS the
secret) lets the decoder recover it with probability 1 from one record: canonicalisation is necessary. -/
theorem free_text_leaks (n : ℕ) :
    successProb (Ω := Unit) (fun _ => 1) (fun _ (m : Fin (2 ^ n)) (v : Fin (2 ^ n)) => if v = id m then 1 else 0)
      (fun _ v m => if m = id v then 1 else 0) = 1 :=
  attain_injective id id (fun _ => rfl)

end SC04

/-! ## 4. GPU time-slicing contention channel -/

section GPU

variable {J : ℕ}

/-- per-quantum certificate: the larger of the two observation likelihoods -/
noncomputable def wmax (W : Bool → Fin J → ℝ) (o : Fin J) : ℝ := max (W true o) (W false o)

/-- the per-quantum round kernel: the sender picks occupancy s from enc (adaptive to the full history), then the
receiver's quantised completion time o ~ W s -/
noncomputable def gpuK {Ω M : Type} (enc : Ω → M → List (Bool × Fin J) → Bool → ℝ) (W : Bool → Fin J → ℝ) :
    Ω → M → List (Bool × Fin J) → Bool × Fin J → ℝ :=
  fun ω m h z => enc ω m h z.1 * W z.1 z.2

/-- **GPU contention channel.** Adversary class: SHARED_SEED, ADAPTIVE_FEEDBACK. Over m quanta, any adaptive sender
and decoder recover a uniform message with probability ≤ (Σ_o max_s W s o)^m / |M|. -/
theorem gpu_bound {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] (m : ℕ)
    (ρ : Ω → ℝ) (enc : Ω → M → List (Bool × Fin J) → Bool → ℝ) (W : Bool → Fin J → ℝ)
    (dec : Ω → List (Fin J) → M → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω x h, IsDist (enc ω x h)) (hW : ∀ s o, 0 ≤ W s o)
    (hdec : ∀ ω t, IsDist (dec ω t)) :
    ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ x, val (gpuK enc W ω x) (fun t => dec ω t x) m [])
      ≤ (∑ o, wmax W o) ^ m / (Fintype.card M : ℝ) := by
  have h := covert_rounds ρ (gpuK enc W) (fun _ o => wmax W o) (fun _ => ∑ o, wmax W o) dec m hρ
    (fun ω x h z => mul_nonneg ((henc ω x h).1 _) (hW _ _))
    (fun ω x h o => by
      simp only [gpuK]
      calc ∑ s, enc ω x h s * W s o ≤ ∑ s, enc ω x h s * wmax W o := by
            apply Finset.sum_le_sum; intro s _
            apply mul_le_mul_of_nonneg_left _ ((henc ω x h).1 s)
            cases s
            · exact le_max_right _ _
            · exact le_max_left _ _
        _ = wmax W o := by rw [← Finset.sum_mul, (henc ω x h).2, one_mul])
    (fun _ o => le_trans (hW true o) (le_max_left _ _))
    (fun _ => Finset.sum_nonneg fun o _ => le_trans (hW true o) (le_max_left _ _))
    (fun _ => le_rfl) hdec
  simpa [Finset.prod_const, card_range] using h

/-- **Partitioning (MIG-style).** If the receiver's observation law does not depend on the sender's occupancy, the
per-quantum mass is 1: the bound is the blind 1/|M| for any number of quanta. -/
theorem gpu_partition (W : Bool → Fin J → ℝ) (hW : IsDist (W false)) (hsame : ∀ o, W true o = W false o) :
    ∑ o, wmax W o = 1 := by
  simp only [wmax, hsame, max_self]
  exact hW.2

/-- **Jitter.** If the scheduler's jitter makes the two observation laws (1+δ)-close in max-ratio
(W busy o ≤ (1+δ)·W idle o), the per-quantum mass is ≤ 1 + δ (maximal leakage ≤ log₂(1+δ) bits). -/
theorem gpu_jitter (W : Bool → Fin J → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hW : IsDist (W false))
    (hratio : ∀ o, W true o ≤ (1 + δ) * W false o) :
    ∑ o, wmax W o ≤ 1 + δ := by
  calc ∑ o, wmax W o ≤ ∑ o, (1 + δ) * W false o := by
        apply Finset.sum_le_sum; intro o _
        apply max_le (hratio o)
        nlinarith [hW.1 o]
    _ = 1 + δ := by rw [← Finset.mul_sum, hW.2, mul_one]

/-- the example matrix, J = 4: idle = (.4,.3,.2,.1), busy = (.1,.2,.3,.4) -/
noncomputable def gpuW : Bool → Fin 4 → ℝ :=
  fun s o => if s then ![1 / 10, 2 / 10, 3 / 10, 4 / 10] o else ![4 / 10, 3 / 10, 2 / 10, 1 / 10] o

theorem gpuW_mass : ∑ o, wmax gpuW o = 14 / 10 := by
  simp only [wmax, gpuW, Fin.sum_univ_four, if_true, Bool.false_eq_true, if_false]
  norm_num [Matrix.cons_val]

/-- **GPU numbers.** With `gpuW` (≈ 0.49 bits per quantum), 10 quanta and a 16-bit message: recovery ≤ 1/2000. -/
theorem gpu_example {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 16) → List (Bool × Fin 4) → Bool → ℝ)
    (dec : Ω → List (Fin 4) → Fin (2 ^ 16) → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω x h, IsDist (enc ω x h)) (hdec : ∀ ω t, IsDist (dec ω t)) :
    ∑ ω, ρ ω * ((Fintype.card (Fin (2 ^ 16)) : ℝ)⁻¹ * ∑ x, val (gpuK enc gpuW ω x) (fun t => dec ω t x) 10 [])
      ≤ 1 / 2000 := by
  have h := gpu_bound 10 ρ enc gpuW dec hρ henc
    (fun s o => by unfold gpuW; split_ifs <;> fin_cases o <;> norm_num [Matrix.cons_val]) hdec
  rw [gpuW_mass] at h
  refine h.trans ?_
  simp only [Fintype.card_fin]
  norm_num

/-- a jittered matrix, 2%-close: idle = (.26,.25,.25,.24), busy = (.24,.25,.25,.26) -/
noncomputable def gpuWj : Bool → Fin 4 → ℝ :=
  fun s o => if s then ![24 / 100, 25 / 100, 25 / 100, 26 / 100] o else ![26 / 100, 25 / 100, 25 / 100, 24 / 100] o

/-- **Jitter numbers.** The jittered matrix has per-quantum mass ≤ 1.0834 (it is (1+δ)-close with δ = 1/12,
since 26/24 = 1 + 1/12); its exact mass is 1.02. -/
theorem gpu_jitter_example : ∑ o, wmax gpuWj o = 102 / 100 ∧ ∑ o, wmax gpuWj o ≤ 1 + 1 / 12 := by
  have hm : ∑ o, wmax gpuWj o = 102 / 100 := by
    simp only [wmax, gpuWj, Fin.sum_univ_four, if_true, Bool.false_eq_true, if_false]
    norm_num [Matrix.cons_val]
  refine ⟨hm, ?_⟩
  apply gpu_jitter gpuWj (1 / 12) (by norm_num)
  · refine ⟨fun o => by unfold gpuWj; fin_cases o <;> norm_num [Matrix.cons_val], ?_⟩
    simp only [gpuWj, Fin.sum_univ_four, Bool.false_eq_true, if_false]; norm_num [Matrix.cons_val]
  · intro o; unfold gpuWj; fin_cases o <;> norm_num [Matrix.cons_val]

end GPU

end ControlStack.ChannelInstances

#print axioms ControlStack.ChannelInstances.covert_rounds
#print axioms ControlStack.ChannelInstances.covert_alphabet
#print axioms ControlStack.ChannelInstances.sc02_accumulated
#print axioms ControlStack.ChannelInstances.rekey_epoch
#print axioms ControlStack.ChannelInstances.sc02_example
#print axioms ControlStack.ChannelInstances.sc02_no_rekey
#print axioms ControlStack.ChannelInstances.canonical_seq
#print axioms ControlStack.ChannelInstances.log_channel
#print axioms ControlStack.ChannelInstances.log_example
#print axioms ControlStack.ChannelInstances.free_text_leaks
#print axioms ControlStack.ChannelInstances.gpu_bound
#print axioms ControlStack.ChannelInstances.gpu_partition
#print axioms ControlStack.ChannelInstances.gpu_jitter
#print axioms ControlStack.ChannelInstances.gpuW_mass
#print axioms ControlStack.ChannelInstances.gpu_example
#print axioms ControlStack.ChannelInstances.gpu_jitter_example
