/-
F6/F2: untrusted-monitor collusion and honeypot-phase learning (SC-24: "untrusted monitor colludes with generator or
learns honeypot phase").

An untrusted monitor U sees a view v of each input and decides PASS/FLAG. Honeypots (trusted synthetic attacks) and
real attacks induce view laws P_h and P_r. The honeypot test (`HoneypotBridge.lean`: honeypot PASS counts are
binomial with parameter h = honeypot pass rate) measures U's pass rate on P_h. The question is when that measurement
transfers to real attacks, whatever U's intent.

Results.
1. Indistinguishability (any monitor; the adversary class is irrelevant because the decision sees only v):
   - `pass_transfer`: |pass_real − pass_honeypot| ≤ TV(P_h, P_r) for every randomised decision rule β(v) ∈ [0, 1];
   - `pass_equal`: if P_h = P_r, the honeypot-measured recall IS the real recall, regardless of collusion intent.
   Leakage form (`collusion_ml`, one-shot `Leakage.transfer`): a colluding monitor's success at "pass real attacks,
   flag honeypots" is ≤ 2^{ML(phase → view)} · max prior, with 2^{ML} = Σ_v max(P_h v, P_r v).
   `collusion_uniform`: with a uniform phase prior this is exactly (1 + TV)/2, so the collusion advantage is ≤ TV/2.
2. Collusion signal, SHARED_SEED (the generator and monitor share a codebook). A trusted canonicalisation κ maps
   each view to one of K canonical classes, and the monitor sees only κ(v).
   - `canon_channel`: any shared-codebook covert message from generator to monitor (uniform over M) is decoded with
     probability ≤ K/|M|, i.e. ≤ log₂ K bits per item.
   - `stego_fools_honeypots`: without canonicalisation a 1-bit steganographic flag gives perfect collusion. The
     monitor passes every real attack and flags every honeypot (honeypots don't carry the flag), so honeypot
     measurement alone is fooled. TV = 1, and the bound of `pass_transfer` is tight.
   - `canon_restores`: after a canonicalisation that erases the flag (K = 1), honeypot and real pass rates coincide.
3. Adaptive phase learning, ADAPTIVE_FEEDBACK (`phase_learning`). The phase φ ∈ {test, deployment} is hidden for a
   whole stream of m items. Each item's visible output (views, the monitor's own actions, any feedback) may depend
   on the full hidden and visible history, but is dominated per round by a certificate of mass ≤ L = 2^λ (λ bits
   of maximal leakage per item). Then the monitor guesses the phase correctly with probability ≤ L^m / 2
   (`Leakage.seq_transfer_const`, `Leakage.mass_le_pow`).
   `phase_example`: binary-symmetric phase leak with crossover 99/200 (L = 101/100), m = 10 items gives
   P(correct) ≤ (101/100)^10/2 < 0.553, against 1/2 blind.

Limits (what is NOT claimed).
- The monitor's decision depends ONLY on the stated view. Side inputs (timestamps, ordering, metadata, a shared
  clock) must be inside v, or inside the certificate in result 3. Complete mediation of the view is a premise.
- TV and leakage are properties of the view laws, which must be estimated or bounded. Honeypots that are
  distinguishable from real attacks (TV large) make the honeypot test uninformative. That is the content of
  `stego_fools_honeypots`, not a defect of the bound.
- Canonicalisation bounds the channel by log K bits per item; it does not make K small. The semantic content an
  attack needs may itself carry many bits. Result 2 bounds only covert signalling through the canonical form.
- Per-item leakage λ in result 3 is a worst-case-over-history premise. Bounds grow as L^m and become vacuous
  (≥ 1) after about 1/λ items, so phases must be re-randomised, not reused.
- Classical: total variation, maximal leakage, covert-channel counting. No novelty is claimed.
-/
import ControlStack.Core.Leakage

namespace ControlStack.MonitorCollusion

open Finset ControlStack.Covert ControlStack.Leakage

/-! ## 1. Indistinguishability transfers honeypot calibration -/

section Transfer

variable {V : Type} [Fintype V]

/-- pass rate of a randomised decision rule β (β v = probability of PASS on view v) under view law P -/
noncomputable def passRate (P β : V → ℝ) : ℝ := ∑ v, P v * β v

/-- total variation distance -/
noncomputable def tv (P Q : V → ℝ) : ℝ := (1 / 2) * ∑ v, |P v - Q v|

/-- **Honeypot calibration transfers up to TV.** For every decision rule depending only on the view,
|pass_real − pass_honeypot| ≤ TV(P_h, P_r). Holds for any monitor, colluding or not. -/
theorem pass_transfer (Ph Pr β : V → ℝ) (hh : IsDist Ph) (hr : IsDist Pr) (hβ : ∀ v, 0 ≤ β v ∧ β v ≤ 1) :
    |passRate Pr β - passRate Ph β| ≤ tv Ph Pr := by
  have hzero : ∑ v, (Pr v - Ph v) * (1 / 2) = 0 := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hr.2, hh.2]; ring
  have e : passRate Pr β - passRate Ph β = ∑ v, (Pr v - Ph v) * (β v - 1 / 2) := by
    unfold passRate
    have : ∑ v, (Pr v - Ph v) * (β v - 1 / 2) = ∑ v, (Pr v - Ph v) * β v - ∑ v, (Pr v - Ph v) * (1 / 2) := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro v _; ring
    rw [this, hzero, sub_zero, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro v _; ring
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold tv
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro v _
  rw [abs_mul, abs_sub_comm (Pr v) (Ph v)]
  have hb : |β v - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith [(hβ v).1, (hβ v).2]
  nlinarith [abs_nonneg (Ph v - Pr v)]

/-- **Equal view laws: the honeypot-measured recall is the real recall**, whatever the monitor intends. -/
theorem pass_equal (Ph Pr β : V → ℝ) (heq : Ph = Pr) : passRate Pr β = passRate Ph β := by
  rw [heq]

/-- 2^{maximal leakage} of a binary phase: Σ_v max(P v, Q v) = 1 + TV(P, Q) -/
theorem sum_max_eq (P Q : V → ℝ) (hP : IsDist P) (hQ : IsDist Q) :
    ∑ v, max (P v) (Q v) = 1 + tv P Q := by
  have e : ∀ v, max (P v) (Q v) = (P v + Q v + |P v - Q v|) / 2 := by
    intro v
    rcases le_total (P v) (Q v) with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring
  simp_rw [e]
  unfold tv
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, hP.2, hQ.2]
  ring

/-- **Collusion through the view, maximal-leakage form.** Phase φ (true = real attack, false = honeypot) with prior
p, view v ~ lik φ, monitor action a ~ δ(v) (true = PASS). The colluder's payoff is 1 iff it passes a real attack or
flags a honeypot. Then success ≤ (Σ_v max_φ lik φ v) · max_φ p φ (one-shot `Leakage.transfer`). -/
theorem collusion_ml (p : Bool → ℝ) (lik : Bool → V → ℝ) (δ : V → Bool → ℝ)
    (hp : ∀ φ, 0 ≤ p φ) (hlik : ∀ φ v, 0 ≤ lik φ v) (hδ : ∀ v, IsDist (δ v)) :
    ∑ φ, p φ * ∑ v, lik φ v * ∑ a, δ v a * (if a = φ then 1 else 0)
      ≤ (∑ v, max (lik true v) (lik false v)) * max (p true) (p false) := by
  refine transfer p lik (fun v => max (lik true v) (lik false v)) δ (fun φ a => if a = φ then 1 else 0)
    (max (p true) (p false)) hp ?_ ?_ hδ (fun _ _ => by split_ifs <;> norm_num) ?_
  · intro φ v; cases φ
    · exact le_max_right _ _
    · exact le_max_left _ _
  · intro v; exact le_trans (hlik true v) (le_max_left _ _)
  · intro a; cases a <;> simp

/-- **Uniform phase prior:** collusion success ≤ (1 + TV(P_h, P_r))/2, so the advantage over guessing is ≤ TV/2. -/
theorem collusion_uniform (Ph Pr : V → ℝ) (hh : IsDist Ph) (hr : IsDist Pr) (δ : V → Bool → ℝ)
    (hδ : ∀ v, IsDist (δ v)) :
    ∑ φ, (1 / 2 : ℝ) * ∑ v, (if φ then Pr v else Ph v) * ∑ a, δ v a * (if a = φ then 1 else 0)
      ≤ (1 + tv Pr Ph) / 2 := by
  have h := collusion_ml (fun _ => (1 / 2 : ℝ)) (fun φ v => if φ then Pr v else Ph v) δ
    (fun _ => by norm_num) (fun φ v => by cases φ <;> simp [hh.1 v, hr.1 v]) hδ
  simp only [if_true, Bool.false_eq_true, if_false, max_self] at h
  rw [sum_max_eq Pr Ph hr hh] at h
  linarith

end Transfer

/-! ## 2. Collusion signals and canonicalisation -/

section Canon

variable {V : Type} [Fintype V]

/-- **Canonicalisation bounds the collusion channel to log₂ K bits per item.** Adversary class: SHARED_SEED (the
encoder `enc` and decoder `dec` are a fixed shared codebook). The generator embeds a uniform message m ∈ M in its
output v ~ enc m; a trusted transformation κ reduces v to one of K canonical classes; the monitor decodes from κ(v)
only. Then P(decode = m) ≤ K/|M|. -/
theorem canon_channel {M : Type} [Fintype M] [DecidableEq M] [Nonempty M] (K : ℕ) (κ : V → Fin K)
    (enc : M → V → ℝ) (henc : ∀ m, IsDist (enc m)) (dec : Fin K → M → ℝ) (hdec : ∀ k, IsDist (dec k)) :
    ∑ m, (Fintype.card M : ℝ)⁻¹ * ∑ v, enc m v * ∑ a, dec (κ v) a * (if a = m then 1 else 0)
      ≤ (K : ℝ) * (Fintype.card M : ℝ)⁻¹ := by
  -- push the encoder forward through κ
  set enc' : M → Fin K → ℝ := fun m k => ∑ v ∈ univ.filter (fun v => κ v = k), enc m v
  have hfib : ∀ (m : M) (F : Fin K → ℝ), ∑ v, enc m v * F (κ v) = ∑ k, enc' m k * F k := by
    intro m F
    rw [← Finset.sum_fiberwise univ κ (fun v => enc m v * F (κ v))]
    apply Finset.sum_congr rfl; intro k _
    simp only [enc', Finset.sum_mul]
    apply Finset.sum_congr rfl; intro v hv
    rw [(mem_filter.1 hv).2]
  have henc' : ∀ m, IsDist (enc' m) := by
    intro m
    refine ⟨fun k => Finset.sum_nonneg fun v _ => (henc m).1 v, ?_⟩
    have := hfib m (fun _ => 1)
    simp only [mul_one] at this
    rw [← this, (henc m).2]
  have h := covert_from_transfer enc' dec henc' hdec
  simp only [Fintype.card_fin] at h
  calc _ = ∑ m, (Fintype.card M : ℝ)⁻¹ * ∑ k, enc' m k * ∑ a, dec k a * (if a = m then 1 else 0) := by
        apply Finset.sum_congr rfl; intro m _
        rw [hfib m (fun k => ∑ a, dec k a * (if a = m then 1 else 0))]
    _ ≤ _ := h

end Canon

section Witness

/-- views: one steganographic bit. Real attacks (from the colluding generator) carry the flag; honeypots don't. -/
def stegoReal : Bool → ℝ := fun v => if v then 1 else 0
def stegoHoney : Bool → ℝ := fun v => if v then 0 else 1
/-- the colluding monitor: PASS iff the flag is present -/
def stegoMonitor : Bool → ℝ := fun v => if v then 1 else 0

/-- **A 1-bit stego flag fools honeypot measurement.** The colluding monitor passes EVERY real attack (real pass
rate 1, i.e. recall 0) while flagging EVERY honeypot (honeypot pass rate 0, i.e. measured recall 1). TV = 1, so
`pass_transfer` is tight here. -/
theorem stego_fools_honeypots :
    passRate stegoReal stegoMonitor = 1 ∧ passRate stegoHoney stegoMonitor = 0 ∧ tv stegoHoney stegoReal = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [passRate, tv, stegoReal, stegoHoney, stegoMonitor]

/-- **Canonicalisation that erases the flag restores honeypot calibration.** With κ : Bool → Fin 1 (K = 1), every
monitor reading only κ(v) has the same pass rate on honeypots and real attacks. -/
theorem canon_restores (β : Fin 1 → ℝ) :
    passRate stegoReal (fun v => β ((fun _ => 0 : Bool → Fin 1) v)) =
      passRate stegoHoney (fun v => β ((fun _ => 0 : Bool → Fin 1) v)) := by
  simp [passRate, stegoReal, stegoHoney]

end Witness

/-! ## 3. Adaptive phase learning over a stream -/

section Phase

variable {Y O : Type} [Fintype Y] [Fintype O]

/-- **Phase learning is bounded by accumulated leakage.** Adversary class: ADAPTIVE_FEEDBACK. A hidden phase
φ ∈ {test, deployment}, uniform, fixed for a stream of m items. The round kernel K φ (views, the monitor's own
actions, feedback; hidden per-round state allowed) depends on the full history. Each round is dominated by a
phase-independent certificate c of per-round mass ≤ L. Then any final phase guess is correct with probability
≤ L^m / 2. -/
theorem phase_learning (K : Bool → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (L : ℝ)
    (hK0 : ∀ φ h z, 0 ≤ K φ h z) (hdom : ∀ φ, Dominated (K φ) c) (hc0 : ∀ g o, 0 ≤ c g o) (hL0 : 0 ≤ L)
    (hL : ∀ g, ∑ o, c g o ≤ L) (guess : List O → Bool → ℝ) (hg : ∀ t, IsDist (guess t)) (m : ℕ) :
    ∑ φ, (1 / 2 : ℝ) * val (K φ) (fun t => guess t φ) m [] ≤ (1 / 2) * L ^ m := by
  have h := seq_transfer_const (fun _ : Bool => (1 / 2 : ℝ)) K c (fun φ t => guess t φ) (1 / 2) m
    (fun _ => by norm_num) hK0 hdom hc0 (fun φ t => (hg t).1 φ)
    (fun t => by rw [← Finset.mul_sum, (hg t).2]; norm_num)
  exact h.trans (mul_le_mul_of_nonneg_left (mass_le_pow c L hc0 hL0 hL m []) (by norm_num))

/-- binary-symmetric phase leak: each item's visible bit equals the phase with probability 101/200 -/
noncomputable def bscK : Bool → List (Unit × Bool) → Unit × Bool → ℝ :=
  fun φ _ z => if z.2 = φ then 101 / 200 else 99 / 200

theorem bscK_dist (φ : Bool) (h : List (Unit × Bool)) : IsDist (bscK φ h) := by
  refine ⟨fun z => by unfold bscK; split_ifs <;> norm_num, ?_⟩
  simp only [bscK, Fintype.sum_prod_type, Fintype.univ_unit, Finset.sum_singleton, Fintype.sum_bool]
  cases φ <;> norm_num

/-- **Non-vacuous instance.** Crossover 99/200 (per-item 2^λ = 101/100, λ ≈ 0.0144 bits), m = 10 items: every
adaptive monitor guesses the phase correctly with probability ≤ (101/100)^10/2 < 0.553 (blind: 1/2). -/
theorem phase_example (guess : List Bool → Bool → ℝ) (hg : ∀ t, IsDist (guess t)) :
    ∑ φ, (1 / 2 : ℝ) * val (bscK φ) (fun t => guess t φ) 10 [] < 0.553 := by
  have h := phase_learning bscK (fun _ _ => 101 / 200) (101 / 100)
    (fun φ h z => (bscK_dist φ h).1 z)
    (fun φ h o => by
      simp only [Fintype.univ_unit, Finset.sum_singleton, bscK]; split_ifs <;> norm_num)
    (fun _ _ => by norm_num) (by norm_num)
    (fun g => by simp; norm_num) guess hg 10
  refine lt_of_le_of_lt h ?_
  norm_num

end Phase

end ControlStack.MonitorCollusion

#print axioms ControlStack.MonitorCollusion.pass_transfer
#print axioms ControlStack.MonitorCollusion.pass_equal
#print axioms ControlStack.MonitorCollusion.sum_max_eq
#print axioms ControlStack.MonitorCollusion.collusion_ml
#print axioms ControlStack.MonitorCollusion.collusion_uniform
#print axioms ControlStack.MonitorCollusion.canon_channel
#print axioms ControlStack.MonitorCollusion.stego_fools_honeypots
#print axioms ControlStack.MonitorCollusion.canon_restores
#print axioms ControlStack.MonitorCollusion.phase_learning
#print axioms ControlStack.MonitorCollusion.phase_example
