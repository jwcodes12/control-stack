/-
F3 at datacenter scale: a timed model of distributed HALT with bounded delivery, in-flight effects, fencing epochs at
the effect sink, and a global budget (STACK-MAP.md item 10). Builds on the single-gate halt results in
`HaltLiveness.lean` (`DeliveredWithin`: halt liveness only under a bounded-delivery premise).

Model (discrete time, ticks t ∈ ℕ, horizon T).
- Nodes i < n (e.g. workers on GPU hosts). Node i initiates e i t effects at tick t, at most ρ per tick (`Rate`).
- The trusted controller issues HALT at tick t0. Node i receives it at t0 + δ i and initiates nothing afterwards
  (`HaltAbsorbs`, local and absorbing). Bounded delivery: δ i ≤ Δ for every node (`Delivered`).
- An effect initiated at tick t lands at the effect sink at t + lat i t, with lat ≤ L (`Latency`, in flight).
- Each effect carries the fencing epoch ep i t held by its node. HALT bumps the epoch to e0 + 1; nodes hold at
  most e0 (`HoldsOld`: only the controller mints epochs). The sink learns of the halt at t0 + ε.
- The effect sink (`sinkRun`) processes landing events in ANY order. It accepts an event iff
  (fencing off ∨ landing time < t0 + ε ∨ epoch ≥ e0 + 1) ∧ fewer than G events were accepted so far
  (global budget, SC-28 style).

Results. Adversary class TRACE_ARBITRARY throughout: arbitrary emission schedules within the rate, arbitrary
latencies ≤ L, arbitrary delivery delays within the stated premise, arbitrary arrival order at the sink.
1. Unfenced HALT window:
   - `initiated_after_le`: effects initiated at or after t0 are ≤ Σ_i ρ·δ_i ≤ n·ρ·Δ;
   - `landed_after_le`: effects landing at or after t0 are ≤ n·ρ·(L + Δ), i.e. the in-flight window adds L ticks.
2. Fencing at the sink:
   - `fenced_after_eps`: accepted effects landing at or after t0 + ε number EXACTLY 0, for any delivery delays,
     any rates, any latencies and any arrival order. No delivery premise is needed;
   - `fenced_window`: accepted effects landing at or after t0 are ≤ n·ρ·(L + ε). Fencing converts the
     n·ρ·(L + Δ) window into n·ρ·(L + ε), independent of node delivery.
   This is the standard fencing-token / lease-epoch argument, proved in this model.
3. Global budget: `sink_budget` (≤ G accepted, always). `unfenced_composed` and `fenced_composed` give
   ≤ min(G, …).
4. Witnesses:
   - `partition_unbounded`: a partitioned node (the delivery premise fails) lands unboundedly many effects
     after t0 at an unfenced sink;
   - `partition_fenced`: the same node is held to ≤ ρ·ε by a fencing sink;
   - `token_leak`: a node holding the NEW epoch (premise `HoldsOld` fails) gets an effect accepted after t0 + ε.
5. Numbers, n = 1000 nodes, ρ = 10 effects/tick, Δ = 5 ticks, L = 0:
   - `example_unfenced`: ≤ 50 000 effects after HALT;
   - `example_fenced`: ε = 1 gives ≤ 10 000, and 0 after t0 + 1.

Limits (what is NOT claimed).
- Discrete time; no clock-skew model beyond the delivery bound Δ and the sink's learning delay ε.
- Fencing needs the sink to check epochs on EVERY effect, and nodes must not obtain the new epoch. Both are premises
  (`fence = true` and `HoldsOld`), i.e. correspondence obligations on the real effect sink and token issuer.
  `token_leak` shows the second is necessary; `partition_unbounded` shows what happens without the first.
- Effects not routed through a fencing sink (a side channel or another sink) are outside the model.
- The per-tick rate ρ and latency bound L are premises (F5 metering and network bounds).
- Classical distributed-systems reasoning (fencing tokens are standard); no novelty is claimed.
-/
import Mathlib.Tactic

namespace ControlStack.DistributedHalt

open Finset

/-! ## Counting effects in a time window -/

/-- a rate-ρ stream whose nonzero entries satisfying P lie in [lo, hi) contributes ≤ ρ·(hi − lo) -/
theorem sum_window (T ρ lo hi : ℕ) (e : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P]
    (he : ∀ t, e t ≤ ρ) (hz : ∀ t, P t → e t ≠ 0 → lo ≤ t ∧ t < hi) :
    ∑ t ∈ range T, (if P t then e t else 0) ≤ ρ * (hi - lo) := by
  calc ∑ t ∈ range T, (if P t then e t else 0) ≤ ∑ t ∈ range T, (if lo ≤ t ∧ t < hi then ρ else 0) := by
        apply sum_le_sum; intro t _
        by_cases hP : P t
        · by_cases h0 : e t = 0
          · simp [hP, h0]
          · have hw := hz t hP h0
            rw [if_pos hP, if_pos hw]; exact he t
        · simp [hP]
    _ = ((range T).filter (fun t => lo ≤ t ∧ t < hi)).card * ρ := by
        rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul]
    _ ≤ (hi - lo) * ρ := by
        apply Nat.mul_le_mul_right
        calc _ ≤ (Ico lo hi).card := card_le_card (fun t ht => by simp at ht ⊢; omega)
          _ = hi - lo := Nat.card_Ico lo hi
    _ = ρ * (hi - lo) := mul_comm _ _

/-! ## Premises of the node model -/

/-- each node initiates at most ρ effects per tick -/
def Rate (ρ : ℕ) (e : ℕ → ℕ → ℕ) : Prop := ∀ i t, e i t ≤ ρ

/-- after receiving HALT (at t0 + δ i) node i initiates nothing: local, absorbing -/
def HaltAbsorbs (t0 : ℕ) (δ : ℕ → ℕ) (e : ℕ → ℕ → ℕ) : Prop := ∀ i t, t0 + δ i ≤ t → e i t = 0

/-- bounded delivery: every node receives HALT within Δ ticks (cf. `HaltLiveness.DeliveredWithin`) -/
def Delivered (n Δ : ℕ) (δ : ℕ → ℕ) : Prop := ∀ i, i < n → δ i ≤ Δ

/-- in-flight latency of each effect is at most L ticks -/
def Latency (L : ℕ) (lat : ℕ → ℕ → ℕ) : Prop := ∀ i t, lat i t ≤ L

/-- nodes hold at most the pre-halt epoch e0 (only the trusted controller mints the new epoch) -/
def HoldsOld (e0 : ℕ) (ep : ℕ → ℕ → ℕ) : Prop := ∀ i t, ep i t ≤ e0

/-! ## 1. The unfenced HALT window -/

/-- effects initiated at or after the HALT tick t0 -/
def initiatedAfter (n T t0 : ℕ) (e : ℕ → ℕ → ℕ) : ℕ :=
  ∑ i ∈ range n, ∑ t ∈ range T, (if t0 ≤ t then e i t else 0)

/-- effects landing at or after t0 -/
def landedAfter (n T t0 : ℕ) (e lat : ℕ → ℕ → ℕ) : ℕ :=
  ∑ i ∈ range n, ∑ t ∈ range T, (if t0 ≤ t + lat i t then e i t else 0)

/-- **Initiated after HALT ≤ Σ ρ·δ_i ≤ n·ρ·Δ.** Adversary class: TRACE_ARBITRARY. -/
theorem initiated_after_le (n T t0 ρ Δ : ℕ) (e : ℕ → ℕ → ℕ) (δ : ℕ → ℕ)
    (hr : Rate ρ e) (hh : HaltAbsorbs t0 δ e) (hd : Delivered n Δ δ) :
    initiatedAfter n T t0 e ≤ ∑ i ∈ range n, ρ * δ i ∧ initiatedAfter n T t0 e ≤ n * ρ * Δ := by
  have h1 : initiatedAfter n T t0 e ≤ ∑ i ∈ range n, ρ * δ i := by
    apply sum_le_sum; intro i _
    have := sum_window T ρ t0 (t0 + δ i) (e i) (fun t => t0 ≤ t) (hr i)
      (fun t ht h0 => ⟨ht, by by_contra hc; exact h0 (hh i t (by omega))⟩)
    simpa using this
  refine ⟨h1, h1.trans ?_⟩
  calc ∑ i ∈ range n, ρ * δ i ≤ ∑ _i ∈ range n, ρ * Δ := by
        apply sum_le_sum; intro i hi
        exact Nat.mul_le_mul_left _ (hd i (mem_range.1 hi))
    _ = n * ρ * Δ := by rw [sum_const, card_range, smul_eq_mul, mul_assoc]

/-- **Landing after HALT ≤ n·ρ·(L + Δ)** (in-flight effects add L ticks). Adversary class: TRACE_ARBITRARY. -/
theorem landed_after_le (n T t0 ρ Δ L : ℕ) (e lat : ℕ → ℕ → ℕ) (δ : ℕ → ℕ)
    (hr : Rate ρ e) (hh : HaltAbsorbs t0 δ e) (hd : Delivered n Δ δ) (hl : Latency L lat) :
    landedAfter n T t0 e lat ≤ n * ρ * (L + Δ) := by
  calc landedAfter n T t0 e lat ≤ ∑ _i ∈ range n, ρ * (L + Δ) := by
        apply sum_le_sum; intro i hi
        have hδ := hd i (mem_range.1 hi)
        have := sum_window T ρ (t0 - L) (t0 + δ i) (e i) (fun t => t0 ≤ t + lat i t) (hr i)
          (fun t ht h0 => ⟨by have := hl i t; omega, by by_contra hc; exact h0 (hh i t (by omega))⟩)
        refine this.trans (Nat.mul_le_mul_left _ (by omega))
    _ = n * ρ * (L + Δ) := by rw [sum_const, card_range, smul_eq_mul, mul_assoc]

/-! ## 2. The effect sink: fencing epochs and a global budget -/

/-- the sink's acceptance rule for a landing event (time, epoch) -/
def accepts (fence : Bool) (t0 ε e0 : ℕ) (ev : ℕ × ℕ) : Bool :=
  !fence || decide (ev.1 < t0 + ε) || decide (e0 + 1 ≤ ev.2)

def sinkStep (fence : Bool) (t0 ε e0 G : ℕ) (s : List (ℕ × ℕ)) (ev : ℕ × ℕ) : List (ℕ × ℕ) :=
  if accepts fence t0 ε e0 ev && decide (s.length < G) then s ++ [ev] else s

/-- the accepted effects, for landing events processed in the given (arbitrary) order -/
def sinkRun (fence : Bool) (t0 ε e0 G : ℕ) (evs : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  evs.foldl (sinkStep fence t0 ε e0 G) []

theorem foldl_sublist (fence : Bool) (t0 ε e0 G : ℕ) :
    ∀ (evs : List (ℕ × ℕ)) (s : List (ℕ × ℕ)), ∃ l, evs.foldl (sinkStep fence t0 ε e0 G) s = s ++ l ∧
      l.Sublist (evs.filter (accepts fence t0 ε e0)) := by
  intro evs
  induction evs with
  | nil => intro s; exact ⟨[], by simp, by simp⟩
  | cons ev rest ih =>
    intro s
    rw [List.foldl_cons]
    by_cases hacc : (accepts fence t0 ε e0 ev && decide (s.length < G)) = true
    · obtain ⟨l, hl, hsub⟩ := ih (s ++ [ev])
      have hstep : sinkStep fence t0 ε e0 G s ev = s ++ [ev] := by simp only [sinkStep, if_pos hacc]
      have ha : accepts fence t0 ε e0 ev = true := by simp only [Bool.and_eq_true] at hacc; exact hacc.1
      refine ⟨ev :: l, by rw [hstep, hl]; simp, ?_⟩
      rw [List.filter_cons_of_pos ha]
      exact hsub.cons₂ ev
    · obtain ⟨l, hl, hsub⟩ := ih s
      have hstep : sinkStep fence t0 ε e0 G s ev = s := by simp only [sinkStep, if_neg hacc]
      refine ⟨l, by rw [hstep, hl], ?_⟩
      by_cases ha : accepts fence t0 ε e0 ev = true
      · rw [List.filter_cons_of_pos ha]; exact hsub.cons ev
      · rw [List.filter_cons_of_neg ha]; exact hsub

theorem foldl_len (fence : Bool) (t0 ε e0 G : ℕ) :
    ∀ (evs : List (ℕ × ℕ)) (s : List (ℕ × ℕ)), s.length ≤ G →
      (evs.foldl (sinkStep fence t0 ε e0 G) s).length ≤ G := by
  intro evs
  induction evs with
  | nil => intro s hs; simpa using hs
  | cons ev rest ih =>
    intro s hs
    rw [List.foldl_cons]
    apply ih
    unfold sinkStep
    split_ifs with h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      simp; omega
    · exact hs

/-- every accepted effect was a landing event that passed the acceptance rule -/
theorem sink_sublist (fence : Bool) (t0 ε e0 G : ℕ) (evs : List (ℕ × ℕ)) :
    (sinkRun fence t0 ε e0 G evs).Sublist (evs.filter (accepts fence t0 ε e0)) := by
  obtain ⟨l, hl, hsub⟩ := foldl_sublist fence t0 ε e0 G evs []
  unfold sinkRun; rw [hl]; simpa using hsub

/-- **Global budget (SC-28 style):** at most G effects are ever accepted, in any arrival order. -/
theorem sink_budget (fence : Bool) (t0 ε e0 G : ℕ) (evs : List (ℕ × ℕ)) :
    (sinkRun fence t0 ε e0 G evs).length ≤ G :=
  foldl_len fence t0 ε e0 G evs [] (by simp)

theorem sink_count (fence : Bool) (t0 ε e0 G : ℕ) (evs : List (ℕ × ℕ)) (q : ℕ × ℕ → Bool) :
    (sinkRun fence t0 ε e0 G evs).countP q ≤ evs.countP (fun ev => q ev && accepts fence t0 ε e0 ev) := by
  rw [← List.countP_filter]
  exact (sink_sublist fence t0 ε e0 G evs).countP_le

/-- **Fencing: nothing lands after t0 + ε.** Adversary class: TRACE_ARBITRARY. If every landing event carries an
epoch ≤ e0, the fencing sink accepts NO effect landing at or after t0 + ε, for any delivery delays, rates,
latencies and arrival order. -/
theorem fenced_after_eps (t0 ε e0 G : ℕ) (evs : List (ℕ × ℕ)) (hold : ∀ ev ∈ evs, ev.2 ≤ e0) :
    (sinkRun true t0 ε e0 G evs).countP (fun ev => decide (t0 + ε ≤ ev.1)) = 0 := by
  rw [List.countP_eq_zero]
  intro ev hev
  have hmem := (sink_sublist true t0 ε e0 G evs).subset hev
  rw [List.mem_filter] at hmem
  have h2 := hold ev hmem.1
  have hacc := hmem.2
  simp only [accepts, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at hacc
  simp only [decide_eq_true_eq]
  omega

/-! ### The node stream -/

/-- all landing events (landing time, epoch) of n nodes over horizon T -/
def stream (n T : ℕ) (e lat ep : ℕ → ℕ → ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i => (List.range T).flatMap fun t => List.replicate (e i t) (t + lat i t, ep i t)

theorem listsum_range (f : ℕ → ℕ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem stream_countP (n T : ℕ) (e lat ep : ℕ → ℕ → ℕ) (q : ℕ × ℕ → Bool) :
    (stream n T e lat ep).countP q
      = ∑ i ∈ range n, ∑ t ∈ range T, (if q (t + lat i t, ep i t) = true then e i t else 0) := by
  unfold stream
  rw [List.countP_flatMap, ← listsum_range]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, List.countP_flatMap]
  rw [← listsum_range]
  congr 1
  apply List.map_congr_left
  intro t _
  simp [List.countP_replicate]

theorem stream_epochs (n T : ℕ) (e lat ep : ℕ → ℕ → ℕ) (e0 : ℕ) (hold : HoldsOld e0 ep) :
    ∀ ev ∈ stream n T e lat ep, ev.2 ≤ e0 := by
  intro ev hev
  simp only [stream, List.mem_flatMap, List.mem_replicate] at hev
  obtain ⟨i, -, t, -, -, rfl⟩ := hev
  exact hold i t

/-- **Fencing window.** Adversary class: TRACE_ARBITRARY. With fencing, accepted effects landing at or after t0 are
≤ n·ρ·(L + ε). NO delivery premise: nodes may never receive the HALT. -/
theorem fenced_window (n T t0 ε e0 G ρ L : ℕ) (e lat ep : ℕ → ℕ → ℕ)
    (hr : Rate ρ e) (hl : Latency L lat) (hold : HoldsOld e0 ep) :
    (sinkRun true t0 ε e0 G (stream n T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) ≤ n * ρ * (L + ε) := by
  refine (sink_count true t0 ε e0 G _ _).trans ?_
  rw [stream_countP]
  calc _ ≤ ∑ _i ∈ range n, ρ * (L + ε) := by
        apply sum_le_sum; intro i _
        have := sum_window T ρ (t0 - L) (t0 + ε) (e i)
          (fun t => (decide (t0 ≤ t + lat i t) && accepts true t0 ε e0 (t + lat i t, ep i t)) = true) (hr i)
          (by
            intro t ht _
            have h2 := hold i t
            have h3 := hl i t
            simp only [accepts, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
              decide_eq_true_eq] at ht
            omega)
        refine this.trans (Nat.mul_le_mul_left _ (by omega))
    _ = n * ρ * (L + ε) := by rw [sum_const, card_range, smul_eq_mul, mul_assoc]

/-! ## 3. Composition with the global budget -/

/-- **Unfenced, bounded delivery, global budget:** accepted effects landing after t0 ≤ min(G, n·ρ·(L + Δ)). -/
theorem unfenced_composed (n T t0 ε e0 G ρ Δ L : ℕ) (e lat ep : ℕ → ℕ → ℕ) (δ : ℕ → ℕ)
    (hr : Rate ρ e) (hh : HaltAbsorbs t0 δ e) (hd : Delivered n Δ δ) (hl : Latency L lat) :
    (sinkRun false t0 ε e0 G (stream n T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1))
      ≤ min G (n * ρ * (L + Δ)) := by
  apply le_min
  · exact List.countP_le_length.trans (sink_budget false t0 ε e0 G _)
  · refine (sink_count false t0 ε e0 G _ _).trans ?_
    rw [stream_countP]
    refine le_trans (le_of_eq ?_) (landed_after_le n T t0 ρ Δ L e lat δ hr hh hd hl)
    unfold landedAfter
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro t _
    simp [accepts]

/-- **Fenced, any delivery, global budget:** accepted effects landing after t0 ≤ min(G, n·ρ·(L + ε)), and none at or
after t0 + ε. -/
theorem fenced_composed (n T t0 ε e0 G ρ L : ℕ) (e lat ep : ℕ → ℕ → ℕ)
    (hr : Rate ρ e) (hl : Latency L lat) (hold : HoldsOld e0 ep) :
    (sinkRun true t0 ε e0 G (stream n T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) ≤ min G (n * ρ * (L + ε)) ∧
    (sinkRun true t0 ε e0 G (stream n T e lat ep)).countP (fun ev => decide (t0 + ε ≤ ev.1)) = 0 :=
  ⟨le_min (List.countP_le_length.trans (sink_budget true t0 ε e0 G _)) (fenced_window n T t0 ε e0 G ρ L e lat ep hr hl hold),
    fenced_after_eps t0 ε e0 G _ (stream_epochs n T e lat ep e0 hold)⟩

/-! ## 4. Witnesses -/

/-- a sink that accepts everything in budget returns its input -/
theorem foldl_all (fence : Bool) (t0 ε e0 G : ℕ) :
    ∀ (evs s : List (ℕ × ℕ)), (∀ ev ∈ evs, accepts fence t0 ε e0 ev = true) → s.length + evs.length ≤ G →
      evs.foldl (sinkStep fence t0 ε e0 G) s = s ++ evs := by
  intro evs
  induction evs with
  | nil => intro s _ _; simp
  | cons ev rest ih =>
    intro s hacc hlen
    rw [List.foldl_cons]
    have hstep : sinkStep fence t0 ε e0 G s ev = s ++ [ev] := by
      unfold sinkStep
      rw [if_pos]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hacc ev (by simp), by simp at hlen; omega⟩
    rw [hstep, ih (s ++ [ev]) (fun x hx => hacc x (by simp [hx])) (by simp at hlen ⊢; omega)]
    simp

/-- the partitioned node: one node, never halted, one effect per tick, no latency -/
def partitionE : ℕ → ℕ → ℕ := fun _ _ => 1

theorem partition_count (T t0 : ℕ) :
    ∑ i ∈ range 1, ∑ t ∈ range T, (if t0 ≤ t + 0 then partitionE i t else 0) = T - t0 := by
  simp only [sum_range_one, add_zero, partitionE]
  rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_one]
  have : (range T).filter (fun t => t0 ≤ t) = Ico t0 T := by ext t; simp; omega
  rw [this, Nat.card_Ico]

theorem stream_length (n T : ℕ) (e lat ep : ℕ → ℕ → ℕ) :
    (stream n T e lat ep).length = ∑ i ∈ range n, ∑ t ∈ range T, e i t := by
  have := stream_countP n T e lat ep (fun _ => true)
  simpa [List.countP_true] using this

/-- **Delivery is necessary without fencing.** A partitioned node (it never receives HALT; the delivery premise is
false) lands more than any bound M of effects after t0 at an unfenced sink with ample budget. -/
theorem partition_unbounded (t0 ε e0 M : ℕ) :
    ∃ T, M < (sinkRun false t0 ε e0 (T + 1) (stream 1 T partitionE (fun _ _ => 0) (fun _ _ => e0))).countP
      (fun ev => decide (t0 ≤ ev.1)) := by
  refine ⟨t0 + M + 1, ?_⟩
  set T := t0 + M + 1
  have hall : sinkRun false t0 ε e0 (T + 1) (stream 1 T partitionE (fun _ _ => 0) (fun _ _ => e0))
      = stream 1 T partitionE (fun _ _ => 0) (fun _ _ => e0) := by
    unfold sinkRun
    rw [foldl_all false t0 ε e0 (T + 1) _ [] (fun ev _ => by simp [accepts])]
    · simp
    · rw [stream_length]; simp [partitionE]
  rw [hall, stream_countP]
  have := partition_count T t0
  simp only [decide_eq_true_eq] at this ⊢
  omega

/-- **The same partitioned node at a fencing sink:** ≤ ρ·ε = ε effects after t0, for every horizon T. -/
theorem partition_fenced (t0 ε e0 G T : ℕ) :
    (sinkRun true t0 ε e0 G (stream 1 T partitionE (fun _ _ => 0) (fun _ _ => e0))).countP
      (fun ev => decide (t0 ≤ ev.1)) ≤ ε := by
  have := fenced_window 1 T t0 ε e0 G 1 0 partitionE (fun _ _ => 0) (fun _ _ => e0)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  simpa using this

/-- **Fencing needs the old-epoch premise.** A node holding the NEW epoch e0 + 1 gets an effect accepted at
t0 + ε. -/
theorem token_leak (t0 ε e0 : ℕ) :
    (sinkRun true t0 ε e0 1 [(t0 + ε, e0 + 1)]).countP (fun ev => decide (t0 + ε ≤ ev.1)) = 1 := by
  simp [sinkRun, sinkStep, accepts]

/-! ## 5. Numbers: n = 1000 nodes, ρ = 10 effects/tick, Δ = 5 ticks, L = 0 -/

/-- without fencing: ≤ 50 000 effects land after HALT -/
theorem example_unfenced (T t0 ε e0 G : ℕ) (e lat ep : ℕ → ℕ → ℕ) (δ : ℕ → ℕ)
    (hr : Rate 10 e) (hh : HaltAbsorbs t0 δ e) (hd : Delivered 1000 5 δ) (hl : Latency 0 lat) :
    (sinkRun false t0 ε e0 G (stream 1000 T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) ≤ 50000 :=
  (unfenced_composed 1000 T t0 ε e0 G 10 5 0 e lat ep δ hr hh hd hl).trans (min_le_right _ _)

/-- with fencing, ε = 1: ≤ 10 000 effects land after HALT, none after t0 + 1, whatever the delivery -/
theorem example_fenced (T t0 e0 G : ℕ) (e lat ep : ℕ → ℕ → ℕ)
    (hr : Rate 10 e) (hl : Latency 0 lat) (hold : HoldsOld e0 ep) :
    (sinkRun true t0 1 e0 G (stream 1000 T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) ≤ 10000 ∧
    (sinkRun true t0 1 e0 G (stream 1000 T e lat ep)).countP (fun ev => decide (t0 + 1 ≤ ev.1)) = 0 := by
  obtain ⟨h1, h2⟩ := fenced_composed 1000 T t0 1 e0 G 10 0 e lat ep hr hl hold
  exact ⟨h1.trans (min_le_right _ _), h2⟩

end ControlStack.DistributedHalt

#print axioms ControlStack.DistributedHalt.initiated_after_le
#print axioms ControlStack.DistributedHalt.landed_after_le
#print axioms ControlStack.DistributedHalt.sink_budget
#print axioms ControlStack.DistributedHalt.fenced_after_eps
#print axioms ControlStack.DistributedHalt.fenced_window
#print axioms ControlStack.DistributedHalt.unfenced_composed
#print axioms ControlStack.DistributedHalt.fenced_composed
#print axioms ControlStack.DistributedHalt.partition_unbounded
#print axioms ControlStack.DistributedHalt.partition_fenced
#print axioms ControlStack.DistributedHalt.token_leak
#print axioms ControlStack.DistributedHalt.example_unfenced
#print axioms ControlStack.DistributedHalt.example_fenced
