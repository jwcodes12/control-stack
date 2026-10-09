/-
F2 observation completeness by DESIGN: a trusted timed-release gate (ASSURANCE-LEDGER.md: `observation_complete`,
SC-01/02/04/05/07/24).

An agent (sender) produces messages whose content, size AND timing may all depend on a secret. A trusted release
gate sits between it and the receiver:
- it accepts a message only if its size is ≤ L (oversized messages are refused, a content-only rule);
- it buffers accepted messages in a FIFO queue;
- at every release slot (one per T ticks, public and fixed) it emits exactly one frame, padded to size L: the next
  queued message, or a dummy frame if the queue is empty;
- design `D L` adds stop-on-underflow: after the first dummy, it emits only dummies for the rest of the session.
The receiver observes (slot, frame) for every slot of the session. The tick of slot i is i·T, so the timed view is
the frame list. Time is counted in slots; `sched` lists the messages the sender submits during each slot.

Results (design `D L`: padded, stop-on-underflow, unbounded queue):
- `view_shape`: for EVERY sender schedule, the view is `render L (cs.take k) S`: the first k messages of the
  accepted content sequence `cs` as padded frames, then S − k dummies. So the view depends on the sender's timing
  only through ONE number k ≤ S. Timing leakage is ≤ log₂(S+1) bits per session, however the sender times its
  messages.
- `ready_view` and `timing_noninterference`: if the sender is READY (message j is submitted no later than slot j,
  for every j released in the session), then k = min(S, |cs|), and the view is a function of the content sequence
  alone. Two ready schedules with the same content give the same view: the timing channel has capacity 0.
- `timed_leakage` (counting form): with message contents canonicalised to K classes, any deterministic sender and
  decoder recover a secret m ∈ M for at most (S+1)·K^S values of m. Uniformly, P(recover) ≤ (S+1)·K^S/|M|: content
  ≤ S·log₂K bits plus timing ≤ log₂(S+1) bits. This matches `ChannelInstances.canonical_seq` (K^S) up to the (S+1)
  timing factor.
- Price:
  - `ready_latency`: a ready message j is released exactly at slot j (tick j·T), so its added latency is
    T × (number of messages ahead of it);
  - `throughput`: at most one frame per slot, each of size L, so ≤ L bytes per T ticks;
  - `view_length`: the view always has exactly S frames.
Witnesses (`decide`):
- `release_on_arrival_leaks_timing`: without batching, two schedules with the same content but different timing are
  distinguishable, while the timed gate gives identical views;
- `variable_size_leaks`: without padding, the frame size reveals the secret;
- `overflow_leaks_timing`: a bounded queue that drops the newest message when full makes the RELEASED CONTENT depend
  on timing.

What this does NOT address: observations that do NOT go through the gate. Cache and memory contention, power,
shared hardware and co-tenant side channels (the SC-01 refutation on a shared host) remain, and need their own
certificates (`ChannelInstances.gpu_bound`, `Leakage.covert_side_bound`). The gate's own processing time must not be
receiver-visible (the release clock is the only clock the receiver sees). Readiness is the sender's obligation for
zero timing leakage; without it, k leaks. Constant-rate release and padding are classical; no novelty is claimed.
-/
import Mathlib.Tactic
import Mathlib.Data.List.GetD

namespace ControlStack.TimedRelease

open Finset

structure Msg where
  content : ℕ
  size : ℕ
deriving DecidableEq, Repr

inductive Frame where
  | dummy
  /-- a released message: its content and the size the receiver sees -/
  | data (c sz : ℕ)
deriving DecidableEq, Repr

/-- gate configuration: frame size L, padding, stop-on-underflow, optional queue capacity (drop newest beyond it) -/
structure Cfg where
  L : ℕ
  pad : Bool
  stop : Bool
  cap : Option ℕ

/-- the design: padded, stop-on-underflow, unbounded queue -/
def D (L : ℕ) : Cfg := ⟨L, true, true, none⟩

structure GSt where
  q : List Msg
  out : List Frame
  stopped : Bool
deriving DecidableEq, Repr

def g0 : GSt := ⟨[], [], false⟩

def ok (C : Cfg) (m : Msg) : Bool := decide (m.size ≤ C.L)

def enqueue (C : Cfg) (q : List Msg) (arr : List Msg) : List Msg :=
  match C.cap with
  | none => q ++ arr.filter (ok C)
  | some c => (q ++ arr.filter (ok C)).take c

def frameOf (C : Cfg) (m : Msg) : Frame := .data m.content (if C.pad then C.L else m.size)

/-- one release slot: enqueue this slot's submissions, then emit exactly one frame -/
def slot (C : Cfg) (g : GSt) (arr : List Msg) : GSt :=
  if g.stopped then ⟨enqueue C g.q arr, g.out ++ [.dummy], true⟩
  else match enqueue C g.q arr with
    | [] => ⟨[], g.out ++ [.dummy], C.stop⟩
    | m :: rest => ⟨rest, g.out ++ [frameOf C m], false⟩

/-- the receiver's timed view of a session: one frame per slot -/
def view (C : Cfg) (sched : List (List Msg)) : List Frame := (sched.foldl (slot C) g0).out

/-- the accepted message sequence -/
def acc (C : Cfg) (sched : List (List Msg)) : List Msg := sched.flatten.filter (ok C)

/-- the canonical rendering: content frames, then dummies, S frames in total -/
def render (L : ℕ) (cs : List ℕ) (S : ℕ) : List Frame :=
  cs.map (fun c => Frame.data c L) ++ List.replicate (S - cs.length) .dummy

/-! ## The view's shape -/

/-- the invariant of design `D L` after the accepted messages `A` -/
def Inv (L : ℕ) (A : List Msg) (g : GSt) : Prop :=
  ∃ d e, d ≤ A.length ∧ g.q = A.drop d ∧ g.out = (A.take d).map (frameOf (D L)) ++ List.replicate e .dummy ∧
    (g.stopped = false → e = 0) ∧ (g.stopped = true → 0 < e)

theorem slot_inv (L : ℕ) (A : List Msg) (g : GSt) (a : List Msg) (h : Inv L A g) :
    Inv L (A ++ a.filter (ok (D L))) (slot (D L) g a) := by
  obtain ⟨d, e, hd, hq, ho, hs1, hs2⟩ := h
  have henq : enqueue (D L) g.q a = (A ++ a.filter (ok (D L))).drop d := by
    simp only [enqueue, D, hq]; rw [List.drop_append_of_le_length hd]
  have htake : (A ++ a.filter (ok (D L))).take d = A.take d := List.take_append_of_le_length hd
  unfold slot
  by_cases hst : g.stopped = true
  · rw [if_pos hst]
    refine ⟨d, e + 1, by simp; omega, henq, ?_, by simp, fun _ => by omega⟩
    simp only [ho, htake, List.replicate_succ', List.append_assoc]
  · rw [if_neg hst]
    have he : e = 0 := hs1 (by simpa using hst)
    subst he
    rw [henq]
    cases hc : (A ++ a.filter (ok (D L))).drop d with
    | nil =>
      refine ⟨d, 1, by simp; omega, hc.symm, ?_, by simp [D], fun _ => by omega⟩
      simp [ho, htake]
    | cons m rest =>
      have hlen : d < (A ++ a.filter (ok (D L))).length := by
        by_contra hc'; rw [List.drop_eq_nil_of_le (by omega)] at hc; cases hc
      have hm : (A ++ a.filter (ok (D L)))[d]? = some m := by
        rw [← List.head?_drop, hc]; rfl
      refine ⟨d + 1, 0, by omega, ?_, ?_, fun _ => rfl, by simp⟩
      · rw [← List.drop_drop, hc]; rfl
      · simp only [ho, List.replicate_zero, List.append_nil]
        rw [List.take_succ, hm, ← htake]; simp

theorem fold_inv (L : ℕ) (l : List (List Msg)) :
    ∀ (A : List Msg) (g : GSt), Inv L A g → Inv L (A ++ acc (D L) l) (l.foldl (slot (D L)) g) := by
  induction l with
  | nil => intro A g h; simpa [acc] using h
  | cons a l ih =>
    intro A g h
    have := ih _ _ (slot_inv L A g a h)
    simpa [acc, List.flatten_cons, List.filter_append, List.append_assoc] using this

theorem fold_length (C : Cfg) (l : List (List Msg)) (g : GSt) :
    (l.foldl (slot C) g).out.length = g.out.length + l.length := by
  induction l generalizing g with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    have : (slot C g a).out.length = g.out.length + 1 := by
      unfold slot; split_ifs
      · simp
      · split <;> simp
    rw [this]; simp; omega

/-- **The view always has exactly S frames** (one per slot). -/
theorem view_length (C : Cfg) (sched : List (List Msg)) : (view C sched).length = sched.length := by
  simpa [view, g0] using fold_length C sched g0

/-- **View shape.** For every sender schedule, the view is `render L (cs.take k) S` for some k ≤ min(S, |cs|):
the timing affects the view only through k. -/
theorem view_shape (L : ℕ) (sched : List (List Msg)) :
    ∃ k, k ≤ (acc (D L) sched).length ∧ k ≤ sched.length ∧
      view (D L) sched = render L (((acc (D L) sched).map Msg.content).take k) sched.length := by
  obtain ⟨d, e, hd, -, ho, -, -⟩ := fold_inv L sched [] g0 ⟨0, 0, by simp, by simp [g0], by simp [g0], by simp [g0],
    by simp [g0]⟩
  simp only [List.nil_append] at hd ho
  have hlen := view_length (D L) sched
  have hout : view (D L) sched = (((acc (D L) sched).take d).map (frameOf (D L))) ++ List.replicate e .dummy := ho
  rw [hout] at hlen
  simp only [List.length_append, List.length_map, List.length_take, List.length_replicate] at hlen
  refine ⟨d, hd, by omega, ?_⟩
  rw [hout]
  unfold render
  simp only [List.map_take, List.map_map, List.length_take, List.length_map]
  congr 2
  omega

/-! ## Readiness: zero timing leakage -/

/-- the sender is ready: for every message j released in the session (j < min(S, |cs|)), at least j + 1 messages
were accepted by the end of slot j -/
def Ready (L : ℕ) (sched : List (List Msg)) : Prop :=
  ∀ j, j < sched.length → j < (acc (D L) sched).length → j + 1 ≤ (acc (D L) (sched.take (j + 1))).length

theorem acc_take_prefix (C : Cfg) (sched : List (List Msg)) (i : ℕ) : acc C (sched.take i) <+: acc C sched := by
  unfold acc
  exact ((List.take_prefix i sched).flatten).filter _

theorem acc_take_succ (C : Cfg) (sched : List (List Msg)) (i : ℕ) (hi : i < sched.length) :
    acc C (sched.take (i + 1)) = acc C (sched.take i) ++ (sched[i]).filter (ok C) := by
  rw [List.take_succ, List.getElem?_eq_getElem hi]
  simp only [acc, Option.toList_some, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.filter_append]

/-- the gate's exact state after i slots of a ready schedule -/
theorem ready_state (L : ℕ) (sched : List (List Msg)) (hr : Ready L sched) :
    ∀ i, i ≤ sched.length →
      (sched.take i).foldl (slot (D L)) g0 =
        ⟨(acc (D L) (sched.take i)).drop (min i (acc (D L) sched).length),
         ((acc (D L) (sched.take i)).take (min i (acc (D L) sched).length)).map (frameOf (D L)) ++
           List.replicate (i - min i (acc (D L) sched).length) .dummy,
         decide ((acc (D L) sched).length < i)⟩ ∧
      min i (acc (D L) sched).length ≤ (acc (D L) (sched.take i)).length := by
  set m := (acc (D L) sched).length with hm
  intro i
  induction i with
  | zero => intro _; simp [g0, acc]
  | succ i ih =>
    intro hi
    obtain ⟨hst, hle⟩ := ih (by omega)
    have hfold : (sched.take (i + 1)).foldl (slot (D L)) g0 =
        slot (D L) ((sched.take i).foldl (slot (D L)) g0) sched[i] := by
      rw [List.take_succ, List.getElem?_eq_getElem (by omega), List.foldl_append]; rfl
    have hA := acc_take_succ (D L) sched i (by omega)
    have hA'le : (acc (D L) (sched.take (i + 1))).length ≤ m := (acc_take_prefix (D L) sched (i + 1)).length_le
    set A := acc (D L) (sched.take i)
    set A' := acc (D L) (sched.take (i + 1))
    have hmono : A.length ≤ A'.length := by rw [hA]; simp
    have henq (k : ℕ) (hk : k ≤ A.length) : enqueue (D L) (A.drop k) sched[i] = A'.drop k := by
      show A.drop k ++ sched[i].filter (ok (D L)) = A'.drop k
      rw [hA, List.drop_append_of_le_length hk]
    have htk (k : ℕ) (hk : k ≤ A.length) : A'.take k = A.take k := by
      rw [hA]; exact List.take_append_of_le_length hk
    rw [hfold, hst]
    unfold slot
    rcases Nat.lt_trichotomy i m with hlt | heq | hgt
    · -- i < m: the queue holds message i (readiness), released now
      have hmin : min i m = i := by omega
      have hmin' : min (i + 1) m = i + 1 := by omega
      have hready : i + 1 ≤ A'.length := hr i (by omega) hlt
      have hstop : decide (m < i) = false := by simp; omega
      rw [if_neg (by simp [hstop]), hmin, henq i (by omega)]
      have hcons : A'.drop i = A'[i] :: A'.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by omega)]
      rw [hcons]
      refine ⟨?_, by omega⟩
      have e1 : (A'.take (i + 1)).map (frameOf (D L)) = (A.take i).map (frameOf (D L)) ++ [frameOf (D L) A'[i]] := by
        rw [List.take_succ, List.getElem?_eq_getElem (by omega), ← htk i (by omega), List.map_append]; rfl
      simp only [hmin', GSt.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · trivial
      · rw [e1]; simp
      · simp; omega
    · -- i = m: the queue is empty; the first dummy, then stop
      subst heq
      have hmin : min m m = m := by omega
      have hmin' : min (m + 1) m = m := by omega
      have hstop : decide (m < m) = false := by simp
      rw [if_neg (by simp), hmin, henq m (by omega)]
      have hnil : A'.drop m = [] := List.drop_eq_nil_of_le hA'le
      rw [hnil]
      refine ⟨?_, by omega⟩
      simp only [hmin', GSt.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · first | trivial | rfl | exact hnil.symm
      · rw [htk m (by omega)]; simp
      · simp [D]
    · -- i > m: already stopped, another dummy
      have hmin : min i m = m := by omega
      have hmin' : min (i + 1) m = m := by omega
      have hstop : decide (m < i) = true := by simp; omega
      rw [if_pos hstop, hmin, henq m (by omega)]
      refine ⟨?_, by omega⟩
      simp only [hmin', GSt.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · trivial
      · rw [htk m (by omega), List.append_assoc, ← List.replicate_succ']
        congr 2; omega
      · simp; omega

/-- **Ready view.** For a ready sender the view is `render L (cs.take (min S |cs|)) S`, a function of the
accepted content sequence and the session length only. -/
theorem ready_view (L : ℕ) (sched : List (List Msg)) (hr : Ready L sched) :
    view (D L) sched =
      render L (((acc (D L) sched).map Msg.content).take (min sched.length (acc (D L) sched).length)) sched.length := by
  have h := (ready_state L sched hr sched.length le_rfl).1
  rw [List.take_length] at h
  unfold view render
  rw [h]
  simp only [List.map_take, List.map_map, List.length_take, List.length_map]
  congr 2
  omega

/-- **Timing noninterference.** Two ready schedules of the same length with the same accepted content sequence give
the SAME view, however differently they are timed: the timing channel has capacity 0. -/
theorem timing_noninterference (L : ℕ) (s₁ s₂ : List (List Msg)) (h₁ : Ready L s₁) (h₂ : Ready L s₂)
    (hlen : s₁.length = s₂.length)
    (hcs : (acc (D L) s₁).map Msg.content = (acc (D L) s₂).map Msg.content) :
    view (D L) s₁ = view (D L) s₂ := by
  rw [ready_view L s₁ h₁, ready_view L s₂ h₂, hlen, hcs]
  have : (acc (D L) s₁).length = (acc (D L) s₂).length := by
    have := congrArg List.length hcs; simpa using this
  rw [this]

/-- **Latency.** For a ready sender, message j (j < min(S, |cs|)) is released exactly at slot j (tick j·T). A
message submitted at slot a_j therefore waits T·(j − a_j): T times the number of messages ahead of it. -/
theorem ready_latency (L : ℕ) (sched : List (List Msg)) (hr : Ready L sched) (j : ℕ)
    (hj : j < min sched.length (acc (D L) sched).length) :
    (view (D L) sched)[j]? = some (.data ((acc (D L) sched)[j]'(by omega)).content L) := by
  rw [ready_view L sched hr]
  unfold render
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hj]

/-- **Throughput.** Every released frame is a dummy or a padded frame of size L, and there is exactly one per slot:
at most L bytes per T ticks. -/
theorem throughput (L : ℕ) (sched : List (List Msg)) :
    (view (D L) sched).length = sched.length ∧ ∀ f ∈ view (D L) sched, f = .dummy ∨ ∃ c, f = .data c L := by
  refine ⟨view_length _ _, fun f hf => ?_⟩
  obtain ⟨k, -, -, hv⟩ := view_shape L sched
  rw [hv] at hf
  unfold render at hf
  rcases List.mem_append.1 hf with h | h
  · obtain ⟨c, -, rfl⟩ := List.mem_map.1 h; exact Or.inr ⟨c, rfl⟩
  · exact Or.inl (List.eq_of_mem_replicate h)

/-! ## Leakage counting -/

/-- **Total leakage.** With message contents canonicalised to K classes, a deterministic sender `enc` (any timing,
sessions of S slots) and decoder `dec` recover the secret for at most (S+1)·K^S secrets: content ≤ S·log₂K bits,
timing ≤ log₂(S+1) bits per session. -/
theorem timed_leakage {M : Type} [Fintype M] [DecidableEq M] (L S K : ℕ) (hK : 0 < K)
    (enc : M → List (List Msg)) (hlen : ∀ m, (enc m).length = S)
    (hcls : ∀ m, ∀ x ∈ acc (D L) (enc m), x.content < K) (dec : List Frame → M) :
    (univ.filter (fun m => dec (view (D L) (enc m)) = m)).card ≤ (S + 1) * K ^ S := by
  classical
  let k : M → ℕ := fun m => Classical.choose (view_shape L (enc m))
  have hk : ∀ m, k m ≤ (acc (D L) (enc m)).length ∧ k m ≤ (enc m).length ∧
      view (D L) (enc m) = render L (((acc (D L) (enc m)).map Msg.content).take (k m)) (enc m).length :=
    fun m => Classical.choose_spec (view_shape L (enc m))
  let code : M → List ℕ := fun m => ((acc (D L) (enc m)).map Msg.content).take (k m)
  have hcode_len : ∀ m, (code m).length ≤ S := fun m => by
    simp only [code, List.length_take, List.length_map]; have := (hk m).2.1; rw [hlen] at this; omega
  have hcode_lt : ∀ m, ∀ x ∈ code m, x < K := fun m x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hx)
    exact hcls m y hy
  let g : M → Fin (S + 1) × (Fin S → Fin K) := fun m =>
    (⟨(code m).length, by have := hcode_len m; omega⟩,
     fun i => ⟨(code m).getD i 0, by
        rcases Nat.lt_or_ge i.1 (code m).length with h | h
        · rw [List.getD_eq_getElem _ _ h]; exact hcode_lt m _ (List.getElem_mem h)
        · rw [List.getD_eq_default _ _ h]; exact hK⟩)
  have hview : ∀ m, view (D L) (enc m) = render L (code m) S := fun m => by rw [(hk m).2.2, hlen]
  have hinj : Set.InjOn g (univ.filter (fun m => dec (view (D L) (enc m)) = m) : Set M) := by
    intro m₁ h₁ m₂ h₂ he
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at h₁ h₂
    have hl : (code m₁).length = (code m₂).length := by
      have := congrArg (fun p => (p.1 : ℕ)) he; simpa [g] using this
    have hc : code m₁ = code m₂ := by
      apply List.ext_getElem hl
      intro n hn1 hn2
      have hS : n < S := lt_of_lt_of_le hn1 (hcode_len m₁)
      have := congrArg (fun p => ((p.2 ⟨n, hS⟩ : Fin K) : ℕ)) he
      simp only [g] at this
      rwa [List.getD_eq_getElem _ _ hn1, List.getD_eq_getElem _ _ hn2] at this
    rw [← h₁, ← h₂, hview, hview, hc]
  have := Finset.card_le_card_of_injOn g (fun m _ => Finset.mem_univ (g m)) hinj
  simpa [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun] using this

/-! ## Witnesses -/

def m5 : Msg := ⟨5, 3⟩
def m6 : Msg := ⟨6, 3⟩

/-- the same content, timed differently: both at slot 0, or one per slot (both ready) -/
def early : List (List Msg) := [[m5, m6], [], []]
def spread : List (List Msg) := [[m5], [m6], []]

/-- release on arrival: each slot shows exactly what arrived in it -/
def onArrival (C : Cfg) (sched : List (List Msg)) : List (List Frame) :=
  sched.map (fun a => (a.filter (ok C)).map (frameOf C))

/-- **Release on arrival leaks timing** (one bit per message: which slot it arrived in); the timed gate gives the
same view for both timings. -/
theorem release_on_arrival_leaks_timing :
    onArrival (D 8) early ≠ onArrival (D 8) spread ∧ view (D 8) early = view (D 8) spread := by
  decide

/-- **Variable-size frames leak.** Same content, size 3 vs 7: unpadded frames differ, padded frames do not. -/
theorem variable_size_leaks :
    view ⟨8, false, true, none⟩ [[⟨5, 3⟩]] ≠ view ⟨8, false, true, none⟩ [[⟨5, 7⟩]] ∧
    view (D 8) [[⟨5, 3⟩]] = view (D 8) [[⟨5, 7⟩]] := by
  decide

/-- **A timing-dependent overflow policy leaks.** With a queue of capacity 1 that drops the newest message, the early
schedule loses message 6 and the spread one does not: the RELEASED content depends on timing. The unbounded queue of
the design releases the same content for both. -/
theorem overflow_leaks_timing :
    view ⟨8, true, false, some 1⟩ early ≠ view ⟨8, true, false, some 1⟩ spread ∧
    view (D 8) early = view (D 8) spread := by
  decide

end ControlStack.TimedRelease

#print axioms ControlStack.TimedRelease.view_shape
#print axioms ControlStack.TimedRelease.ready_view
#print axioms ControlStack.TimedRelease.timing_noninterference
#print axioms ControlStack.TimedRelease.ready_latency
#print axioms ControlStack.TimedRelease.throughput
#print axioms ControlStack.TimedRelease.timed_leakage
#print axioms ControlStack.TimedRelease.release_on_arrival_leaks_timing
#print axioms ControlStack.TimedRelease.variable_size_leaks
#print axioms ControlStack.TimedRelease.overflow_leaks_timing
