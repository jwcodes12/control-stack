/-
SC-07 refinement: the runtime's event structure (scenarios/SC-07/harness/gw.py, job.py, sink.py, run_sc07.py;
prereg/SC07-EGRESS-QUOTA.md) as a concrete machine, with a forward simulation into `SC07Liveness`. This is
criterion 3, as for SC-16, SC-18, SC-25, SC-26, SC-27 and SC-28.

Concrete machine: the gateway namespace's nftables `forward` chain (`CSt`, `COp`, `stepC`).
- `pkt ip port payload hdr`: an upload packet from the job namespace (saddr = the job), to `ip:port`. Its on-wire
  IP length is `payload + hdr` (IP and TCP headers, the `hdr` bytes). The rules apply in order:
  1. after HALT, the chain is the single rule `counter name "halt_drop" drop`;
  2. a packet whose (ip, port) is not allowlisted falls through to `counter name "deny_drop" drop` (policy drop);
  3. an allowlisted packet reaches `quota name "job_q"`. The kernel adds its IP length to `consumed` first, then
     DROPS it if `consumed ≥ QUOTA` (`quota_drop`). Prereg calibration: "the crossing packet is itself dropped
     (`consumed ≥ quota` after adding it)". Once over, `consumed` keeps growing, so every later packet is dropped;
  4. otherwise it is accepted (`fwd_up`) and recorded with its window.
- `resetQuota`: `nft reset quota`, which opens a new window. The runtime has one window per run.
- `halt`: `flush chain …; add rule … halt_drop drop`, atomically.
- Flag `quotaRule`: false is the runtime's negative-control ruleset (H6: no quota object, no quota rule).

α (into `SC07Liveness.St`; `Env` = allowlist `(ip, port) ↦ Nat.pair ip port`, `q = QUOTA − 1`, admins [0]):
- forwarded packets ↦ the forwarded-send log (destination, PAYLOAD bytes, window);
- the current window's forwarded payload ↦ used; window ↦ window; halted ↦ halted.
Events map as:
- a forwarded packet ↦ [send];
- every dropped packet (halt, deny, quota) ↦ [];
- `resetQuota` ↦ [tick]; `halt` ↦ [halt].

THE HEADER RELATION (premise and tolerance, as the prereg's TOL_QUOTA / TOL_AGREE):
- the quota counts ON-WIRE bytes, payload + hdr, with hdr ≥ 0. So forwarded payload ≤ forwarded wire bytes
  (`wire_eq_payload_add_hdr`). The model's "bits" are PAYLOAD bytes.
- The wire bound is strict: forwarded wire bytes per window < QUOTA (`concrete_wire_lt`). Hence payload ≤ QUOTA − 1.
  The runtime's TOL_QUOTA = 1 500 B (sink ≤ QUOTA + TOL_QUOTA) is measurement slack the model does not need.
- `sink_within_quota`: under the premise that the sink's byte count is at most the forwarded payload (TCP
  delivers each byte once), the sink's count is ≤ QUOTA − 1. That is within QUOTA + TOL_QUOTA for every TOL ≥ 0.
- The other direction is TOL_AGREE in the prereg: fwd_up − sink = hdr per packet plus retransmissions. It is
  measured, not modelled.

Results (deployed: quota rule present; adversary class TRACE_ARBITRARY: any packets to any (ip, port), any sizes and
header lengths, any resets, HALT at any point):
- `simulation`, `simulation_run`.
- `concrete_safe` (`SC07Liveness.sc07_safe` transferred):
  - every forwarded packet went to an allowlisted (ip, port);
  - every window's forwarded PAYLOAD is ≤ QUOTA − 1.
- `concrete_wire_lt`: every window's forwarded ON-WIRE bytes are < QUOTA.
- `concrete_halt_freezes` (`SC07Liveness.halt_freezes` transferred): after HALT, the forwarded log never changes.
- `quota_rule_absent_breaks` (the H6 control): without the quota rule, 24 payload bytes leave in one window with
  QUOTA = 10. With it, the crossing packet is dropped and 4 leave.
- `crossing_packet_dropped`: the deployed gateway drops the packet that would reach the quota, so it forwards
  strictly less than QUOTA on the wire (matches calibration: sink − QUOTA < 0 in every repetition).

Premises:
- the gateway namespace is the job's only route (H5, `exclusive_effect_path`);
- `nft_quota` semantics as above (the kernel is trusted, prereg §2);
- the header relation above.

Not covered:
- that gw.py installs exactly this ruleset. It is TESTED: the JSON ruleset is checked in H2/H6.
- the return direction (`fwd_down`);
- TCP retransmission and GSO segmentation: a GSO packet is one `pkt` of its IP length;
- HALT latency: TOL_HALT covers bytes in flight when `nft` returned. Here HALT is atomic.
Classical forward simulation; no novelty.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC07Liveness

namespace ControlStack.SC07Refinement

/-! ## The concrete machine -/

/-- the gateway configuration: allowlisted (ip, port) pairs, the quota threshold, whether the quota rule exists -/
structure CCfg where
  allow : List (ℕ × ℕ)
  Q : ℕ
  quotaRule : Bool

/-- a forwarded upload packet (`fwd_up`): destination, payload bytes, on-wire IP length, window -/
structure FwdRec where
  ip : ℕ
  port : ℕ
  payload : ℕ
  wire : ℕ
  window : ℕ
deriving DecidableEq, Repr

structure CSt where
  halted : Bool
  /-- the named quota object's `consumed` bytes -/
  consumed : ℕ
  /-- ghost: the number of quota resets -/
  window : ℕ
  fwd : List FwdRec
  quotaDrop : ℕ
  denyDrop : ℕ
  haltDrop : ℕ
deriving DecidableEq, Repr

inductive COp where
  | pkt (ip port payload hdr : ℕ)
  | resetQuota
  | halt
deriving DecidableEq, Repr

def cinit : CSt := ⟨false, 0, 0, [], 0, 0, 0⟩

def stepC (K : CCfg) (s : CSt) : COp → CSt
  | .pkt ip port pl hd =>
    if s.halted then { s with haltDrop := s.haltDrop + 1 }
    else if (ip, port) ∈ K.allow then
      if K.quotaRule then
        if K.Q ≤ s.consumed + (pl + hd) then
          { s with consumed := s.consumed + (pl + hd), quotaDrop := s.quotaDrop + 1 }
        else { s with consumed := s.consumed + (pl + hd), fwd := s.fwd ++ [⟨ip, port, pl, pl + hd, s.window⟩] }
      else { s with fwd := s.fwd ++ [⟨ip, port, pl, pl + hd, s.window⟩] }
    else { s with denyDrop := s.denyDrop + 1 }
  | .resetQuota => if s.halted then { s with consumed := 0 } else { s with consumed := 0, window := s.window + 1 }
  | .halt => { s with halted := true }

def runC (K : CCfg) (s : CSt) (ops : List COp) : CSt := ops.foldl (stepC K) s

theorem runC_cons (K : CCfg) (s : CSt) (o : COp) (ops : List COp) :
    runC K s (o :: ops) = runC K (stepC K s o) ops := rfl

theorem runC_append (K : CCfg) (s : CSt) (a b : List COp) : runC K s (a ++ b) = runC K (runC K s a) b := by
  simp [runC, List.foldl_append]

/-- forwarded payload bytes in window `w` -/
def payloadIn (l : List FwdRec) (w : ℕ) : ℕ := ((l.filter (fun r => r.window = w)).map FwdRec.payload).sum

/-- forwarded on-wire bytes in window `w` -/
def wireIn (l : List FwdRec) (w : ℕ) : ℕ := ((l.filter (fun r => r.window = w)).map FwdRec.wire).sum

theorem payloadIn_append (l : List FwdRec) (r : FwdRec) (w : ℕ) :
    payloadIn (l ++ [r]) w = payloadIn l w + (if r.window = w then r.payload else 0) := by
  unfold payloadIn; by_cases h : r.window = w <;> simp [List.filter_append, h]

theorem wireIn_append (l : List FwdRec) (r : FwdRec) (w : ℕ) :
    wireIn (l ++ [r]) w = wireIn l w + (if r.window = w then r.wire else 0) := by
  unfold wireIn; by_cases h : r.window = w <;> simp [List.filter_append, h]

theorem payloadIn_le_wireIn (l : List FwdRec) (h : ∀ r ∈ l, r.payload ≤ r.wire) (w : ℕ) :
    payloadIn l w ≤ wireIn l w := by
  induction l using List.reverseRecOn with
  | nil => simp [payloadIn, wireIn]
  | append_singleton l r ih =>
    rw [payloadIn_append, wireIn_append]
    have := ih (fun x hx => h x (List.mem_append_left _ hx))
    have hr := h r (List.mem_append_right _ (List.mem_singleton_self _))
    split_ifs <;> omega

theorem in_gt (l : List FwdRec) (w : ℕ) (h : ∀ r ∈ l, r.window < w) : payloadIn l w = 0 ∧ wireIn l w = 0 := by
  have hf : l.filter (fun r => r.window = w) = [] :=
    List.filter_eq_nil_iff.2 (fun r hr => by have := h r hr; simp; omega)
  simp [payloadIn, wireIn, hf]

/-! ## Concrete invariant (deployed) -/

structure CInv (s : CSt) : Prop where
  hdr : ∀ r ∈ s.fwd, r.payload ≤ r.wire
  wins : ∀ r ∈ s.fwd, r.window ≤ s.window
  cons : s.halted = false → wireIn s.fwd s.window ≤ s.consumed

theorem cinv_init : CInv cinit := ⟨by simp [cinit], by simp [cinit], fun _ => by simp [cinit, wireIn]⟩

theorem cinv_step (K : CCfg) (hK : K.quotaRule = true) (s : CSt) (o : COp) (h : CInv s) : CInv (stepC K s o) := by
  cases o with
  | pkt ip port pl hd =>
    simp only [stepC, hK, ite_true]
    split_ifs with hh ha hq
    · exact ⟨h.hdr, h.wins, fun hf => by simp [hh] at hf⟩
    · exact ⟨h.hdr, h.wins, fun hf => by have := h.cons hf; simp only at this ⊢; omega⟩
    · refine ⟨fun r hr => ?_, fun r hr => ?_, fun hf => ?_⟩
      · rcases List.mem_append.1 hr with hr | hr
        · exact h.hdr r hr
        · simp at hr; subst hr; simp
      · rcases List.mem_append.1 hr with hr | hr
        · exact h.wins r hr
        · simp at hr; subst hr; exact le_rfl
      · have := h.cons hf
        simp only [wireIn_append, ite_true]
        omega
    · exact ⟨h.hdr, h.wins, h.cons⟩
  | resetQuota =>
    simp only [stepC]
    split_ifs with hh
    · exact ⟨h.hdr, h.wins, fun hf => by simp [hh] at hf⟩
    · refine ⟨h.hdr, fun r hr => (h.wins r hr).trans (Nat.le_succ _), fun _ => ?_⟩
      show wireIn s.fwd (s.window + 1) ≤ 0
      rw [(in_gt s.fwd (s.window + 1) (fun r hr => Nat.lt_succ_of_le (h.wins r hr))).2]
  | halt => exact ⟨h.hdr, h.wins, fun hf => by cases hf⟩

theorem cinv_run (K : CCfg) (hK : K.quotaRule = true) (s : CSt) (ops : List COp) (h : CInv s) :
    CInv (runC K s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [runC_cons]; exact ih _ (cinv_step K hK s o h)

/-! ## Abstraction and forward simulation -/

/-- the model's environment: allowlist as `Nat.pair ip port`, quota `q = QUOTA − 1` payload bytes, admin 0 -/
def envOf (K : CCfg) : SC07Liveness.Env := ⟨K.allow.map (fun e => Nat.pair e.1 e.2), K.Q - 1, [0]⟩

def toFwd (r : FwdRec) : SC07Liveness.Fwd := ⟨Nat.pair r.ip r.port, r.payload, r.window⟩

def α (s : CSt) : SC07Liveness.St := ⟨s.window, payloadIn s.fwd s.window, s.fwd.map toFwd, s.halted⟩

def opsOf (K : CCfg) (s : CSt) : COp → List SC07Liveness.Op
  | .pkt ip port pl hd =>
    if s.halted = false ∧ (ip, port) ∈ K.allow ∧ s.consumed + (pl + hd) < K.Q then [.send (Nat.pair ip port) pl]
    else []
  | .resetQuota => [.tick]
  | .halt => [.halt 0]

theorem simulation (K : CCfg) (hK : K.quotaRule = true) (s : CSt) (o : COp) (h : CInv s) :
    α (stepC K s o) = SC07Liveness.run (envOf K) SC07Liveness.full (α s) (opsOf K s o) := by
  cases o with
  | pkt ip port pl hd =>
    simp only [stepC, opsOf, hK, ite_true]
    by_cases hh : s.halted = true
    · rw [ite_eq_left hh, ite_eq_right (by simp [hh])]; rfl
    · have hf : s.halted = false := by simpa using hh
      rw [ite_eq_right hh]
      by_cases ha : (ip, port) ∈ K.allow
      · rw [ite_eq_left ha]
        by_cases hq : K.Q ≤ s.consumed + (pl + hd)
        · rw [ite_eq_left hq, ite_eq_right (by omega)]; rfl
        · rw [ite_eq_right hq, ite_eq_left ⟨hf, ha, by omega⟩]
          have hle := (payloadIn_le_wireIn s.fwd h.hdr s.window).trans (h.cons hf)
          have hmem : Nat.pair ip port ∈ (envOf K).allow := List.mem_map.2 ⟨(ip, port), ha, rfl⟩
          have hguard : (SC07Liveness.full.allowCheck = true → Nat.pair ip port ∈ (envOf K).allow) ∧
              (SC07Liveness.full.quotaCheck = true → (α s).used + pl ≤ (envOf K).q) := by
            refine ⟨fun _ => hmem, fun _ => ?_⟩
            show payloadIn s.fwd s.window + pl ≤ K.Q - 1
            omega
          simp only [SC07Liveness.run, List.foldl_cons, List.foldl_nil, SC07Liveness.step]
          rw [ite_eq_right (by simp [α, hf]), ite_eq_left hguard]
          simp [α, payloadIn_append, toFwd]
      · rw [ite_eq_right ha, ite_eq_right (by tauto)]; rfl
  | resetQuota =>
    simp only [stepC, opsOf, SC07Liveness.run, List.foldl_cons, List.foldl_nil, SC07Liveness.step]
    by_cases hh : s.halted = true
    · rw [ite_eq_left hh, ite_eq_left (show (α s).halted = true ∧ SC07Liveness.full.haltCheck = true from ⟨hh, rfl⟩)]
      rfl
    · rw [ite_eq_right hh, ite_eq_right (by simp [α, hh])]
      simp [α, (in_gt s.fwd (s.window + 1) (fun r hr => Nat.lt_succ_of_le (h.wins r hr))).1]
  | halt =>
    simp only [stepC, opsOf, SC07Liveness.run, List.foldl_cons, List.foldl_nil, SC07Liveness.step]
    rw [ite_eq_left (show (0 : ℕ) ∈ (envOf K).admins from List.mem_singleton_self 0)]
    rfl

def absTrace (K : CCfg) : CSt → List COp → List SC07Liveness.Op
  | _, [] => []
  | s, o :: ops => opsOf K s o ++ absTrace K (stepC K s o) ops

theorem simulation_run (K : CCfg) (hK : K.quotaRule = true) (s : CSt) (ops : List COp) (h : CInv s) :
    α (runC K s ops) = SC07Liveness.run (envOf K) SC07Liveness.full (α s) (absTrace K s ops) := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    change α (runC K (stepC K s o) ops) = _
    rw [ih _ (cinv_step K hK s o h), simulation K hK s o h]
    simp [absTrace, SC07Liveness.run, List.foldl_append]

theorem α_cinit : α cinit = SC07Liveness.init := rfl

/-! ## Transfer -/

theorem wsum_α (s : CSt) (w : ℕ) : SC07Liveness.wsum (α s) w = payloadIn s.fwd w := by
  simp [SC07Liveness.wsum, α, payloadIn, List.filter_map, Function.comp_def, toFwd]; rfl

/-- **SC-07 gateway safety for the concrete nftables gateway** (`SC07Liveness.sc07_safe` transferred). For every
packet sequence, every forwarded packet went to an allowlisted (ip, port), and every window's forwarded PAYLOAD is
≤ QUOTA − 1. -/
theorem concrete_safe (K : CCfg) (hK : K.quotaRule = true) (ops : List COp) :
    (∀ r ∈ (runC K cinit ops).fwd, (r.ip, r.port) ∈ K.allow) ∧
      ∀ w, payloadIn (runC K cinit ops).fwd w ≤ K.Q - 1 := by
  have e := simulation_run K hK cinit ops cinv_init
  rw [α_cinit] at e
  obtain ⟨hd, hw⟩ := SC07Liveness.sc07_safe (envOf K) (absTrace K cinit ops)
  rw [← e] at hd hw
  refine ⟨fun r hr => ?_, fun w => by rw [← wsum_α]; exact hw w⟩
  obtain ⟨⟨a, b⟩, hab, he⟩ := List.mem_map.1 (hd (toFwd r) (List.mem_map.2 ⟨r, hr, rfl⟩))
  obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 he
  exact hab

/-- **The header relation.** Each forwarded packet's on-wire length is its payload plus its header bytes, so per
window the quota's wire bytes are the model's payload plus the header overhead. -/
theorem wire_eq_payload_add_hdr (K : CCfg) (ops : List COp) :
    ∀ r ∈ (runC K cinit ops).fwd, ∃ hd, r.wire = r.payload + hd := by
  have key : ∀ (ops : List COp) (s : CSt), (∀ r ∈ s.fwd, ∃ hd, r.wire = r.payload + hd) →
      ∀ r ∈ (runC K s ops).fwd, ∃ hd, r.wire = r.payload + hd := by
    intro ops
    induction ops with
    | nil => intro s h; exact h
    | cons o ops ih =>
      intro s h
      apply ih
      intro r hr
      cases o with
      | pkt ip port pl hd =>
        simp only [stepC] at hr
        split_ifs at hr <;> first | exact h r hr | (rcases List.mem_append.1 hr with hr | hr
                                                    · exact h r hr
                                                    · simp at hr; subst hr; exact ⟨hd, rfl⟩)
      | resetQuota => simp only [stepC] at hr; split_ifs at hr <;> exact h r hr
      | halt => exact h r hr
  exact key ops cinit (by simp [cinit])

/-- **On the wire, strictly below the quota**: every window's forwarded IP bytes are < QUOTA (the crossing packet is
dropped). -/
theorem concrete_wire_lt (K : CCfg) (hK : K.quotaRule = true) (hQ : 0 < K.Q) (ops : List COp) (w : ℕ) :
    wireIn (runC K cinit ops).fwd w < K.Q := by
  -- a packet is forwarded only if `consumed + len < QUOTA`, and `consumed` ≥ the current window's wire bytes
  have key : ∀ (ops : List COp) (s : CSt), CInv s → (∀ w, wireIn s.fwd w < K.Q) →
      ∀ w, wireIn (runC K s ops).fwd w < K.Q := by
    intro ops
    induction ops with
    | nil => intro s _ h; exact h
    | cons o ops ih =>
      intro s hinv hw
      rw [runC_cons]
      apply ih _ (cinv_step K hK s o hinv)
      intro w'
      cases o with
      | pkt ip port pl hd =>
        simp only [stepC, hK, ite_true]
        split_ifs with hh ha hq
        · exact hw w'
        · exact hw w'
        · rw [wireIn_append]
          split_ifs with hww
          · have := hinv.cons (by simpa using hh)
            simp only at hww ⊢
            subst hww
            omega
          · simpa using hw w'
        · exact hw w'
      | resetQuota => simp only [stepC]; split_ifs <;> exact hw w'
      | halt => exact hw w'
  exact key ops cinit cinv_init (fun _ => by simp [cinit, wireIn, hQ]) w

/-- **HALT freezes forwarding** (`SC07Liveness.halt_freezes` transferred): after a HALT, the forwarded log never
changes. -/
theorem concrete_halt_freezes (K : CCfg) (hK : K.quotaRule = true) (pre post : List COp)
    (hh : (runC K cinit pre).halted = true) : (runC K cinit (pre ++ post)).fwd = (runC K cinit pre).fwd := by
  have hinv := cinv_run K hK cinit pre cinv_init
  have e := simulation_run K hK _ post hinv
  rw [SC07Liveness.halt_freezes _ _ _ hh] at e
  have hlog := congrArg SC07Liveness.St.log e
  simp only [α] at hlog
  -- the forwarded log only grows, so equal images under `toFwd` have equal length and are equal
  have hpre : ∀ (ops : List COp) (s : CSt), s.fwd <+: (runC K s ops).fwd := by
    intro ops
    induction ops with
    | nil => intro s; exact List.prefix_refl _
    | cons o ops ih =>
      intro s
      refine List.IsPrefix.trans ?_ (ih _)
      cases o with
      | pkt ip port pl hd =>
        simp only [stepC]; split_ifs <;> first | exact List.prefix_refl _ | exact List.prefix_append _ _
      | resetQuota => simp only [stepC]; split_ifs <;> exact List.prefix_refl _
      | halt => exact List.prefix_refl _
  obtain ⟨t, ht⟩ := hpre post (runC K cinit pre)
  have hlen := congrArg List.length hlog
  simp only [List.length_map] at hlen
  rw [runC_append, ← ht]
  rw [← ht, List.length_append] at hlen
  have : t = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp [this]

/-- **The sink's count is within the quota**, under the premise that the sink received at most the forwarded payload
(TCP delivers each byte once): ≤ QUOTA − 1, hence ≤ QUOTA + TOL_QUOTA for every tolerance. -/
theorem sink_within_quota (K : CCfg) (hK : K.quotaRule = true) (ops : List COp) (w sinkBytes tol : ℕ)
    (hsink : sinkBytes ≤ payloadIn (runC K cinit ops).fwd w) : sinkBytes ≤ K.Q - 1 ∧ sinkBytes ≤ K.Q + tol :=
  ⟨hsink.trans ((concrete_safe K hK ops).2 w), by have := hsink.trans ((concrete_safe K hK ops).2 w); omega⟩

/-! ## Witnesses -/

/-- QUOTA = 10; allowlisted 10.207.2.10:8080 as (1, 8080); not allowlisted (2, 8080) -/
def K0 (quotaRule : Bool) : CCfg := ⟨[(1, 8080)], 10, quotaRule⟩

/-- **The H6 control: no quota rule ⇒ the per-window bound fails.** Three 8-byte payloads (1 header byte each) leave
in one window, 24 > QUOTA − 1; with the quota rule, only the first leaves. -/
theorem quota_rule_absent_breaks :
    payloadIn (runC (K0 false) cinit [.pkt 1 8080 8 1, .pkt 1 8080 8 1, .pkt 1 8080 8 1]).fwd 0 = 24 ∧
      payloadIn (runC (K0 true) cinit [.pkt 1 8080 8 1, .pkt 1 8080 8 1, .pkt 1 8080 8 1]).fwd 0 = 8 := by
  decide

/-- **The crossing packet is dropped**: 4 + 1 bytes forwarded (consumed 5), the next brings consumed to 10 = QUOTA
and is dropped, and so is every later one. Forwarded wire bytes 5 < 10; the non-allowlisted packet is denied. -/
theorem crossing_packet_dropped :
    let t := runC (K0 true) cinit [.pkt 1 8080 4 1, .pkt 1 8080 4 1, .pkt 1 8080 1 0, .pkt 2 8080 1 0]
    payloadIn t.fwd 0 = 4 ∧ wireIn t.fwd 0 = 5 ∧ t.quotaDrop = 2 ∧ t.denyDrop = 1 := by
  decide

/-- HALT, then a quota reset and more packets: nothing more is forwarded -/
theorem halt_witness :
    (runC (K0 true) cinit [.pkt 1 8080 2 1, .halt, .resetQuota, .pkt 1 8080 2 1]).fwd = [⟨1, 8080, 2, 3, 0⟩] := by
  decide

end ControlStack.SC07Refinement

#print axioms ControlStack.SC07Refinement.simulation
#print axioms ControlStack.SC07Refinement.simulation_run
#print axioms ControlStack.SC07Refinement.concrete_safe
#print axioms ControlStack.SC07Refinement.wire_eq_payload_add_hdr
#print axioms ControlStack.SC07Refinement.concrete_wire_lt
#print axioms ControlStack.SC07Refinement.concrete_halt_freezes
#print axioms ControlStack.SC07Refinement.sink_within_quota
#print axioms ControlStack.SC07Refinement.quota_rule_absent_breaks
#print axioms ControlStack.SC07Refinement.crossing_packet_dropped
#print axioms ControlStack.SC07Refinement.halt_witness
