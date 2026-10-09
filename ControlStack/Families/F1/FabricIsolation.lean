/-
F1 for RDMA-style fabrics (STACK-MAP `gpu_interconnect`: `fabric_partition_enforced`, `rdma_mediated`).

One-sided RDMA, GPUDirect and peer copies bypass the host kernel, so the gate must sit at the NIC/fabric. Abstract
model:
- memory regions are REGISTERED, each registration an incarnation recorded in an append-only history with
  (incarnation, region, protection domain = owning tenant, access key);
- a remote access succeeds only if the region's current incarnation is live (not deregistered), the presented key
  equals its key, AND (`pdCheck`) the requester's protection domain is the region's;
- deregistration revokes the incarnation's key; with `rotate`, every registration must use a key never used before.

Results (adversary class TRACE_ARBITRARY: any registrations, deregistrations and accesses by any tenant presenting
any key, including leaked or guessed ones):
- `fabric_safe`: no cross-tenant access: every successful access was by the region's own tenant;
- `revocation_absorbing`: no access ever succeeds with a key revoked before it (the log records the revocation-list
  length at each access);
- witnesses: `shared_pd_breaks` (a protection domain shared across tenants: a leaked key gives cross-tenant access),
  `stale_key_reuse_breaks` (re-registration without key rotation revives a revoked key), `honest_access`,
  `dereg_blocks`;
- `guess_bound`: a guessing adversary. A key drawn uniformly from a space of size K is hit by a list of m guesses
  with probability ≤ m/K (union bound, on the finite uniform space). With failure-only feedback an adaptive guesser is
  a fixed list, so the bound covers it too. With `pdCheck`, a guessed key is useless across tenants anyway; the bound
  matters for the same-PD (intra-tenant) and shared-PD cases.

Limits: this models the policy layer of the NIC/fabric manager, not NIC firmware, switch or IOMMU correctness, and
not fabric contention channels (`fabric_contention_channel`, a measurement). Real fabrics need measurement (GPU-1
prereg and a future fabric prereg). No new mathematics.
-/
import Mathlib.Tactic

namespace ControlStack.FabricIsolation

/-- a registration: incarnation number, region, protection domain (tenant), key -/
structure Reg where
  inc : ℕ
  region : ℕ
  pd : ℕ
  key : ℕ
deriving DecidableEq, Repr

/-- a successful access: requester, region, the region's PD, key used, revocation-list length at that time -/
structure Acc where
  req : ℕ
  region : ℕ
  pd : ℕ
  key : ℕ
  rlen : ℕ
deriving DecidableEq, Repr

structure St where
  /-- registration history, newest first -/
  regs : List Reg
  dead : List ℕ
  revoked : List ℕ
  log : List Acc
deriving DecidableEq, Repr

inductive Op where
  | register (tenant region key : ℕ)
  | dereg (tenant region : ℕ)
  | access (tenant region key : ℕ)
deriving DecidableEq, Repr

structure Checks where
  pdCheck : Bool
  rotate : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true⟩

def init : St := ⟨[], [], [], []⟩

/-- the current incarnation of a region -/
def regOf (s : St) (r : ℕ) : Option Reg := s.regs.find? (fun g => g.region = r)

def live (s : St) (g : Reg) : Prop := g.inc ∉ s.dead

def step (C : Checks) (s : St) : Op → St
  | .register t r k =>
    if C.rotate = true → k ∉ s.regs.map Reg.key then
      { s with regs := ⟨s.regs.length, r, t, k⟩ :: s.regs }
    else s
  | .dereg t r =>
    match regOf s r with
    | none => s
    | some g =>
      if g.pd = t ∧ g.inc ∉ s.dead then { s with dead := s.dead ++ [g.inc], revoked := s.revoked ++ [g.key] }
      else s
  | .access t r k =>
    match regOf s r with
    | none => s
    | some g =>
      if g.inc ∉ s.dead ∧ g.key = k ∧ (C.pdCheck = true → g.pd = t) then
        { s with log := s.log ++ [⟨t, r, g.pd, k, s.revoked.length⟩] }
      else s

def run (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step C) s

theorem run_cons (C : Checks) (s : St) (o : Op) (ops : List Op) : run C s (o :: ops) = run C (step C s o) ops := rfl

/-! ## Safety -/

/-- an access by the region's own tenant, with a key not revoked before it -/
def AccOk (s : St) (a : Acc) : Prop := a.req = a.pd ∧ a.rlen ≤ s.revoked.length ∧ a.key ∉ s.revoked.take a.rlen

structure Inv (s : St) : Prop where
  keys_nodup : (s.regs.map Reg.key).Nodup
  incs : ∀ g ∈ s.regs, g.inc < s.regs.length
  incs_nodup : (s.regs.map Reg.inc).Nodup
  live_key : ∀ g ∈ s.regs, g.inc ∉ s.dead → g.key ∉ s.revoked
  revoked_used : ∀ k ∈ s.revoked, k ∈ s.regs.map Reg.key
  log : ∀ a ∈ s.log, AccOk s a

theorem inv_init : Inv init := ⟨by simp [init], by simp [init], by simp [init], by simp [init], by simp [init],
  by simp [init]⟩

theorem AccOk.mono {s t : St} (h : s.revoked <+: t.revoked) {a : Acc} (ha : AccOk s a) : AccOk t a := by
  obtain ⟨u, hu⟩ := h
  refine ⟨ha.1, ha.2.1.trans (hu ▸ by simp), ?_⟩
  rw [← hu, List.take_append_of_le_length ha.2.1]
  exact ha.2.2

theorem step_inv (s : St) (o : Op) (h : Inv s) : Inv (step full s o) := by
  cases o with
  | register t r k =>
    by_cases hk : k ∈ s.regs.map Reg.key
    · have e : step full s (.register t r k) = s := by simp [step, full, hk]
      rw [e]; exact h
    · have e : step full s (.register t r k) = { s with regs := ⟨s.regs.length, r, t, k⟩ :: s.regs } := by
        simp [step, full, hk]
      rw [e]
      refine ⟨?_, fun g hg => ?_, ?_, fun g hg hd => ?_, fun k' hk' => ?_, fun a ha => ?_⟩
      · show ((⟨s.regs.length, r, t, k⟩ :: s.regs).map Reg.key).Nodup
        simp only [List.map_cons, List.nodup_cons]; exact ⟨hk, h.keys_nodup⟩
      · change g ∈ (⟨s.regs.length, r, t, k⟩ :: s.regs) at hg
        show g.inc < (⟨s.regs.length, r, t, k⟩ :: s.regs).length
        simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · simp
        · have := h.incs g hg; simp; omega
      · show ((⟨s.regs.length, r, t, k⟩ :: s.regs).map Reg.inc).Nodup
        simp only [List.map_cons, List.nodup_cons]
        exact ⟨fun hm => by obtain ⟨g, hg, he⟩ := List.mem_map.1 hm; have := h.incs g hg; omega, h.incs_nodup⟩
      · change g ∈ (⟨s.regs.length, r, t, k⟩ :: s.regs) at hg
        simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact fun hr => hk (h.revoked_used _ hr)
        · exact h.live_key g hg hd
      · show k' ∈ (⟨s.regs.length, r, t, k⟩ :: s.regs).map Reg.key
        simp only [List.map_cons, List.mem_cons]; exact Or.inr (h.revoked_used k' hk')
      · exact h.log a ha
  | dereg t r =>
    simp only [step]
    split
    · exact h
    · rename_i g hg
      split_ifs with hc
      · have hgm : g ∈ s.regs := List.mem_of_find?_eq_some hg
        refine ⟨h.keys_nodup, h.incs, h.incs_nodup, fun g' hg' hd => ?_, fun k hk => ?_,
          fun a ha => AccOk.mono (List.prefix_append _ _) (h.log a ha)⟩
        · simp only [List.mem_append, List.mem_singleton, not_or] at hd
          simp only [List.mem_append, List.mem_singleton, not_or]
          refine ⟨h.live_key g' hg' hd.1, fun hkey => hd.2 ?_⟩
          -- keys are unique across the history, so g' = g
          have := List.inj_on_of_nodup_map h.keys_nodup hg' hgm hkey
          rw [this]
        · rcases List.mem_append.1 hk with hk | hk
          · exact h.revoked_used k hk
          · simp at hk; subst hk; exact List.mem_map.2 ⟨g, hgm, rfl⟩
      · exact h
  | access t r k =>
    simp only [step]
    split
    · exact h
    · rename_i g hg
      split_ifs with hc
      · obtain ⟨hlive, hkey, hpd⟩ := hc
        simp only [full, true_implies] at hpd
        have hgm : g ∈ s.regs := List.mem_of_find?_eq_some hg
        refine ⟨h.keys_nodup, h.incs, h.incs_nodup, h.live_key, h.revoked_used, fun a ha => ?_⟩
        rcases List.mem_append.1 ha with ha | ha
        · exact h.log a ha
        · simp at ha; subst ha
          refine ⟨hpd.symm, le_rfl, ?_⟩
          rw [List.take_length, ← hkey]
          exact h.live_key g hgm hlive
      · exact h

theorem run_inv (s : St) (ops : List Op) (h : Inv s) : Inv (run full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv s o h)

/-- **No cross-tenant access.** Every successful access was by the region's own tenant. -/
theorem fabric_safe (ops : List Op) : ∀ a ∈ (run full init ops).log, a.req = a.pd :=
  fun a ha => ((run_inv init ops inv_init).log a ha).1

/-- **Revocation is absorbing.** No access succeeds with a key revoked before it. -/
theorem revocation_absorbing (ops : List Op) :
    ∀ a ∈ (run full init ops).log, a.key ∉ (run full init ops).revoked.take a.rlen :=
  fun a ha => ((run_inv init ops inv_init).log a ha).2.2

/-! ## Witnesses: tenants 1 and 2, region 0, key 5 -/

theorem honest_access : (run full init [.register 1 0 5, .access 1 0 5]).log = [⟨1, 0, 1, 5, 0⟩] := by decide

/-- **Shared protection domain**: without the PD check, tenant 2 with a leaked key reads tenant 1's region. -/
theorem shared_pd_breaks :
    (run ⟨false, true⟩ init [.register 1 0 5, .access 2 0 5]).log = [⟨2, 0, 1, 5, 0⟩] ∧
    (run full init [.register 1 0 5, .access 2 0 5]).log = [] := by
  decide

/-- **Stale key reuse**: without key rotation, re-registering the region with the revoked key 5 makes the revoked
capability work again; with rotation the re-registration is refused and the access fails. -/
theorem stale_key_reuse_breaks :
    let ops := [Op.register 1 0 5, .dereg 1 0, .register 1 0 5, .access 1 0 5]
    (run ⟨true, false⟩ init ops).log = [⟨1, 0, 1, 5, 1⟩] ∧ (run ⟨true, false⟩ init ops).revoked = [5] ∧
    (run full init ops).log = [] := by
  decide

/-- deregistration blocks later access with the old key -/
theorem dereg_blocks : (run full init [.register 1 0 5, .dereg 1 0, .access 1 0 5]).log = [] := by decide

/-! ## Key guessing -/

/-- **Guessing bound.** A key uniform on a space of size K is among a list of m guesses with probability ≤ m/K. -/
theorem guess_bound (K : ℕ) (hK : 0 < K) (g : List (Fin K)) :
    ((Finset.univ.filter (fun k : Fin K => k ∈ g)).card : ℝ) / K ≤ g.length / K := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 : Finset.univ.filter (fun k : Fin K => k ∈ g) = g.toFinset := by
    ext k; simp
  rw [h1]
  exact_mod_cast List.toFinset_card_le g

/-- e.g. 2^20 guesses against a 64-bit key space succeed with probability ≤ 2^-44 -/
theorem guess_example (g : List (Fin (2 ^ 64))) (hg : g.length ≤ 2 ^ 20) :
    ((Finset.univ.filter (fun k : Fin (2 ^ 64) => k ∈ g)).card : ℝ) / (2 ^ 64 : ℕ) ≤ 1 / 2 ^ 44 := by
  refine (guess_bound (2 ^ 64) (by positivity) g).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (g.length : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hg
  push_cast
  nlinarith

end ControlStack.FabricIsolation

#print axioms ControlStack.FabricIsolation.fabric_safe
#print axioms ControlStack.FabricIsolation.revocation_absorbing
#print axioms ControlStack.FabricIsolation.honest_access
#print axioms ControlStack.FabricIsolation.shared_pd_breaks
#print axioms ControlStack.FabricIsolation.stale_key_reuse_breaks
#print axioms ControlStack.FabricIsolation.dereg_blocks
#print axioms ControlStack.FabricIsolation.guess_bound
#print axioms ControlStack.FabricIsolation.guess_example
