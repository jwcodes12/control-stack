/-
Honest liveness of attested key release UNDER ADVERSARY INTERLEAVING. This closes the liveness gap noted for
`F4/AttestedKeyRelease.lean`, whose `honest_liveness` ran the four honest steps back to back.

`progress_interleaved`: the honest workload's steps [issue, quote, request, decrypt] run with arbitrary operations
m1, m2, m3 interleaved between them. These are any adversary, environment or admin operations: spawns, quotes,
requests for any key, replays, ticks, revocations, compromises, other decrypts. At the end, the workload has decrypted,
UNLESS exactly one of the following happened:
- (a) EXPIRY: more than W ticks passed between the honest issue and the honest request;
- (b) REVOCATION: the session's measurement was not allowlisted at the request;
- (c) SESSION DEATH: the session was gone at the quote or at the decrypt;
- (d) NONCE THEFT: before the honest request, another attested request consumed the honest nonce with a release to
  a DIFFERENT key.
Nothing else blocks progress. Witnesses show each blocker occurs:
- `expiry_blocks`, `revocation_blocks`, `death_blocks`;
- `nonce_theft_blocks`. A competing workload running allowlisted code quotes the broker's freshly issued nonce
  first. This is an availability finding: the nonce is not bound to the requester. The fix is a broker that binds
  each nonce to the requesting session at issue. Safety is unaffected: the thief is itself an attested,
  allowlisted session.

Availability under an adversarial scheduler:
- `tick_starvation`: if the scheduler (adversary) delays every honest round by D > W ticks between the issue and the
  request, the honest workload is never released the key and never decrypts, for any number of rounds.
- `expiry_blocks` / `expiry_ok`: the same round succeeds with W ≥ D. So W must exceed the worst-case scheduling
  delay; that is a measured quantity (`measured_rates`).

Model only; no novelty is claimed.
-/
import Mathlib.Tactic
import ControlStack.Families.F4.AttestedKeyRelease

namespace ControlStack.AttestedLiveness

open ControlStack.AttestedKeyRelease

/-! ## Stability lemmas -/

theorem run_append (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (a b : List Op) :
    run A W C s (a ++ b) = run A W C (run A W C s a) b := by
  simp [run, List.foldl_append]

theorem run_cons (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (o : Op) (ops : List Op) :
    run A W C s (o :: ops) = run A W C (step A W C s o) ops := rfl

/-- session k either runs code c or is gone for good (k is already allocated) -/
def Alive (k c : ℕ) (s : St) : Prop := k < s.nextKey ∧ ((k, c) ∈ s.sessions ∨ ∀ c', (k, c') ∉ s.sessions)

theorem step_alive (A : List ℕ) (W : ℕ) (s : St) (o : Op) (k c : ℕ) (h : Alive k c s) :
    Alive k c (step A W full s o) := by
  obtain ⟨hlt, h⟩ := h
  cases o with
  | spawn c' =>
    refine ⟨Nat.lt_succ_of_lt hlt, ?_⟩
    simp only [step]
    rcases h with h | h
    · exact Or.inl (List.mem_append_left _ h)
    · right; intro c'' hm
      rcases List.mem_append.1 hm with hm | hm
      · exact h c'' hm
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm; omega
  | compromise k' =>
    simp only [step]
    split_ifs
    · refine ⟨hlt, ?_⟩
      by_cases hkk : k' = k
      · subst hkk; right; intro c'' hm; simp at hm
      · rcases h with h | h
        · left; exact List.mem_filter.2 ⟨h, by simp; omega⟩
        · right; intro c'' hm; exact h c'' (List.mem_filter.1 hm).1
    · exact ⟨hlt, h⟩
  | modify k' c' => exact ⟨hlt, h⟩
  | _ =>
    simp only [step]
    repeat' split
    all_goals exact ⟨hlt, h⟩

theorem run_alive (A : List ℕ) (W : ℕ) (s : St) (ops : List Op) (k c : ℕ) (h : Alive k c s) :
    Alive k c (run A W full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => exact ih _ (step_alive A W s o k c h)

theorem alive_code (W : ℕ) (s : St) (hs : Inv W s) (k c : ℕ) (h : Alive k c s) :
    codeOf s k = some c ∨ codeOf s k = none := by
  rcases h.2 with h | h
  · exact Or.inl (codeOf_of_mem h hs.k0)
  · right
    unfold codeOf
    rw [List.find?_eq_none.2 (fun x hx hxk => h x.2 (by
      have : x = (k, x.2) := Prod.ext (by simpa using hxk) rfl
      rw [← this]; exact hx))]
    rfl

/-- reports, issued nonces and releases only grow -/
theorem step_grow (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (o : Op) :
    (∀ x ∈ s.reports, x ∈ (step A W C s o).reports) ∧ (∀ x ∈ s.issued, x ∈ (step A W C s o).issued) ∧
      ∀ x ∈ s.rels, x ∈ (step A W C s o).rels := by
  cases o <;> simp only [step] <;> (repeat' split) <;>
    exact ⟨fun x hx => by simp [hx], fun x hx => by simp [hx], fun x hx => by simp [hx]⟩

theorem run_grow (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (ops : List Op) :
    (∀ x ∈ s.reports, x ∈ (run A W C s ops).reports) ∧ (∀ x ∈ s.issued, x ∈ (run A W C s ops).issued) ∧
      ∀ x ∈ s.rels, x ∈ (run A W C s ops).rels := by
  induction ops generalizing s with
  | nil => exact ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩
  | cons o ops ih =>
    obtain ⟨a1, a2, a3⟩ := step_grow A W C s o
    obtain ⟨b1, b2, b3⟩ := ih (step A W C s o)
    exact ⟨fun x h => b1 x (a1 x h), fun x h => b2 x (a2 x h), fun x h => b3 x (a3 x h)⟩

/-- used nonces are exactly the nonces of releases -/
def UInv (s : St) : Prop := s.used = s.rels.map (fun e => e.2.1.nonce)

theorem step_uinv (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (o : Op) (h : UInv s) : UInv (step A W C s o) := by
  cases o with
  | request pk r =>
    simp only [step]
    split_ifs
    · unfold UInv at h ⊢; simp [h]
    · exact h
  | _ =>
    simp only [step]
    repeat' split
    all_goals exact h

theorem run_uinv (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (ops : List Op) (h : UInv s) : UInv (run A W C s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => exact ih _ (step_uinv A W C s o h)

theorem uinv_init (a0 : List ℕ) : UInv (init a0) := rfl

/-! ## Progress under interleaving -/

/-- **Interleaved honest progress, characterised exactly.** From any reachable state with a live session k running
code c, run the honest steps [issue, quote k n, request k ⟨c, n, k⟩, decrypt k] (n is the issued nonce) with
arbitrary operations m1, m2, m3 in between. At the end, k has decrypted with code c, or one of these holds:
- the session was gone at the quote;
- the nonce expired before the request (t0 + W < now);
- c was not allowlisted at the request;
- the honest nonce was consumed by a release to another key;
- the session was gone at the decrypt. -/
theorem progress_interleaved (A : List ℕ) (W : ℕ) (s0 : St) (hs : Inv W s0) (hu : UInv s0) (k c : ℕ)
    (hk : (k, c) ∈ s0.sessions) (m1 m2 m3 : List Op) :
    let n := s0.nextNonce
    let t0 := s0.now
    let s1 := run A W full (step A W full s0 .issue) m1
    let s2 := run A W full (step A W full s1 (.quote k n)) m2
    let s3 := run A W full (step A W full s2 (.request k ⟨c, n, k⟩)) m3
    (∃ t, (k, c, t) ∈ (step A W full s3 (.decrypt k)).decs) ∨ codeOf s1 k = none ∨ t0 + W < s2.now ∨
      c ∉ s2.allow ∨ (∃ e ∈ s2.rels, e.2.1.nonce = n ∧ e.1 ≠ k) ∨ codeOf s3 k = none := by
  intro n t0 s1 s2 s3
  -- invariants along the way
  have i1 : Inv W s1 := run_inv A W _ m1 (step_inv A W s0 _ hs)
  have i2 : Inv W s2 := run_inv A W _ m2 (step_inv A W s1 _ i1)
  have i3 : Inv W s3 := run_inv A W _ m3 (step_inv A W s2 _ i2)
  have u2 : UInv s2 := run_uinv A W full _ m2 (step_uinv A W full s1 _ (run_uinv A W full _ m1 (step_uinv A W full s0 _ hu)))
  have a1 : Alive k c s1 := run_alive A W _ m1 k c (step_alive A W s0 _ k c ⟨hs.k1 _ hk, Or.inl hk⟩)
  have a3 : Alive k c s3 :=
    run_alive A W _ m3 k c (step_alive A W s2 _ k c (run_alive A W _ m2 k c (step_alive A W s1 _ k c a1)))
  rcases alive_code W s1 i1 k c a1 with hc1 | hc1
  swap; · exact Or.inr (Or.inl hc1)
  -- the issued nonce
  have hiA : (n, t0) ∈ (step A W full s0 .issue).issued := by simp [step, n, t0]
  have hi1 : (n, t0) ∈ s1.issued := (run_grow A W full _ m1).2.1 _ hiA
  have hq : step A W full s1 (.quote k n) = { s1 with reports := s1.reports ++ [⟨c, n, k⟩] } := by
    simp only [step, hc1]; rw [if_pos ⟨(n, t0), hi1, rfl⟩]
  have hr2 : (⟨c, n, k⟩ : Report) ∈ s2.reports := (run_grow A W full _ m2).1 _ (by rw [hq]; simp)
  have hi2 : (n, t0) ∈ s2.issued := (run_grow A W full _ m2).2.1 _ (by rw [hq]; exact hi1)
  by_cases hexp : t0 + W < s2.now
  · exact Or.inr (Or.inr (Or.inl hexp))
  by_cases hal : c ∈ s2.allow
  swap; · exact Or.inr (Or.inr (Or.inr (Or.inl hal)))
  -- a release to k exists after the honest request
  have hrel : (∃ e ∈ s3.rels, e.1 = k) ∨ ∃ e ∈ s2.rels, e.2.1.nonce = n ∧ e.1 ≠ k := by
    by_cases hused : n ∈ s2.used
    · rw [u2] at hused
      obtain ⟨e, he, hen⟩ := List.mem_map.1 hused
      by_cases hek : e.1 = k
      · left
        exact ⟨e, (run_grow A W full _ m3).2.2 _ ((step_grow A W full s2 _).2.2 _ he), hek⟩
      · exact Or.inr ⟨e, he, hen, hek⟩
    · left
      have hpass : Pass full W s2 k ⟨c, n, k⟩ :=
        ⟨fun _ => hr2, fun _ => ⟨⟨(n, t0), hi2, rfl, by omega⟩, hused⟩, fun _ => hal, fun _ => rfl⟩
      refine ⟨(k, ⟨c, n, k⟩, s2.now), (run_grow A W full _ m3).2.2 _ ?_, rfl⟩
      simp only [step]; rw [if_pos hpass]; simp
  rcases hrel with hrel | hrel
  swap; · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hrel))))
  rcases alive_code W s3 i3 k c a3 with hc3 | hc3
  · left
    refine ⟨s3.now, ?_⟩
    simp only [step, hc3]; rw [if_pos hrel]; simp
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc3))))

/-! ## Each blocker occurs (A0 = admin 0, W = 2, allowlist {1}) -/

/-- (a) expiry: 3 ticks between issue and request exceed W = 2. With W = 3 the same schedule succeeds. -/
def expiryTrace : List Op :=
  [.spawn 1, .issue, .quote 0 0, .tick, .tick, .tick, .request 0 ⟨1, 0, 0⟩, .decrypt 0]

theorem expiry_blocks : (run A0 2 full (init [1]) expiryTrace).decs = [] := by decide

theorem expiry_ok : (run A0 3 full (init [1]) expiryTrace).decs = [(0, 1, 3)] := by decide

/-- (b) revocation between quote and request -/
theorem revocation_blocks :
    (run A0 2 full (init [1]) [.spawn 1, .issue, .quote 0 0, .revoke 0 1, .request 0 ⟨1, 0, 0⟩, .decrypt 0]).decs =
      [] := by decide

/-- (c) session death between release and decrypt (the key was released, but nobody can use it) -/
theorem death_blocks :
    let s := run A0 2 full (init [1]) [.spawn 1, .issue, .quote 0 0, .request 0 ⟨1, 0, 0⟩, .compromise 0, .decrypt 0]
    s.decs = [] ∧ s.rels = [(0, ⟨1, 0, 0⟩, 0)] := by decide

/-- (d) nonce theft: a competing allowlisted session (key 1) quotes the honest nonce 0 first and consumes it. The
honest request (key 0) is refused. -/
theorem nonce_theft_blocks :
    let s := run A0 2 full (init [1])
      [.spawn 1, .spawn 1, .issue, .quote 1 0, .request 1 ⟨1, 0, 1⟩, .quote 0 0, .request 0 ⟨1, 0, 0⟩, .decrypt 0]
    s.decs = [] ∧ s.rels = [(1, ⟨1, 0, 1⟩, 0)] := by decide

/-! ## Starvation by an adversarial tick schedule -/

def tickN (D : ℕ) : List Op := List.replicate D .tick

theorem run_ticks (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (D : ℕ) :
    (run A W C s (tickN D)).now = s.now + D ∧ (run A W C s (tickN D)).issued = s.issued ∧
      (run A W C s (tickN D)).rels = s.rels ∧ (run A W C s (tickN D)).decs = s.decs ∧
      (run A W C s (tickN D)).sessions = s.sessions := by
  induction D generalizing s with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ D ih =>
    rw [show tickN (D + 1) = .tick :: tickN D from rfl, run_cons]
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (step A W C s .tick)
    refine ⟨?_, h2, h3, h4, h5⟩
    rw [h1]; simp only [step]; omega

/-- one honest round, delayed by D ticks between issue and request -/
def honestRound (k c D : ℕ) (s : St) : List Op :=
  [.issue, .quote k s.nextNonce] ++ tickN D ++ [.request k ⟨c, s.nextNonce, k⟩, .decrypt k]

theorem round_starves (A : List ℕ) (W : ℕ) (s : St) (hs : Inv W s) (k c D : ℕ) (hD : W < D)
    (hno : ∀ e ∈ s.rels, e.1 ≠ k) :
    (run A W full s (honestRound k c D s)).rels = s.rels ∧ (run A W full s (honestRound k c D s)).decs = s.decs ∧
      Inv W (run A W full s (honestRound k c D s)) := by
  refine ⟨?_, ?_, run_inv A W s _ hs⟩ <;>
  · set n := s.nextNonce
    set sA := step A W full s .issue
    set sB := step A W full sA (.quote k n)
    have hB : sB.now = s.now ∧ sB.issued = s.issued ++ [(n, s.now)] ∧ sB.rels = s.rels ∧ sB.decs = s.decs := by
      simp only [sB, sA, step]
      split
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩
    set sC := run A W full sB (tickN D)
    obtain ⟨c1, c2, c3, c4, -⟩ := run_ticks A W full sB D
    have iC : Inv W sC := run_inv A W sB _ (step_inv A W sA _ (step_inv A W s _ hs))
    have hnp : ¬ Pass full W sC k ⟨c, n, k⟩ := by
      rintro ⟨-, hfr, -, -⟩
      obtain ⟨⟨p, hp, hpn, hpt⟩, -⟩ := hfr rfl
      have hmem : (n, s.now) ∈ sC.issued := by rw [c2, hB.2.1]; simp
      have := iC.n3 p hp _ hmem hpn
      rw [c1, hB.1] at hpt
      simp only at this; omega
    have hreq : step A W full sC (.request k ⟨c, n, k⟩) = sC := by simp only [step]; rw [if_neg hnp]
    have hnrel : ¬ ∃ e ∈ sC.rels, e.1 = k := by
      rintro ⟨e, he, hek⟩; rw [c3, hB.2.2.1] at he; exact hno e he hek
    have hdec : step A W full sC (.decrypt k) = sC := by
      simp only [step]; split
      · rfl
      · rw [if_neg hnrel]
    have hrun : run A W full s (honestRound k c D s) = sC := by
      simp only [honestRound, run_append, run_cons]
      show step A W full (step A W full sC (.request k ⟨c, n, k⟩)) (.decrypt k) = sC
      rw [hreq, hdec]
    rw [hrun]
    first | rw [c3, hB.2.2.1] | rw [c4, hB.2.2.2]

/-- `m` honest rounds, each delayed by D ticks -/
def starveRuns (A : List ℕ) (W k c D : ℕ) : ℕ → St → St
  | 0, s => s
  | m + 1, s => starveRuns A W k c D m (run A W full s (honestRound k c D s))

/-- **Tick starvation.** If the scheduler delays every honest round by D > W ticks between the nonce issue and the
request, the honest workload gets no release and no decrypt, for every number of rounds. W must exceed the
worst-case scheduling delay. -/
theorem tick_starvation (A : List ℕ) (W : ℕ) (k c D : ℕ) (hD : W < D) (m : ℕ) (s : St) (hs : Inv W s)
    (hno : ∀ e ∈ s.rels, e.1 ≠ k) :
    (starveRuns A W k c D m s).rels = s.rels ∧ (starveRuns A W k c D m s).decs = s.decs := by
  induction m generalizing s with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := round_starves A W s hs k c D hD hno
    obtain ⟨i1, i2⟩ := ih _ h3 (by rw [h1]; exact hno)
    exact ⟨i1.trans h1, i2.trans h2⟩

/-- the starvation theorem applies from the start: a fresh deployment with the honest session spawned -/
theorem starvation_example (m : ℕ) :
    (starveRuns A0 2 0 1 3 m (run A0 2 full (init [1]) [.spawn 1])).decs = [] := by
  have hs : Inv 2 (run A0 2 full (init [1]) [.spawn 1]) := run_inv A0 2 _ _ (inv_init 2 [1])
  rw [(tick_starvation A0 2 0 1 3 (by norm_num) m _ hs (by decide)).2]
  decide

end ControlStack.AttestedLiveness

#print axioms ControlStack.AttestedLiveness.progress_interleaved
#print axioms ControlStack.AttestedLiveness.expiry_blocks
#print axioms ControlStack.AttestedLiveness.expiry_ok
#print axioms ControlStack.AttestedLiveness.revocation_blocks
#print axioms ControlStack.AttestedLiveness.death_blocks
#print axioms ControlStack.AttestedLiveness.nonce_theft_blocks
#print axioms ControlStack.AttestedLiveness.round_starves
#print axioms ControlStack.AttestedLiveness.tick_starvation
#print axioms ControlStack.AttestedLiveness.starvation_example
