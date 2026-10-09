/-
Attestation-gated release of the model-weight key on CC-mode GPU nodes (STACK-MAP: "attestation-gated weight-key
release"). MODEL ONLY: a protocol-level state machine, not a model of any vendor's attestation format.

A key broker holds the weight-decryption key. It releases the key, wrapped to a session public key, only against an
attestation report that is:
- genuine: signed by the TEE (`sig`);
- fresh: carries a broker-issued nonce, unused and not expired after W ticks (`fresh`);
- allowlisted: its measurement (code digest) is on the allowlist (`allow`);
- session-bound: the report binds the session key the release is wrapped to (`bind`).
Weights are decrypted only by a live session that holds the private key of a released wrapping key.

Actors, all through `step`, interleaved arbitrarily:
- honest attested workloads;
- an adversary who can spawn sessions running any (unattested) code, replay any genuine report, present reports for
  other measurements, request on behalf of other sessions (any `pk`), and present arbitrary reports where signatures
  are not checked;
- the environment: `compromise` (a session's private key becomes known to the adversary, e.g. a torn-down session
  that was not scrubbed) and `modify` (post-attestation code change, refused under TEE integrity);
- admins: allowlist add and revoke.
Session keys are allocated fresh (`nextKey`); a session's identity is its key.

Results, all under the full checks (`full`):
- `weights_only_in_attested`: every decrypt event (session k, code c) has an earlier release step j, a request
  wrapping to k, at which the report was genuine, fresh (issued, unused, unexpired), allowlisted and bound to k. The
  decrypting code c IS the attested measurement (TEE integrity).
- `no_debug_decrypt` / `allow_clean`: if admins never allowlist a debug measurement, no debug build ever decrypts.
- `revocation_absorbing`: once a measurement is revoked, it is never re-allowlisted and no later release is made
  against it.
- `replay_window`: a release wrapped to a key compromised at time t_c happens no later than t_c + W. Freshness
  bounds the replay window. Releases made before the compromise are lost anyway: that is `key_custody`.
- `leak_needs_release`: the adversary decrypts only with a compromised key that was released.
- `honest_liveness`: from any reachable state, a live session running allowlisted code that runs [issue, quote,
  request, decrypt] decrypts.
Witnesses (each check is necessary):
- `replay_without_freshness`: a captured report of a session compromised at t = 0 is replayed at t = 3 > 0 + W; the
  key is released to the compromised key and the adversary decrypts.
- `relay_without_binding`: an attacker session (unattested code 9) presents an honest report; the key is wrapped to
  the attacker's key and code 9 decrypts.
- `debug_allowlisted`: an allowlist containing a debug-build measurement releases to the debug build, which decrypts
  (plaintext exportable).
- `toctou_without_integrity`: the code is changed after attestation; code 9, never attested, decrypts.

Premises (ledger `attestedKeyLedger`), each environment unless stated:
- TEE integrity and measurement correctness: a quote reports the code actually running, and code cannot change
  after launch;
- signature unforgeability (issuer_authenticity): only TEE quotes are genuine;
- broker key custody (key_custody): the weight key leaves the broker only wrapped, by `request`;
- nonce unpredictability: a quote can carry only an already-issued nonce;
- allowlist hygiene: no debug builds (organisational).
No novelty is claimed: this is the standard remote-attestation key-release pattern.
-/
import Mathlib.Tactic
import ControlStack.Core.Cert

namespace ControlStack.AttestedKeyRelease

/-! ## Model -/

/-- an attestation report: measurement (code digest), nonce, bound session key -/
structure Report where
  meas : ℕ
  nonce : ℕ
  bound : ℕ
deriving DecidableEq, Repr

/-- which checks the broker and the TEE enforce -/
structure Cfg where
  sig : Bool
  fresh : Bool
  allow : Bool
  bind : Bool
  integrity : Bool
deriving DecidableEq, Repr

def full : Cfg := ⟨true, true, true, true, true⟩

structure St where
  now : ℕ
  nextNonce : ℕ
  /-- (nonce, issue time) -/
  issued : List (ℕ × ℕ)
  used : List ℕ
  allow : List ℕ
  revoked : List ℕ
  nextKey : ℕ
  /-- live sessions: (session key, code currently running) -/
  sessions : List (ℕ × ℕ)
  /-- genuine TEE quotes -/
  reports : List Report
  /-- releases: (wrapped-to key, report, time) -/
  rels : List (ℕ × Report × ℕ)
  /-- decrypt events: (session key, code at decrypt, time) -/
  decs : List (ℕ × ℕ × ℕ)
  /-- compromised keys: (key, time) -/
  adv : List (ℕ × ℕ)
  /-- adversary decrypts: (key, time) -/
  leaks : List (ℕ × ℕ)
deriving DecidableEq, Repr

inductive Op where
  | tick
  | issue
  | spawn (code : ℕ)
  | quote (k n : ℕ)
  | request (pk : ℕ) (r : Report)
  | decrypt (k : ℕ)
  | modify (k code : ℕ)
  | compromise (k : ℕ)
  | advDecrypt (k : ℕ)
  | allowAdd (caller m : ℕ)
  | revoke (caller m : ℕ)
deriving DecidableEq, Repr

def init (a0 : List ℕ) : St := ⟨0, 0, [], [], a0, [], 0, [], [], [], [], [], []⟩

/-- the code running in live session k -/
def codeOf (s : St) (k : ℕ) : Option ℕ := (s.sessions.find? (fun p => p.1 = k)).map Prod.snd

/-- the broker's release checks under configuration C -/
def Pass (C : Cfg) (W : ℕ) (s : St) (pk : ℕ) (r : Report) : Prop :=
  (C.sig = true → r ∈ s.reports) ∧
  (C.fresh = true → (∃ p ∈ s.issued, p.1 = r.nonce ∧ s.now ≤ p.2 + W) ∧ r.nonce ∉ s.used) ∧
  (C.allow = true → r.meas ∈ s.allow) ∧ (C.bind = true → r.bound = pk)

instance (C : Cfg) (W : ℕ) (s : St) (pk : ℕ) (r : Report) : Decidable (Pass C W s pk r) := by
  unfold Pass; infer_instance

def step (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) : Op → St
  | .tick => { s with now := s.now + 1 }
  | .issue => { s with issued := s.issued ++ [(s.nextNonce, s.now)], nextNonce := s.nextNonce + 1 }
  | .spawn c => { s with sessions := s.sessions ++ [(s.nextKey, c)], nextKey := s.nextKey + 1 }
  | .quote k n =>
    match codeOf s k with
    | none => s
    | some c => if ∃ p ∈ s.issued, p.1 = n then { s with reports := s.reports ++ [⟨c, n, k⟩] } else s
  | .request pk r =>
    if Pass C W s pk r then { s with rels := s.rels ++ [(pk, r, s.now)], used := s.used ++ [r.nonce] } else s
  | .decrypt k =>
    match codeOf s k with
    | none => s
    | some c => if ∃ e ∈ s.rels, e.1 = k then { s with decs := s.decs ++ [(k, c, s.now)] } else s
  | .modify k c =>
    if C.integrity then s else { s with sessions := s.sessions.map fun p => if p.1 = k then (k, c) else p }
  | .compromise k =>
    if (codeOf s k).isSome then
      { s with sessions := s.sessions.filter (fun p => p.1 ≠ k), adv := s.adv ++ [(k, s.now)] }
    else s
  | .advDecrypt k =>
    if (∃ a ∈ s.adv, a.1 = k) ∧ (∃ e ∈ s.rels, e.1 = k) then { s with leaks := s.leaks ++ [(k, s.now)] } else s
  | .allowAdd c m => if c ∈ A ∧ m ∉ s.revoked then { s with allow := s.allow ++ [m] } else s
  | .revoke c m =>
    if c ∈ A then { s with allow := s.allow.filter (fun x => x ≠ m), revoked := s.revoked ++ [m] } else s

def run (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (ops : List Op) : St := ops.foldl (step A W C) s

theorem run_snoc (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (l : List Op) (o : Op) :
    run A W C s (l ++ [o]) = step A W C (run A W C s l) o := by
  simp [run, List.foldl_append]

theorem codeOf_some {s : St} {k c : ℕ} (h : codeOf s k = some c) : (k, c) ∈ s.sessions := by
  unfold codeOf at h
  cases hf : s.sessions.find? (fun p => p.1 = k) with
  | none => rw [hf] at h; simp at h
  | some p =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hk : p.1 = k := by simpa using List.find?_some hf
    have hm := List.mem_of_find?_eq_some hf
    rw [← hk, ← h]; exact hm

theorem codeOf_of_mem {s : St} {k c : ℕ} (h : (k, c) ∈ s.sessions)
    (huniq : ∀ p ∈ s.sessions, ∀ q ∈ s.sessions, p.1 = q.1 → p.2 = q.2) : codeOf s k = some c := by
  unfold codeOf
  cases hf : s.sessions.find? (fun p => p.1 = k) with
  | none => rw [List.find?_eq_none] at hf; exact absurd (by simp) (hf _ h)
  | some p =>
    have hk : p.1 = k := by simpa using List.find?_some hf
    simp only [Option.map_some, Option.some.injEq]
    exact huniq p (List.mem_of_find?_eq_some hf) (k, c) h hk

/-! ## The invariant (full checks) -/

structure Inv (W : ℕ) (s : St) : Prop where
  n1 : ∀ p ∈ s.issued, p.1 < s.nextNonce
  n2 : ∀ p ∈ s.issued, p.2 ≤ s.now
  n3 : ∀ p ∈ s.issued, ∀ q ∈ s.issued, p.1 = q.1 → p.2 = q.2
  n4 : ∀ n ∈ s.used, n < s.nextNonce
  k0 : ∀ p ∈ s.sessions, ∀ q ∈ s.sessions, p.1 = q.1 → p.2 = q.2
  k1 : ∀ p ∈ s.sessions, p.1 < s.nextKey
  k2 : ∀ a ∈ s.adv, a.1 < s.nextKey
  k3 : ∀ p ∈ s.sessions, ∀ a ∈ s.adv, p.1 ≠ a.1
  r1 : ∀ r ∈ s.reports, r.bound < s.nextKey
  r2 : ∀ r ∈ s.reports, ∃ p ∈ s.issued, p.1 = r.nonce
  /-- TEE integrity: a live session's code is the measurement of every report bound to its key -/
  r3 : ∀ r ∈ s.reports, ∀ p ∈ s.sessions, p.1 = r.bound → p.2 = r.meas
  r4 : ∀ r ∈ s.reports, ∀ a ∈ s.adv, r.bound = a.1 → ∃ p ∈ s.issued, p.1 = r.nonce ∧ p.2 ≤ a.2
  v1 : ∀ m ∈ s.revoked, m ∉ s.allow
  e1 : ∀ e ∈ s.rels, e.2.1 ∈ s.reports ∧ e.2.1.bound = e.1
  e2 : ∀ e ∈ s.rels, e.2.2 ≤ s.now
  e3 : ∀ e ∈ s.rels, ∀ a ∈ s.adv, e.1 = a.1 → e.2.2 ≤ a.2 + W
  d1 : ∀ d ∈ s.decs, ∃ e ∈ s.rels, e.1 = d.1 ∧ e.2.1.meas = d.2.1
  l1 : ∀ l ∈ s.leaks, (∃ a ∈ s.adv, a.1 = l.1) ∧ ∃ e ∈ s.rels, e.1 = l.1

theorem inv_init (W : ℕ) (a0 : List ℕ) : Inv W (init a0) := by
  constructor <;> simp [init]

theorem step_inv (A : List ℕ) (W : ℕ) (s : St) (o : Op) (h : Inv W s) : Inv W (step A W full s o) := by
  cases o with
  | tick =>
    exact { h with n2 := fun p hp => Nat.le_succ_of_le (h.n2 p hp), e2 := fun e he => Nat.le_succ_of_le (h.e2 e he) }
  | issue =>
    refine { h with n1 := ?_, n2 := ?_, n3 := ?_, n4 := ?_, r2 := ?_, r4 := ?_ }
    · intro p hp; simp only [step, List.mem_append, List.mem_singleton] at hp ⊢
      rcases hp with hp | rfl
      · exact Nat.lt_succ_of_lt (h.n1 p hp)
      · exact Nat.lt_succ_self _
    · intro p hp; simp only [step, List.mem_append, List.mem_singleton] at hp ⊢
      rcases hp with hp | rfl
      · exact h.n2 p hp
      · exact le_rfl
    · intro p hp q hq hpq; simp only [step, List.mem_append, List.mem_singleton] at hp hq
      rcases hp with hp | rfl <;> rcases hq with hq | rfl
      · exact h.n3 p hp q hq hpq
      · have := h.n1 p hp; simp only at hpq; omega
      · have := h.n1 q hq; simp only at hpq; omega
      · rfl
    · intro n hn; exact Nat.lt_succ_of_lt (h.n4 n hn)
    · intro r hr; obtain ⟨p, hp, e⟩ := h.r2 r hr; exact ⟨p, List.mem_append_left _ hp, e⟩
    · intro r hr a ha hra; obtain ⟨p, hp, e, t⟩ := h.r4 r hr a ha hra
      exact ⟨p, List.mem_append_left _ hp, e, t⟩
  | spawn c =>
    refine { h with k0 := ?_, k1 := ?_, k2 := ?_, k3 := ?_, r1 := ?_, r3 := ?_ }
    · intro p hp q hq hpq; simp only [step, List.mem_append, List.mem_singleton] at hp hq
      rcases hp with hp | rfl <;> rcases hq with hq | rfl
      · exact h.k0 p hp q hq hpq
      · have := h.k1 p hp; simp only at hpq; omega
      · have := h.k1 q hq; simp only at hpq; omega
      · rfl
    · intro p hp; simp only [step, List.mem_append, List.mem_singleton] at hp ⊢
      rcases hp with hp | rfl
      · exact Nat.lt_succ_of_lt (h.k1 p hp)
      · exact Nat.lt_succ_self _
    · intro a ha; exact Nat.lt_succ_of_lt (h.k2 a ha)
    · intro p hp a ha; simp only [step, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact h.k3 p hp a ha
      · have := h.k2 a ha; simp only; omega
    · intro r hr; exact Nat.lt_succ_of_lt (h.r1 r hr)
    · intro r hr p hp hpr; simp only [step, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact h.r3 r hr p hp hpr
      · have := h.r1 r hr; simp only at hpr; omega
  | quote k n =>
    simp only [step]
    split
    · exact h
    · rename_i c hc
      split_ifs with hn
      · have hkc := codeOf_some hc
        refine { h with r1 := ?_, r2 := ?_, r3 := ?_, r4 := ?_, e1 := ?_ }
        · intro r hr; simp only [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact h.r1 r hr
          · exact h.k1 _ hkc
        · intro r hr; simp only [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact h.r2 r hr
          · exact hn
        · intro r hr p hp hpr; simp only [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact h.r3 r hr p hp hpr
          · exact h.k0 p hp (k, c) hkc hpr
        · intro r hr a ha hra; simp only [List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact h.r4 r hr a ha hra
          · exact absurd hra (h.k3 _ hkc a ha)
        · intro e he; obtain ⟨h1, h2⟩ := h.e1 e he; exact ⟨List.mem_append_left _ h1, h2⟩
      · exact h
  | request pk r =>
    simp only [step]
    split_ifs with hp
    · obtain ⟨hsig, hfr, _, hbind⟩ := hp
      obtain ⟨⟨q, hq, hqn, hqt⟩, _⟩ := hfr rfl
      refine { h with n4 := ?_, e1 := ?_, e2 := ?_, e3 := ?_, d1 := ?_, l1 := ?_ }
      · intro n hn; simp only [List.mem_append, List.mem_singleton] at hn
        rcases hn with hn | rfl
        · exact h.n4 n hn
        · rw [← hqn]; exact h.n1 q hq
      · intro e he; simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact h.e1 e he
        · exact ⟨hsig rfl, hbind rfl⟩
      · intro e he; simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact h.e2 e he
        · exact le_rfl
      · intro e he a ha hea; simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact h.e3 e he a ha hea
        · obtain ⟨p, hp, hpn, hpt⟩ := h.r4 r (hsig rfl) a ha ((hbind rfl).trans hea)
          have := h.n3 p hp q hq (hpn.trans hqn.symm)
          simp only; omega
      · intro d hd; obtain ⟨e, he, h1, h2⟩ := h.d1 d hd; exact ⟨e, List.mem_append_left _ he, h1, h2⟩
      · intro l hl; obtain ⟨h1, e, he, h2⟩ := h.l1 l hl; exact ⟨h1, e, List.mem_append_left _ he, h2⟩
    · exact h
  | decrypt k =>
    simp only [step]
    split
    · exact h
    · rename_i c hc
      split_ifs with hr
      · refine { h with d1 := ?_ }
        intro d hd; simp only [List.mem_append, List.mem_singleton] at hd
        rcases hd with hd | rfl
        · exact h.d1 d hd
        · obtain ⟨e, he, hek⟩ := hr
          obtain ⟨hrep, hb⟩ := h.e1 e he
          exact ⟨e, he, hek, (h.r3 _ hrep (k, c) (codeOf_some hc) (hb.trans hek).symm).symm⟩
      · exact h
  | modify k c => exact h
  | compromise k =>
    simp only [step]
    split_ifs with hk
    · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hk
      have hkc := codeOf_some hc
      refine { h with k0 := ?_, k1 := ?_, k2 := ?_, k3 := ?_, r3 := ?_, r4 := ?_, e3 := ?_, d1 := ?_, l1 := ?_ }
      · intro p hp q hq; exact h.k0 p (List.mem_filter.1 hp).1 q (List.mem_filter.1 hq).1
      · intro p hp; exact h.k1 p (List.mem_filter.1 hp).1
      · intro a ha; simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact h.k2 a ha
        · exact h.k1 (k, c) hkc
      · intro p hp a ha; simp only [List.mem_append, List.mem_singleton] at ha
        have hp' := List.mem_filter.1 hp
        rcases ha with ha | rfl
        · exact h.k3 p hp'.1 a ha
        · simpa using hp'.2
      · intro r hr p hp; exact h.r3 r hr p (List.mem_filter.1 hp).1
      · intro r hr a ha hra; simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · obtain ⟨p, hp, e, t⟩ := h.r4 r hr a ha hra; exact ⟨p, hp, e, t⟩
        · obtain ⟨p, hp, e⟩ := h.r2 r hr; exact ⟨p, hp, e, h.n2 p hp⟩
      · intro e he a ha hea; simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact h.e3 e he a ha hea
        · have := h.e2 e he; simp only; omega
      · intro d hd; exact h.d1 d hd
      · intro l hl; obtain ⟨⟨a, ha, h1⟩, h2⟩ := h.l1 l hl; exact ⟨⟨a, List.mem_append_left _ ha, h1⟩, h2⟩
    · exact h
  | advDecrypt k =>
    simp only [step]
    split_ifs with hk
    · refine { h with l1 := ?_ }
      intro l hl; simp only [List.mem_append, List.mem_singleton] at hl
      rcases hl with hl | rfl
      · exact h.l1 l hl
      · exact hk
    · exact h
  | allowAdd c m =>
    simp only [step]
    split_ifs with hc
    · refine { h with v1 := ?_ }
      intro x hx hxa; simp only [List.mem_append, List.mem_singleton] at hxa
      rcases hxa with hxa | rfl
      · exact h.v1 x hx hxa
      · exact hc.2 hx
    · exact h
  | revoke c m =>
    simp only [step]
    split_ifs with hc
    · refine { h with v1 := ?_ }
      intro x hx hxa; simp only [List.mem_append, List.mem_singleton] at hx
      have := List.mem_filter.1 hxa
      rcases hx with hx | rfl
      · exact h.v1 x hx this.1
      · simp at this
    · exact h

theorem run_inv (A : List ℕ) (W : ℕ) (s : St) (ops : List Op) (h : Inv W s) : Inv W (run A W full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => exact ih _ (step_inv A W s o h)

/-! ## Releases happen only at passing request steps -/

theorem step_rels (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (o : Op) :
    ∀ e ∈ (step A W C s o).rels, e ∈ s.rels ∨ ∃ pk r, o = .request pk r ∧ Pass C W s pk r ∧ e = (pk, r, s.now) := by
  intro e he
  cases o with
  | request pk r =>
    simp only [step] at he
    split_ifs at he with hp
    · rcases List.mem_append.1 he with he | he
      · exact Or.inl he
      · simp only [List.mem_singleton] at he; exact Or.inr ⟨pk, r, rfl, hp, he⟩
    · exact Or.inl he
  | _ =>
    left
    simp only [step] at he
    repeat' split at he
    all_goals exact he

/-- **Release soundness (trace form).** Every release is an earlier `request` step at which the checks passed, in
the state reached by the trace prefix before that step. -/
theorem rels_sound (A : List ℕ) (W : ℕ) (C : Cfg) (s0 : St) (ops : List Op) :
    ∀ e ∈ (run A W C s0 ops).rels, e ∈ s0.rels ∨
      ∃ j, ∃ hj : j < ops.length, ops[j] = .request e.1 e.2.1 ∧ Pass C W (run A W C s0 (ops.take j)) e.1 e.2.1 ∧
        e.2.2 = (run A W C s0 (ops.take j)).now := by
  induction ops using List.reverseRecOn with
  | nil => intro e he; exact Or.inl he
  | append_singleton l o ih =>
    intro e he
    rw [run_snoc] at he
    rcases step_rels A W C _ o e he with he | ⟨pk, r, rfl, hp, rfl⟩
    · rcases ih e he with h | ⟨j, hj, h1, h2, h3⟩
      · exact Or.inl h
      · refine Or.inr ⟨j, by simp; omega, ?_, ?_, ?_⟩
        · rw [List.getElem_append_left hj]; exact h1
        · rw [List.take_append_of_le_length hj.le]; exact h2
        · rw [List.take_append_of_le_length hj.le]; exact h3
    · refine Or.inr ⟨l.length, by simp, by simp, ?_, ?_⟩
      · simp only [List.take_left']; exact hp
      · simp only [List.take_left']

/-- the full checks, spelled out -/
def Attested (W : ℕ) (s : St) (pk : ℕ) (r : Report) : Prop :=
  r ∈ s.reports ∧ (∃ p ∈ s.issued, p.1 = r.nonce ∧ s.now ≤ p.2 + W) ∧ r.nonce ∉ s.used ∧ r.meas ∈ s.allow ∧
    r.bound = pk

theorem pass_full (W : ℕ) (s : St) (pk : ℕ) (r : Report) (h : Pass full W s pk r) : Attested W s pk r :=
  ⟨h.1 rfl, (h.2.1 rfl).1, (h.2.1 rfl).2, h.2.2.1 rfl, h.2.2.2 rfl⟩

/-! ## Main results -/

/-- **Weights only in attested sessions.** For every legal trace from the initial state (any adversary
interleaving), every decrypt event (session k, code c, time) has an earlier release step j, a request wrapping to k
with a report r. At step j, r was genuine, carried a broker-issued nonce that was unused and unexpired, had an
allowlisted measurement, and was bound to k. The decrypting code c is r's measurement. -/
theorem weights_only_in_attested (A : List ℕ) (W : ℕ) (a0 : List ℕ) (ops : List Op) :
    ∀ d ∈ (run A W full (init a0) ops).decs, ∃ j, ∃ hj : j < ops.length, ∃ r : Report,
      ops[j] = .request d.1 r ∧ Attested W (run A W full (init a0) (ops.take j)) d.1 r ∧ r.meas = d.2.1 := by
  intro d hd
  obtain ⟨e, he, hed, hem⟩ := (run_inv A W _ ops (inv_init W a0)).d1 d hd
  rcases rels_sound A W full (init a0) ops e he with h | ⟨j, hj, h1, h2, -⟩
  · simp [init] at h
  · exact ⟨j, hj, e.2.1, hed ▸ h1, hed ▸ pass_full W _ _ _ h2, hem⟩

/-- **Allowlist hygiene suffices against debug builds**: if the initial allowlist has no debug measurement and no
`allowAdd` in the trace adds one, then every prefix's allowlist is clean -/
theorem allow_clean (A : List ℕ) (W : ℕ) (C : Cfg) (debug : List ℕ) (s : St) (ops : List Op)
    (h0 : ∀ m ∈ s.allow, m ∉ debug) (hops : ∀ c m, Op.allowAdd c m ∈ ops → m ∉ debug) :
    ∀ m ∈ (run A W C s ops).allow, m ∉ debug := by
  induction ops generalizing s with
  | nil => exact h0
  | cons o ops ih =>
    apply ih
    · intro m hm
      cases o with
      | allowAdd c m' =>
        simp only [step] at hm
        split_ifs at hm
        · rcases List.mem_append.1 hm with hm | hm
          · exact h0 m hm
          · simp only [List.mem_singleton] at hm; subst hm; exact hops c _ List.mem_cons_self
        · exact h0 m hm
      | revoke c m' =>
        simp only [step] at hm
        split_ifs at hm
        · exact h0 m (List.mem_filter.1 hm).1
        · exact h0 m hm
      | _ =>
        simp only [step] at hm
        repeat' split at hm
        all_goals exact h0 m hm
    · intro c m hm; exact hops c m (List.mem_cons_of_mem _ hm)

/-- **No debug build decrypts** when admins never allowlist one -/
theorem no_debug_decrypt (A : List ℕ) (W : ℕ) (a0 debug : List ℕ) (ops : List Op) (h0 : ∀ m ∈ a0, m ∉ debug)
    (hops : ∀ c m, Op.allowAdd c m ∈ ops → m ∉ debug) :
    ∀ d ∈ (run A W full (init a0) ops).decs, d.2.1 ∉ debug := by
  intro d hd
  obtain ⟨j, hj, r, -, hatt, hm⟩ := weights_only_in_attested A W a0 ops d hd
  rw [← hm]
  exact allow_clean A W full debug (init a0) (ops.take j) h0
    (fun c m hm => hops c m (List.mem_of_mem_take hm)) _ hatt.2.2.2.1

theorem revoked_mono (A : List ℕ) (W : ℕ) (C : Cfg) (s : St) (ops : List Op) (m : ℕ) (hm : m ∈ s.revoked) :
    m ∈ (run A W C s ops).revoked := by
  induction ops generalizing s with
  | nil => exact hm
  | cons o ops ih =>
    apply ih
    cases o with
    | revoke c m' =>
      simp only [step]; split_ifs
      · exact List.mem_append_left _ hm
      · exact hm
    | _ =>
      simp only [step]
      repeat' split
      all_goals exact hm

/-- **Revocation is absorbing per measurement.** From a reachable state where m is revoked, m is never allowlisted
again, and every later release is against a different measurement. -/
theorem revocation_absorbing (A : List ℕ) (W : ℕ) (s : St) (hs : Inv W s) (m : ℕ) (hm : m ∈ s.revoked)
    (ops : List Op) :
    m ∉ (run A W full s ops).allow ∧ ∀ e ∈ (run A W full s ops).rels, e ∈ s.rels ∨ e.2.1.meas ≠ m := by
  refine ⟨(run_inv A W s ops hs).v1 m (revoked_mono A W full s ops m hm), fun e he => ?_⟩
  rcases rels_sound A W full s ops e he with h | ⟨j, hj, -, h2, -⟩
  · exact Or.inl h
  · right
    intro hem
    have hinv := run_inv A W s (ops.take j) hs
    have hrev := revoked_mono A W full s (ops.take j) m hm
    exact hinv.v1 m hrev (hem ▸ (pass_full W _ _ _ h2).2.2.2.1)

/-- **Freshness bounds the replay window.** In every reachable state, a release wrapped to a key compromised at time
t_c happened no later than t_c + W. Releases before the compromise are lost with the key: that is `key_custody`. -/
theorem replay_window (A : List ℕ) (W : ℕ) (a0 : List ℕ) (ops : List Op) :
    ∀ e ∈ (run A W full (init a0) ops).rels, ∀ a ∈ (run A W full (init a0) ops).adv, e.1 = a.1 → e.2.2 ≤ a.2 + W :=
  (run_inv A W _ ops (inv_init W a0)).e3

/-- the adversary decrypts only with a compromised key to which the weight key was released -/
theorem leak_needs_release (A : List ℕ) (W : ℕ) (a0 : List ℕ) (ops : List Op) :
    ∀ l ∈ (run A W full (init a0) ops).leaks, (∃ a ∈ (run A W full (init a0) ops).adv, a.1 = l.1) ∧
      ∃ e ∈ (run A W full (init a0) ops).rels, e.1 = l.1 :=
  (run_inv A W _ ops (inv_init W a0)).l1

/-- **Honest liveness.** From any reachable state, a live session k running allowlisted code c that runs the honest
protocol (broker issues a nonce, the TEE quotes it, the workload requests with its own key, then decrypts) decrypts
the weights. -/
theorem honest_liveness (A : List ℕ) (W : ℕ) (s : St) (hs : Inv W s) (k c : ℕ) (hk : (k, c) ∈ s.sessions)
    (hc : c ∈ s.allow) :
    (k, c, s.now) ∈ (run A W full s
      [.issue, .quote k s.nextNonce, .request k ⟨c, s.nextNonce, k⟩, .decrypt k]).decs := by
  have hcode : codeOf s k = some c := codeOf_of_mem hk hs.k0
  set n := s.nextNonce
  set s1 := step A W full s .issue
  have h1 : codeOf s1 k = some c := hcode
  have hn1 : ∃ p ∈ s1.issued, p.1 = n := ⟨(n, s.now), by simp [s1, step, n], rfl⟩
  set s2 := step A W full s1 (.quote k n)
  have hs2 : s2 = { s1 with reports := s1.reports ++ [⟨c, n, k⟩] } := by
    simp only [s2, step, h1]; rw [if_pos hn1]
  have hpass : Pass full W s2 k ⟨c, n, k⟩ := by
    rw [hs2]
    refine ⟨fun _ => by simp, fun _ => ⟨⟨(n, s.now), by simp [s1, step, n], rfl, by simp [s1, step]⟩, ?_⟩,
      fun _ => hc, fun _ => rfl⟩
    intro hu
    have := hs.n4 _ hu
    simp [n] at this
  set s3 := step A W full s2 (.request k ⟨c, n, k⟩)
  have hs3 : s3 = { s2 with rels := s2.rels ++ [(k, ⟨c, n, k⟩, s2.now)], used := s2.used ++ [n] } := by
    simp only [s3, step]; rw [if_pos hpass]
  have h3 : codeOf s3 k = some c := by rw [hs3, hs2]; exact h1
  have hrel : ∃ e ∈ s3.rels, e.1 = k := ⟨(k, ⟨c, n, k⟩, s2.now), by rw [hs3]; simp, rfl⟩
  show (k, c, s.now) ∈ (step A W full s3 (.decrypt k)).decs
  simp only [step, h3]
  rw [if_pos hrel]
  have : s3.now = s.now := by rw [hs3, hs2]; rfl
  simp [this]

/-! ## Witnesses: every check is necessary -/

/-- admin 0, expiry window W = 2; honest code 1, debug build 7, attacker code 9 -/
def A0 : List ℕ := [0]

/-- **Replay without freshness.** Session 0 (code 1) quotes nonce 0; its key is compromised at t = 0, before any
release. At t = 3 > 0 + W the adversary replays the captured report. Without the freshness check, the key is
wrapped to the compromised key and the adversary decrypts. With the full checks, nothing is released and nothing
leaks. -/
def replayTrace : List Op :=
  [.spawn 1, .issue, .quote 0 0, .compromise 0, .tick, .tick, .tick, .request 0 ⟨1, 0, 0⟩, .advDecrypt 0]

theorem replay_without_freshness :
    let bad := run A0 2 { full with fresh := false } (init [1]) replayTrace
    let good := run A0 2 full (init [1]) replayTrace
    bad.rels = [(0, ⟨1, 0, 0⟩, 3)] ∧ bad.adv = [(0, 0)] ∧ bad.leaks = [(0, 3)] ∧
      good.rels = [] ∧ good.leaks = [] := by
  decide

/-- **Relay without session binding.** An attacker session (key 1, unattested code 9) presents the honest session's
genuine, fresh, allowlisted report and asks for the key wrapped to ITS key. Without binding, the release goes to key
1 and code 9 decrypts. With binding, nothing is released. -/
def relayTrace : List Op := [.spawn 1, .spawn 9, .issue, .quote 0 0, .request 1 ⟨1, 0, 0⟩, .decrypt 1]

theorem relay_without_binding :
    (run A0 2 { full with bind := false } (init [1]) relayTrace).decs = [(1, 9, 0)] ∧
    (run A0 2 full (init [1]) relayTrace).decs = [] := by
  decide

/-- **Allowlist too broad.** With the debug build's measurement 7 on the allowlist, a debug-build session attests
and decrypts (its plaintext is exportable). With a clean allowlist it gets nothing. -/
def debugTrace : List Op := [.spawn 7, .issue, .quote 0 0, .request 0 ⟨7, 0, 0⟩, .decrypt 0]

theorem debug_allowlisted :
    (run A0 2 full (init [1, 7]) debugTrace).decs = [(0, 7, 0)] ∧ (run A0 2 full (init [1]) debugTrace).decs = [] := by
  decide

/-- **TOCTOU without TEE integrity.** Code 1 is attested and the key released; the code is then changed to 9 before
decryption. Without integrity, code 9, never attested and not allowlisted, decrypts. With integrity, the change is
refused and code 1 decrypts. -/
def toctouTrace : List Op := [.spawn 1, .issue, .quote 0 0, .request 0 ⟨1, 0, 0⟩, .modify 0 9, .decrypt 0]

theorem toctou_without_integrity :
    (run A0 2 { full with integrity := false } (init [1]) toctouTrace).decs = [(0, 9, 0)] ∧
    (run A0 2 full (init [1]) toctouTrace).decs = [(0, 1, 0)] := by
  decide

/-- **Revocation in action**: after measurement 1 is revoked, an attested request is refused and re-adding 1 is
refused -/
theorem revocation_example :
    (run A0 2 full (init [1])
      [.spawn 1, .revoke 0 1, .issue, .quote 0 0, .request 0 ⟨1, 0, 0⟩, .allowAdd 0 1, .issue, .quote 0 1,
        .request 0 ⟨1, 1, 0⟩, .decrypt 0]).rels = [] ∧
    (run A0 2 full (init [1]) [.spawn 1, .issue, .quote 0 0, .request 0 ⟨1, 0, 0⟩, .decrypt 0]).decs =
      [(0, 1, 0)] := by
  decide

/-! ## Premise ledger -/

open ControlStack.Cert in
def attestedKeyLedger : List (String × PremiseKind) :=
  [("weights only in attested sessions", .proofObligation "ControlStack.AttestedKeyRelease.weights_only_in_attested"),
   ("revocation absorbing per measurement",
     .proofObligation "ControlStack.AttestedKeyRelease.revocation_absorbing"),
   ("freshness bounds the replay window", .proofObligation "ControlStack.AttestedKeyRelease.replay_window"),
   ("honest liveness", .proofObligation "ControlStack.AttestedKeyRelease.honest_liveness"),
   ("TEE integrity and measurement correctness: quotes report the running code; no post-launch code change",
     .environment),
   ("signature unforgeability: only TEE quotes verify (issuer_authenticity)", .environment),
   ("broker key custody: the weight key leaves the broker only wrapped, via request (key_custody)", .environment),
   ("nonce unpredictability: quotes carry only already-issued nonces", .environment),
   ("allowlist hygiene: no debug-build measurement is allowlisted", .organisational),
   ("broker and TEE implementation conform to this model", .correspondence)]

end ControlStack.AttestedKeyRelease

#print axioms ControlStack.AttestedKeyRelease.step_inv
#print axioms ControlStack.AttestedKeyRelease.rels_sound
#print axioms ControlStack.AttestedKeyRelease.weights_only_in_attested
#print axioms ControlStack.AttestedKeyRelease.no_debug_decrypt
#print axioms ControlStack.AttestedKeyRelease.revocation_absorbing
#print axioms ControlStack.AttestedKeyRelease.replay_window
#print axioms ControlStack.AttestedKeyRelease.leak_needs_release
#print axioms ControlStack.AttestedKeyRelease.honest_liveness
#print axioms ControlStack.AttestedKeyRelease.replay_without_freshness
#print axioms ControlStack.AttestedKeyRelease.relay_without_binding
#print axioms ControlStack.AttestedKeyRelease.debug_allowlisted
#print axioms ControlStack.AttestedKeyRelease.toctou_without_integrity
#print axioms ControlStack.AttestedKeyRelease.revocation_example

#eval IO.println (ControlStack.Cert.ledgerJson ControlStack.AttestedKeyRelease.attestedKeyLedger)
