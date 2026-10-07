/-
Lean model of the covert-channel gateway (`gateway/gateway.py`) and its end-to-end guarantee.

One channel with schema S (finite) and `slots` slots. The sender emits a trace of RAW actions from an arbitrary finite
alphabet R (bounded length L): each action is a send attempt validated by `valid : R → Option S`, or anything else.
`run` is the gateway: it appends accepted values while slots remain, and on ANY refusal (invalid payload, slot overflow,
side action) it blanks the episode. `deliver` gives the receiver `Fin slots → Option S` (NULL = none).

`gateway_bound`: for every shared seed, every randomised adaptive encoder producing raw traces, and every decoder of the
delivered view, P(recover a uniform secret) ≤ (|S| + 1)^slots / |M|. The proof pushes the trace law through `deliver ∘ run`
and applies `Covert.covert_bound`; nothing about the encoder is assumed.
-/
import ControlStack.CovertChannel

namespace ControlStack.GatewayModel

open ControlStack.Covert

/-- raw sender actions: a send attempt with an arbitrary payload, or any other action (denied) -/
inductive Act (R : Type) where
  | send : R → Act R
  | other : Act R
  deriving DecidableEq, Fintype

/-- gateway state: accepted values (in order) and whether the episode has been blanked -/
structure St (S : Type) where
  buf : List S
  blanked : Bool

/-- one gateway step -/
def step {R S : Type} (valid : R → Option S) (slots : ℕ) (st : St S) : Act R → St S
  | .other => { st with blanked := true }
  | .send r =>
    match valid r with
    | none => { st with blanked := true }
    | some v => if st.buf.length < slots then { st with buf := st.buf ++ [v] } else { st with blanked := true }

/-- run a whole trace from the empty state -/
def run {R S : Type} (valid : R → Option S) (slots : ℕ) (tr : List (Act R)) : St S :=
  tr.foldl (step valid slots) ⟨[], false⟩

/-- what the receiver sees -/
def deliver {S : Type} (slots : ℕ) (st : St S) : Fin slots → Option S :=
  fun i => if st.blanked then none else st.buf[i.val]?

/-- Any refusal anywhere in the trace blanks the delivery. -/
theorem blank_absorbing {R S : Type} (valid : R → Option S) (slots : ℕ) (tr : List (Act R)) (st : St S)
    (h : st.blanked = true) : (tr.foldl (step valid slots) st).blanked = true := by
  induction tr generalizing st with
  | nil => simpa
  | cons a tr ih =>
    apply ih
    cases a with
    | other => rfl
    | send r =>
      simp only [step]
      cases valid r with
      | none => rfl
      | some v => split_ifs <;> simp [h]

theorem other_blanks {R S : Type} (valid : R → Option S) (slots : ℕ) (pre post : List (Act R)) :
    deliver slots (run valid slots (pre ++ Act.other :: post)) = fun _ => none := by
  funext i
  have : (run valid slots (pre ++ Act.other :: post)).blanked = true := by
    unfold run
    rw [List.foldl_append, List.foldl_cons]
    exact blank_absorbing valid slots post _ rfl
  simp [deliver, this]

/-- pushforward of a trace law to a view law -/
noncomputable def push {T V : Type} [Fintype T] [DecidableEq V] (f : T → V) (p : T → ℝ) : V → ℝ :=
  fun v => ∑ t, if f t = v then p t else 0

theorem push_dist {T V : Type} [Fintype T] [Fintype V] [DecidableEq V] (f : T → V) (p : T → ℝ) (hp : IsDist p) :
    IsDist (push f p) := by
  refine ⟨fun v => Finset.sum_nonneg fun t _ => by split_ifs; exact hp.1 t; exact le_refl _, ?_⟩
  unfold push
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact hp.2

/-- **End-to-end gateway bound.** Traces of length L over raw actions `Act R`; any shared seed, any randomised
adaptive encoder of traces, any decoder of the delivered view: success ≤ (|S|+1)^slots / |M|. -/
theorem gateway_bound {Ω M R S : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R] [Fintype S] [DecidableEq S]
    (valid : R → Option S) (slots L : ℕ)
    (ρ : Ω → ℝ) (enc : Ω → M → (Fin L → Act R) → ℝ) (dec : Ω → (Fin slots → Option S) → M → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) :
    (∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ tr, enc ω m tr *
        dec ω (deliver slots (run valid slots (List.ofFn tr))) m))
      ≤ ((Fintype.card S : ℝ) + 1) ^ slots / (Fintype.card M : ℝ) := by
  classical
  set view : (Fin L → Act R) → (Fin slots → Option S) := fun tr => deliver slots (run valid slots (List.ofFn tr))
  have hpush : ∀ ω m, (∑ tr, enc ω m tr * dec ω (deliver slots (run valid slots (List.ofFn tr))) m) =
      ∑ v, push view (enc ω m) v * dec ω v m := by
    intro ω m
    unfold push
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun tr _ => ?_
    rw [Finset.sum_eq_single (view tr)]
    · simp [view]
    · intro v _ hv; simp [Ne.symm hv]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h := covert_bound ρ (fun ω m => push view (enc ω m)) dec hρ (fun ω m => push_dist _ _ (henc ω m)) hdec
  unfold successProb at h
  simp_rw [hpush]
  refine le_trans h (le_of_eq ?_)
  simp [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Nat.cast_pow]

/-- the buffer never exceeds the slot count -/
theorem buf_le {R S : Type} (valid : R → Option S) (slots : ℕ) (tr : List (Act R)) (st : St S)
    (h : st.buf.length ≤ slots) : (tr.foldl (step valid slots) st).buf.length ≤ slots := by
  induction tr generalizing st with
  | nil => simpa
  | cons a tr ih =>
    apply ih
    cases a with
    | other => simpa [step] using h
    | send r =>
      simp only [step]
      cases valid r with
      | none => simpa using h
      | some v =>
        split_ifs with hl
        · simp; omega
        · simpa using h

/-- reachable views: a prefix of j accepted values (j ≤ slots), the rest NULL -/
abbrev Prefix (S : Type) (slots : ℕ) := (j : Fin (slots + 1)) × (Fin j → S)

def toPrefix {S : Type} (slots : ℕ) (st : St S) (h : st.buf.length ≤ slots) : Prefix S slots :=
  if hb : st.blanked then ⟨0, fun i => i.elim0⟩
  else ⟨⟨st.buf.length, by omega⟩, fun i => st.buf.get ⟨i.val, i.isLt⟩⟩

def embedPrefix {S : Type} (slots : ℕ) (p : Prefix S slots) : Fin slots → Option S :=
  fun i => if h : i.val < p.1.val then some (p.2 ⟨i.val, h⟩) else none

theorem deliver_eq_embed {S : Type} (slots : ℕ) (st : St S) (h : st.buf.length ≤ slots) :
    deliver slots st = embedPrefix slots (toPrefix slots st h) := by
  funext i
  by_cases hb : st.blanked
  · simp [deliver, embedPrefix, toPrefix, hb]
  · have e : toPrefix slots st h = ⟨⟨st.buf.length, by omega⟩, fun i => st.buf.get ⟨i.val, i.isLt⟩⟩ := by
      simp [toPrefix, hb]
    rw [e]
    unfold deliver embedPrefix
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    by_cases hi : i.val < st.buf.length
    · simp [hi]
    · simp [hi, List.getElem?_eq_none (by omega)]

/-- **Reachable-view bound (review P1-3).** Success ≤ (Σ_{j ≤ slots} |S|^j) / |M|, tighter than (|S|+1)^slots / |M|. -/
theorem gateway_bound_reachable {Ω M R S : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R] [Fintype S]
    [DecidableEq S] (valid : R → Option S) (slots L : ℕ)
    (ρ : Ω → ℝ) (enc : Ω → M → (Fin L → Act R) → ℝ) (dec : Ω → (Fin slots → Option S) → M → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) :
    (∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ tr, enc ω m tr *
        dec ω (deliver slots (run valid slots (List.ofFn tr))) m))
      ≤ (∑ j : Fin (slots + 1), (Fintype.card S : ℝ) ^ (j : ℕ)) / (Fintype.card M : ℝ) := by
  classical
  have hlen : ∀ tr : Fin L → Act R, (run valid slots (List.ofFn tr)).buf.length ≤ slots :=
    fun tr => buf_le valid slots _ _ (by simp)
  set pv : (Fin L → Act R) → Prefix S slots := fun tr => toPrefix slots _ (hlen tr)
  have hview : ∀ tr, deliver slots (run valid slots (List.ofFn tr)) = embedPrefix slots (pv tr) :=
    fun tr => deliver_eq_embed slots _ (hlen tr)
  have hpush : ∀ ω m, (∑ tr, enc ω m tr * dec ω (deliver slots (run valid slots (List.ofFn tr))) m) =
      ∑ v, push pv (enc ω m) v * dec ω (embedPrefix slots v) m := by
    intro ω m
    unfold push
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun tr _ => ?_
    rw [Finset.sum_eq_single (pv tr)]
    · simp [hview tr]
    · intro v _ hv; simp [Ne.symm hv]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h := covert_bound ρ (fun ω m => push pv (enc ω m)) (fun ω v => dec ω (embedPrefix slots v)) hρ
    (fun ω m => push_dist _ _ (henc ω m)) (fun ω v => hdec ω _)
  unfold successProb at h
  simp_rw [hpush]
  refine le_trans h (le_of_eq ?_)
  congr 1
  simp [Prefix, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin, Nat.cast_sum, Nat.cast_pow]

#print axioms gateway_bound_reachable
#print axioms other_blanks
#print axioms gateway_bound

end ControlStack.GatewayModel
