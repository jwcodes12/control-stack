/-
Multi-channel gateway core matching `gateway/gateway.py` (`Gateway.send/act/close/deliver`), extending the
single-channel `GatewayModel`.

Events on raw traces: `send (some c) r` (a send attempt on channel c with raw payload r), `send none r` (unknown
channel), `other` (any side action, `act`), `close`. Semantics, as in the Python:
- after `close` the snapshot is frozen: every later event leaves the state unchanged (`AFTER_CLOSE`);
- before `close`: unknown channel, `other`, slot overflow or a payload rejected by `valid c` blank the episode;
  otherwise the validated value is appended to channel c;
- `close` snapshots: a blanked episode delivers all-NULL on every channel, otherwise each channel delivers its accepted
  values padded with NULL. If the trace never closes, the trusted harness closes at the end (`finalView`).

Proved (standard axioms):
- `refusal_blanks`: a refusal before close makes the final view all-NULL on every channel;
- `close_freezes`: events after close never change the final view;
- `view_reachable`: every final view lies in the image of the prefix tuples, whose number is
  `viewSpace slots S = ∏_c Σ_{j ≤ slots c} |S c|^j` (`card_prefixes`), exactly the Python `view_space_size`;
- `core_bound`: for every shared seed, adaptive randomised encoder of raw event traces of any fixed length and any
  decoder, P(recover a uniform secret on M) ≤ viewSpace / |M|.
-/
import ControlStack.GatewayModel

namespace ControlStack.GatewayCore

open ControlStack.Covert ControlStack.GatewayModel

inductive Ev (C : ℕ) (R : Type) where
  | send : Option (Fin C) → R → Ev C R
  | other : Ev C R
  | close : Ev C R

variable {C : ℕ} {R : Type} {S : Fin C → Type} {slots : Fin C → ℕ}

abbrev View (S : Fin C → Type) (slots : Fin C → ℕ) := (c : Fin C) → Fin (slots c) → Option (S c)

structure GSt (S : Fin C → Type) (slots : Fin C → ℕ) where
  buf : (c : Fin C) → List (S c)
  blanked : Bool
  snap : Option (View S slots)

/-- channel c's single-channel state -/
def chan (st : GSt S slots) (c : Fin C) : St (S c) := ⟨st.buf c, st.blanked⟩

/-- the view a close would deliver now -/
def viewOf (st : GSt S slots) : View S slots := fun c => deliver (slots c) (chan st c)

def gstep (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (e : Ev C R) : GSt S slots :=
  match st.snap with
  | some _ => st
  | none =>
    match e with
    | .other => { st with blanked := true }
    | .close => { st with snap := some (viewOf st) }
    | .send none _ => { st with blanked := true }
    | .send (some c) r =>
      if (st.buf c).length < slots c then
        match valid c r with
        | none => { st with blanked := true }
        | some v => { st with buf := Function.update st.buf c (st.buf c ++ [v]) }
      else { st with blanked := true }

def init : GSt S slots := ⟨fun _ => [], false, none⟩

def runG (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (tr : List (Ev C R)) : GSt S slots :=
  tr.foldl (gstep valid) st

/-- what the receiver gets: the snapshot, or the harness's close at the end of the trace -/
def finalView (st : GSt S slots) : View S slots := st.snap.getD (viewOf st)

/-! ### Blanking and freezing -/

lemma frozen (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (v : View S slots)
    (h : st.snap = some v) (tr : List (Ev C R)) : runG valid st tr = st := by
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    unfold runG at ih ⊢
    rw [List.foldl_cons]
    have : gstep valid st e = st := by unfold gstep; rw [h]
    rw [this]; exact ih

/-- **Close freezes the delivery.** -/
theorem close_freezes (valid : (c : Fin C) → R → Option (S c)) (pre post : List (Ev C R)) :
    finalView (runG valid (init (S := S) (slots := slots)) (pre ++ .close :: post)) =
      finalView (runG valid (init (S := S) (slots := slots)) (pre ++ [.close])) := by
  unfold runG
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil]
  set st := pre.foldl (gstep valid) (init (S := S) (slots := slots))
  cases hs : st.snap with
  | some v =>
    have h1 : gstep valid st .close = st := by unfold gstep; rw [hs]
    rw [h1]
    exact congrArg finalView (frozen valid st v hs post)
  | none =>
    have h1 : (gstep valid st .close).snap = some (viewOf st) := by unfold gstep; rw [hs]
    exact congrArg finalView (frozen valid _ _ h1 post)

/-- the all-NULL view -/
def nullView : View S slots := fun _ _ => none

lemma blanked_stays (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (hb : st.blanked = true)
    (hs : st.snap = none ∨ st.snap = some nullView) (tr : List (Ev C R)) :
    (runG valid st tr).blanked = true ∧
      ((runG valid st tr).snap = none ∨ (runG valid st tr).snap = some nullView) := by
  induction tr generalizing st with
  | nil => exact ⟨hb, hs⟩
  | cons e tr ih =>
    unfold runG; rw [List.foldl_cons]
    apply ih
    · unfold gstep
      cases st.snap with
      | some _ => exact hb
      | none =>
        cases e with
        | other => rfl
        | close => exact hb
        | send oc r =>
          cases oc with
          | none => rfl
          | some c =>
            simp only
            split_ifs
            · cases valid c r <;> simp [hb]
            · rfl
    · rcases hs with hs | hs
      · unfold gstep; rw [hs]
        cases e with
        | other => left; rfl
        | close =>
          right
          show some (viewOf st) = some nullView
          congr 1; funext c i; simp [viewOf, deliver, chan, hb, nullView]
        | send oc r =>
          left
          cases oc with
          | none => rfl
          | some c =>
            simp only
            split_ifs
            · cases valid c r <;> rfl
            · rfl
      · right; simp [gstep, hs]

lemma finalView_blanked (st : GSt S slots) (hb : st.blanked = true)
    (hs : st.snap = none ∨ st.snap = some nullView) : finalView st = nullView := by
  rcases hs with hs | hs
  · unfold finalView; rw [hs]; funext c i; simp [viewOf, deliver, chan, hb, nullView]
  · unfold finalView; rw [hs]; rfl

/-- **Refusal blanks.** If, before any close, the trace contains a side action, an unknown channel, a rejected payload
or a slot overflow — i.e. a step that sets `blanked` — the final view is all-NULL on every channel. -/
theorem refusal_blanks (valid : (c : Fin C) → R → Option (S c)) (pre post : List (Ev C R)) (e : Ev C R)
    (hpre : (runG valid (init (S := S) (slots := slots)) pre).snap = none)
    (he : (gstep valid (runG valid (init (S := S) (slots := slots)) pre) e).blanked = true) :
    finalView (runG valid (init (S := S) (slots := slots)) (pre ++ e :: post)) = nullView := by
  have hrun : runG valid (init (S := S) (slots := slots)) (pre ++ e :: post) =
      runG valid (gstep valid (runG valid (init (S := S) (slots := slots)) pre) e) post := by
    simp [runG, List.foldl_append]
  rw [hrun]
  set st := runG valid (init (S := S) (slots := slots)) pre
  have hs : (gstep valid st e).snap = none ∨ (gstep valid st e).snap = some nullView := by
    unfold gstep; rw [hpre]
    cases e with
    | other => left; rfl
    | close =>
      right
      have hb : st.blanked = true := by
        have := he; unfold gstep at this; rw [hpre] at this; exact this
      show some (viewOf st) = some nullView
      congr 1; funext c i; simp [viewOf, deliver, chan, hb, nullView]
    | send oc r =>
      left
      cases oc with
      | none => rfl
      | some c =>
        simp only
        split_ifs
        · cases valid c r <;> rfl
        · rfl
  have := blanked_stays valid _ he hs post
  exact finalView_blanked _ this.1 this.2

/-- the side action `act` refuses and blanks (Python `act`, alert `DENIED_ACTION`) -/
theorem other_blanks (valid : (c : Fin C) → R → Option (S c)) (pre post : List (Ev C R))
    (hpre : (runG valid (init (S := S) (slots := slots)) pre).snap = none) :
    finalView (runG valid (init (S := S) (slots := slots)) (pre ++ .other :: post)) = nullView := by
  apply refusal_blanks valid pre post .other hpre
  unfold gstep; rw [hpre]

/-! ### Reachable views and their exact count -/

/-- prefix tuples: per channel, j ≤ slots c accepted values -/
abbrev Prefixes (S : Fin C → Type) (slots : Fin C → ℕ) := (c : Fin C) → Prefix (S c) (slots c)

def embedAll (p : Prefixes S slots) : View S slots := fun c => embedPrefix (slots c) (p c)

/-- the Python `view_space_size`: ∏_c Σ_{j ≤ slots c} |S c|^j -/
def viewSpace (slots : Fin C → ℕ) (sz : Fin C → ℕ) : ℕ := ∏ c, ∑ j ∈ Finset.range (slots c + 1), sz c ^ j

theorem card_prefixes [∀ c, Fintype (S c)] [∀ c, DecidableEq (S c)] :
    Fintype.card (Prefixes S slots) = viewSpace slots (fun c => Fintype.card (S c)) := by
  unfold viewSpace Prefixes Prefix
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl; intro c _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin]
  exact (Finset.sum_range (fun j => Fintype.card (S c) ^ j)).symm

def Inv (st : GSt S slots) : Prop :=
  (∀ c, (st.buf c).length ≤ slots c) ∧ ∀ v, st.snap = some v → v ∈ Set.range (embedAll (S := S) (slots := slots))

lemma viewOf_reachable (st : GSt S slots) (h : ∀ c, (st.buf c).length ≤ slots c) :
    viewOf st ∈ Set.range (embedAll (S := S) (slots := slots)) :=
  ⟨fun c => toPrefix (slots c) (chan st c) (h c), by
    funext c; exact (deliver_eq_embed (slots c) (chan st c) (h c)).symm⟩

lemma gstep_inv (valid : (c : Fin C) → R → Option (S c)) (st : GSt S slots) (e : Ev C R) (h : Inv st) :
    Inv (gstep valid st e) := by
  obtain ⟨hlen, hsnap⟩ := h
  cases hs : st.snap with
  | some v =>
    have : gstep valid st e = st := by unfold gstep; rw [hs]
    rw [this]; exact ⟨hlen, hsnap⟩
  | none =>
    simp only [gstep, hs]
    cases e with
    | other => exact ⟨hlen, fun v hv => by simp [hs] at hv⟩
    | close =>
      refine ⟨hlen, fun v hv => ?_⟩
      simp only [Option.some.injEq] at hv
      rw [← hv]; exact viewOf_reachable st hlen
    | send oc r =>
      cases oc with
      | none => exact ⟨hlen, fun v hv => by simp [hs] at hv⟩
      | some c =>
        simp only
        split_ifs with hl
        · cases valid c r with
          | none => exact ⟨hlen, fun v hv => by simp [hs] at hv⟩
          | some x =>
            refine ⟨fun c' => ?_, fun v hv => by simp [hs] at hv⟩
            by_cases hc : c' = c
            · subst hc; simp; omega
            · simp [Function.update_of_ne hc, hlen c']
        · exact ⟨hlen, fun v hv => by simp [hs] at hv⟩

lemma runG_inv (valid : (c : Fin C) → R → Option (S c)) (tr : List (Ev C R)) (st : GSt S slots) (h : Inv st) :
    Inv (runG valid st tr) := by
  induction tr generalizing st with
  | nil => exact h
  | cons e tr ih => unfold runG; rw [List.foldl_cons]; exact ih _ (gstep_inv valid st e h)

/-- **Every delivered view is reachable**: it is the embedding of a prefix tuple. -/
theorem view_reachable (valid : (c : Fin C) → R → Option (S c)) (tr : List (Ev C R)) :
    finalView (runG valid (init (S := S) (slots := slots)) tr) ∈ Set.range (embedAll (S := S) (slots := slots)) := by
  have h0 : Inv (init (S := S) (slots := slots)) := ⟨fun c => by simp [init], fun v hv => by simp [init] at hv⟩
  obtain ⟨hlen, hsnap⟩ := runG_inv valid tr _ h0
  unfold finalView
  cases hs : (runG valid init tr).snap with
  | some v => exact hsnap v hs
  | none => exact viewOf_reachable _ hlen

/-- **End-to-end core bound.** Traces of L raw events; any shared seed, any randomised adaptive encoder of traces, any
decoder of the final view: success ≤ ∏_c Σ_{j ≤ slots c} |S c|^j / |M|. -/
theorem core_bound {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] [Fintype R]
    [∀ c, Fintype (S c)] [∀ c, DecidableEq (S c)]
    [Fintype (Ev C R)] (valid : (c : Fin C) → R → Option (S c)) (L : ℕ)
    (ρ : Ω → ℝ) (enc : Ω → M → (Fin L → Ev C R) → ℝ) (dec : Ω → View S slots → M → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) :
    (∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ tr, enc ω m tr *
        dec ω (finalView (runG valid (init (S := S) (slots := slots)) (List.ofFn tr))) m))
      ≤ (viewSpace slots (fun c => Fintype.card (S c)) : ℝ) / (Fintype.card M : ℝ) := by
  classical
  set pv : (Fin L → Ev C R) → Prefixes S slots := fun tr => Classical.choose (view_reachable valid (List.ofFn tr))
  have hview : ∀ tr, finalView (runG valid (init (S := S) (slots := slots)) (List.ofFn tr)) = embedAll (pv tr) :=
    fun tr => (Classical.choose_spec (view_reachable valid (List.ofFn tr))).symm
  have hpush : ∀ ω m, (∑ tr, enc ω m tr *
      dec ω (finalView (runG valid (init (S := S) (slots := slots)) (List.ofFn tr))) m) =
      ∑ p, push pv (enc ω m) p * dec ω (embedAll p) m := by
    intro ω m
    unfold push
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun tr _ => ?_
    rw [Finset.sum_eq_single (pv tr)]
    · simp [hview tr]
    · intro p _ hp; simp [Ne.symm hp]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h := covert_bound ρ (fun ω m => push pv (enc ω m)) (fun ω p => dec ω (embedAll p)) hρ
    (fun ω m => push_dist _ _ (henc ω m)) (fun ω p => hdec ω _)
  unfold successProb at h
  simp_rw [hpush]
  refine le_trans h (le_of_eq ?_)
  rw [card_prefixes]

/-- SC-01: one channel, eight repair ids, one slot: nine views per episode, as in contract.json. -/
theorem sc01_episode_views : viewSpace (C := 1) (fun _ => 1) (fun _ => 8) = 9 := by decide

#print axioms close_freezes
#print axioms refusal_blanks
#print axioms other_blanks
#print axioms card_prefixes
#print axioms view_reachable
#print axioms core_bound
#print axioms sc01_episode_views

end ControlStack.GatewayCore
