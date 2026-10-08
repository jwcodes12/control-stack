/-
Transition model of the gateway's durable lifetime ledger (gateway/gateway.py, `LifetimeLedger`).

State: `none` (missing, corrupt or mismatched database: every admission refused) or `some f`, where f ℓ is the
committed product of admitted episode view-space sizes for lineage ℓ (initially 1). Events:
- `charge ℓ k`: one serialised transaction (BEGIN IMMEDIATE … COMMIT). Admits iff f ℓ · k ≤ cap, committing f ℓ · k;
- `abort ℓ k`: the same transaction interrupted before COMMIT (process crash, SQLite error): no state change, no
  admission (an admission is only reported after COMMIT returns);
- `reopen`: process restart / reconnect: durable state unchanged;
- `corrupt`: the database becomes missing or invalid: state `none`, never silently re-created;
- `restore g`: an operator restores an older valid snapshot g.

Proved:
- `ledger_safe`: on every trace with no `restore`, for every lineage the product of admitted sizes is ≤ cap;
- `restore_breaks`: one `restore` of an older valid snapshot lets the admitted product exceed cap, so the
  no-rollback assumption in PREREG-SC01-REPAIR.md is necessary, not merely convenient;
- `lifetime_secret_bound`: composed with `covert_bound_lifetime`, the views of the admitted episodes of a lineage give
  P(recover a uniform secret on M) ≤ cap / |M|.

Correspondence assumptions (not proved): concurrent charges serialise (SQLite BEGIN IMMEDIATE), COMMIT is atomic and
durable (synchronous=FULL), the trusted supervisor supplies lineages and never re-creates a ledger, and the sizes charged
are the episode view-space sizes actually enforced by the gateway.
-/
import Mathlib.Tactic
import ControlStack.CovertChannel

namespace ControlStack.LifetimeLedger

inductive Ev (L : Type) where
  | charge (ℓ : L) (k : ℕ)
  | abort (ℓ : L) (k : ℕ)
  | reopen
  | corrupt
  | restore (g : L → ℕ)

def Ev.isRestore {L : Type} : Ev L → Prop
  | .restore _ => True
  | _ => False

variable {L : Type} [DecidableEq L]

/-- one event: new state and the admission it reports, if any -/
def step (cap : ℕ) : Option (L → ℕ) → Ev L → Option (L → ℕ) × Option (L × ℕ)
  | none, .restore g => (some g, none)
  | none, _ => (none, none)
  | some f, .charge ℓ k =>
      if f ℓ * k ≤ cap then (some (Function.update f ℓ (f ℓ * k)), some (ℓ, k)) else (some f, none)
  | some f, .abort _ _ => (some f, none)
  | some f, .reopen => (some f, none)
  | some _, .corrupt => (none, none)
  | some _, .restore g => (some g, none)

/-- run a trace from a state, accumulating admissions in order -/
def run (cap : ℕ) : Option (L → ℕ) × List (L × ℕ) → List (Ev L) → Option (L → ℕ) × List (L × ℕ)
  | st, [] => st
  | (s, adm), e :: es => run cap ((step cap s e).1, adm ++ (step cap s e).2.toList) es

/-- product of admitted sizes for lineage ℓ -/
def pr (ℓ : L) (adm : List (L × ℕ)) : ℕ := ((adm.filter (fun a => a.1 = ℓ)).map Prod.snd).prod

lemma pr_append_one (ℓ ℓ' : L) (k : ℕ) (adm : List (L × ℕ)) :
    pr ℓ' (adm ++ [(ℓ, k)]) = pr ℓ' adm * (if ℓ = ℓ' then k else 1) := by
  unfold pr
  by_cases h : ℓ = ℓ' <;> simp [List.filter_append, h]

def Inv (cap : ℕ) (st : Option (L → ℕ) × List (L × ℕ)) : Prop :=
  (∀ f, st.1 = some f → ∀ ℓ, f ℓ = pr ℓ st.2) ∧ ∀ ℓ, pr ℓ st.2 ≤ cap

lemma step_inv (cap : ℕ) (s : Option (L → ℕ)) (adm : List (L × ℕ)) (e : Ev L) (he : ¬ e.isRestore)
    (h : Inv cap (s, adm)) : Inv cap ((step cap s e).1, adm ++ (step cap s e).2.toList) := by
  obtain ⟨hf, hcap⟩ := h
  cases s with
  | none =>
      cases e <;> simp_all [step, Inv, Ev.isRestore]
  | some f =>
      cases e with
      | charge ℓ k =>
          by_cases hk : f ℓ * k ≤ cap
          · simp only [step, hk, ite_true, Option.toList_some]
            refine ⟨?_, ?_⟩
            · intro g hg ℓ'
              simp only [Option.some.injEq] at hg
              subst hg
              rw [pr_append_one]
              by_cases hl : ℓ = ℓ'
              · subst hl; simp [hf f rfl ℓ]
              · simp [Function.update_of_ne (Ne.symm hl), hl, hf f rfl ℓ']
            · intro ℓ'
              rw [pr_append_one]
              by_cases hl : ℓ = ℓ'
              · subst hl; simp only [ite_true]; rw [← hf f rfl ℓ]; exact hk
              · simp [hl, hcap ℓ']
          · simp only [step, hk, ite_false, Option.toList_none, List.append_nil]
            exact ⟨hf, hcap⟩
      | abort _ _ => exact ⟨by simpa [step] using hf, by simpa [step] using hcap⟩
      | reopen => exact ⟨by simpa [step] using hf, by simpa [step] using hcap⟩
      | corrupt => simp [step, Inv, hcap]
      | restore g => exact absurd trivial he

lemma run_inv (cap : ℕ) : ∀ (es : List (Ev L)) (st : Option (L → ℕ) × List (L × ℕ)),
    (∀ e ∈ es, ¬ e.isRestore) → Inv cap st → Inv cap (run cap st es)
  | [], st, _, h => h
  | e :: es, (s, adm), hes, h => by
      simp only [run]
      exact run_inv cap es _ (fun e' he' => hes e' (List.mem_cons_of_mem e he'))
        (step_inv cap s adm e (hes e List.mem_cons_self) h)

/-- **Ledger safety.** From a freshly created ledger (every lineage at 1, nothing admitted), on every trace of
charges, aborts, reopens and corruptions — but no snapshot restores — every lineage's admitted product is ≤ cap. -/
theorem ledger_safe (cap : ℕ) (hcap : 1 ≤ cap) (es : List (Ev L)) (hes : ∀ e ∈ es, ¬ e.isRestore) (ℓ : L) :
    pr ℓ (run cap (some (fun _ => 1), []) es).2 ≤ cap := by
  have h0 : Inv cap ((some (fun _ => 1), []) : Option (L → ℕ) × List (L × ℕ)) :=
    ⟨fun f hf ℓ => by simp only [Option.some.injEq] at hf; subst hf; simp [pr], fun ℓ => by simp [pr, hcap]⟩
  exact (run_inv cap es _ hes h0).2 ℓ

/-- **The no-rollback assumption is necessary.** Restoring the initial (older, valid) snapshot once lets a lineage
be admitted at product cap², exceeding cap whenever cap ≥ 2. -/
theorem restore_breaks (cap : ℕ) (hcap : 2 ≤ cap) (ℓ : L) :
    cap < pr ℓ (run cap (some (fun _ => 1), [])
      [.charge ℓ cap, .restore (fun _ => 1), .charge ℓ cap]).2 := by
  simp [run, step, pr]
  nlinarith

open ControlStack.Covert in
/-- **Lifetime secret bound.** If a receiver lineage's whole observation is the tuple of views of its admitted
episodes, with sizes respecting the ledger (∏ |V e| ≤ cap, as `ledger_safe` guarantees for the charged sizes), then
P(recover a uniform secret on M) ≤ cap / |M|. -/
theorem lifetime_secret_bound {Ω M : Type} [Fintype Ω] [Fintype M] [Nonempty M] {E : ℕ}
    (V : Fin E → Type) [∀ e, Fintype (V e)] [∀ e, DecidableEq (V e)] (cap : ℕ)
    (hV : ∏ e, Fintype.card (V e) ≤ cap)
    (ρ : Ω → ℝ) (enc : Ω → M → ((e : Fin E) → V e) → ℝ) (dec : Ω → ((e : Fin E) → V e) → M → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) :
    successProb ρ enc dec ≤ (cap : ℝ) / (Fintype.card M : ℝ) := by
  have h := covert_bound_lifetime V ρ enc dec hρ henc hdec
  have hM : (0 : ℝ) < Fintype.card M := by exact_mod_cast Fintype.card_pos
  calc successProb ρ enc dec ≤ (∏ e, (Fintype.card (V e) : ℝ)) / Fintype.card M := h
    _ ≤ (cap : ℝ) / Fintype.card M := by
        gcongr
        exact_mod_cast hV

#print axioms ledger_safe
#print axioms restore_breaks
#print axioms lifetime_secret_bound

end ControlStack.LifetimeLedger
