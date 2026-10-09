/-
ControlCert: a small calculus of certificates with explicit, named premises (the typed assumption ledger).

Purpose. The scenario results in this library are each "premises ⇒ bound" for a different event or quantity. Stacking
them in prose hides which premise each number rests on. A certificate here packages
- a list of NAMED premises, each with its Lean meaning (`Premise.holds`);
- a bound on a concrete event probability (`ProbCert`, over a finite probability space) or on a concrete real
  quantity (`QtyCert`: an expectation computed by the `val` machinery, or an effect count);
- a SOUNDNESS proof: if every listed premise holds, the event or quantity is within the bound.
Soundness is a real theorem about the stated event or quantity. The rules only ever ADD premises, so the final
certificate's premise list is the complete assumption ledger of the composed bound.

Rules (each proved):
- `ProbCert.ofDet`: deterministic certificates (bound 0) from a trace theorem;
- `ProbCert.union`: union bound, with no independence needed (premises append, bounds add);
- `ProbCert.min` / `QtyCert.min`: two certificates for the same event or quantity (bound min);
- `ProbCert.mono`: event inclusion;
- `ProbCert.prod`: product rule, ONLY with an explicit independence premise that is added to the ledger.
  `product_needs_independence` shows the rule is unsound without it: two layers fired by one score each miss with
  probability 1/10, yet miss jointly with probability 1/10, not 1/100 (`Necessity.scoreLaw`);
- `QtyCert.add`, `QtyCert.weaken`, `ProbCert.toQty`; `Stack` collects several certificates under one union of
  premises.
Instances: `sc26Cert` (SC-26 payment gate, deterministic), `attackRoundsCert` (F6 reserved audit with recall r,
expected attack rounds before the first catch), `damageCert` (F6 + F5 + F3 expected damage with global cap and
in-flight budget), `fencedHaltCert` (F3 fenced distributed HALT, effect counts).

Worked example (`stackExample`, `stack_sound`): a deployment combining
- SC-26 payments,
- a reserved hidden audit (N = 100 rounds, 10 audits, recall 1/2),
- a fenced distributed HALT (1000 nodes, 10 effects/tick, ε = 1, L = 0).
Composed bounds:
- unauthorized payments: probability 0;
- expected attack rounds before the first catch: ≤ 19;
- expected damage: ≤ min(G, 19·D + F);
- effects landing after HALT: ≤ min(G', 10 000), and 0 after t0 + 1.
All premises are listed. `stackLedger` is the `#eval`-able list of premise names, proved equal to the certificate's
actual premise list (`stack_ledger_eq`).

What the calculus does NOT do.
- It does not discharge premises. Soundness holds only relative to the listed premises, and the hard work
  (correspondence, measurement, independent review) is exactly checking them.
- The union bound is often loose. `min` keeps the better of two bounds but does not combine evidence.
- Premise names are labels; their meaning is the `holds` proposition. Two premises with the same name are not
  identified or deduplicated. The ledger is a list, not a set.
- Certificates about different quantities in a `Stack` are only collected, not composed. Composing them needs a
  joint model (e.g. `DamageBound` composes F6 with F5/F3 inside one kernel), and where such a link is a modelling
  choice it appears as a named premise ("damage ≤ D·X + F", "damage ≤ G").
- Classical bookkeeping; no novelty is claimed.
-/
import ControlStack.Scenarios.SC26Transaction
import ControlStack.Families.F6.DamageBound
import ControlStack.Families.F3.DistributedHalt
import ControlStack.Witnesses.Necessity

namespace ControlStack.Cert

open Finset

/-! ## Premises and the ledger -/

/-- a named premise with its meaning -/
structure Premise where
  name : String
  holds : Prop

/-- every premise in the list holds -/
def AllHold (ps : List Premise) : Prop := ∀ p ∈ ps, p.holds

theorem AllHold.append {ps qs : List Premise} (h : AllHold (ps ++ qs)) : AllHold ps ∧ AllHold qs :=
  ⟨fun p hp => h p (List.mem_append_left _ hp), fun p hp => h p (List.mem_append_right _ hp)⟩

theorem AllHold.cons {p : Premise} {ps : List Premise} (h : AllHold (p :: ps)) : p.holds ∧ AllHold ps :=
  ⟨h p List.mem_cons_self, fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

/-- the assumption ledger: premise names -/
def ledger (ps : List Premise) : List String := ps.map Premise.name

/-! ## Event probabilities on a finite space -/

section Prob

variable {Ω : Type} [Fintype Ω]

open Classical in
/-- probability of event A under weights μ -/
noncomputable def prob (μ : Ω → ℝ) (A : Ω → Prop) : ℝ := ∑ ω, if A ω then μ ω else 0

theorem prob_nonneg (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (A : Ω → Prop) : 0 ≤ prob μ A := by
  classical
  unfold prob; exact Finset.sum_nonneg fun ω _ => by split_ifs; exact hμ ω; exact le_rfl

theorem prob_mono (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (A B : Ω → Prop) (h : ∀ ω, A ω → B ω) :
    prob μ A ≤ prob μ B := by
  classical
  unfold prob
  apply Finset.sum_le_sum; intro ω _
  by_cases hA : A ω
  · rw [if_pos hA, if_pos (h ω hA)]
  · rw [if_neg hA]; split_ifs; exact hμ ω; exact le_rfl

theorem prob_or_le (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (A B : Ω → Prop) :
    prob μ (fun ω => A ω ∨ B ω) ≤ prob μ A + prob μ B := by
  classical
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro ω _
  have := hμ ω
  split_ifs <;> first | linarith | tauto

theorem prob_empty (μ : Ω → ℝ) (A : Ω → Prop) (h : ∀ ω, ¬A ω) : prob μ A = 0 := by
  classical
  unfold prob; exact Finset.sum_eq_zero fun ω _ => by rw [if_neg (h ω)]

/-- a certificate for the probability of event A -/
structure ProbCert (μ : Ω → ℝ) (A : Ω → Prop) where
  premises : List Premise
  bound : ℝ
  sound : AllHold premises → prob μ A ≤ bound

/-- **Deterministic certificate:** a trace theorem that excludes A under the premises gives bound 0 -/
def ProbCert.ofDet {μ : Ω → ℝ} {A : Ω → Prop} (ps : List Premise) (h : AllHold ps → ∀ ω, ¬A ω) :
    ProbCert μ A :=
  ⟨ps, 0, fun hp => le_of_eq (prob_empty μ A (h hp))⟩

/-- **Union bound** (no independence needed): premises append, bounds add -/
def ProbCert.union {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) {A B : Ω → Prop} (c₁ : ProbCert μ A) (c₂ : ProbCert μ B) :
    ProbCert μ (fun ω => A ω ∨ B ω) :=
  ⟨c₁.premises ++ c₂.premises, c₁.bound + c₂.bound, fun hp => by
    obtain ⟨h1, h2⟩ := hp.append
    exact (prob_or_le μ hμ A B).trans (add_le_add (c₁.sound h1) (c₂.sound h2))⟩

/-- two certificates for the same event: keep the smaller bound, need both premise lists -/
def ProbCert.min {μ : Ω → ℝ} {A : Ω → Prop} (c₁ c₂ : ProbCert μ A) : ProbCert μ A :=
  ⟨c₁.premises ++ c₂.premises, Min.min c₁.bound c₂.bound, fun hp => by
    obtain ⟨h1, h2⟩ := hp.append
    exact le_min (c₁.sound h1) (c₂.sound h2)⟩

/-- event inclusion -/
def ProbCert.mono {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) {A B : Ω → Prop} (hAB : ∀ ω, A ω → B ω) (c : ProbCert μ B) :
    ProbCert μ A :=
  ⟨c.premises, c.bound, fun hp => (prob_mono μ hμ A B hAB).trans (c.sound hp)⟩

/-- the independence premise the product rule needs (it enters the ledger) -/
def indepPremise (μ : Ω → ℝ) (A B : Ω → Prop) : Premise :=
  ⟨"independence: P(A ∧ B) = P(A)·P(B)", prob μ (fun ω => A ω ∧ B ω) = prob μ A * prob μ B⟩

/-- **Product rule, only with an explicit independence premise.** -/
def ProbCert.prod {μ : Ω → ℝ} (hμ : ∀ ω, 0 ≤ μ ω) {A B : Ω → Prop} (c₁ : ProbCert μ A) (c₂ : ProbCert μ B) :
    ProbCert μ (fun ω => A ω ∧ B ω) :=
  ⟨indepPremise μ A B :: (c₁.premises ++ c₂.premises), c₁.bound * c₂.bound, fun hp => by
    obtain ⟨hind, hrest⟩ := hp.cons
    obtain ⟨h1, h2⟩ := hrest.append
    have hA := c₁.sound h1
    have hB := c₂.sound h2
    have hA0 := prob_nonneg μ hμ A
    have hB0 := prob_nonneg μ hμ B
    change prob μ (fun ω => A ω ∧ B ω) = prob μ A * prob μ B at hind
    rw [hind]
    exact mul_le_mul hA hB hB0 (hA0.trans hA)⟩

end Prob

/-- **The product rule is unsound without independence.** Two layers fired by the same score
(`Necessity.scoreLaw`): each misses with probability 1/10 (a valid premise-free certificate with bound 1/10 each),
but they miss jointly with probability 1/10 > 1/10 · 1/10. The independence premise fails here. -/
theorem product_needs_independence :
    prob Necessity.scoreLaw (fun s => s = false) = 1 / 10 ∧
    prob Necessity.scoreLaw (fun s => s = false ∧ s = false) = 1 / 10 ∧
    (1 / 10 : ℝ) * (1 / 10) < prob Necessity.scoreLaw (fun s => s = false ∧ s = false) ∧
    prob Necessity.scoreLaw (fun s => s = false ∧ s = false) ≠
      prob Necessity.scoreLaw (fun s => s = false) * prob Necessity.scoreLaw (fun s => s = false) := by
  have h1 : prob Necessity.scoreLaw (fun s => s = false) = 1 / 10 := by
    simp [prob, Necessity.scoreLaw]
  have h2 : prob Necessity.scoreLaw (fun s => s = false ∧ s = false) = 1 / 10 := by
    simp [prob, Necessity.scoreLaw]
  refine ⟨h1, h2, by rw [h2]; norm_num, by rw [h1, h2]; norm_num⟩

/-! ## Quantity certificates (expectations, effect counts) -/

/-- a certificate for a real quantity q (an expectation from the `val` machinery, an effect count, ...) -/
structure QtyCert (q : ℝ) where
  premises : List Premise
  bound : ℝ
  sound : AllHold premises → q ≤ bound

def QtyCert.min {q : ℝ} (c₁ c₂ : QtyCert q) : QtyCert q :=
  ⟨c₁.premises ++ c₂.premises, Min.min c₁.bound c₂.bound, fun hp => by
    obtain ⟨h1, h2⟩ := hp.append
    exact le_min (c₁.sound h1) (c₂.sound h2)⟩

def QtyCert.add {q₁ q₂ : ℝ} (c₁ : QtyCert q₁) (c₂ : QtyCert q₂) : QtyCert (q₁ + q₂) :=
  ⟨c₁.premises ++ c₂.premises, c₁.bound + c₂.bound, fun hp => by
    obtain ⟨h1, h2⟩ := hp.append
    exact add_le_add (c₁.sound h1) (c₂.sound h2)⟩

def QtyCert.weaken {q : ℝ} (c : QtyCert q) (b : ℝ) (hb : c.bound ≤ b) : QtyCert q :=
  ⟨c.premises, b, fun hp => (c.sound hp).trans hb⟩

def ProbCert.toQty {Ω : Type} [Fintype Ω] {μ : Ω → ℝ} {A : Ω → Prop} (c : ProbCert μ A) : QtyCert (prob μ A) :=
  ⟨c.premises, c.bound, c.sound⟩

/-! ## Stacks: several certificates under one premise ledger -/

/-- a collection of named claims that all hold under the union of the premises -/
structure Stack where
  premises : List Premise
  claims : List (String × Prop)
  sound : AllHold premises → ∀ c ∈ claims, c.2

def Stack.empty : Stack := ⟨[], [], fun _ c hc => by simp at hc⟩

/-- add a quantity certificate as a named claim "q ≤ bound" -/
def Stack.push {q : ℝ} (s : Stack) (name : String) (c : QtyCert q) : Stack :=
  ⟨s.premises ++ c.premises, s.claims ++ [(name, q ≤ c.bound)], fun hp x hx => by
    obtain ⟨h1, h2⟩ := hp.append
    rcases List.mem_append.1 hx with hx | hx
    · exact s.sound h1 x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact c.sound h2⟩

/-! ## Instances -/

section Instances

/-- **SC-26 (deterministic).** For any randomised attacker choosing among finitely many traces, an unauthorized
payment (a state violating `Good`) has probability 0, under: every operation is legal (no untrusted operation carries
the gate credential) and the deployed checks form a sound configuration. -/
noncomputable def sc26Cert {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (R : SC26.Roles) (cap : ℕ) (C : SC26.Checks)
    (trace : Ω → List SC26.Op) :
    ProbCert μ (fun ω => ¬ SC26.Good R cap (SC26.run R cap C SC26.init (trace ω))) :=
  ProbCert.ofDet
    [⟨"SC26.legal: no untrusted operation carries the gate credential", ∀ ω, ∀ o ∈ trace ω, SC26.legal R o⟩,
     ⟨"SC26.sound_config: payload, distinct, cap, receiver dedup and auth checks enabled", SC26.Sound C⟩]
    (fun hp ω hbad => by
      obtain ⟨hl, hrest⟩ := hp.cons
      obtain ⟨hs, -⟩ := hrest.cons
      exact hbad (SC26.safe_of_sound R cap hs (trace ω) (hl ω)))

variable {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]

open ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall

/-- the F6 kernel premises (as in `ReservedRecall.adaptive_recall_bound`), as named ledger entries -/
def f6Premises (Bh : ℕ) (r : ℝ) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) : List Premise :=
  [⟨"F6.strategy: the attacker's attack bit has law σ(visible history)", ∀ g, IsDist (σ g)⟩,
   ⟨"F6.kernel_nonneg", ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z⟩,
   ⟨"F6.kernel_subdist", ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1⟩,
   ⟨"F6.recall: per-history, an attacked reserved round escapes w.p. ≤ (1−r); hidden schedule, no leak",
     ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool),
      ∑ y, K S h (y, (a, (), false)) ≤
        σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)⟩]

omit [DecidableEq Y] in
theorem f6_of (Bh : ℕ) (r : ℝ) (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) (hp : AllHold (f6Premises Bh r K σ)) :
    (∀ g, IsDist (σ g)) ∧ (∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z) ∧
    (∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1) ∧
    (∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool),
      ∑ y, K S h (y, (a, (), false)) ≤
        σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) := by
  obtain ⟨h1, hp⟩ := hp.cons
  obtain ⟨h2, hp⟩ := hp.cons
  obtain ⟨h3, hp⟩ := hp.cons
  obtain ⟨h4, -⟩ := hp.cons
  exact ⟨h1, h2, h3, h4⟩

/-- **F6: expected attack rounds before the first catch** (reserved hidden audit, recall r, adaptive attacker):
≤ Σ_{j=1}^{N} hypMiss N Bh j r. -/
noncomputable def attackRoundsCert (y0 : Y) (Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ) :
    QtyCert (∑ S : Finset (Fin N), pU N Bh S * val (K S) (fun t => (DamageBound.ucX N t : ℝ)) N []) :=
  ⟨f6Premises Bh r K σ, ∑ j ∈ range N, hypMiss N Bh (j + 1) r, fun hp => by
    obtain ⟨hσ, hK0, hK1, hrec⟩ := f6_of Bh r K σ hp
    exact DamageBound.expected_uc y0 Bh hB r hr0 hr1 K σ hσ hK0 hK1 hrec⟩

/-- **F6 + F5 + F3: expected damage** with per-step cap D, in-flight budget F after halt-on-catch, and global cap G
(e.g. SC-26's cap): ≤ min(G, D · Σ hypMiss + F). The two damage premises are modelling links and enter the ledger. -/
noncomputable def damageCert (y0 : Y) (Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ)
    (D F G : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (hG : 0 ≤ G) (dmg : List (AOut Unit) → ℝ) :
    QtyCert (∑ S : Finset (Fin N), pU N Bh S * val (K S) dmg N []) :=
  ⟨f6Premises Bh r K σ ++
    [⟨"F5/F3.per_step_cap_and_inflight: damage ≤ D·(attack rounds before first catch) + F",
       ∀ t, dmg t ≤ D * DamageBound.ucX N t + F⟩,
     ⟨"F5.global_cap: damage ≤ G on every transcript (e.g. the SC-26 cap)", ∀ t, dmg t ≤ G⟩],
   Min.min G (D * ∑ j ∈ range N, hypMiss N Bh (j + 1) r + F), fun hp => by
    obtain ⟨hf6, hrest⟩ := hp.append
    obtain ⟨hσ, hK0, hK1, hrec⟩ := f6_of Bh r K σ hf6
    obtain ⟨hdD, hrest⟩ := hrest.cons
    obtain ⟨hdG, -⟩ := hrest.cons
    exact DamageBound.damage_cap_inflight y0 Bh hB r hr0 hr1 K σ hσ hK0 hK1 hrec D F G hD hF hG dmg hdD hdG⟩

end Instances

section Halt

open ControlStack.DistributedHalt

/-- the fenced-HALT premises -/
def haltPremises (ρ L e0 : ℕ) (e lat ep : ℕ → ℕ → ℕ) : List Premise :=
  [⟨"F3.rate: each node initiates ≤ ρ effects per tick (F5 metering)", Rate ρ e⟩,
   ⟨"F3.latency: in-flight latency ≤ L ticks", Latency L lat⟩,
   ⟨"F3.fencing: nodes hold only the pre-halt epoch; the sink checks epochs", HoldsOld e0 ep⟩]

/-- **F3 fenced distributed HALT:** effects landing after t0 ≤ min(G, n·ρ·(L+ε)), with no delivery premise. -/
def fencedHaltCert (n T t0 ε e0 G ρ L : ℕ) (e lat ep : ℕ → ℕ → ℕ) :
    QtyCert (((sinkRun true t0 ε e0 G (stream n T e lat ep)).countP (fun ev => decide (t0 ≤ ev.1)) : ℕ) : ℝ) :=
  ⟨haltPremises ρ L e0 e lat ep, ((Min.min G (n * ρ * (L + ε)) : ℕ) : ℝ), fun hp => by
    obtain ⟨hr, hp⟩ := hp.cons
    obtain ⟨hl, hp⟩ := hp.cons
    obtain ⟨hold, -⟩ := hp.cons
    exact_mod_cast (fenced_composed n T t0 ε e0 G ρ L e lat ep hr hl hold).1⟩

/-- **F3 fencing:** nothing is accepted at or after t0 + ε. -/
def fencedAfterCert (n T t0 ε e0 G ρ L : ℕ) (e lat ep : ℕ → ℕ → ℕ) :
    QtyCert (((sinkRun true t0 ε e0 G (stream n T e lat ep)).countP (fun ev => decide (t0 + ε ≤ ev.1)) : ℕ) : ℝ) :=
  ⟨haltPremises ρ L e0 e lat ep, 0, fun hp => by
    obtain ⟨hr, hp⟩ := hp.cons
    obtain ⟨hl, hp⟩ := hp.cons
    obtain ⟨hold, -⟩ := hp.cons
    have := (fenced_composed n T t0 ε e0 G ρ L e lat ep hr hl hold).2
    rw [this]; simp⟩

end Halt

/-! ## The worked stack certificate -/

section Example

open ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall

variable {Ω : Type} [Fintype Ω] {Y : Type} [Fintype Y] [DecidableEq Y]

/-- `hypMiss` sum at the design point: N = 100, 10 reserved audits, recall 1/2 -/
theorem design_attack_rounds : ∑ j ∈ range 100, hypMiss 100 10 (j + 1) (1 / 2) ≤ 19 :=
  DamageBound.example_r_half

/-- **The stack.** SC-26 payments + reserved hidden audit (N = 100, Bh = 10, r = 1/2) + fenced distributed HALT
(1000 nodes, ρ = 10, L = 0, ε = 1). -/
noncomputable def stackExample (μ : Ω → ℝ) (R : SC26.Roles) (cap : ℕ) (C : SC26.Checks)
    (trace : Ω → List SC26.Op)
    (y0 : Y) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ)
    (D F G : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (hG : 0 ≤ G) (dmg : List (AOut Unit) → ℝ)
    (T t0 e0 G' : ℕ) (e lat ep : ℕ → ℕ → ℕ) : Stack :=
  ((((Stack.empty.push "P(unauthorized payment)" (sc26Cert μ R cap C trace).toQty).push
      "E[attack rounds before first catch]"
      ((attackRoundsCert y0 10 (by norm_num) (1 / 2) (by norm_num) (by norm_num) K σ).weaken 19
        design_attack_rounds)).push
      "E[damage]"
      ((damageCert y0 10 (by norm_num) (1 / 2) (by norm_num) (by norm_num) K σ D F G hD hF hG dmg).weaken
        (Min.min G (D * 19 + F))
        (min_le_min le_rfl (by have := mul_le_mul_of_nonneg_left design_attack_rounds hD; linarith)))).push
      "effects landing after HALT"
      ((fencedHaltCert 1000 T t0 1 e0 G' 10 0 e lat ep).weaken (Min.min (G' : ℝ) 10000) (by
        show ((Min.min G' (1000 * 10 * (0 + 1)) : ℕ) : ℝ) ≤ Min.min (G' : ℝ) 10000
        norm_num))).push
    "effects landing at or after t0 + 1" (fencedAfterCert 1000 T t0 1 e0 G' 10 0 e lat ep)

/-- **Soundness of the stack:** if every premise in the ledger holds, every listed bound holds. -/
theorem stack_sound (μ : Ω → ℝ) (R : SC26.Roles) (cap : ℕ) (C : SC26.Checks) (trace : Ω → List SC26.Op)
    (y0 : Y) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ)
    (D F G : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (hG : 0 ≤ G) (dmg : List (AOut Unit) → ℝ)
    (T t0 e0 G' : ℕ) (e lat ep : ℕ → ℕ → ℕ)
    (hp : AllHold (stackExample μ R cap C trace y0 K σ D F G hD hF hG dmg T t0 e0 G' e lat ep).premises) :
    ∀ c ∈ (stackExample μ R cap C trace y0 K σ D F G hD hF hG dmg T t0 e0 G' e lat ep).claims, c.2 :=
  (stackExample μ R cap C trace y0 K σ D F G hD hF hG dmg T t0 e0 G' e lat ep).sound hp

/-- the claims of the stack, spelled out -/
theorem stack_claims (μ : Ω → ℝ) (R : SC26.Roles) (cap : ℕ) (C : SC26.Checks) (trace : Ω → List SC26.Op)
    (y0 : Y) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ)
    (D F G : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (hG : 0 ≤ G) (dmg : List (AOut Unit) → ℝ)
    (T t0 e0 G' : ℕ) (e lat ep : ℕ → ℕ → ℕ)
    (hp : AllHold (stackExample μ R cap C trace y0 K σ D F G hD hF hG dmg T t0 e0 G' e lat ep).premises) :
    prob μ (fun ω => ¬ SC26.Good R cap (SC26.run R cap C SC26.init (trace ω))) ≤ 0 ∧
    ∑ S : Finset (Fin 100), pU 100 10 S * val (K S) (fun t => (DamageBound.ucX 100 t : ℝ)) 100 [] ≤ 19 ∧
    ∑ S : Finset (Fin 100), pU 100 10 S * val (K S) dmg 100 [] ≤ Min.min G (D * 19 + F) ∧
    (((DistributedHalt.sinkRun true t0 1 e0 G' (DistributedHalt.stream 1000 T e lat ep)).countP
      (fun ev => decide (t0 ≤ ev.1)) : ℕ) : ℝ) ≤ Min.min (G' : ℝ) 10000 ∧
    (((DistributedHalt.sinkRun true t0 1 e0 G' (DistributedHalt.stream 1000 T e lat ep)).countP
      (fun ev => decide (t0 + 1 ≤ ev.1)) : ℕ) : ℝ) ≤ 0 := by
  have h := stack_sound μ R cap C trace y0 K σ D F G hD hF hG dmg T t0 e0 G' e lat ep hp
  have m : ∀ (n : String) (P : Prop),
      (n, P) ∈ (stackExample μ R cap C trace y0 K σ D F G hD hF hG dmg T t0 e0 G' e lat ep).claims → P :=
    fun n P hm => h (n, P) hm
  refine ⟨m "P(unauthorized payment)" _ ?_, m "E[attack rounds before first catch]" _ ?_, m "E[damage]" _ ?_,
    m "effects landing after HALT" _ ?_, m "effects landing at or after t0 + 1" _ ?_⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_singleton_self _)))))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_singleton_self _))))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
  · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- **The assumption ledger** of the stack (closed, `#eval`-able) -/
def stackLedger : List String :=
  ["SC26.legal: no untrusted operation carries the gate credential",
   "SC26.sound_config: payload, distinct, cap, receiver dedup and auth checks enabled",
   "F6.strategy: the attacker's attack bit has law σ(visible history)",
   "F6.kernel_nonneg",
   "F6.kernel_subdist",
   "F6.recall: per-history, an attacked reserved round escapes w.p. ≤ (1−r); hidden schedule, no leak",
   "F6.strategy: the attacker's attack bit has law σ(visible history)",
   "F6.kernel_nonneg",
   "F6.kernel_subdist",
   "F6.recall: per-history, an attacked reserved round escapes w.p. ≤ (1−r); hidden schedule, no leak",
   "F5/F3.per_step_cap_and_inflight: damage ≤ D·(attack rounds before first catch) + F",
   "F5.global_cap: damage ≤ G on every transcript (e.g. the SC-26 cap)",
   "F3.rate: each node initiates ≤ ρ effects per tick (F5 metering)",
   "F3.latency: in-flight latency ≤ L ticks",
   "F3.fencing: nodes hold only the pre-halt epoch; the sink checks epochs",
   "F3.rate: each node initiates ≤ ρ effects per tick (F5 metering)",
   "F3.latency: in-flight latency ≤ L ticks",
   "F3.fencing: nodes hold only the pre-halt epoch; the sink checks epochs"]

/-- the ledger IS the stack's premise list (names), for every instantiation -/
theorem stack_ledger_eq (μ : Ω → ℝ) (R : SC26.Roles) (cap : ℕ) (C : SC26.Checks) (trace : Ω → List SC26.Op)
    (y0 : Y) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ)
    (D F G : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (hG : 0 ≤ G) (dmg : List (AOut Unit) → ℝ)
    (T t0 e0 G' : ℕ) (e lat ep : ℕ → ℕ → ℕ) :
    ledger (stackExample μ R cap C trace y0 K σ D F G hD hF hG dmg T t0 e0 G' e lat ep).premises = stackLedger := by
  rfl

/-- the ledger without repeats (for printing; the certificate itself keeps the list) -/
def stackLedgerDedup : List String := stackLedger.dedup

end Example

end ControlStack.Cert

#eval ControlStack.Cert.stackLedgerDedup

#print axioms ControlStack.Cert.prob_or_le
#print axioms ControlStack.Cert.ProbCert.prod
#print axioms ControlStack.Cert.product_needs_independence
#print axioms ControlStack.Cert.sc26Cert
#print axioms ControlStack.Cert.attackRoundsCert
#print axioms ControlStack.Cert.damageCert
#print axioms ControlStack.Cert.fencedHaltCert
#print axioms ControlStack.Cert.fencedAfterCert
#print axioms ControlStack.Cert.stack_sound
#print axioms ControlStack.Cert.stack_claims
#print axioms ControlStack.Cert.stack_ledger_eq
