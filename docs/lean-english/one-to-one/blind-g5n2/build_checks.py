from pathlib import Path
import re
OUT=Path(__file__).resolve().parent

def save(n,opens,body,proof,witness):
 cid=f'bg5n2_{n}'
 p=next((OUT/'typed').glob(f'{n}-*.lean'))
 src=p.read_text()
 src=re.sub(r'--[^\n]*','',src)
 src=re.sub(r'^import .*\n','',src,flags=re.M)
 src=re.sub(r'^namespace .*\n|^end .*\n|^open .*\n','',src,flags=re.M).strip()
 statement=f'namespace PL_{cid}\n{opens}\n{src}\n\n{body}\nend PL_{cid}\n'
 (OUT/f'{cid}.statement.lean').write_text(statement)
 (OUT/f'{cid}.proof.lean').write_text(opens+'\n'+proof+'\n\ntheorem witness : Witness := by\n  unfold Witness\n'+witness+'\n')

S='open ControlStack.SC23Isolation'
T='open ControlStack.SC23IsolationV2 ControlStack.Authenticated ControlStack.Gate'
A='open ControlStack ControlStack.AuthInstances ControlStack.AuthenticatedLog'
C='open Finset ControlStack.MonitorCollusion ControlStack.Covert ControlStack.Leakage'
# Each Orig expression below is the original declaration's conclusion, with its
# parameters held fixed. Back expressions come from the frozen translation.
save(1,S,'''def Claim : Prop :=
  (Back_noninterference = (∀ (E : Env) (ops ops' : List Op),
    List.Forall₂ SameExceptContent ops ops' → Rel (run E full init ops) (run E full init ops'))) ∧
  (∀ (E : Env) (ops ops' : List Op), List.Forall₂ SameExceptContent ops ops' →
    (Rel (run E full init ops) (run E full init ops') ↔
     Rel (run E full init ops) (run E full init ops')))
def Witness : Prop :=
  List.Forall₂ SameExceptContent
    ([.toolResult 66, .derive, .act 5 [1] 0] : List Op)
    [.toolResult 0, .derive, .act 5 [1] 0] ∧
  (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed = [⟨5,[41],false,none⟩]''',
'''theorem claim : Claim := by
  exact ⟨rfl, fun _ _ _ _ => Iff.rfl⟩''',
'''  constructor
  · repeat' constructor
  · decide''')
save(2,S,'''def Orig : Prop :=
  (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed =
    (run E0 full init [.toolResult 0, .derive, .act 5 [1] 0]).executed ∧
  (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed = [⟨5,[41],false,none⟩]
def Claim : Prop := Back_w1_impossible ↔ Orig
def Witness : Prop := (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed = [⟨5,[41],false,none⟩]''',
'''theorem claim : Claim := by
  rfl''','''  decide''')
save(3,S,'''def Claim : Prop :=
  (Back_sc23_isolated_safe = (∀ (E : Env) (ops : List Op),
    ∀ x ∈ (run E full init ops).executed, ActOk E (run E full init ops) x)) ∧
  (∀ (E : Env) (ops : List Op) (x : Act), x ∈ (run E full init ops).executed →
    (ActOk E (run E full init ops) x ↔
     (x.tool ∈ E.sensitive → x.tainted = true →
       ∃ n, x.conf = some n ∧ ∃ cf ∈ (run E full init ops).confs,
         cf.n = n ∧ cf.tool = x.tool ∧ cf.vals = x.vals ∧ cf.by_ ∈ E.users)))
def Witness : Prop :=
  (run E0 full init [.toolResult 66, .confirm 1 7 5 [66], .act 5 [0] 7]).executed = [⟨5,[66],true,some 7⟩]''',
'''theorem claim : Claim := by
  exact ⟨rfl, fun _ _ _ _ => Iff.rfl⟩''','''  decide''')
save(4,T,'''def Claim : Prop :=
  (Back_noninterference_authed = (∀ (E : Env) (ops ops' : List (ℕ × Op)),
    List.Forall₂ (fun io io' => io.1 = io'.1 ∧ SameExceptContent io.2 io'.2) ops ops' →
      Rel ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops)
        ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops'))) ∧
  (∀ (E : Env) (ops ops' : List (ℕ × Op)),
    List.Forall₂ (fun io io' => io.1 = io'.1 ∧ SameExceptContent io.2 io'.2) ops ops' →
    (Rel ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops)
       ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops') ↔
     Rel ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops)
       ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops')))
def Witness : Prop :=
  List.Forall₂ (fun io io' : ℕ × Op => io.1 = io'.1 ∧ SameExceptContent io.2 io'.2)
    [(7,.toolResult 66), (1,.derive), (1,.act 5 [1] 0)]
    [(7,.toolResult 0), (1,.derive), (1,.act 5 [1] 0)] ∧
  ((authed (raw E0) ControlStack.SC23IsolationV2.claim).run init
    [(7,.toolResult 66), (1,.derive), (1,.act 5 [1] 0)]).executed = [⟨5,[0],false,none⟩]''',
'''theorem claim : Claim := by
  exact ⟨rfl, fun _ _ _ _ => Iff.rfl⟩''',
'''  constructor
  · apply List.Forall₂.cons ⟨rfl, Or.inr ⟨66,0,rfl,rfl⟩⟩
    apply List.Forall₂.cons ⟨rfl, Or.inl rfl⟩
    apply List.Forall₂.cons ⟨rfl, Or.inl rfl⟩
    exact List.Forall₂.nil
  · decide''')
save(5,'open ControlStack.SC23IsolationV2', '''def Orig : Prop :=
  (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed =
    (run E0 full init [.toolResult 0, .derive, .act 5 [1] 0]).executed ∧
  (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed = [⟨5,[0],false,none⟩]
def Claim : Prop := Back_w1_impossible_v2 ↔ Orig
def Witness : Prop := (run E0 full init [.toolResult 66, .derive, .act 5 [1] 0]).executed = [⟨5,[0],false,none⟩]''',
'''theorem claim : Claim := by
  rfl''','''  decide''')
save(6,T,'''def Claim : Prop :=
  (Back_sc23v2_safe_authenticated = (∀ (E : Env) (U : List ℕ),
    (∀ u ∈ U, u ∉ E.users) → ∀ (ops : List (ℕ × Op)),
    ∀ x ∈ ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops).executed,
    x.tool ∈ E.sensitive → x.tainted = true →
      ∃ c n, c ∈ E.users ∧ c ∉ U ∧ (c, Op.confirm c n x.tool x.vals) ∈ ops)) ∧
  (∀ (E : Env) (U : List ℕ), (∀ u ∈ U, u ∉ E.users) →
    ∀ (ops : List (ℕ × Op)) (x : Act),
      x ∈ ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops).executed →
      x.tool ∈ E.sensitive → x.tainted = true →
      ((∃ (c n : ℕ), c ∈ E.users ∧ c ∉ U ∧ (c, Op.confirm c n x.tool x.vals) ∈ ops) ↔
       (∃ c n, c ∈ E.users ∧ c ∉ U ∧ (c, Op.confirm c n x.tool x.vals) ∈ ops)))
def Witness : Prop :=
  (∀ u ∈ ([7] : List ℕ), u ∉ E0.users) ∧
  ((authed (raw E0) ControlStack.SC23IsolationV2.claim).run init
    [(7,.toolResult 66),(1,.confirm 1 7 5 [66]),(7,.act 5 [0] 7)]).executed = [⟨5,[66],true,some 7⟩]''',
'''theorem claim : Claim := by
  exact ⟨rfl, fun _ _ _ _ _ _ _ _ => Iff.rfl⟩''',
'''  constructor
  · simp [E0]
  · decide''')
save(7,A,'''def BackAt (P : SC23.Policy) (U : List ℕ) (ops : List (ℕ × SC23.Op)) : Prop :=
  let s := authRun (SC23.step P SC23.full) claim23 SC23.init ops
  SC23.Good P s ∧ ∀ cf ∈ s.confs,
    ∃ c : ℕ, c ∈ P.users ∧ c ∉ U ∧ c = cf.by_ ∧
      (c, SC23.Op.confirm c cf.n cf.tool cf.vals) ∈ ops
def OrigAt (P : SC23.Policy) (U : List ℕ) (ops : List (ℕ × SC23.Op)) : Prop :=
  let s := authRun (SC23.step P SC23.full) claim23 SC23.init ops
  SC23.Good P s ∧ ∀ cf ∈ s.confs, ∃ c o, (c,o) ∈ ops ∧ c ∉ U ∧
    (o = SC23.Op.confirm c cf.n cf.tool cf.vals ∧ c = cf.by_ ∧ c ∈ P.users)
def Claim : Prop :=
  (Back_sc23_safe_authenticated = (∀ (P : SC23.Policy) (U : List ℕ),
    (∀ u ∈ U, u ∉ P.users) → ∀ ops, BackAt P U ops)) ∧
  (∀ (P : SC23.Policy) (U : List ℕ) (ops : List (ℕ × SC23.Op)),
    (∀ u ∈ U, u ∉ P.users) → (BackAt P U ops ↔ OrigAt P U ops))
def Witness : Prop :=
  (∀ u ∈ ([7] : List ℕ), u ∉ SC23.P0.users) ∧
  (authRun (SC23.step SC23.P0 SC23.full) claim23 SC23.init
    [(7,.toolResult 0 66),(1,.confirm 1 7 5 [66]),(7,.act 5 [0] 7)]).executed = [⟨5,[66],true,some 7⟩]''',
'''theorem claim : Claim := by
  refine ⟨rfl, ?_⟩
  intro P U ops _
  constructor
  · rintro ⟨hg, hc⟩
    refine ⟨hg, ?_⟩
    intro cf hcf
    obtain ⟨c, hu, hn, he, hm⟩ := hc cf hcf
    exact ⟨c, SC23.Op.confirm c cf.n cf.tool cf.vals, hm, hn, rfl, he, hu⟩
  · rintro ⟨hg, hc⟩
    refine ⟨hg, ?_⟩
    intro cf hcf
    obtain ⟨c, o, hm, hn, ho, he, hu⟩ := hc cf hcf
    subst o
    exact ⟨c, hu, hn, he, hm⟩''',
'''  constructor
  · simp [SC23.P0]
  · decide''')
save(8,A,'''def Orig : Prop :=
  (authRun (SC23.step SC23.P0 SC23.full) (fun _ => none) SC23.init forged23).executed = [⟨5,[66],true,some 7⟩] ∧
  (authRun (SC23.step SC23.P0 SC23.full) claim23 SC23.init forged23).executed = []
def Claim : Prop := Back_forged23_acts_without_auth ↔ Orig
def Witness : Prop :=
  forged23 = [(7,SC23.Op.toolResult 0 66),(7,SC23.Op.confirm 1 7 5 [66]),(7,SC23.Op.act 5 [0] 7)] ∧
  Back_forged23_acts_without_auth''',
'''theorem claim : Claim := by
  rfl''','''  constructor
  · rfl
  · unfold Back_forged23_acts_without_auth
    decide''')
save(9,C,'''def Claim : Prop :=
  (Back_pass_transfer = (∀ (V : Type) [Fintype V] (P Q β : V → ℝ),
    IsDist P → IsDist Q → (∀ v, 0 ≤ β v ∧ β v ≤ 1) →
      |passRate P β - passRate Q β| ≤ tv P Q)) ∧
  (∀ (V : Type) [Fintype V] (P Q β : V → ℝ),
    IsDist P → IsDist Q → (∀ v, 0 ≤ β v ∧ β v ≤ 1) →
      (|passRate P β - passRate Q β| ≤ tv P Q ↔
       |passRate Q β - passRate P β| ≤ tv P Q))
def Witness : Prop :=
  IsDist stegoReal ∧ IsDist stegoHoney ∧
  (∀ v, 0 ≤ stegoMonitor v ∧ stegoMonitor v ≤ 1) ∧
  passRate stegoReal stegoMonitor = 1 ∧ passRate stegoHoney stegoMonitor = 0 ∧ tv stegoReal stegoHoney = 1''',
'''theorem claim : Claim := by
  refine ⟨rfl, ?_⟩
  intro V _ P Q β _ _ _
  rw [abs_sub_comm (passRate P β) (passRate Q β)]''',
'''  norm_num [IsDist, stegoReal, stegoHoney, stegoMonitor, passRate, tv]
  all_goals intro v; cases v <;> norm_num''')
save(10,C,'''def Claim : Prop :=
  (Back_collusion_uniform = (∀ (V : Type) [Fintype V] (P Q : V → ℝ) (monitor : V → Bool → ℝ),
    IsDist P → IsDist Q → (∀ v, IsDist (monitor v)) →
      (passRate P (fun v => monitor v true) + passRate Q (fun v => monitor v false))/2 ≤ (1+tv P Q)/2)) ∧
  (∀ (V : Type) [Fintype V] (P Q : V → ℝ) (monitor : V → Bool → ℝ),
    IsDist P → IsDist Q → (∀ v, IsDist (monitor v)) →
    ((passRate P (fun v => monitor v true) + passRate Q (fun v => monitor v false))/2 ≤ (1+tv P Q)/2 ↔
     (∑ φ : Bool, (1/2 : ℝ) * ∑ v, (if φ then P v else Q v) *
       ∑ a : Bool, monitor v a * (if a = φ then 1 else 0)) ≤ (1+tv P Q)/2))
def Witness : Prop :=
  IsDist stegoReal ∧ IsDist stegoHoney ∧
  (∀ v : Bool, IsDist (fun a : Bool => if a = v then (1:ℝ) else 0)) ∧
  (passRate stegoReal (fun v => if true = v then 1 else 0) +
    passRate stegoHoney (fun v => if false = v then 1 else 0))/2 = 1''',
'''theorem claim : Claim := by
  refine ⟨rfl, ?_⟩
  intro V _ P Q monitor _ _ _
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
    Bool.true_eq_false, mul_zero, mul_one, zero_add, add_zero]
  unfold passRate
  ring_nf''',
'''  norm_num [IsDist, stegoReal, stegoHoney, passRate, Fintype.sum_bool]
  all_goals intro v; cases v <;> norm_num''')
save(11,C,'''noncomputable def OrigSeed {M V : Type} [Fintype M] [Fintype V] [DecidableEq M]
    (K : ℕ) (canon : V → Fin K) (enc : M → V → ℝ) (dec : Fin K → M → ℝ) : ℝ :=
  ∑ m, (Fintype.card M : ℝ)⁻¹ * ∑ v, enc m v * ∑ a, dec (canon v) a * (if a = m then 1 else 0)
noncomputable def BackSeed {M V : Type} [Fintype M] [Fintype V]
    (K : ℕ) (canon : V → Fin K) (enc : M → V → ℝ) (dec : Fin K → M → ℝ) : ℝ :=
  (Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ v, enc m v * dec (canon v) m
def OriginalFamily : Prop :=
  ∀ (M V : Type) [Fintype M] [Fintype V] [DecidableEq M] [Nonempty M]
    (K : ℕ) (canon : V → Fin K) (enc : M → V → ℝ),
    (∀ m, IsDist (enc m)) → ∀ (dec : Fin K → M → ℝ),
    (∀ k, IsDist (dec k)) →
      OrigSeed K canon enc dec ≤ (K : ℝ) * (Fintype.card M : ℝ)⁻¹
def Claim : Prop :=
  (∀ (M V : Type) [Fintype M] [Fintype V] [DecidableEq M]
    (K : ℕ) (canon : V → Fin K) (enc : M → V → ℝ) (dec : Fin K → M → ℝ),
    (BackSeed K canon enc dec ≤ (K : ℝ)/(Fintype.card M : ℝ) ↔
     OrigSeed K canon enc dec ≤ (K : ℝ)*(Fintype.card M : ℝ)⁻¹)) ∧
  (Back_canon_channel ↔ OriginalFamily)
def Witness : Prop :=
  IsDist (fun _ : Unit => (1:ℝ)) ∧
  (∀ m : Bool, IsDist (fun v : Bool => if v = m then (1:ℝ) else 0)) ∧
  (∀ k : Fin 2, IsDist (fun m : Bool => if m = (k.val == 1) then (1:ℝ) else 0)) ∧
  successProb (fun _ : Unit => (1:ℝ))
    (fun (_ : Unit) (m v : Bool) => if v = m then 1 else 0)
    (fun (_ : Unit) (v m : Bool) => if m = (((if v then 1 else 0 : Fin 2).val) == 1) then 1 else 0) = 1''',
'''theorem seed_eq {M V : Type} [Fintype M] [Fintype V] [DecidableEq M]
    (K : ℕ) (canon : V → Fin K) (enc : M → V → ℝ) (dec : Fin K → M → ℝ) :
    BackSeed K canon enc dec = OrigSeed K canon enc dec := by
  simp [BackSeed, OrigSeed, Finset.mul_sum]

theorem claim : Claim := by
  classical
  constructor
  · intro M V _ _ _ K canon enc dec
    rw [seed_eq, div_eq_mul_inv]
  · constructor
    · intro hb M V _ _ _ _ K canon enc he dec hd
      have h := hb Unit M V K canon (fun _ => 1) (fun _ => enc) (fun _ => dec)
        (by norm_num [IsDist]) (fun _ => he) (fun _ => hd)
      simp only [successProb, Fintype.univ_unit, Finset.sum_singleton, one_mul] at h
      change BackSeed K canon enc dec ≤ (K:ℝ)/(Fintype.card M:ℝ) at h
      simpa only [seed_eq, div_eq_mul_inv] using h
    · intro ho Ω M V _ _ _ _ K canon ρ enc dec hρ he hd
      change (∑ ω, ρ ω * BackSeed K canon (enc ω) (dec ω)) ≤ (K:ℝ)/(Fintype.card M:ℝ)
      calc
        _ ≤ ∑ ω, ρ ω * ((K:ℝ)*(Fintype.card M:ℝ)⁻¹) := by
          apply Finset.sum_le_sum
          intro ω _
          apply mul_le_mul_of_nonneg_left _ (hρ.1 ω)
          rw [seed_eq]
          exact ho M V K canon (enc ω) (he ω) (dec ω) (hd ω)
        _ = _ := by rw [← Finset.sum_mul, hρ.2, one_mul, div_eq_mul_inv]''',
'''  norm_num [IsDist, successProb, Fintype.sum_bool]''')
save(12,C,'''def OriginalFamily : Prop :=
  ∀ (Y O : Type) [Fintype Y] [Fintype O]
    (K : Bool → List (Y × O) → Y × O → ℝ) (c : List O → O → ℝ) (L : ℝ),
    (∀ φ h z, 0 ≤ K φ h z) → (∀ φ, Dominated (K φ) c) →
    (∀ g o, 0 ≤ c g o) → 0 ≤ L → (∀ g, ∑ o, c g o ≤ L) →
    ∀ (guess : List O → Bool → ℝ), (∀ t, IsDist (guess t)) → ∀ m,
      (∑ φ : Bool, (1/2:ℝ)*val (K φ) (fun t => guess t φ) m []) ≤ (1/2)*L^m
def Claim : Prop :=
  (∀ (Y O : Type) [Fintype Y] [Fintype O]
    (K : Bool → List (Y × O) → Y × O → ℝ) (L : ℝ)
    (guess : List O → Bool → ℝ) (m : ℕ),
    ((val (K false) (fun t => guess t false) m [] +
      val (K true) (fun t => guess t true) m []) / 2 ≤ L^m/2 ↔
     (∑ φ : Bool, (1/2:ℝ)*val (K φ) (fun t => guess t φ) m []) ≤ (1/2)*L^m)) ∧
  (Back_phase_learning ↔ OriginalFamily)
def Witness : Prop :=
  (∀ φ h z, 0 ≤ bscK φ h z) ∧
  (∀ φ, Dominated (bscK φ) (fun _ _ => (101/200:ℝ))) ∧
  (∀ g : List Bool, (∑ _o : Bool, (101/200:ℝ)) ≤ 101/100) ∧
  (∀ t : List Bool, IsDist (fun _ : Bool => (1/2:ℝ))) ∧
  (101/100:ℝ)^10/2 < 553/1000''',
'''theorem pointwise {Y O : Type} [Fintype Y] [Fintype O]
    (K : Bool → List (Y × O) → Y × O → ℝ) (L : ℝ)
    (guess : List O → Bool → ℝ) (m : ℕ) :
    (val (K false) (fun t => guess t false) m [] +
      val (K true) (fun t => guess t true) m []) / 2 ≤ L^m/2 ↔
    (∑ φ : Bool, (1/2:ℝ)*val (K φ) (fun t => guess t φ) m []) ≤ (1/2)*L^m := by
  simp only [Fintype.sum_bool]
  ring_nf

theorem claim : Claim := by
  classical
  refine ⟨fun _ _ _ _ K L guess m => pointwise K L guess m, ?_⟩
  constructor
  · intro hb Y O _ _ K c L hK hd _ hL hm guess hg m
    exact (pointwise K L guess m).1 (hb Y O K c L guess m hK hd hL hm hg)
  · intro ho Y O _ _ K c L guess m hK hd hL hm hg
    rcases isEmpty_or_nonempty Y with he | hn
    · letI := he
      cases m with
      | zero =>
        change (guess [] false + guess [] true)/2 ≤ L^0/2
        have hs := (hg []).2
        simp only [Fintype.sum_bool] at hs
        norm_num
        linarith
      | succ m =>
        simp only [ControlStack.Leakage.val, Finset.univ_eq_empty, Finset.sum_empty, zero_add, zero_div]
        exact div_nonneg (pow_nonneg hL _) (by norm_num)
    · letI := hn
      let y : Y := Classical.choice hn
      have hc : ∀ g o, 0 ≤ c g o := by
        intro g o
        have h := hd false (g.map (fun a => (y,a))) o
        have hz : 0 ≤ ∑ y', K false (g.map (fun a => (y,a))) (y',o) :=
          Finset.sum_nonneg (fun y' _ => hK false _ (y',o))
        have := hz.trans h
        simpa [List.map_map, Function.comp_def] using this
      exact (pointwise K L guess m).2 (ho Y O K c L hK hd hc hL hm guess hg m)''',
'''  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro φ h z
    unfold bscK
    split_ifs <;> norm_num
  · intro φ h o
    simp only [Dominated, Fintype.univ_unit, Finset.sum_singleton, bscK]
    split_ifs <;> norm_num
  · intro g
    norm_num [Fintype.sum_bool]
  · intro t
    norm_num [IsDist, Fintype.sum_bool]
  · norm_num''')
# Gate concrete limits alongside the non-vacuity witnesses.
def augment(n,defs,extra,extra_proof):
 cid=f'bg5n2_{n}'
 p=OUT/f'{cid}.statement.lean'
 s=p.read_text().replace('def Witness : Prop :=','def BasicWitness : Prop :=')
 s=s.replace(f'end PL_{cid}',f'{defs}\ndef LimitWitness : Prop :=\n{extra}\ndef Witness : Prop := BasicWitness ∧ LimitWitness\nend PL_{cid}')
 p.write_text(s)
 p=OUT/f'{cid}.proof.lean'
 s=p.read_text().replace('theorem witness : Witness := by\n  unfold Witness','theorem basicWitness : BasicWitness := by\n  unfold BasicWitness')
 s += '\n\ntheorem witness : Witness := by\n  refine ⟨basicWitness, ?_⟩\n  unfold LimitWitness\n'+extra_proof+'\n'
 p.write_text(s)
augment(1,'', '''  List.Forall₂ SameExceptContent
    ([.toolResult 66,.confirm 1 7 5 [66],.act 5 [0] 7] : List Op)
    [.toolResult 0,.confirm 1 7 5 [66],.act 5 [0] 7] ∧
  (run E0 full init [.toolResult 66,.confirm 1 7 5 [66],.act 5 [0] 7]).executed = [⟨5,[66],true,some 7⟩] ∧
  (run E0 full init [.toolResult 0,.confirm 1 7 5 [66],.act 5 [0] 7]).executed = []''',
'''  refine ⟨?_, ?_, ?_⟩
  · repeat' constructor
  · decide
  · decide''')
augment(3,'', '''  (run E0 full init [.toolResult 66,.confirm 1 7 5 [66],.act 5 [0] 7,.act 5 [0] 7]).executed =
    [⟨5,[66],true,some 7⟩,⟨5,[66],true,some 7⟩]''', '''  decide''')
augment(12,'''def HeavyK : Bool → List (Unit × Unit) → Unit × Unit → ℝ := fun _ _ _ => 3
def HeavyC : List Unit → Unit → ℝ := fun _ _ => 3
noncomputable def HalfGuess : List Unit → Bool → ℝ := fun _ _ => 1/2''',
'''  (∀ φ h z, 0 ≤ HeavyK φ h z) ∧
  (∀ φ, Dominated (HeavyK φ) HeavyC) ∧
  (∀ g o, 0 ≤ HeavyC g o) ∧ (0 ≤ (3:ℝ)) ∧
  (∀ g, (∑ o, HeavyC g o) ≤ 3) ∧
  (∀ t, IsDist (HalfGuess t)) ∧
  (val (HeavyK false) (fun t => HalfGuess t false) 1 [] +
    val (HeavyK true) (fun t => HalfGuess t true) 1 []) / 2 = 3/2 ∧
  (1:ℝ) < 3/2''',
'''  norm_num [HeavyK, HeavyC, HalfGuess, Dominated, IsDist,
    ControlStack.Leakage.val, Fintype.sum_bool]''')
