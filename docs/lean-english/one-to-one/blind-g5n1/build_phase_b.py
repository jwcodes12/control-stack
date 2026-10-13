from pathlib import Path
import json,hashlib,difflib
O=Path(__file__).resolve().parent
R=O.parents[3]
G=R/'docs/lean-english/one-to-one'
source=(G/'run_gate.py').read_text()
source=source.replace('parents[3]', 'parents[4]').replace("OUT/'leangate_imports.py'", "OUT.parent/'leangate_imports.py'").replace("ControlStack.Deployment.Witnesses ControlStack.Deployment.TranscriptReplay",'ControlStack.Scenarios.EvalIntegrity ControlStack.Scenarios.EvalIntegrityAdaptive ControlStack.Scenarios.SC23Injection').replace("g0_*.statement.lean", "bg5n1_*.statement.lean")
(O/'run_gate_blind.py').write_text(source)
(O/'run_gate_blind.diff').write_text(''.join(difflib.unified_diff((G/'run_gate.py').read_text().splitlines(True),source.splitlines(True),fromfile='run_gate.py',tofile='blind-g5n1/run_gate_blind.py')))
common='open ControlStack.EvalIntegrity ControlStack.EvalIntegrityAdaptive ControlStack.AuditBudget ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall\nopen scoped BigOperators\n'
pars={1:'(E : Env) (ops : List Op)',2:'(N B k : ℕ) (rep truth : Fin N → ℕ)',3:'(N B k : ℕ) (rep truth : Fin N → ℕ)',4:'(N B k : ℕ) (S : Finset (Fin N))',5:'(N B k : ℕ) (σ : List (AOut Unit) → Bool → ℝ)',6:'(N B k : ℕ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ)',7:'(N B k : ℕ) (r : ℝ) (Y : Type) [Fintype Y] (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ)',8:'(N B k : ℕ) (rep truth : Fin N → ℕ)',9:'(P : Policy) (ops : List Op)',10:'(P : Policy) (s : St) (ops : List Op)'}
args={1:'E ops',2:'N B k rep truth',3:'N B k rep truth',4:'N B k S',5:'N B k σ',6:'N B k Y K σ',7:'N B k r Y K σ',8:'N B k rep truth',9:'P ops',10:'P s ops'}
base_h=['B ≤ N','∀ g, IsDist (σ g)','∀ S ∈ randomSchedules N B, ∀ h yo, 0 ≤ K S h yo','∀ S ∈ randomSchedules N B, ∀ h, (∑ y, ∑ o, K S h (y, o)) ≤ 1','∀ S ∈ randomSchedules N B, ∀ h a, (∑ y, ∑ f : Bool, K S h (y, (a, (), f))) ≤ σ (h.map Prod.snd) a']
rec='∀ S ∈ randomSchedules N B, ∀ h a, (∑ y, K S h (y, (a, (), false))) ≤ σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)'
hs={1:[],2:['(corrupt rep truth).card = k'],3:['0 < N','B ≤ N','(corrupt rep truth).card = k'],4:['S.card = B','k ≤ N - B'],5:['B ≤ N','∀ g, IsDist (σ g)'],6:base_h,7:[base_h[0],'0 ≤ r','r ≤ 1']+base_h[1:]+[rec],8:['(corrupt rep truth).card = k'],9:[],10:['s.halted = true']}
cs={1:'∀ p ∈ (run E full init ops).published, PubOk E p',2:'survival (randomSchedules N B) (corrupt rep truth) = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)',3:'survival (randomSchedules N B) (corrupt rep truth) ≤ (((N - B : ℕ) : ℝ) / (N : ℝ)) ^ k',4:'∃ A : Finset (Fin N), A.card = k ∧ Disjoint S A ∧ survival {S} A = 1',5:'(∑ S ∈ randomSchedules N B, (Nat.choose N B : ℝ)⁻¹ * val (hiddenK (N := N) σ S) (survInd k S) N []) ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)',6:'(∑ S ∈ randomSchedules N B, (Nat.choose N B : ℝ)⁻¹ * val (K S) (successInd k S) N []) ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)',7:'(∑ S ∈ randomSchedules N B, (Nat.choose N B : ℝ)⁻¹ * val (K S) (recallSucc (N := N) k) N []) ≤ hypMiss N B k r',8:'survival (randomSchedules N B) (corrupt rep truth) = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)',9:'Good P (run P full init ops)',10:'run P full s ops = s'}
orig_cs=dict(cs)
orig_cs[3]='survival (randomSchedules N B) (corrupt rep truth) ≤ (((N : ℝ) - B) / N) ^ k'
orig_cs[5]='(∑ S : Finset (Fin N), (if S ∈ randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) * val (hiddenK (N := N) σ S) (survInd k S) N []) ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)'
for n in [6,7]: orig_cs[n]=cs[n].replace('∑ S ∈ randomSchedules N B, (Nat.choose N B : ℝ)⁻¹ *','∑ S : Finset (Fin N), pU N B S *')
witness={
1:'''def wEnv : Env := ⟨[0, 1], fun _ => 0, 7, [9]⟩
def wOps : List Op := [.report 0 0 7, .report 1 9 7, .reexec 0, .publish]
def Witness : Prop := (run wEnv full init wOps).published = [([(1,9,7),(0,0,7)], [0])]''',
2:'''def wRep (i : Fin 2) : ℕ := if i = 0 then 1 else 0
def Witness : Prop := (corrupt wRep (fun _ => 0)).card = 1 ∧ 1 ≤ (2 : ℕ) ∧ (randomSchedules 2 1).Nonempty''',
3:'''def wRep (i : Fin 2) : ℕ := if i = 0 then 1 else 0
def Witness : Prop := 0 < (2 : ℕ) ∧ 1 ≤ (2 : ℕ) ∧ (corrupt wRep (fun _ => 0)).card = 1 ∧ (randomSchedules 2 1).Nonempty''',
4:'''def Witness : Prop := ({0} : Finset (Fin 2)).card = 1 ∧ 1 ≤ 2 - (1 : ℕ) ∧ ∃ A : Finset (Fin 2), A.card = 1 ∧ Disjoint ({0} : Finset (Fin 2)) A''',
5:'''noncomputable def wSigma (_ : List (AOut Unit)) (_ : Bool) : ℝ := 1/2
def Witness : Prop := HBack 2 1 1 wSigma ∧ wSigma [] true > 0 ∧ wSigma [] false > 0''',
6:'''noncomputable def wSigma (_ : List (AOut Unit)) (_ : Bool) : ℝ := 1/2
noncomputable def wKernel (_ : Finset (Fin 2)) (_ : List (Unit × AOut Unit)) (z : Unit × AOut Unit) : ℝ := if z.2.2.2 = false then 1/2 else 0
def Witness : Prop := HBack 2 1 1 Unit wKernel wSigma ∧ wKernel {0} [] ((), (true, (), false)) > 0''',
7:'''noncomputable def wSigma (_ : List (AOut Unit)) (_ : Bool) : ℝ := 1/2
noncomputable def wKernel (_ : Finset (Fin 2)) (_ : List (Unit × AOut Unit)) (_ : Unit × AOut Unit) : ℝ := 1/4
noncomputable def cSigma (_ : List (AOut Unit)) (a : Bool) : ℝ := if a = false then 1 else 0
noncomputable def cKernel (_ : Finset (Fin 2)) (_ : List (Unit × AOut Unit)) (z : Unit × AOut Unit) : ℝ := if z.2.1 = true ∧ z.2.2.2 = true then 1 else 0
def StrictScope : Prop := HOrig 2 1 1 (1/2) Unit cKernel cSigma ∧ ¬ HBack 2 1 1 (1/2) Unit cKernel cSigma
def Witness : Prop := HBack 2 1 1 (1/2) Unit wKernel wSigma ∧ wKernel {0} [] ((), (true, (), false)) > 0''',
8:'''def wRep (i : Fin 2) : ℕ := if i = 0 then 1 else 0
def Witness : Prop := (corrupt wRep (fun _ => 0)).card = 1 ∧ 1 ≤ (2 : ℕ) ∧ (randomSchedules 2 1).Nonempty''',
9:'''def wPolicy : Policy := ⟨[1], [9], [7]⟩
def wOps : List Op := [.toolResult 0 42, .confirm 1 3 7 [42], .act 7 [0] 3]
def Witness : Prop := (run wPolicy full init wOps).executed = [⟨7, [42], true, some 3⟩] ∧ (run wPolicy full init wOps).used = [3]''',
10:'''def wPolicy : Policy := ⟨[1], [9], [7]⟩
def wState : St := ⟨[⟨0, 42, true, true⟩], [⟨3, 7, [42], 1⟩], [3], [⟨7, [42], true, some 3⟩], true⟩
def wOps : List Op := [.userInput 1 99, .confirm 1 4 7 [99], .act 7 [0] 4, .halt 9]
def Witness : Prop := wState.halted = true ∧ wState.store ≠ [] ∧ wState.executed ≠ [] ∧ run wPolicy full wState wOps = wState'''}
orig_call={1:'sc21_safe E ops',2:'sc21_undetected_prob rep truth h',3:'sc21_undetected_le_pow rep truth h.1 h.2.1 h.2.2',4:'observable_sample_nogo S h.1 h.2',5:'sc21_adaptive k B h.1 σ h.2',6:'sc21_adaptive_content k B h.1 K σ h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2',7:'sc21_adaptive_recall k B h.1 r h.2.1 h.2.2.1 K σ h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2',8:'sc22_unreplicated_misreport rep truth h',9:'sc23_safe P ops',10:'halt_freezes P s ops h'}
for n in range(1,11):
 p=next((O/'typed').glob(f'{n}-*.lean')); raw=p.read_text(); name='Back_'+p.stem.split('-',1)[1]
 # Preserve the compiled Back definition verbatim; relocate only its enclosing namespace.
 back=raw[raw.index('def Back_'):raw.rindex('\nend ')].strip()
 par=pars[n]; a=args[n]; hb=hs[n]; ho=list(hb)
 if n in [6,7]: ho[ho.index(base_h[3])]='∀ S ∈ randomSchedules N B, ∀ h, (∑ z, K S h z) ≤ 1'
 if n==7: ho.remove(base_h[4])
 conj=lambda xs:' ∧\n  '.join('('+x+')' for x in xs) if xs else 'True'
 opening=common if n<9 else 'open ControlStack.SC23\nopen scoped BigOperators\n'
 cid=f'bg5n1_{n}'
 s=f'namespace PL_{cid}\n{opening}\n{back}\n\ndef HBack {par} : Prop :=\n  {conj(hb)}\ndef HOrig {par} : Prop :=\n  {conj(ho)}\nnoncomputable def BackAt {par} : Prop :=\n  {cs[n]}\nnoncomputable def OrigAt {par} : Prop :=\n  {orig_cs[n]}\n\n{witness[n]}\n\ndef Claim : Prop :=\n  ({name} ↔ ∀ {par}, HBack {a} → BackAt {a}) ∧\n'
 if n!=7: s+=f'  (∀ {par}, HBack {a} ↔ HOrig {a}) ∧\n  (∀ {par}, HBack {a} → (BackAt {a} ↔ OrigAt {a}))\n'
 else: s+=f'  (∀ {par}, HBack {a} → HOrig {a}) ∧\n  (∀ {par}, HBack {a} → (BackAt {a} ↔ OrigAt {a})) ∧\n  (∀ {par}, (HOrig {a} → OrigAt {a}) → (HBack {a} → BackAt {a})) ∧\n  StrictScope\n'
 s+=f'end PL_{cid}\n'
 schema=f'by simp only [{name}, HBack, BackAt, and_imp, true_implies]'
 hyp='by intros; rfl'
 concl='by intros; rfl'
 if n==3: concl='''by
    intro N B k rep truth h
    unfold BackAt OrigAt
    rw [Nat.cast_sub h.2.1]'''
 if n in [5,6,7]:
  if n in [6,7]: hyp='by intros; simp only [HBack, HOrig, Fintype.sum_prod_type]'
  concl=f'''by
    intro {a.replace(' Y ', ' Y inst ')} h
    classical
    unfold BackAt OrigAt
    {'unfold pU' if n>5 else ''}
    simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]'''
 if n==7: hyp='''by
    intro N B k r Y inst K σ h
    rcases h with ⟨hB, hr0, hr1, hσ, h0, h1, hmarg, hrec⟩
    exact ⟨hB, hr0, hr1, hσ, h0, by simpa only [Fintype.sum_prod_type] using h1, hrec⟩'''
 proof=f'theorem original_type {par} (h : HOrig {a}) : OrigAt {a} :=\n  {"by " if n in [1,9] else "by "}exact {orig_call[n]}\n\ntheorem claim : Claim := by\n  refine ⟨{schema}, ?_, ?_⟩\n  · exact {hyp}\n'
 if n!=7: proof+=f'  · exact {concl.replace(chr(10), chr(10)+"  ")}\n'
 else:
  proof=f'theorem original_type {par} (h : HOrig {a}) : OrigAt {a} := by exact {orig_call[n]}\n\ntheorem scope_inclusion : ∀ {par}, HBack {a} → HOrig {a} := {hyp}\ntheorem conclusion_iff : ∀ {par}, HBack {a} → (BackAt {a} ↔ OrigAt {a}) := {concl}\n\ntheorem strict_scope : StrictScope := by\n  constructor\n  · simp only [HOrig, cKernel, cSigma, IsDist, AOut, Fintype.sum_prod_type, Fintype.sum_bool]\n    norm_num\n  · intro h\n    have hm := h.2.2.2.2.2.2.1 ({{0}} : Finset (Fin 2)) (by decide) [] true\n    norm_num [cKernel, cSigma, Fintype.sum_bool] at hm\n\ntheorem claim : Claim := by\n  refine ⟨{schema}, scope_inclusion, conclusion_iff, ?_, strict_scope⟩\n  intro {a.replace(' Y ', ' Y inst ')} law h\n  exact (conclusion_iff {a} h).mpr (law (scope_inclusion {a} h))\n'
 if n in [1,9,10]: proof+='\ntheorem witness : Witness := by unfold Witness; decide\n'
 elif n in [2,3,8]: proof+='\ntheorem witness : Witness := by\n  unfold Witness\n  refine '+('⟨by decide, by decide, ?_⟩' if n!=3 else '⟨by decide, by decide, by decide, ?_⟩')+'\n  exact ⟨{0}, by decide⟩\n'
 elif n==4: proof+='\ntheorem witness : Witness := by\n  refine ⟨by decide, by decide, {1}, by decide, by decide⟩\n'
 elif n==5: proof+='\ntheorem witness : Witness := by\n  norm_num [Witness, HBack, wSigma, IsDist, Fintype.sum_bool]\n'
 elif n==6: proof+='\ntheorem witness : Witness := by\n  norm_num [Witness, HBack, wKernel, wSigma, IsDist, AOut, Fintype.sum_prod_type, Fintype.sum_bool]\n'
 elif n==7: proof+='\ntheorem witness : Witness := by\n  unfold Witness HBack\n  norm_num [wKernel, wSigma, IsDist, AOut, Fintype.sum_prod_type, Fintype.sum_bool]\n  intro S hS h\n  split_ifs <;> norm_num\n'
 (O/f'{cid}.statement.lean').write_text(s)
 (O/f'{cid}.proof.lean').write_text(opening+'\n'+proof)
