from pathlib import Path
import re, hashlib, json, difflib
OUT=Path(__file__).resolve().parent
HELPER=OUT.parent
src=(HELPER/'run_gate.py').read_text()
# Relocation changes only path configuration, the input glob, and trusted module imports.
src=src.replace('parents[3]', 'parents[4]').replace("'ControlStack.Deployment.Witnesses ControlStack.Deployment.TranscriptReplay'", "'ControlStack.Scenarios.SC26Transaction ControlStack.Scenarios.SC26Refinement ControlStack.Scenarios.SC26Authenticated ControlStack.Core.AuthenticatedAdv ControlStack.Scenarios.SC26Liveness'").replace("'g0_*.statement.lean'", "'bg6n2_*.statement.lean'")
(OUT/'run_gate_blind.py').write_text(src)
(OUT/'run-gate-config.diff').write_text(''.join(difflib.unified_diff((HELPER/'run_gate.py').read_text().splitlines(True),src.splitlines(True),fromfile='run_gate.py',tofile='blind-g6n2/run_gate_blind.py')))
(OUT/'leangate_imports.py').write_bytes((HELPER/'leangate_imports.py').read_bytes())
common='open ControlStack.SC26\n'
auth='open ControlStack.SC26Authenticated ControlStack.Authenticated ControlStack.Gate\n'
ref='open ControlStack.SC26Refinement\n'
hon='def honestOps : List Op := [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .arrive 0]\n'
chon='def honestCOps : List COp := [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .transmit 0, .bankProcess 0]\n'
at={1:'def BackAt (R : Roles) (cap : ℕ) (s : St) : Prop := Good R cap s\n',
2:'''def BackAt (R : Roles) (s : St) : Prop :=
  ∀ e ∈ s.bank, ∃ (r : Req) (a : ℕ),
    reqOf s e.1 = some r ∧ r.tx = e.2 ∧ (e.1, a, e.2) ∈ s.approvals ∧
    a ∈ R.approvers ∧ a ∉ R.agents ∧ a ≠ r.requester
''',
3:'def BackAt (s : St) : Prop := s.reserved.Nodup\n',
4:'''def BackAt (s t : St) : Prop :=
  (∀ m : ℕ × Tx, m ∈ t.net ↔ m ∈ s.net) ∧
  (∀ e ∈ t.bank, e ∈ s.bank ∨ e ∈ s.net)
''',
5:'def BackAt (R : Roles) (cap : ℕ) (s : CSt) : Prop := Good R cap (α s)\n',
6:'''def BackAt (s t : CSt) : Prop :=
  t.wire = s.wire ∧ (∀ e ∈ t.bank, e ∈ s.bank ∨ e ∈ s.wire)
''',
7:'''def BackAt (R : Roles) (cap : ℕ) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good R cap s ∧ ∀ e ∈ s.bank, ∃ a : ℕ,
    a ∈ R.approvers ∧ a ∉ U ∧ (a, Op.approve a e.1 e.2) ∈ ops
''',
8:'''def BackAt (b : List (ℕ × Tx)) (ops : List (ℕ × Op)) (guarded : List (ℕ × Tx)) : Prop :=
  (0, tx1) ∈ b ∧ (∀ io ∈ ops, io.1 ∉ R0.approvers) ∧ guarded = []
''',
9:'''def BackAt (R : Roles) (cap : ℕ) (hon : List (ℕ × Op)) (s : St) : Prop :=
  Good R cap s ∧ ∀ e ∈ s.bank, ∃ a : ℕ,
    a ∈ R.approvers ∧ (a, Op.approve a e.1 e.2) ∈ hon
''',
10:'''def BackAt (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req) (caller : ℕ) : Prop :=
  (k, r.tx) ∈ (run R cap full s [Op.execute caller k, Op.deliver k, Op.arrive k]).bank
'''}
orig={n:at[n].replace('BackAt','OrigAt') for n in at}
orig[4]='''def OrigAt (s t : St) : Prop :=
  t.net = s.net ∧ (∀ e ∈ t.bank, e ∈ s.bank ∨ e ∈ s.net)
'''
orig[8]='''def OrigAt (b : List (ℕ × Tx)) (ops : List (ℕ × Op)) (guarded : List (ℕ × Tx)) : Prop :=
  b = [(0, tx1)] ∧ (¬ ∃ a ∈ R0.approvers, (a, Op.approve a 0 tx1) ∈ ops) ∧ guarded = []
'''
params={1:'∀ (R : Roles) (cap : ℕ) (C : Checks) (ops : List Op), Sound C → (∀ o ∈ ops, legal R o) →',
2:'∀ (R : Roles) (cap : ℕ) (ops : List Op), (∀ a ∈ R.approvers, a ∉ R.agents) → (∀ o ∈ ops, legal R o) →',
3:'∀ (R : Roles) (cap : ℕ) (ops : List Op),',
4:'∀ (R : Roles) (cap : ℕ) (s : St) (ops : List Op), s.halted = true → (∀ o ∈ ops, legal R o) →',
5:'∀ (R : Roles) (cap : ℕ) (ops : List COp), (∀ o ∈ ops, legalC R o) →',
6:'∀ (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp), s.halted = true → (∀ o ∈ ops, legalC R o) →',
7:'∀ (R : Roles) (cap : ℕ) (U : List ℕ) (ops : List (ℕ × Op)), (∀ a ∈ R.approvers, a ∉ U) → BankHyp R ops →',
9:'∀ (R : Roles) (cap : ℕ) (U : List ℕ) (hon ops : List (ℕ × Op)), AdvTrace U hon ops → (∀ a ∈ R.approvers, a ∉ U) → R.gate ∉ U → BankHyp R hon →',
10:'∀ (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req) (caller : ℕ), Inv R cap s → s.halted = false → reqOf s k = some r → Approved R s k r → k ∉ s.reserved → s.spent + r.tx.amount ≤ cap →'}
args={1:'R cap (run R cap C init ops)',2:'R (run R cap full init ops)',3:'(run R cap full init ops)',4:'s (run R cap full s ops)',5:'R cap (runC R cap true cinit ops)',6:'s (runC R cap true s ops)',7:'R cap U ops ((authed (raw R cap) ControlStack.SC26Authenticated.claim).run init ops)',9:'R cap hon ((authed (raw R cap) ControlStack.SC26Authenticated.claim).run init ops)',10:'R cap s k r caller'}
point={1:'∀ (R : Roles) (cap : ℕ) (s : St), BackAt R cap s ↔ OrigAt R cap s',2:'∀ (R : Roles) (s : St), BackAt R s ↔ OrigAt R s',3:'∀ (s : St), BackAt s ↔ OrigAt s',5:'∀ (R : Roles) (cap : ℕ) (s : CSt), BackAt R cap s ↔ OrigAt R cap s',6:'∀ (s t : CSt), BackAt s t ↔ OrigAt s t',7:'∀ (R : Roles) (cap : ℕ) (U : List ℕ) (ops : List (ℕ × Op)) (s : St), BackAt R cap U ops s ↔ OrigAt R cap U ops s',9:'∀ (R : Roles) (cap : ℕ) (hon : List (ℕ × Op)) (s : St), BackAt R cap hon s ↔ OrigAt R cap hon s',10:'∀ (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req) (caller : ℕ), BackAt R cap s k r caller ↔ OrigAt R cap s k r caller'}
hyp='''def BankHyp (R : Roles) (ops : List (ℕ × Op)) : Prop :=
  ∀ io ∈ ops, match io.2 with
  | .bankCall _ _ _ => io.1 ≠ R.gate
  | _ => True
def OrigBankHyp (R : Roles) (ops : List (ℕ × Op)) : Prop :=
  ∀ io ∈ ops, ∀ c k tx, io.2 = .bankCall c k tx → io.1 ≠ R.gate
def HypAgreement : Prop := ∀ (R : Roles) (U : List ℕ) (ops : List (ℕ × Op)),
  ((∀ a ∈ R.approvers, a ∉ U) ↔ (∀ u ∈ U, u ∉ R.approvers)) ∧
  (BankHyp R ops ↔ OrigBankHyp R ops)
'''
hproof='''theorem hypotheses_agree : HypAgreement := by
  intro R U ops
  constructor
  · constructor
    · intro h u hu ha; exact h u ha hu
    · intro h a ha hu; exact h a hu ha
  · constructor
    · intro h io hio c k tx heq
      have hi := h io hio
      rw [heq] at hi
      exact hi
    · intro h io hio
      cases ho : io.2 with
      | bankCall c k tx => exact h io hio c k tx ho
      | _ => trivial
'''
sig={1:'by\n  intro R cap C ops hC hops\n  exact safe_of_sound R cap hC ops hops',2:'by\n  intro R cap ops hd hl\n  exact sc26_safe_disjoint R cap hd ops hl',3:'by\n  intro R cap ops\n  exact sc26_once R cap ops',4:'by\n  intro R cap s ops hh hl\n  exact ControlStack.SC26.halt_freezes R cap s ops hl hh',5:'by\n  intro R cap ops hl\n  exact concrete_safe R cap ops hl',6:'by\n  intro R cap s ops hh hl\n  exact concrete_halt R cap s ops hl hh',7:'by\n  intro R cap U ops hu hg\n  exact sc26_safe_authenticated R cap U ops hu hg',8:'forged_approval_pays_without_auth',9:'by\n  intro R cap U hon ops ha hu hg hh\n  exact sc26_consent_from_honest_script R cap U hon ops ha hu hg hh',10:'by\n  intro R cap s k r c hi hh hr ha hk hc\n  exact honest_progress R cap s hi c k r hh hr ha hk hc'}
# Nonempty, successful executions, with each claim's actual hypotheses satisfied.
witness={1:'''Sound full ∧ (∀ o ∈ honestOps, legal R0 o) ∧
  (run R0 20 full init honestOps).bank = [(0, tx1)]''',2:'''(∀ a ∈ R0.approvers, a ∉ R0.agents) ∧ (∀ o ∈ honestOps, legal R0 o) ∧
  (run R0 20 full init honestOps).bank = [(0, tx1)]''',3:'''(run R0 20 full init honestOps).reserved = [0] ∧
  (run R0 20 full init honestOps).spent = 10 ∧
  (run R0 20 full init honestOps).bank = [(0, tx1)]''',4:'''haltedStart.halted = true ∧ (∀ o ∈ [Op.arrive 0], legal R0 o) ∧
  haltedStart.bank = [] ∧ haltedStart.net = [(0, tx1)] ∧
  (run R0 20 full haltedStart [.arrive 0]).bank = [(0, tx1)]''',5:'''(∀ o ∈ honestCOps, legalC R0 o) ∧
  (runC R0 20 true cinit honestCOps).bank = [(0, tx1)]''',6:'''haltedCStart.halted = true ∧ (∀ o ∈ [COp.bankProcess 0], legalC R0 o) ∧
  haltedCStart.bank = [] ∧ haltedCStart.wire = [(0, tx1)] ∧
  (runC R0 20 true haltedCStart [.bankProcess 0]).bank = [(0, tx1)]''',7:'''(∀ a ∈ R0.approvers, a ∉ ([1] : List ℕ)) ∧ BankHyp R0 honestTrace ∧
  ((authed (raw R0 20) ControlStack.SC26Authenticated.claim).run init honestTrace).bank = [(0, tx1)]''',8:'''forged.length = 5 ∧ R0.agents = [1] ∧ R0.approvers = [2] ∧
  tx1.amount = 10 ∧
  ((raw R0 20).run init (forged.map Prod.snd)).bank = [(0, tx1)] ∧
  ((authed (raw R0 20) ControlStack.SC26Authenticated.claim).run init forged).bank = []''',9:'''AdvTrace [1] honScript honestTrace ∧ (∀ a ∈ R0.approvers, a ∉ ([1] : List ℕ)) ∧
  R0.gate ∉ ([1] : List ℕ) ∧ BankHyp R0 honScript ∧
  ((authed (raw R0 20) ControlStack.SC26Authenticated.claim).run init honestTrace).bank = [(0, tx1)]''',10:'''Inv R0 20 ready ∧ ready.halted = false ∧ reqOf ready 0 = some ⟨0, 1, tx1⟩ ∧
  Approved R0 ready 0 ⟨0, 1, tx1⟩ ∧ 0 ∉ ready.reserved ∧ ready.spent + tx1.amount ≤ 20 ∧
  (0, tx1) ∈ (run R0 20 full ready [.execute 1 0, .deliver 0, .arrive 0]).bank'''}
for p in sorted((OUT/'typed').glob('*.lean')):
 n=int(p.name.split('-')[0]); cid=f'bg6n2_{n}'
 text=p.read_text(); ns=re.search(r'^namespace (.+)$',text,re.M).group(1)
 body=text.split('namespace '+ns+'\n',1)[1].rsplit('end '+ns,1)[0]
 body=re.sub(r'def Back_\w+ : Prop', 'def Back : Prop', body)
 opens=common + (ref if n in [5,6] else '') + (auth if n in [7,8,9] else '') + ('open ControlStack.AuthenticatedAdv\n' if n in [7,9] else '') + ('open ControlStack.SC26Liveness\n' if n==10 else '')
 statement=f'namespace PL_{cid}\n'+opens+body+'\n'+at[n]+orig[n]
 if n in [7,9]:statement+=hyp
 if n!=8:
  backenv=params[n]+'\n    BackAt '+args[n]
  origenv=(params[n].replace('(∀ a ∈ R.approvers, a ∉ U)','(∀ u ∈ U, u ∉ R.approvers)').replace('BankHyp','OrigBankHyp'))+'\n    OrigAt '+args[n]
 else:
  backenv='BackAt ((raw R0 20).run init (forged.map Prod.snd)).bank forged\n    ((authed (raw R0 20) ControlStack.SC26Authenticated.claim).run init forged).bank'
  origenv='OrigAt ((authed (raw R0 20) (fun _ => none)).run init forged).bank forged\n    ((authed (raw R0 20) ControlStack.SC26Authenticated.claim).run init forged).bank'
 statement+='def BackEnvelope : Prop := '+backenv+'\ndef OrigEnvelope : Prop := '+origenv+'\n'
 if n in point:
  statement+='def Claim : Prop := (Back ↔ BackEnvelope) ∧ ('+point[n]+')'+(' ∧ HypAgreement' if n in [7,9] else '')+'\n'
  proof='theorem original_signature : OrigEnvelope := '+sig[n]+'\n'
  if n in [7,9]:proof+=hproof
  proof+='theorem claim : Claim := by\n  refine ⟨Iff.rfl, '+('⟨?_, hypotheses_agree⟩' if n in [7,9] else '?_')+'⟩\n  '+{1:'intro R cap s',2:'intro R s',3:'intro s',5:'intro R cap s',6:'intro s t',7:'intro R cap U ops s',9:'intro R cap hon s',10:'intro R cap s k r caller'}[n]+'\n  exact Iff.rfl\n'
 elif n==4:
  statement+='''def Claim : Prop := (Back ↔ BackEnvelope) ∧
  (OrigEnvelope → Back) ∧
  (∀ (s t : St), OrigAt s t → BackAt s t) ∧
  (∃ (s t : St), s.halted = true ∧ BackAt s t ∧ ¬ OrigAt s t)
'''
  proof='''theorem original_signature : OrigEnvelope := '''+sig[n]+'''
theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_, ?_, ?_⟩
  · intro h R cap s ops hh hl
    obtain ⟨he, hb⟩ := h R cap s ops hh hl
    exact ⟨fun m => by rw [he], hb⟩
  · intro s t h
    exact ⟨fun m => by rw [h.1], h.2⟩
  · exact ⟨{ init with halted := true, net := [(0, tx1)] },
      { init with halted := true, net := [(0, tx1), (0, tx1)] },
      by decide, by simp [BackAt, init], by simp [OrigAt, init]⟩
'''
 else:
  statement+='''def Claim : Prop := (Back ↔ BackEnvelope) ∧
  (OrigEnvelope → Back) ∧
  (∀ (b : List (ℕ × Tx)) (guarded : List (ℕ × Tx)),
    OrigAt b forged guarded → BackAt b forged guarded) ∧
  (∃ (b : List (ℕ × Tx)) (guarded : List (ℕ × Tx)),
    BackAt b forged guarded ∧ ¬ OrigAt b forged guarded) ∧
  (∃ (ops : List (ℕ × Op)),
    OrigAt [(0, tx1)] ops [] ∧ ¬ BackAt [(0, tx1)] ops [])
'''
  proof='''theorem original_signature : OrigEnvelope := forged_approval_pays_without_auth
theorem raw_none_same (R : Roles) (cap : ℕ) (s : St) (ops : List (ℕ × Op)) :
    (authed (raw R cap) (fun _ => none)).run s ops = (raw R cap).run s (ops.map Prod.snd) := by
  induction ops generalizing s with
  | nil => rfl
  | cons io ops ih =>
    change (authed (raw R cap) (fun _ => none)).run ((raw R cap).step s io.2) ops =
      (raw R cap).run ((raw R cap).step s io.2) (ops.map Prod.snd)
    exact ih _
theorem original_to_back : OrigEnvelope → Back := by
  intro h
  change OrigAt _ _ _ at h
  unfold Back
  rw [← raw_none_same]
  exact ⟨by rw [h.1]; simp, by decide, h.2.2⟩
theorem claim : Claim := by
  refine ⟨Iff.rfl, original_to_back, ?_, ?_, ?_⟩
  · intro b guarded h
    exact ⟨by rw [h.1]; simp, by decide, h.2.2⟩
  · exact ⟨[(0, tx1), (0, tx1)], [], by simp [BackAt, forged, R0], by simp [OrigAt]⟩
  · exact ⟨[(2, Op.deliver 0)], by simp [OrigAt, R0], by simp [BackAt, R0]⟩
'''
 if n in [1,2,3]: statement+=hon
 if n==4: statement+='def haltedStart : St := { init with halted := true, net := [(0, tx1)] }\n'
 if n==5: statement+=chon
 if n==6:statement+='def haltedCStart : CSt := { cinit with halted := true, wire := [(0, tx1)] }\n'
 if n==10:statement+='def ready : St := ⟨1, [⟨0, 1, tx1⟩], [(0, 2, tx1)], [], 0, false, [], []⟩\n'
 statement+='def Witness : Prop := '+witness[n]+'\nend PL_'+cid+'\n'
 if n==1: proof+='theorem witness : Witness := by\n  unfold Witness\n  exact ⟨sound_full, by simp [honestOps, legal], by decide⟩\n'
 elif n==9:proof+='''theorem witness : Witness := by
  unfold Witness
  refine ⟨?_, by simp [R0], by simp [R0], by simp [BankHyp, honScript], by decide⟩
  refine ⟨advScript, by decide, ?_⟩
  exact .right _ (.left _ (.right _ (.right _ (.right _ .nil))))
'''
 elif n==10:proof+='''theorem witness : Witness := by
  unfold Witness
  refine ⟨?_, by decide, by decide, ?_, by decide, by decide, by decide⟩
  · constructor <;> simp [ready, reqOf, Approved, amt, tx1, R0]
  · exact ⟨2, by decide, by decide, by decide⟩
'''
 elif n==2:proof+='theorem witness : Witness := by\n  unfold Witness\n  exact ⟨by simp [R0], by simp [honestOps, legal], by decide⟩\n'
 elif n==4:proof+='theorem witness : Witness := by\n  unfold Witness\n  exact ⟨rfl, by simp [legal], rfl, rfl, by decide⟩\n'
 elif n==5:proof+='theorem witness : Witness := by\n  unfold Witness\n  exact ⟨by simp [honestCOps, legalC], by decide⟩\n'
 elif n==6:proof+='theorem witness : Witness := by\n  unfold Witness\n  exact ⟨rfl, by simp [legalC], rfl, rfl, by decide⟩\n'
 elif n==7:proof+='theorem witness : Witness := by\n  unfold Witness\n  exact ⟨by simp [R0], by simp [BankHyp, honestTrace], by decide⟩\n'
 else:proof+='theorem witness : Witness := by\n  unfold Witness\n  decide\n'
 proof=opens+proof
 (OUT/(cid+'.statement.lean')).write_text(statement)
 (OUT/(cid+'.proof.lean')).write_text(proof)
print('Wrote 10 statement/proof pairs and relocated unchanged security gate.')
