"""Save pointwise comparisons of frozen translations and inspected source signatures."""
from pathlib import Path
import json, hashlib
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[3]
T = 'ControlStack.TrustedBroker.'
D = 'ControlStack.Deployment.'
TR = D+'TranscriptReplay.'
C = 'ControlStack.CheckedTrace.'
opens = 'open ControlStack ControlStack.TrustedBroker ControlStack.Deployment ControlStack.Deployment.TranscriptReplay\n'
params = {
1: '(R : Roles) (table : IndexedBrokerTable R) (start : Nat) (rs : List (CheckedTrace.Receipt Nat Nat))',
2: '(roles : Roles) (s t : State)',
3: '(roles : Roles) (s t : State)',
4: "(roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease) (r' : Request) (now : Nat) (a' : Approval) (l' : Lease)",
5: '(roles : Roles) (s t : State)',
6: '',
7: "(now : Nat) (a' : Approval) (l' : Lease)",
8: ''}
args = {1:'R table start rs',2:'roles s t',3:'roles s t',4:"roles s r a l r' now a' l'",5:'roles s t',6:'',7:"now a' l'",8:''}
hyps = {1:'CheckedTrace.verified table.step start rs = true',2:'Safe s → Step roles s t',3:'Coherent s → Step roles s t',4:"r'.nonce = r.nonce",5:'Safe s → Trace roles s t',6:'',7:'',8:''}
conclusions = {
1:'TrustedBroker.Trace R (table.interpret start) (table.interpret (CheckedTrace.recordedEnd start rs))',
2:'Safe t',3:'Coherent t',
4:"¬ Allowed roles (committed s r a l) now r' a' l'",
5:'Safe t',6:'TrustedBroker.Safe s10',
7:"¬ TrustedBroker.Allowed R s8 now q8 a' l'",
8:'CheckedTrace.verified table.step 0 withoutLastRelease = true'}
# Original signatures keep their actual binder order. Only pointwise comparisons align arguments.
orig_sigs = {
1:'∀ (R : Roles) (table : IndexedBrokerTable R) (rs : List (CheckedTrace.Receipt Nat Nat)) (start : Nat), CheckedTrace.verified table.step start rs = true → TrustedBroker.Trace R (table.interpret start) (table.interpret (CheckedTrace.recordedEnd start rs))',
2:'∀ (roles : Roles) (s t : State), Safe s → Step roles s t → Safe t',
3:'∀ (roles : Roles) (s t : State), Coherent s → Step roles s t → Coherent t',
4:"∀ (roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease) (now : Nat) (r' : Request) (a' : Approval) (l' : Lease), r'.nonce = r.nonce → ¬ Allowed roles (committed s r a l) now r' a' l'",
5:'∀ (roles : Roles) (s t : State), Safe s → Trace roles s t → Safe t',
6:conclusions[6],7:"∀ (now : Nat) (a' : Approval) (l' : Lease), "+conclusions[7],8:conclusions[8]}
witnesses = {
1:'∃ (R : Roles) (table : IndexedBrokerTable R) (start : Nat) (rs : List (CheckedTrace.Receipt Nat Nat)), rs ≠ [] ∧ CheckedTrace.verified table.step start rs = true ∧ (table.interpret start).spent < (table.interpret (CheckedTrace.recordedEnd start rs)).spent',
2:'∃ (roles : Roles) (s t : State), Safe s ∧ Step roles s t ∧ s.spent < t.spent',
3:'∃ (roles : Roles) (s t : State), Coherent s ∧ Step roles s t ∧ 1 ∉ s.consumed ∧ 1 ∈ t.consumed',
4:"∃ (roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease) (now : Nat) (r' : Request), Allowed roles s now r a l ∧ r'.nonce = r.nonce ∧ 0 < r.cost ∧ ¬ Allowed roles (committed s r a l) now r' a l",
5:'∃ (roles : Roles) (s t : State), Safe s ∧ Trace roles s t ∧ s.spent < t.spent ∧ t.releases = 2',
6:'s10.spent = 2 ∧ s10.cap = 2 ∧ s10.releases = 2 ∧ s10.consumed = [2, 1] ∧ (s10.leases 1).map Lease.used = some 1 ∧ (s10.leases 2).map Lease.used = some 1',
7:'q8 = q7 ∧ s8 = committed s7 q7 a1 l1 ∧ Allowed R s7 ControlStack.Deployment.TranscriptReplay.now q7 a1 l1 ∧ s8.approvals 1 = some {a1 with used := true}',
8:'receipts.length = 10 ∧ withoutLastRelease.length = 9 ∧ withoutLastRelease ≠ [] ∧ CheckedTrace.recordedEnd 0 withoutLastRelease = 9 ∧ CheckedTrace.recordedEnd 0 receipts = 10 ∧ CheckedTrace.verified table.step 0 receipts = true ∧ CheckedTrace.verified table.step 0 withoutMiddleRelease = false ∧ CheckedTrace.verified table.step 0 withoutDenial = false'}
prefix='(.cons tx0 (.cons tx1 (.cons tx2 (.cons tx3 (.cons tx4 (.cons tx5 (.cons tx6 (.nil s7))))))))'
allowed='''by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | exact ⟨23703, rfl⟩ | exact Or.inl rfl | decide'''
proofs = {
1:'''by
  refine ⟨R, table, 0, receipts, ?_, transcript_checked, ?_⟩
  · decide
  · decide''',
2:f'''by
  refine ⟨R, s7, s8, ?_, tx7, ?_⟩
  · exact trace_preserves R s0 s7 (initial_safe 2) {prefix}
  · decide''',
3:f'''by
  refine ⟨R, s7, s8, ?_, tx7, ?_, ?_⟩
  · exact trace_coherent R s0 s7 (initial_coherent 2) {prefix}
  · decide
  · decide''',
4:f'''by
  refine ⟨R, s7, q7, a1, l1, ControlStack.Deployment.TranscriptReplay.now, q8, ?_, rfl, ?_, ?_⟩
  · exact {allowed}
  · decide
  · exact committed_nonce_unusable R s7 q7 a1 l1 ControlStack.Deployment.TranscriptReplay.now q8 a1 l1 rfl''',
5:'''by
  refine ⟨R, s0, s10, initial_safe 2, runtime_trace, ?_, ?_⟩ <;> decide''',
6:'by unfold Witness; decide',
7:f'''by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact {allowed}
  · decide''',
8:'by unfold Witness; decide'}
mapping={}
for f in sorted((OUT/'typed').glob('*.lean')):
 n=int(f.name.split('-')[0]);name=f.stem.split('-',1)[1];cid=f'bg0n2_{n}'
 text=f.read_text();body=text[text.index('def Back_'):text.rindex('\nend ')].strip()
 back_name='Back_'+name
 # Retain the frozen definition text exactly, with its original ambient namespace opened.
 ambient=D if n==1 else T if n in [2,3,4,5] else TR
 header=f'namespace PL_{cid}\nopen {ambient.rstrip(".")}\n'+opens
 back_term='BackConclusion '+args[n]
 orig_term='OrigConclusion '+args[n]
 quantifier=('∀ '+params[n]+', ') if params[n] else ''
 implications=(hyps[n]+' → ') if hyps[n] else ''
 back_shape=quantifier+implications+back_term
 pointwise=quantifier+implications+'('+back_term+' ↔ '+orig_term+')'
 orig_params=params[n]
 if n==1:
  orig_params='(R : Roles) (table : IndexedBrokerTable R) (rs : List (CheckedTrace.Receipt Nat Nat)) (start : Nat)'
 elif n==4:
  orig_params="(roles : Roles) (s : State) (r : Request) (a : Approval) (l : Lease) (now : Nat) (r' : Request) (a' : Approval) (l' : Lease)"
 orig_shape=(('∀ '+orig_params+', ') if orig_params else '')+implications+orig_term
 source_name=ambient+name
 statement=header+'\n'+body+'\n\n'
 statement+=f'def BackConclusion {params[n]} : Prop :=\n  {conclusions[n]}\n\n'
 statement+=f'def OrigConclusion {params[n]} : Prop :=\n  {conclusions[n]}\n\n'
 statement+=f'def OrigSignature : Prop :=\n  {orig_sigs[n]}\n\n'
 statement+=f'theorem originalSignatureChecked : OrigSignature :=\n  @{source_name}\n\n'
 statement+=f'def Claim : Prop :=\n  ({back_name} = ({back_shape})) ∧\n  (OrigSignature = ({orig_shape})) ∧\n  ({pointwise})\n\n'
 statement+=f'def Witness : Prop :=\n  {witnesses[n]}\n\nend PL_{cid}\n'
 claim='by\n  refine ⟨rfl, rfl, ?_⟩\n  '+('intros\n  ' if params[n] or hyps[n] else '')+'exact Iff.rfl'
 proof=opens+f'theorem claim : Claim := {claim}\n\ntheorem witness : Witness := {proofs[n]}\n'
 (OUT/f'{cid}.statement.lean').write_text(statement)
 (OUT/f'{cid}.proof.lean').write_text(proof)
 src=ROOT/('ControlStack/Deployment/R2Contracts.lean' if n==1 else 'ControlStack/TrustedBroker.lean' if n in [2,3,4,5] else 'ControlStack/Deployment/TranscriptReplay.lean')
 source=src.read_text();sig=source[source.index('theorem '+name):].split(':=',1)[0].strip()
 mapping[cid]={'typed_file':str(f.relative_to(OUT)), 'typed_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'original_file':str(src.relative_to(ROOT)), 'original_signature_text':sig, 'conclusion':conclusions[n], 'hypotheses':hyps[n], 'method':'Definitional equality of frozen Back shape; pointwise iff by Iff.rfl, no use of truth of original theorem. Original signature separately type-checked against its declaration.'}
(OUT/'comparison-map.json').write_text(json.dumps(mapping,indent=2)+'\n')
