from pathlib import Path
import hashlib,json,re
OUT=Path(__file__).resolve().parent
root=OUT.parents[3]
info={
1:('ControlStack/Scenarios/SC28Budget.lean','sc28_safe','BackResult admins G ops','OrigResult admins G ops'),
2:('ControlStack/Scenarios/SC28Budget.lean','revoked_lease_stops','BackResult admins G C s lid ops','OrigResult admins G C s lid ops'),
3:('ControlStack/Scenarios/SC28Budget.lean','fork_shares_lease','BackResult admins G s caller parent child newLid lid','OrigResult admins G s c p ch nl lid'),
4:('ControlStack/Scenarios/SC28Budget.lean','halt_freezes','BackResult admins G s ops','OrigResult admins G s ops'),
5:('ControlStack/Scenarios/AuthInstancesA.lean','sc28_safe_authenticated','''let s := AuthenticatedLog.authRun (SC28.step admins G SC28.full) claim28 SC28.init ops
    BackResult admins G U ops s''','''OrigResult admins G U ops (AuthenticatedLog.authRun (SC28.step admins G full) claim28 SC28.init ops)'''),
6:('ControlStack/Scenarios/AuthInstancesA.lean','forged28_consumes_without_auth','''BackResult
    (run [9] 1000 full init (forged28.map Prod.snd))
    (AuthenticatedLog.authRun (step [9] 1000 full) claim28 init forged28)
    (Authenticated.applied claim28 forged28)''','''OrigResult
    (AuthenticatedLog.authRun (SC28.step [9] 1000 full) (fun _ => none) SC28.init forged28)
    (AuthenticatedLog.authRun (SC28.step [9] 1000 full) claim28 SC28.init forged28)'''),
7:('ControlStack/Scenarios/SC28Liveness.lean','honest_steps_progress','BackResult admins G s w lid units','OrigResult admins G s w lid as'),
8:('ControlStack/Scenarios/SC28Liveness.lean','progress_interleaved','BackResult admins G s w lid a reported p','OrigResult admins G s w lid a p'),
9:('ControlStack/Scenarios/SC28Liveness.lean','global_cap_blocks_honest','''let s := run [9] 10 full init [.issue 9 0 10, .issue 9 1 10, .assignTo 9 1 0, .assignTo 9 2 1, .work 2 10 10]
    BackResult s (step [9] 10 full s (.work 1 1 1))''','''let s := run [9] 10 full init [.issue 9 0 10, .issue 9 1 10, .assignTo 9 1 0, .assignTo 9 2 1, .work 2 10 10]
  OrigResult s (step [9] 10 full s (.work 1 1 1))'''),
10:('ControlStack/Core/AntiRollback.lean','sc28_rollback_safe','''BackResult admins G (runR (SC28.sys admins G) true (rinit (SC28.sys admins G) SC28.init) ops)''','''OrigResult admins G (runR (SC28.sys admins G) true (rinit (SC28.sys admins G) SC28.init) ops)'''),
11:('ControlStack/Scenarios/SC28Refinement.lean','concrete_safe','BackResult G (runC G cinit ops)','OrigResult G (runC G cinit ops)'),
12:('ControlStack/Scenarios/SC28Refinement.lean','concrete_revoked_stops','BackResult G lid first second','OrigResult G lid pre post'),
13:('ControlStack/Scenarios/SC28Refinement.lean','exclusive_placement_safe','BackResult G ops','OrigResult G ops'),
}
# Conclusion cut positions in the byte-preserved back definition.
starts={1:'    Good G',2:'    usedL (run',3:'    leaseOf (step',4:'    (run admins',5:'    let s :=',6:'  let unchecked',7:'    (run admins',8:'    let t :=',9:'  let s :=',10:'    let system :=',11:'    let s :=',12:'    counter (runC',13:'    let s :='}
manifest={}
for n,(path,name,backresult,origresult) in info.items():
 src=(root/path).read_text()
 start=src.index('theorem '+name+' ')
 # The theorem proof delimiter is on its signature's final line; lets in the type differ.
 tail=src[start:]
 end=re.search(r' :=(?: by|\n)',tail).start()
 header=tail[:end]
 (OUT/'original-signatures').mkdir(exist_ok=True)
 (OUT/'original-signatures'/f'{n}.txt').write_text(header+'\n')
 rest=header[len('theorem '+name):].strip()
 # Find the top-level colon that separates parameters from result type.
 depth=0; split=None
 for i,ch in enumerate(rest):
  if ch in '({[': depth+=1
  if ch in ')}]': depth-=1
  if ch==':' and depth==0: split=i;break
 assert split is not None,n
 params=rest[:split].strip(); conclusion=rest[split+1:].strip()
 if n == 9: conclusion=conclusion.replace('\n    ', '\n  ')
 if n in (7,8): params='(admins : List ℕ) (G : ℕ) '+params
 original='def OrigFull : Prop :=\n  '+(('∀ '+params+',\n    ') if params else '')+conclusion+'\n'
 schema='def OrigSchema : Prop :=\n  '+(('∀ '+params+',\n    ') if params else '')+origresult+'\n'
 p=OUT/f'bg7n2_{n}.statement.lean';s=p.read_text()
 back=s[s.index('def BackFull'):s.index('\ndef BackResult') if '\ndef BackResult' in s else s.index('\ndef BackFresh')]
 cut=back.index(starts[n])
 backschema=back[:cut].replace('def BackFull','def BackSchema',1)+'    '+backresult+'\n'
 insertion=original+'\n'+backschema+'\n'+schema+'\n'
 s=s.replace('def Claim : Prop :=\n','def Claim : Prop :=\n  (BackFull ↔ BackSchema) ∧ (OrigFull ↔ OrigSchema) ∧\n',1)
 s=s.replace('def Claim : Prop :=',insertion+'\ndef Claim : Prop :=',1)
 p.write_text(s)
 pp=OUT/f'bg7n2_{n}.proof.lean';t=pp.read_text()
 a=t.index('theorem claim : Claim :=\nby\n')+len('theorem claim : Claim :=\nby\n')
 t=t[:a]+'  refine ⟨Iff.rfl, Iff.rfl, ?_⟩\n'+t[a:]
 # A type annotation checks the imported declaration's signature only. Its proof
 # is not used to establish either direction of the pointwise comparison.
 namespace=re.search(r'namespace (\S+)',next((OUT/'typed').glob(f'{n}-*.lean')).read_text())[1]
 pos=t.index('theorem claim : Claim :=')
 t=t[:pos]+f'#check ({namespace}.{name} : OrigFull)\n\n'+t[pos:]
 pp.write_text(t)
 manifest[str(n)]={'path':path,'declaration':name,'source_sha256':hashlib.sha256(src.encode()).hexdigest(),'signature_sha256':hashlib.sha256((header+'\n').encode()).hexdigest()}
(OUT/'original-signatures/HASHES.json').write_text(json.dumps(manifest,indent=2)+'\n')
