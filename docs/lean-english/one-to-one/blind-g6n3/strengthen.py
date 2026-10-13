"""Link pointwise outcomes mechanically to the frozen Back and original signatures."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent
root=P.parents[3]
items=[('progress_interleaved','SC26Liveness'),('crash_tolerant_progress','SC26Liveness'),('lossy_safe','SC26LossyLiveness'),('lossy_rounds','SC26LossyLiveness'),('lossy_halt_keys','SC26LossyHalt'),('tagged_rounds','SC26LossyHalt')]
excerpts=[]
for n,(name,mod) in enumerate(items,1):
 cid=f'bg6n3_{n}'
 src=(root/f'ControlStack/Scenarios/{mod}.lean').read_text()
 a=src.index('theorem '+name+' '); b=src.index(' := by',a)
 header=src[a:b]
 excerpts.append(header+' := [proof omitted]\n')
 binders,conclusion=header[len('theorem '+name+' '):].rsplit(' :\n',1)
 original=f'def OriginalSignature : Prop :=\n  ∀ {binders},\n{conclusion}\n'
 frozen=next((P/'typed').glob(f'{n}-*.lean')).read_text()
 frozen=frozen[frozen.index('def Back_'):frozen.rindex('\nend ')]
 backbody=frozen.split(': Prop :=',1)[1]
 if n==1:
  backnorm=backbody[:backbody.index('    let beforeExecute')]+ '    BackAt R cap s k r pre mid₁ mid₂ post\n'
  orignorm=f'∀ {binders}, OrigAt R cap s c k r a0 a1 a2 a3'
 elif n==2:
  backnorm=backbody[:backbody.index('    let final')]+ '    BackAt R cap k ops₀ pre mid post\n'
  orignorm=f'∀ {binders}, OrigAt R cap k ops0 pre mid post'
 elif n==3:
  backnorm=backbody[:backbody.index('    Good')]+ '    BackAt R cap ops\n'
  orignorm=f'∀ {binders}, OrigAt R cap ops'
 elif n==5:
  backnorm=backbody[:backbody.index('    ∀ k ∈')]+ '    ∀ k, BackAt R cap s ops k\n'
  binders5=binders[:binders.index(' (hx :')]
  orignorm=f'∀ {binders5}, OrigAt R cap s ops x'
 else:
  mode='L' if n==4 else 'T'
  state='runL R cap true cinit ops₀' if n==4 else 'runT R cap tinit ops₀'
  fin='runL R cap true start (rounds.map roundOps).flatten' if n==4 else 'runT R cap start (rounds.map roundOps).flatten'
  keys='final.bank.map Prod.fst' if n==4 else 'final.c.bank.map Prod.fst'
  cont='((runL R cap true final post).bank.map Prod.fst).count k = 1' if n==4 else '((runT R cap final post).c.bank.map Prod.fst).count k = 1'
  outcome=f'''def BackOutcome (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
    (rounds : List (List LOp × List LOp)) : Prop :=
  let start := {state}
  let final := {fin}
  k ∈ {keys} ∧ ∀ post : List LOp, (∀ o ∈ post, legalL R o) → {cont}
'''
  if n==4:
   backnorm=backbody[:backbody.index('    k ∈ final.bank')]+ '    BackOutcome R cap k ops₀ rounds\n'
  else:
   backnorm=backbody[:backbody.index('    let final')]+ '    BackOutcome R cap k ops₀ rounds\n'
  orignorm=f'∀ {binders}, OrigAt R cap k ops0 rounds post'
 additions=original+f'\ndef BackShape : Prop := Back_{name} ↔\n{backnorm}\ndef OriginalShape : Prop := OriginalSignature ↔\n  {orignorm}\n'
 if n in [4,6]:
  additions=outcome+'\n'+additions+'''\ndef Projection : Prop := ∀ R cap k ops₀ rounds,
  BackOutcome R cap k ops₀ rounds ↔
    ∀ post, (∀ o ∈ post, legalL R o) → BackAt R cap k ops₀ rounds post
'''
  newclaim='def Claim : Prop := Pointwise ∧ BackShape ∧ OriginalShape ∧ Projection\n'
  proofextra='''theorem projection : Projection := by
  intro R cap k ops₀ rounds
  constructor
  · rintro ⟨hm, hc⟩ post hp
    exact ⟨hm, hc post hp⟩
  · intro h
    exact ⟨(h [] (by simp)).1, fun post hp => (h post hp).2⟩

theorem claim : Claim := ⟨pointwise, Iff.rfl, Iff.rfl, projection⟩
'''
 else:
  newclaim='def Claim : Prop := Pointwise ∧ BackShape ∧ OriginalShape\n'
  proofextra='theorem claim : Claim := ⟨pointwise, Iff.rfl, Iff.rfl⟩\n'
 f=P/f'{cid}.statement.lean'; s=f.read_text().replace('def Claim : Prop :=','def Pointwise : Prop :=')
 s=s.replace(f'\nend PL_{cid}', '\n'+additions+'\n'+newclaim+f'\nend PL_{cid}')
 f.write_text(s)
 f=P/f'{cid}.proof.lean'; s=f.read_text().replace('theorem claim : Claim :=', 'theorem pointwise : Pointwise :=')
 f.write_text(s+'\n'+proofextra)
(P/'original-signatures.txt').write_text('\n'.join(excerpts))
