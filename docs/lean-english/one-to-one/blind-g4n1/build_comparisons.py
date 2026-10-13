"""Build comparison artifacts from the already frozen Phase A definitions."""
from pathlib import Path
import hashlib,json
OUT=Path(__file__).resolve().parent
frozen=json.loads((OUT/'typed/HASHES.json').read_text())
assert all(hashlib.sha256((OUT/v['file']).read_bytes()).hexdigest()==v['sha256'] for v in frozen['files'].values())
base='ControlStack.SC18'
resume='ControlStack.SC18Liveness.Resume'
configs={
1:('ControlStack.SC18','(admins : List ℕ) (trusted T : ℕ) (ops : List Op)','admins trusted T ops','(∀ o ∈ ops, legal admins trusted o) →','Good T (run admins trusted T full (init trusted) ops)','Good T (run admins trusted T full (init trusted) ops)'),
2:('ControlStack.SC18','(admins : List ℕ) (trusted T : ℕ) (ops : List Op)','admins trusted T ops','(∀ o ∈ ops, legal admins trusted o) →','(run admins trusted T full (init trusted) ops).cfg = trusted','(run admins trusted T full (init trusted) ops).cfg = trusted'),
3:('ControlStack.SC18','(admins : List ℕ) (trusted T : ℕ) (s : St) (ops : List Op)','admins trusted T s ops','s.halted = true →','(run admins trusted T full s ops).released = s.released','(run admins trusted T full s ops).released = s.released'),
6:('ControlStack.SC18Liveness','(admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (i : ℕ)','admins trusted T s i','s.halted = false → s.sinkUp = true →','i ∈ (ControlStack.SC18.run admins trusted T ControlStack.SC18.full s [.request i, .logWrite i, .release i]).released.map ControlStack.SC18.Rel.id','i ∈ (ControlStack.SC18.run admins trusted T ControlStack.SC18.full s [.request i, .logWrite i, .release i]).released.map ControlStack.SC18.Rel.id'),
7:('ControlStack.SC18Liveness','(admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (i : ℕ) (a0 a1 a2 a3 : List ControlStack.SC18.Op)','admins trusted T s i a0 a1 a2 a3','', '''let beforeLog := ControlStack.SC18.run admins trusted T ControlStack.SC18.full s (a0 ++ [.request i] ++ a1)
    let final := ControlStack.SC18.run admins trusted T ControlStack.SC18.full s (a0 ++ [.request i] ++ a1 ++ [.logWrite i] ++ a2 ++ [.release i] ++ a3)
    i ∈ final.released.map ControlStack.SC18.Rel.id ∨ final.halted = true ∨ beforeLog.sinkUp = false''', '''let t := ControlStack.SC18.run admins trusted T ControlStack.SC18.full s (a0 ++ .request i :: a1 ++ .logWrite i :: a2 ++ .release i :: a3)
    i ∈ t.released.map ControlStack.SC18.Rel.id ∨ t.halted = true ∨
      (ControlStack.SC18.run admins trusted T ControlStack.SC18.full (ControlStack.SC18.step admins trusted T ControlStack.SC18.full (ControlStack.SC18.run admins trusted T ControlStack.SC18.full s a0) (.request i)) a1).sinkUp = false'''),
8:('ControlStack.SC18Liveness','(admins : List ℕ) (trusted T : ℕ) (s : ControlStack.SC18.St) (n : ℕ)','admins trusted T s n','(s.halted = false → s.clock ≤ s.lastAck + T) → s.lastAck + T < s.clock + n →','(ControlStack.SC18.run admins trusted T ControlStack.SC18.full s (List.replicate n ControlStack.SC18.Op.tick)).halted = true','(ControlStack.SC18.run admins trusted T ControlStack.SC18.full s (List.replicate n ControlStack.SC18.Op.tick)).halted = true'),
9:(resume,'(admins : List ℕ) (T : ℕ) (ops : List Op)','admins T ops','', '''let final := run admins T init ops
    (∀ r ∈ final.released, RelOk T final r) ∧ (final.released.map ControlStack.SC18.Rel.id).Nodup''','''(∀ r ∈ (run admins T init ops).released, RelOk T (run admins T init ops) r) ∧ ((run admins T init ops).released.map ControlStack.SC18.Rel.id).Nodup'''),
10:(resume,'(admins : List ℕ) (T : ℕ) (s : St) (i : ℕ)','admins T s i','s.halted = false → s.sinkUp = true → i ∈ s.reqs →','i ∈ (run admins T s [.logWrite i, .release i]).released.map ControlStack.SC18.Rel.id','i ∈ (run admins T s [.logWrite i, .release i]).released.map ControlStack.SC18.Rel.id')}
witnesses={
1:'''let ops : List Op := [.request 0, .logWrite 0, .tick, .release 0]
    (∀ o ∈ ops, legal [9] 0 o) ∧
    (run [9] 0 2 full (init 0) ops).released = [⟨0, 1, 1, 0⟩] ∧
    Good 2 (run [9] 0 2 full (init 0) ops)''',
2:'''let ops : List Op := [.setSink 1 66, .setSink 9 0, .request 0, .logWrite 0, .release 0]
    (∀ o ∈ ops, legal [9] 0 o) ∧
    (run [9] 0 2 full (init 0) ops).cfg = 0 ∧
    (run [9] 0 2 full (init 0) ops).released.map Rel.id = [0]''',
3:'''let s : St := { init 0 with halted := true, clock := 7, released := [⟨0, 1, 0, 0⟩] }
    let ops : List Op := [.tick, .sinkDown, .request 1, .logWrite 1, .release 1]
    s.halted = true ∧ (run [9] 0 2 full s ops).released = s.released ∧
    (run [9] 0 2 full s ops).clock = 7 ∧ (run [9] 0 2 full s ops).sinkUp = false ∧
    step [9] 0 2 full s .tick = s''',
6:'''let s := ControlStack.SC18.init 66
    let t := ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s [.request 0, .logWrite 0, .release 0]
    let old : ControlStack.SC18.St := { ControlStack.SC18.init 0 with released := [⟨0, 0, 100, 0⟩] }
    let oldFinal := ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full old [.request 0, .logWrite 0, .release 0]
    s.halted = false ∧ s.sinkUp = true ∧ t.released = [⟨0, 0, 0, 0⟩] ∧ t.logged = [] ∧
    ¬ ControlStack.SC18.Good 2 t ∧ old.halted = false ∧ old.sinkUp = true ∧
    oldFinal.released = old.released ∧ 0 ∈ oldFinal.released.map ControlStack.SC18.Rel.id ∧
    ¬ ControlStack.SC18.Good 2 oldFinal''',
7:'''let s := ControlStack.SC18.init 0
    let t := ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s
      ([.setSink 1 66] ++ [.request 0] ++ [.tick] ++ [.logWrite 0] ++ [.sinkDown] ++ [.release 0] ++ [.sinkRestore])
    let halted := ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s [.halt 9, .request 0, .logWrite 0, .release 0]
    let down := ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s [.request 0, .sinkDown, .logWrite 0, .release 0]
    let outage := ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s [.request 0, .logWrite 0, .sinkDown, .release 0]
    outage.sinkUp = false ∧ outage.released.map ControlStack.SC18.Rel.id = [0] ∧
    t.released.map ControlStack.SC18.Rel.id = [0] ∧ t.halted = false ∧
    halted.released = [] ∧ halted.halted = true ∧
    down.released = [] ∧ down.halted = false ∧
    (ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s [.request 0, .sinkDown]).sinkUp = false''',
8:'''let s := ControlStack.SC18.init 0
    (s.halted = false → s.clock ≤ s.lastAck + 2) ∧ s.lastAck + 2 < s.clock + 3 ∧
    (ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s (List.replicate 3 ControlStack.SC18.Op.tick)).halted = true ∧
    (ControlStack.SC18.run [9] 0 2 ControlStack.SC18.full s (List.replicate 3 ControlStack.SC18.Op.tick)).clock = 3''',
9:'''let pausedOps : List Op := [.request 0, .logWrite 0, .sinkDown, .tick, .tick, .tick, .release 0]
    let resumedOps := pausedOps ++ [.sinkRestore, .logWrite 0, .release 0]
    (run [9] 2 init pausedOps).released = [] ∧ (run [9] 2 init pausedOps).paused = true ∧
    (run [9] 2 init resumedOps).released = [⟨0, 2, 3, 3⟩] ∧
    BackAt [9] 2 resumedOps''',
10:'''let s : St := { init with reqs := [0], paused := true, clock := 10 }
    let old : St := { s with released := [⟨0, 0, 100, 0⟩] }
    let t := run [9] 2 s [.logWrite 0, .release 0]
    let oldFinal := run [9] 2 old [.logWrite 0, .release 0]
    s.halted = false ∧ s.sinkUp = true ∧ 0 ∈ s.reqs ∧ s.paused = true ∧
    t.released = [⟨0, 1, 10, 10⟩] ∧ t.paused = false ∧
    old.halted = false ∧ old.sinkUp = true ∧ 0 ∈ old.reqs ∧
    oldFinal.released = old.released ∧ 0 ∈ oldFinal.released.map ControlStack.SC18.Rel.id ∧
    ¬ RelOk 2 oldFinal ⟨0, 0, 100, 0⟩'''}
manifest={}
for n,v in frozen['files'].items():
 n=int(n);p=OUT/v['file']; src=p.read_text(); start=src.index('def Back_'); stop=src.rindex('\nend '); back=src[start:stop].strip(); name=back.split()[1]; cid=f'bg4n1_{n}'
 if n in configs:
  ns,params,args,hyp,b,o=configs[n]
  stmt=f'namespace PL_{cid}\nopen {ns}\n\n{back}\n\ndef BackAt {params} : Prop :=\n    {b}\n\ndef OrigAt {params} : Prop :=\n    {o}\n\ndef Claim : Prop :=\n  ({name} ↔ ∀ {params}, {hyp} BackAt {args}) ∧\n  (∀ {params}, {hyp} (BackAt {args} ↔ OrigAt {args}))\n\ndef Witness : Prop :=\n    {witnesses[n]}\n\nend PL_{cid}\n'
  if n==7:
   proof='theorem claim : Claim := by\n  constructor\n  · exact Iff.rfl\n  · intro admins trusted T s i a0 a1 a2 a3\n    simp only [BackAt, OrigAt, ControlStack.SC18.run, List.foldl_append, List.foldl_cons, List.foldl_nil]\n'
  else:
   intros=args+(' hops' if n in [1,2] else ' hh' if n==3 else ' hh hu' if n==6 else ' hinv hn' if n==8 else ' hh hu hr' if n==10 else '')
   proof=f'theorem claim : Claim := by\n  constructor\n  · exact Iff.rfl\n  · intro {intros}\n    exact Iff.rfl\n'
 elif n==5:
  ns='ControlStack.AuthInstances';conclusion=back.split(':=',1)[1].strip()
  stmt=f'''namespace PL_{cid}
open {ns}

{back}

def BackAt : Prop :=
  {conclusion}

def OrigAt : Prop :=
  {conclusion}

def Claim : Prop := ({name} ↔ BackAt) ∧ (BackAt ↔ OrigAt)

def Witness : Prop :=
  forged18 = [(1, ControlStack.SC18.Op.setSink 9 66)] ∧ BackAt

end PL_{cid}
'''
  proof='theorem claim : Claim := ⟨Iff.rfl, Iff.rfl⟩\n'
 else:
  ns='ControlStack.AuthInstances'
  stmt=f'''namespace PL_{cid}
open ControlStack.AuthInstances

{back}

def BackAt (admins : List ℕ) (trusted T : ℕ) (_U : ℕ → Prop)
    (ops : List (ℕ × ControlStack.SC18.Op)) : Prop :=
  ControlStack.SC18.Good T (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC18.step admins trusted T ControlStack.SC18.full)
    claim18 (ControlStack.SC18.init trusted) ops)

def OrigAt (admins : List ℕ) (trusted T : ℕ) (_U : List ℕ)
    (ops : List (ℕ × ControlStack.SC18.Op)) : Prop :=
  ControlStack.SC18.Good T (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC18.step admins trusted T ControlStack.SC18.full)
    claim18 (ControlStack.SC18.init trusted) ops)

def Claim : Prop :=
  ({name} ↔ ∀ (admins : List ℕ) (trusted T : ℕ) (U : ℕ → Prop)
    (ops : List (ℕ × ControlStack.SC18.Op)),
    (∀ a : ℕ, U a → a ∉ admins) →
    (∀ io ∈ ops, ¬ U io.1 → ControlStack.SC18.legal admins trusted io.2) →
    BackAt admins trusted T U ops) ∧
  (∀ (admins : List ℕ) (trusted T : ℕ) (U : List ℕ)
    (ops : List (ℕ × ControlStack.SC18.Op)),
    (∀ a ∈ U, a ∉ admins) →
    (∀ io ∈ ops, io.1 ∉ U → ControlStack.SC18.legal admins trusted io.2) →
    (BackAt admins trusted T (fun a => a ∈ U) ops ↔ OrigAt admins trusted T U ops)) ∧
  (∀ (admins : List ℕ) (trusted T : ℕ) (U : ℕ → Prop)
    (ops : List (ℕ × ControlStack.SC18.Op)), ∃ V : List ℕ,
    ((∀ a, U a → a ∉ admins) ↔ (∀ a ∈ V, a ∉ admins)) ∧
    ((∀ io ∈ ops, ¬ U io.1 → ControlStack.SC18.legal admins trusted io.2) ↔
      (∀ io ∈ ops, io.1 ∉ V → ControlStack.SC18.legal admins trusted io.2)) ∧
    (BackAt admins trusted T U ops ↔ OrigAt admins trusted T V ops))

def Witness : Prop :=
  let ops : List (ℕ × ControlStack.SC18.Op) :=
    [(1, .setSink 9 66), (9, .setSink 9 0), (1, .request 0), (1, .logWrite 0), (1, .release 0)]
  (∀ a : ℕ, a = 1 → a ∉ [9]) ∧
  (∀ io ∈ ops, ¬ (io.1 = 1) → ControlStack.SC18.legal [9] 0 io.2) ∧
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC18.step [9] 0 2 ControlStack.SC18.full) claim18 (ControlStack.SC18.init 0) ops).cfg = 0 ∧
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC18.step [9] 0 2 ControlStack.SC18.full) claim18 (ControlStack.SC18.init 0) ops).released.map ControlStack.SC18.Rel.id = [0]

end PL_{cid}
'''
  proof='''theorem claim : Claim := by
  classical
  refine ⟨Iff.rfl, ?_, ?_⟩
  · intro admins trusted T U ops hU ht
    exact Iff.rfl
  · intro admins trusted T U ops
    let V := (admins ++ ops.map Prod.fst).filter (fun a => decide (U a))
    have memV (a : ℕ) : a ∈ V ↔ a ∈ admins ++ ops.map Prod.fst ∧ U a := by
      simp [V]
      tauto
    refine ⟨V, ?_, ?_, Iff.rfl⟩
    · constructor
      · intro h a ha
        exact h a ((memV a).mp ha).2
      · intro h a hUa ha
        exact h a ((memV a).mpr ⟨List.mem_append_left _ ha, hUa⟩) ha
    · constructor
      · intro h io hio hnV
        apply h io hio
        intro hUi
        apply hnV
        exact (memV io.1).mpr ⟨List.mem_append_right _ (List.mem_map.mpr ⟨io, hio, rfl⟩), hUi⟩
      · intro h io hio hnU
        apply h io hio
        intro hV
        exact hnU ((memV io.1).mp hV).2
'''
 (OUT/f'{cid}.statement.lean').write_text(stmt)
 (OUT/f'{cid}.proof.lean').write_text(proof)
 if n==4:
  witness_proof="""theorem witness : Witness := by
  unfold Witness
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    subst a
    decide
  · intro io hio hni
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hio
    rcases hio with hio | hio | hio | hio | hio
    all_goals subst io
    all_goals simp_all [ControlStack.SC18.legal]
  · decide
  · decide
"""
 elif n in [1,2]:
  if n==1: defs='Witness, ControlStack.SC18.Good, ControlStack.SC18.RelOk, ControlStack.SC18.legal, ControlStack.SC18.run, ControlStack.SC18.step, ControlStack.SC18.full, ControlStack.SC18.init'
  elif n==2: defs='Witness, ControlStack.SC18.legal, ControlStack.SC18.run, ControlStack.SC18.step, ControlStack.SC18.full, ControlStack.SC18.init'
  elif n==6: defs='Witness, ControlStack.SC18.Good, ControlStack.SC18.RelOk, ControlStack.SC18.run, ControlStack.SC18.step, ControlStack.SC18.full, ControlStack.SC18.init'
  else: defs='Witness, BackAt, RelOk, run, step, init'
  witness_proof=f'theorem witness : Witness := by\n  simp [{defs}]\n'
 else:
  defs='Witness, BackAt' if n==5 else 'Witness, ControlStack.SC18Liveness.Resume.RelOk' if n==10 else 'Witness, ControlStack.SC18.Good, ControlStack.SC18.RelOk' if n==6 else 'Witness, BackAt, ControlStack.SC18Liveness.Resume.RelOk' if n==9 else 'Witness'
  witness_proof=f'theorem witness : Witness := by\n  simp only [{defs}]\n  decide\n'
 (OUT/f'{cid}.witness.lean').write_text(witness_proof)
 manifest[str(n)]={'typed_sha256':v['sha256'],'copied_back_definition_sha256':hashlib.sha256(back.encode()).hexdigest(),'namespace_opened':ns,'original':p.name.split('-',1)[1].removesuffix('.lean'),'comparison':'pointwise conclusions with source reconstruction; claim 4 additionally proves finite representation of both hypotheses'}
(OUT/'comparison-map.json').write_text(json.dumps(manifest,indent=2)+'\n')
