"""Create reviewable pointwise comparisons from the frozen Phase A bodies."""
from pathlib import Path
import hashlib, json, re

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[3]
hashes = json.loads((OUT / 'typed/HASHES.json').read_text())['files']
DATA = {}

DATA[1] = dict(
    params='(St Op Eff : Type) [DecidableEq St] [DecidableEq Op] (G : System St Op Eff) (S : Spec G) (initial : St) (ops : List (ROp Op))',
    args='St Op Eff G S initial ops',
    hyp='S.Inv initial',
    back='''let final := runR G true (rinit G initial) ops
  let plain := G.run initial final.committed
  final.anchor.st = plain ∧ final.released = G.effects plain ∧ S.Inv plain ∧
    (∀ e ∈ final.released, S.ok plain e) ∧ final.anchor.ver = final.committed.length''',
    orig='''let t := runR G true (rinit G initial) ops
  t.anchor.st = G.run initial t.committed ∧ t.released = G.effects (G.run initial t.committed) ∧
    S.Inv (G.run initial t.committed) ∧ (∀ e ∈ t.released, S.ok (G.run initial t.committed) e) ∧
    t.anchor.ver = t.committed.length''',
    witness='''∃ (G : System (List ℕ) ℕ ℕ) (S : Spec G), S.Inv [] ∧
  (let t := runR G true (rinit G []) [.write 5, .bump, .write 6, .bump, .rollback 0, .write 7]
   t.committed = [5, 6] ∧ t.anchor.st = [5, 6] ∧ t.released = [5, 6] ∧ t.halted = true) ∧
  (let t := runR G true (rinit G []) [.write 5, .bump, .rollback 1, .write 6, .bump]
   t.committed = [5, 6] ∧ t.halted = false)''',
    wproof='''  unfold Witness
  let G : System (List ℕ) ℕ ℕ := ⟨fun s o => s ++ [o], id⟩
  let S : Spec G := {
    Inv := fun _ => True
    ok := fun s e => e ∈ s
    step_inv := fun _ _ _ => True.intro
    log_prefix := fun s o => List.prefix_append s [o]
    inv_ok := fun _ _ _ he => he }
  refine ⟨G, S, True.intro, ?_, ?_⟩ <;> decide''')

DATA[2] = dict(
    params='(E : Env) (ops : List Op)', args='E ops',
    hyp='Set.InjOn (chainHead E.H E.h0) {l | l ∈ (run E full init ops).accepted ∨ ∃ a ∈ (run E full init ops).anchors, a.2 = some l}',
    back='''let final := run E full init ops
  ∀ m ∈ final.accepted, ∃ a ∈ final.anchors, a.2 = some m''',
    orig='∀ m ∈ (run E full init ops).accepted, ∃ a ∈ (run E full init ops).anchors, a.2 = some m',
    witness='''let t := run E0 full init [.append 5, .anchor, .verify [5]]
  t.accepted = [[5]] ∧ t.anchors = [(6, some [5])] ∧
  Set.InjOn (chainHead E0.H E0.h0) {l | l ∈ t.accepted ∨ ∃ a ∈ t.anchors, a.2 = some l} ∧
  (run E0 full init [.append 5, .rewrite [7], .anchor, .verify [7]]).accepted = [[7]] ∧
  (run E0 full init [.append 5, .anchor, .append 6, .anchor, .verify [5]]).accepted = [[5]]''',
    wproof='''  dsimp only [Witness]
  have ha : (run E0 full init [.append 5, .anchor, .verify [5]]).accepted = [[5]] := by decide
  have hb : (run E0 full init [.append 5, .anchor, .verify [5]]).anchors = [(6, some [5])] := by decide
  refine ⟨ha, hb, ?_, by decide, by decide⟩
  rw [ha, hb]
  simp [Set.InjOn]''')

DATA[3] = dict(params='', args='', hyp=None,
    back='''(run E0 full init [.append 5, .anchor, .rewrite [7], .verify [7]]).accepted = [] ∧
  (run E0 full init [.append 5, .append 6, .anchor, .rewrite [6, 5], .verify [6, 5]]).accepted = []''',
    orig='''(run E0 full init [.append 5, .anchor, .rewrite [7], .verify [7]]).accepted = [] ∧
  (run E0 full init [.append 5, .append 6, .anchor, .rewrite [6, 5], .verify [6, 5]]).accepted = []''',
    witness='''(run E0 full init [.append 5, .anchor, .rewrite [7], .verify [7]]).log = [7] ∧
  (run E0 full init [.append 5, .append 6, .anchor, .rewrite [6, 5], .verify [6, 5]]).log = [6, 5] ∧
  (run E0 full init [.append 5, .append 6, .anchor, .verify [5, 6]]).accepted = [[5, 6]] ∧
  BackAt''', wproof='  unfold Witness BackAt\n  decide')

DATA[4] = dict(params='(E : Env) (s : St) (ops : List Op)', args='E s ops', hyp='s.halted = true',
    back='run E full s ops = s', orig='run E full s ops = s',
    witness='''let s := run E0 full init [.append 5, .anchor, .verify [5], .halt 9]
  s.halted = true ∧ s.accepted = [[5]] ∧
  run E0 full s [.append 6, .rewrite [7], .anchor, .writerAnchor 8, .verify [7], .halt 9] = s''',
    wproof='  unfold Witness\n  decide')

DATA[5] = dict(params='(E : Env) (ops : List Op)', args='E ops',
    hyp='Set.InjOn (chainHead E.H E.h0) {l | l ∈ (run E true init ops).accepted ∨ ∃ a ∈ (run E true init ops).anchors, a.2 = l}',
    back='''let final := run E true init ops
  ∀ m ∈ final.accepted, (∃ a ∈ final.anchors, a.2 = m) ∧
    (∃ latest, final.last = some latest ∧ m <+: latest)''',
    orig='''∀ m ∈ (run E true init ops).accepted,
  (∃ a ∈ (run E true init ops).anchors, a.2 = m) ∧
    ∃ l, (run E true init ops).last = some l ∧ m <+: l''',
    witness='''let t := run E0 true init [.append 5, .anchor, .verify [5]]
  t.accepted = [[5]] ∧ t.anchors = [(6, [5])] ∧ t.last = some [5] ∧
  Set.InjOn (chainHead E0.H E0.h0) {l | l ∈ t.accepted ∨ ∃ a ∈ t.anchors, a.2 = l} ∧
  (let u := run E0 true init [.append 5, .anchor, .append 6, .anchor, .verify [5]]
   u.accepted = [[5]] ∧ u.last = some [5, 6])''',
    wproof='''  dsimp only [Witness]
  have ha : (run E0 true init [.append 5, .anchor, .verify [5]]).accepted = [[5]] := by decide
  have hb : (run E0 true init [.append 5, .anchor, .verify [5]]).anchors = [(6, [5])] := by decide
  refine ⟨ha, hb, by decide, ?_, by decide⟩
  rw [ha, hb]
  simp [Set.InjOn]''')

DATA[6] = dict(params='(E : Env) (s : St) (l : List ℕ) (ops : List Op)', args='E s l ops',
    hyp='Inv E s → (∃ a ∈ s.anchors, a.2 = l)',
    back='∀ a ∈ (run E true s ops).anchors, a ∈ s.anchors ∨ l <+: a.2',
    orig='∀ a ∈ (run E true s ops).anchors, a ∈ s.anchors ∨ l <+: a.2',
    witness='''let s := run E0 true init [.append 5, .anchor]
  Inv E0 s ∧ (∃ a ∈ s.anchors, a.2 = [5]) ∧
  (run E0 true s [.append 6, .anchor]).anchors = [(6, [5]), (607, [5, 6])]''',
    wproof='''  dsimp only [Witness]
  refine ⟨run_inv E0 init _ (inv_init E0), ?_, by decide⟩
  exact ⟨(6, [5]), by decide, rfl⟩''')

DATA[7] = dict(params='(E : Env) (ops : List Op)', args='E ops', hyp=None,
    back='''let final := run E true init ops
  final.anchors.Pairwise (fun a b => a.2 <+: b.2) ∧
  (∀ a ∈ final.anchors, ∃ latest, final.last = some latest ∧ a.2 <+: latest)''',
    orig='''(run E true init ops).anchors.Pairwise (fun a b => a.2 <+: b.2) ∧
  ∀ a ∈ (run E true init ops).anchors, ∃ l, (run E true init ops).last = some l ∧ a.2 <+: l''',
    witness='''let t := run E0 true init [.append 5, .anchor, .append 6, .anchor]
  t.anchors = [(6, [5]), (607, [5, 6])] ∧ t.last = some [5, 6]''',
    wproof='  unfold Witness\n  decide')

DATA[8] = dict(params='(E : Env) (s : St)', args='E s', hyp=None,
    back='''let next := step E true s .anchor
  (next.alarms = s.alarms ++ [s.log] ↔ extendsLast s = false) ∧
  (extendsLast s = false → next.anchors = s.anchors)''',
    orig='''((step E true s .anchor).alarms = s.alarms ++ [s.log] ↔ extendsLast s = false) ∧
  (extendsLast s = false → (step E true s .anchor).anchors = s.anchors)''',
    witness='''let s := run E0 true init [.append 5, .anchor, .rewrite [7]]
  extendsLast s = false ∧ (step E0 true s .anchor).alarms = [[7]] ∧
  (step E0 true s .anchor).anchors = s.anchors ∧
  (step E0 true init .anchor).alarms = []''',
    wproof='  unfold Witness\n  decide')

DATA[9] = dict(params='(E : Env) (ops : List COp)', args='E ops',
    hyp='TraceInj E cinit ops → Set.InjOn (chainHead E.H E.h0) {l | l ∈ (runC E false cinit ops).accepted ∨ ∃ a ∈ ancs (runC E false cinit ops).wlog, a.2 = l}',
    back='''let final := runC E false cinit ops
  ∀ m ∈ final.accepted, (∃ a ∈ ancs final.wlog, a.2 = m) ∧
    (∃ latest, final.ghostLast = some latest ∧ m <+: latest)''',
    orig='''∀ m ∈ (runC E false cinit ops).accepted,
  (∃ a ∈ ancs (runC E false cinit ops).wlog, a.2 = m) ∧
    ∃ l, (runC E false cinit ops).ghostLast = some l ∧ m <+: l''',
    witness='''let ops : List COp := [.append 5, .examine, .verify [5]]
  let t := runC E0 false cinit ops
  TraceInj E0 cinit ops ∧ t.accepted = [[5]] ∧ ancs t.wlog = [(6, [5])] ∧
  t.ghostLast = some [5] ∧
  Set.InjOn (chainHead E0.H E0.h0) {l | l ∈ t.accepted ∨ ∃ a ∈ ancs t.wlog, a.2 = l} ∧
  (let u := runC E0 false cinit [.append 5, .examine, .rewrite [], .examine]
   forks u.wlog = [] ∧ ancs u.wlog = [(6, [5])] ∧ u.accepted = [])''',
    wproof='''  dsimp only [Witness]
  have ht : TraceInj E0 cinit [.append 5, .examine, .verify [5]] := by
    simp [TraceInj, ExamInj, stepC, cinit]
  have ha : (runC E0 false cinit [.append 5, .examine, .verify [5]]).accepted = [[5]] := by decide
  have hb : ancs (runC E0 false cinit [.append 5, .examine, .verify [5]]).wlog = [(6, [5])] := by decide
  refine ⟨ht, ha, hb, by decide, ?_, by decide⟩
  rw [ha, hb]
  simp [Set.InjOn]''')

DATA[10] = dict(params='(E : Env) (first second : List COp) (l : List ℕ)', args='E first second l',
    hyp='TraceInj E cinit (first ++ second) → (∃ a ∈ ancs (runC E false cinit first).wlog, a.2 = l)',
    back='''let middle := runC E false cinit first
  let final := runC E false cinit (first ++ second)
  ∀ a ∈ ancs final.wlog, a ∈ ancs middle.wlog ∨ l <+: a.2''',
    orig='''∀ a ∈ ancs (runC E false cinit (first ++ second)).wlog,
  a ∈ ancs (runC E false cinit first).wlog ∨ l <+: a.2''',
    witness='''let first : List COp := [.append 5, .examine]
  let second : List COp := [.append 6, .examine]
  TraceInj E0 cinit (first ++ second) ∧
  (∃ a ∈ ancs (runC E0 false cinit first).wlog, a.2 = [5]) ∧
  ancs (runC E0 false cinit (first ++ second)).wlog = [(6, [5]), (607, [5, 6])]''',
    wproof='''  dsimp only [Witness]
  refine ⟨?_, ?_, by decide⟩
  · simp [TraceInj, ExamInj, stepC, examine, cinit, anchorIt, Set.InjOn]
  · exact ⟨(6, [5]), by decide, rfl⟩''')

source_map = {}
for n, d in DATA.items():
    p = next((OUT / 'typed').glob(f'{n}-*.lean'))
    assert hashlib.sha256(p.read_bytes()).hexdigest() == hashes[p.name]
    typed = p.read_text()
    ns = re.search(r'^namespace (\S+)', typed, re.M).group(1)
    module = typed.splitlines()[0].removeprefix('import ')
    name = p.stem.split('-', 1)[1]
    # The literal Phase A definition body is kept verbatim, including its notes.
    frozen = typed.split(f'def Back_{name} : Prop :=', 1)[1].rsplit('end ', 1)[0].strip()
    opens = '\n'.join(line for line in typed.splitlines() if line.startswith('open '))
    if n in (2, 5, 9) and 'chainHead' not in opens:
        opens += '\nopen ControlStack.SC27Chain (chainHead)'
    if n == 1:
        back_shape = '∀ (St Op Eff : Type) [DecidableEq St] [DecidableEq Op] (G : System St Op Eff) (S : Spec G) (initial : St), S.Inv initial → ∀ (ops : List (ROp Op)), BackAt St Op Eff G S initial ops'
    else:
        back_shape = ('∀ ' + d['params'] + ', ' if d['params'] else '') + (d['hyp'] + ' → ' if d['hyp'] else '') + 'BackAt ' + d['args']
    pointwise = ('∀ ' + d['params'] + ', ' if d['params'] else '') + (d['hyp'] + ' → ' if d['hyp'] else '') + f'(BackAt {d["args"]} ↔ OrigAt {d["args"]})'
    stmt = f'''namespace PL_bg7n1_{n}
open {ns}
{opens}

def FrozenBack : Prop :=
  {frozen}

def BackAt {d['params']} : Prop :=
  {d['back']}

def OrigAt {d['params']} : Prop :=
  {d['orig']}

def Claim : Prop :=
  (FrozenBack ↔ ({back_shape})) ∧
  ({pointwise})

def Witness : Prop :=
  {d['witness']}

end PL_bg7n1_{n}
'''
    proof = f'open {ns}\n{opens}\n\n'
    proof += 'theorem claim : Claim := by\n  constructor\n  · exact Iff.rfl\n  · ' + ('intros\n    ' if d['params'] else '') + 'exact Iff.rfl\n\n'
    proof += 'theorem witness : Witness := by\n' + d['wproof'] + '\n'
    (OUT / f'bg7n1_{n}.statement.lean').write_text(stmt)
    (OUT / f'bg7n1_{n}.proof.lean').write_text(proof)
    source = ROOT / (module.replace('.', '/') + '.lean')
    text = source.read_text()
    start = text.index('theorem ' + name + ' ' if n != 3 else 'theorem ' + name + ' :')
    end = text.index(':=', start)
    source_map[str(n)] = dict(original=ns + '.' + name, path=str(source.relative_to(ROOT)),
                             line=text[:start].count('\n') + 1,
                             source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                             declaration_header=text[start:end],
                             typed_file=p.name, typed_sha256=hashes[p.name])
(OUT / 'ORIGINALS.json').write_text(json.dumps(source_map, indent=2) + '\n')
