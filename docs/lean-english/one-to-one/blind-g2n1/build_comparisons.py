"""Save comparisons; frozen Back definitions are copied verbatim from typed files."""
from pathlib import Path
import json, hashlib
OUT=Path(__file__).resolve().parent

def frozen(n):
    p=next((OUT/'typed').glob(f'{n}-*.lean'))
    hashes=json.loads((OUT/'typed/HASHES.json').read_text())['files']
    assert hashlib.sha256(p.read_bytes()).hexdigest()==hashes[p.name]
    t=p.read_text()
    return t.split('\nnamespace ',1)[1].split('\n',1)[1].rsplit('\nend ',1)[0].strip()

ok8='''def EnglishOk (E : Env) (s : St) : Prop :=
  ∀ r ∈ s.ran, E.h r.1 ∈ E.allow ∧
    (E.h r.1 ∈ E.interp → ∃ sc, r.2 = some sc ∧ E.h sc ∈ E.scripts)
'''
ok9='''def EnglishOk (P : Policy) (s : St) : Prop :=
  (∀ q ∈ s.procs, ∀ c ∈ q.caps, (q.lin, c) ∈ s.granted) ∧
  (∀ u ∈ s.used, (u.lin, u.cap) ∈ s.granted ∨
    ∃ r ∈ P.elev, u.via = some (r.bin, r.args) ∧ r.cap = u.cap)
'''
ok10='''def EnglishOk (E : Env) (s : St) : Prop :=
  (∀ d ∈ s.decisions, ∃ i w, d.ver = some i ∧
    s.versions[i]? = some (d.val, w) ∧ w ∈ E.admins ∧ i + 1 = d.curLen) ∧
  (∀ b ∈ s.builds, E.h b = E.pinnedDigest)
'''
ok12='''def EnglishOk (s : St) : Prop :=
  ∀ e ∈ s.live, e.reg = true ∧ e.origin ∈ s.active ∧ e.origin ∉ s.ended
'''
proof_rfl='''theorem claim : Claim := by
  refine ⟨rfl, ?_, ?_⟩
  · intros
    exact Iff.rfl
  · intros
    exact Iff.rfl
'''
proof_structure='''theorem claim : Claim := by
  refine ⟨rfl, ?_, ?_⟩
  · intros
    exact Iff.rfl
  · intros
    constructor
    · intro h
      exact ⟨h.1, h.2⟩
    · intro h
      exact ⟨h.%s, h.%s⟩
'''
exec_w='''def Witness : Prop :=
  (s0.ran = [] ∧ s0.halted = false) ∧
  (run E0 full s0 [.exec 1 none, .exec 4 (some 5)]).ran =
    [(10, none), (20, some 30)] ∧
  (run { E0 with interp := [] } full s0 [.write 2 777, .exec 4 (some 2)]).ran =
    [(20, none)]
'''
halt8_w='''def Witness : Prop :=
  let s : St := ⟨[(1, 10)], [(10, none)], true⟩
  s.halted = true ∧ s.files ≠ [] ∧ s.ran ≠ [] ∧
    run E0 full s [.write 1 999, .exec 1 none, .halt 9] = s
'''
halt9_w='''def Witness : Prop :=
  let s : St := ⟨[⟨1, 1, [7]⟩], [(1, 7)], [⟨1, 7, none⟩], true⟩
  s.halted = true ∧ s.procs ≠ [] ∧ s.granted ≠ [] ∧ s.used ≠ [] ∧
    run P0 full s [.start 9 2 1, .grant 9 1 1 8, .use 1 7, .halt 9] = s
'''
halt10_w='''def Witness : Prop :=
  let s : St := ⟨[(5, 9)], some 0, 2, 3, [⟨1, some 0, 5, 1⟩], [40], true⟩
  s.halted = true ∧ s.versions ≠ [] ∧ s.decisions ≠ [] ∧ s.builds ≠ [] ∧
    run E0 full s [.writePolicy 9 6, .decide 2, .build, .halt 9] = s
'''

cases={}
cases[1]=('SC08',ok8+'''def BackAt (E : Env) (files : List (ℕ × ℕ)) (ops : List Op) : Prop :=
  Good E (run E full (⟨files, [], false⟩ : St) ops)
def OrigAt (E : Env) (files : List (ℕ × ℕ)) (ops : List Op) : Prop :=
  Good E (run E full ⟨files, [], false⟩ ops)
def Claim : Prop :=
  (Back_sc08_safe = (∀ E files ops, BackAt E files ops)) ∧
  (∀ E files ops, BackAt E files ops ↔ OrigAt E files ops) ∧
  (∀ E s, EnglishOk E s ↔ Good E s)
'''+exec_w,proof_rfl)

cases[2]=('SC08',ok8+'''def BackAt (E : Env) (C : Checks) (files : List (ℕ × ℕ))
    (halted : Bool) (ops : List Op) : Prop :=
  Good E (run E C (⟨files, [], halted⟩ : St) ops)
def OrigAt (E : Env) (C : Checks) (files : List (ℕ × ℕ)) (ops : List Op) : Prop :=
  Good E (run E C ⟨files, [], false⟩ ops)
def OrigFamily : Prop := ∀ E C files ops, Sound C → OrigAt E C files ops
-- Domain comparison is independent of the truth of the safety conclusion.
def BackDomain (C : Checks) (_halted : Bool) : Prop := Sound C
def OrigDomain (C : Checks) (halted : Bool) : Prop := Sound C ∧ halted = false
def BackCoverage (Q : Checks → Bool → Prop) : Prop :=
  ∀ C halted, BackDomain C halted → Q C halted
def OrigCoverage (Q : Checks → Bool → Prop) : Prop :=
  ∀ C halted, OrigDomain C halted → Q C halted
def Claim : Prop :=
  (Back_safe_of_sound = (∀ E C files halted ops, Sound C → BackAt E C files halted ops)) ∧
  (Back_safe_of_sound → OrigFamily) ∧
  (∀ E C files halted ops, Sound C → halted = false →
    (BackAt E C files halted ops ↔ OrigAt E C files ops)) ∧
  (∀ C halted, OrigDomain C halted → BackDomain C halted) ∧
  (∃ C halted, BackDomain C halted ∧ ¬ OrigDomain C halted) ∧
  (∀ Q, BackCoverage Q → OrigCoverage Q) ∧
  (¬ (∀ Q, OrigCoverage Q → BackCoverage Q)) ∧
  (∀ E s, EnglishOk E s ↔ Good E s)
def Witness : Prop :=
  Sound full ∧ s0.ran = [] ∧ s0.halted = false ∧
  (run E0 full s0 [.exec 1 none, .exec 4 (some 5)]).ran =
    [(10, none), (20, some 30)] ∧
  BackDomain full true ∧ ¬ OrigDomain full true ∧
  (run E0 full (⟨s0.files, [], true⟩ : St) [.exec 1 none]).ran = []
''','''theorem claim : Claim := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h E C files ops hC
    exact h E C files false ops hC
  · intro E C files halted ops _ hh
    subst halted
    exact Iff.rfl
  · intro C halted h
    exact h.1
  · refine ⟨full, true, sound_full, ?_⟩
    intro h
    cases h.2
  · intro Q h C halted hO
    exact h C halted hO.1
  · intro h
    have hB : BackCoverage OrigDomain := h OrigDomain (fun _ _ hO => hO)
    have ht := hB full true sound_full
    cases ht.2
  · intros
    exact Iff.rfl
''')

for n,ns,back,ww in [(3,'SC08','Back_sc08_halt_freezes',halt8_w),(6,'SC09','Back_sc09_halt_freezes',halt9_w),(9,'SC10','Back_sc10_halt_freezes',halt10_w)]:
    param='P' if ns=='SC09' else 'E'
    typ='Policy' if ns=='SC09' else 'Env'
    cases[n]=(ns,f'''def BackAt ({param} : {typ}) (s : St) (ops : List Op) : Prop :=
  run {param} full s ops = s
def OrigAt ({param} : {typ}) (s : St) (ops : List Op) : Prop :=
  run {param} full s ops = s
def Claim : Prop :=
  ({back} = (∀ {param} s ops, s.halted = true → BackAt {param} s ops)) ∧
  (∀ {param} s ops, s.halted = true → (BackAt {param} s ops ↔ OrigAt {param} s ops))
'''+ww,'''theorem claim : Claim := by
  refine ⟨rfl, ?_⟩
  intros
  exact Iff.rfl
''')

cases[4]=('SC09',ok9+'''def BackAt (P : Policy) (ops : List Op) : Prop := Good P (run P full init ops)
def OrigAt (P : Policy) (ops : List Op) : Prop := Good P (run P full init ops)
def Claim : Prop :=
  (Back_sc09_safe = (∀ P ops, BackAt P ops)) ∧
  (∀ P ops, BackAt P ops ↔ OrigAt P ops) ∧
  (∀ P s, EnglishOk P s ↔ Good P s)
def Witness : Prop :=
  init.procs = [] ∧ init.granted = [] ∧ init.used = [] ∧ init.halted = false ∧
  (run P0 full init [.start 9 1 1, .grant 9 1 1 7, .use 1 7,
      .elevate 1 50 3, .spawn 1 2 [7], .use 2 7]).used =
    [⟨1, 7, none⟩, ⟨1, 8, some (50, 3)⟩, ⟨1, 7, none⟩]
''',proof_structure % ('caps','uses'))

cases[5]=('SC09','''def BackAt (P : Policy) (s : St) (p ch : ℕ) (q : Proc) (keep : List ℕ) : Prop :=
  ∀ r ∈ (step P full s (.spawn p ch keep)).procs,
    r ∉ s.procs → r.lin = q.lin ∧ (∀ c ∈ r.caps, c ∈ q.caps)
def OrigAt (P : Policy) (s : St) (p ch : ℕ) (keep : List ℕ) (q : Proc) : Prop :=
  ∀ r ∈ (step P full s (.spawn p ch keep)).procs,
    r ∉ s.procs → r.lin = q.lin ∧ r.caps ⊆ q.caps
def Claim : Prop :=
  (Back_spawn_attenuates = (∀ P s p ch q keep,
    s.halted = false → procOf s p = some q → procOf s ch = none →
      BackAt P s p ch q keep)) ∧
  (∀ P s p ch q keep, s.halted = false → procOf s p = some q →
    procOf s ch = none → (BackAt P s p ch q keep ↔ OrigAt P s p ch keep q)) ∧
  (∀ (xs ys : List ℕ), (∀ c ∈ xs, c ∈ ys) ↔ xs ⊆ ys)
def Witness : Prop :=
  let q : Proc := ⟨1, 3, [7, 7, 8]⟩
  let s : St := ⟨[q], [], [], false⟩
  s.halted = false ∧ procOf s 1 = some q ∧ procOf s 2 = none ∧
  (step P0 full s (.spawn 1 2 [7])).procs = [q, ⟨2, 3, [7, 7]⟩] ∧
  (⟨2, 3, [7, 7]⟩ : Proc) ∉ s.procs ∧
  ([7, 7] : List ℕ) ⊆ [7] ∧ ¬ ([7, 7] : List ℕ).Sublist [7]
''',proof_rfl)

cases[7]=('SC10',ok10+'''def BackAt (E : Env) (ops : List Op) : Prop := Good E (run E full init ops)
def OrigAt (E : Env) (ops : List Op) : Prop := Good E (run E full init ops)
def Claim : Prop :=
  (Back_sc10_safe = (∀ E, E.h E.pinned = E.pinnedDigest → ∀ ops, BackAt E ops)) ∧
  (∀ E, E.h E.pinned = E.pinnedDigest → ∀ ops, BackAt E ops ↔ OrigAt E ops) ∧
  (∀ E s, EnglishOk E s ↔ Good E s)
def Witness : Prop :=
  E0.h E0.pinned = E0.pinnedDigest ∧ init.versions = [] ∧
  init.decisions = [] ∧ init.builds = [] ∧ init.halted = false ∧
  let s := run E0 full init [.writePolicy 9 5, .decide 1, .writePath 666, .build]
  s.decisions = [⟨1, some 0, 5, 1⟩] ∧ s.builds = [40] ∧ s.pathTool = 666
''',proof_structure % ('decs','builds'))

cases[8]=('SC10','''def BackAt (E : Env) (ops : List Op) : Prop :=
  ∀ pv ∈ (run E full init ops).versions, pv.2 ∈ E.admins
def OrigAt (E : Env) (ops : List Op) : Prop :=
  ∀ pv ∈ (run E full init ops).versions, pv.2 ∈ E.admins
def Claim : Prop :=
  (Back_policy_admin_only = (∀ E, E.h E.pinned = E.pinnedDigest → ∀ ops, BackAt E ops)) ∧
  (∀ E, E.h E.pinned = E.pinnedDigest → ∀ ops, BackAt E ops ↔ OrigAt E ops)
def Witness : Prop :=
  E0.h E0.pinned = E0.pinnedDigest ∧ init.versions = [] ∧
  (run E0 full init [.writePolicy 1 999, .writePolicy 9 5, .writePolicy 9 6]).versions =
    [(5, 9), (6, 9)]
''','''theorem claim : Claim := by
  refine ⟨rfl, ?_⟩
  intros
  exact Iff.rfl
''')

cases[10]=('SC12',ok12+'''def BackAt (admins : List ℕ) (ops : List Op) : Prop := Good (run admins full init ops)
def OrigAt (admins : List ℕ) (ops : List Op) : Prop := Good (run admins full init ops)
def Claim : Prop :=
  (Back_sc12_safe = (∀ admins ops, BackAt admins ops)) ∧
  (∀ admins ops, BackAt admins ops ↔ OrigAt admins ops) ∧
  (∀ s, EnglishOk s ↔ Good s)
def Witness : Prop :=
  init.active = [] ∧ init.ended = [] ∧ init.live = [] ∧ init.fired = [] ∧ init.halted = false ∧
  let s := run [9] full init
    [.start 9 1, .spawn 1 5 true 999, .bypass 1 6 true, .fire 5, .endSession 9 1, .fire 5]
  s.fired = [(5, 1, 0)] ∧ s.live = [] ∧ s.ended = [1]
''',proof_rfl)

for n,(ns,body,proof) in cases.items():
    cid=f'bg2n1_{n}'
    statement=f'namespace PL_{cid}\nopen ControlStack.{ns}\n\n{frozen(n)}\n\n{body}\nend PL_{cid}\n'
    witness='theorem witness : Witness := by\n  unfold Witness\n  decide\n'
    if n==2:
        witness='''theorem witness : Witness := by
  unfold Witness BackDomain OrigDomain
  refine ⟨sound_full, rfl, rfl, ?_, sound_full, ?_, ?_⟩
  · decide
  · intro h
    cases h.2
  · decide
'''
    (OUT/f'{cid}.statement.lean').write_text(statement)
    (OUT/f'{cid}.proof.lean').write_text(f'open ControlStack.{ns}\n\n'+proof+'\n'+witness)
