from pathlib import Path
import re
BASE=Path(__file__).resolve().parent

def save(n, statement, proof):
    p=next((BASE/'typed').glob(f'{n}-*.lean'))
    frozen=p.read_text().split('\n',2)[2]
    ns=re.search(r'namespace (\S+)',frozen).group(1)
    decl=re.search(r'def (Back_\w+)',frozen).group(1)
    proof=proof.replace('theorem witness : Witness := by decide',f'theorem witness : Witness := by simp only [Witness, {ns}.{decl}]; decide')
    (BASE/f'bg4n2_{n}.statement.lean').write_text(frozen+f'\nnamespace PL_bg4n2_{n}\n'+statement+f'\nend PL_bg4n2_{n}\n')
    (BASE/f'bg4n2_{n}.proof.lean').write_text(statement.splitlines()[0]+'\n'+proof+'\n')

s18='''open ControlStack.SC18Refinement ControlStack.SC18Liveness
'''
b1='''def BackPoint (T : ℕ) (c : CSt) : Prop :=
  let s := α T c
  (∀ r ∈ s.released, r.id ∈ s.logged.take r.llen ∧ r.clock ≤ r.lastAck + T) ∧
  (s.released.map ControlStack.SC18.Rel.id).Nodup
'''
o1='''def OrigPoint (T : ℕ) (c : CSt) : Prop :=
  (∀ r ∈ c.released, Resume.RelOk T (α T c) r) ∧
  (c.released.map ControlStack.SC18.Rel.id).Nodup
'''
save(1,s18+b1+o1+'''def Claim : Prop := ∀ T ops, BackPoint T (runC real T cinit ops) ↔ OrigPoint T (runC real T cinit ops)
def Witness : Prop := (runC real 1 cinit [.arrive 0, .send 0, .commit 0, .ack 0, .release 0]).released = [⟨0, 1, 0, 0⟩]
''','''def LenInv (s : CSt) : Prop := ∀ r ∈ s.released, r.llen ≤ s.ackd.length

theorem len_step (T : ℕ) (s : CSt) (o : COp) (h : LenInv s) : LenInv (stepC real T s o) := by
  cases o <;> simp only [stepC] <;> (repeat' split)
  all_goals try exact h
  · intro r hr
    simpa only [List.length_append, List.length_singleton] using Nat.le_succ_of_le (h r hr)
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact h r hr
    · simp only [List.mem_singleton] at hr
      subst r
      exact le_rfl

theorem len_run (T : ℕ) (s : CSt) (ops : List COp) (h : LenInv s) : LenInv (runC real T s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => exact ih (stepC real T s o) (len_step T s o h)

theorem back_shape : ControlStack.SC18Refinement.Back_concrete_safe =
    (∀ T ops, BackPoint T (runC real T cinit ops)) := rfl

theorem original_type (T : ℕ) (ops : List COp) : OrigPoint T (runC real T cinit ops) :=
  concrete_safe T ops

theorem claim : Claim := by
  intro T ops
  have hlen := len_run T cinit ops (by intro r hr; simp [cinit] at hr)
  constructor
  · intro hb
    refine ⟨?_, hb.2⟩
    intro r hr
    exact ⟨by simpa [α] using hlen r hr, (hb.1 r hr).1, (hb.1 r hr).2⟩
  · intro ho
    exact ⟨fun r hr => (ho.1 r hr).2, ho.2⟩

theorem witness : Witness := by decide''')

b2='''def BackPoint (T : ℕ) (s : CSt) : Prop := ∀ r ∈ s.released,
  r.id ∈ (s.ackd.map Prod.fst).take r.llen ∧ r.id ∈ s.sinkLog ∧ r.clock ≤ r.lastAck + T
'''
o2='''def OrigPoint (T : ℕ) (s : CSt) : Prop := ∀ r ∈ s.released,
  r.id ∈ (s.ackd.map Prod.fst).take r.llen ∧ r.id ∈ s.sinkLog ∧ r.clock ≤ r.lastAck + T
'''
save(2,s18+b2+o2+'''def Claim : Prop := ∀ T s, BackPoint T s ↔ OrigPoint T s
def Witness : Prop := (runC real 1 cinit [.arrive 0, .send 0, .commit 0, .ack 0, .release 0]).released = [⟨0, 1, 0, 0⟩] ∧
  (runC real 1 cinit [.arrive 0, .send 0, .commit 0, .ack 0, .release 0]).sinkLog = [0]
''','''theorem back_shape : Back_concrete_durable = (∀ T ops, BackPoint T (runC real T cinit ops)) := rfl
theorem original_type (T : ℕ) (ops : List COp) : OrigPoint T (runC real T cinit ops) := concrete_durable T ops
theorem claim : Claim := by intro T s; exact Iff.rfl
theorem witness : Witness := by decide''')

for n,model in [(3,'SC19'),(7,'SC20')]:
    wit='''(run E0 full init [.write 7 5, .snapshot 7, .verify 3 0, .prepare 1 0 7, .approve 2 0, .commit 0 0]).destroyed = [⟨0, 1, 7, 1, 5, 0⟩]''' if n==3 else '''(run E0 full init [.agentWrite 1 1 66, .promote 2 1, .freeze 9 [1], .train]).trained = [[(1, 66)]]'''
    save(n,f'''open ControlStack.{model}
def BackPoint (E : Env) (s : St) : Prop := Good E s
def OrigPoint (E : Env) (s : St) : Prop := Good E s
def Claim : Prop := ∀ E s, BackPoint E s ↔ OrigPoint E s
def Witness : Prop := {wit}
''',f'''theorem back_shape : Back_{model.lower()}_safe = (∀ E ops, BackPoint E (run E full init ops)) := rfl
theorem original_type (E : Env) (ops : List Op) : OrigPoint E (run E full init ops) := {model.lower()}_safe E ops
theorem claim : Claim := by intro E s; exact Iff.rfl
theorem witness : Witness := by decide''')

for n,model in [(4,'SC19'),(8,'SC20')]:
    ops='[.write 7 5, .snapshot 7, .verify 3 0, .prepare 1 0 7, .approve 2 0, .commit 0 0]' if n==4 else '[.ingest 50 0 7, .agentWrite 1 1 66, .edit 1 77, .promote 2 1, .freeze 9 [1], .train]'
    nonempty='s.objs ≠ []' if n==4 else 's.store ≠ []'
    seed='[.write 7 5, .halt 9]' if n==4 else '[.ingest 50 0 7, .halt 9]'
    save(n,f'''open ControlStack.{model}
def BackPoint (E : Env) (s : St) (ops : List Op) : Prop := run E full s ops = s
def OrigPoint (E : Env) (s : St) (ops : List Op) : Prop := run E full s ops = s
def Claim : Prop := ∀ E s ops, s.halted = true → (BackPoint E s ops ↔ OrigPoint E s ops)
def Witness : Prop :=
  let s := run E0 full init {seed}
  s.halted = true ∧ {nonempty} ∧ run E0 full s {ops} = s
''',f'''theorem back_shape : Back_{model.lower()}_halt_freezes =
    (∀ E s ops, s.halted = true → BackPoint E s ops) := rfl
theorem original_type (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : OrigPoint E s ops := halt_freezes E s ops hh
theorem claim : Claim := by intro E s ops hh; exact Iff.rfl
theorem witness : Witness := by decide''')

for n,model,field,ctor in [(6,'SC19','destroyed','[⟨0, 1, 7, 1, 5, 0⟩]'),(10,'SC20','trained','[[(1, 66)]]')]:
    typ='List Destroy' if n==6 else 'List (List (ℕ × ℕ))'
    save(n,f'''open ControlStack.{model} ControlStack.AuthInstances ControlStack.AuthenticatedLog
def BackPoint (withoutAuth withAuth : {typ}) : Prop := withoutAuth = {ctor} ∧ withAuth = []
def OrigPoint (withoutAuth withAuth : {typ}) : Prop := withoutAuth = {ctor} ∧ withAuth = []
def Claim : Prop := ∀ withoutAuth withAuth, BackPoint withoutAuth withAuth ↔ OrigPoint withoutAuth withAuth
def Witness : Prop := Back_forged{model[2:]}_{'destroys' if n==6 else 'trains'}_without_auth
''',f'''theorem back_shape : Back_forged{model[2:]}_{'destroys' if n==6 else 'trains'}_without_auth =
    BackPoint (authRun (step E0 full) (fun _ => none) init forged{model[2:]}).{field}
      (authRun (step E0 full) claim{model[2:]} init forged{model[2:]}).{field} := rfl
theorem original_type : OrigPoint (authRun (step E0 full) (fun _ => none) init forged{model[2:]}).{field}
    (authRun (step E0 full) claim{model[2:]} init forged{model[2:]}).{field} := forged{model[2:]}_{'destroys' if n==6 else 'trains'}_without_auth
theorem claim : Claim := by intro withoutAuth withAuth; exact Iff.rfl
theorem witness : Witness := by decide''')

save(5,'''open ControlStack.SC19 ControlStack.AuthInstances ControlStack.AuthenticatedLog
def BackPoint (E : Env) (U : ℕ → Prop) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good E s ∧
  (∀ a ∈ s.approvals,
    (a.2.1, Op.approve a.2.1 a.1) ∈ ops ∧ a.2.1 ∈ E.approvers ∧ ¬ U a.2.1) ∧
  (∀ i ∈ s.verified, ∃ c, (c, Op.verify c i) ∈ ops ∧ c ∈ E.verifiers ∧ ¬ U c)
def OrigPredicatePoint (E : Env) (U : ℕ → Prop) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good E s ∧
  (∀ a ∈ s.approvals, ∃ c o, (c, o) ∈ ops ∧ ¬ U c ∧
    (o = Op.approve c a.1 ∧ c = a.2.1 ∧ c ∈ E.approvers)) ∧
  (∀ i ∈ s.verified, ∃ c o, (c, o) ∈ ops ∧ ¬ U c ∧ (o = Op.verify c i ∧ c ∈ E.verifiers))
def OrigPoint (E : Env) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good E s ∧
  (∀ a ∈ s.approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
    (o = Op.approve c a.1 ∧ c = a.2.1 ∧ c ∈ E.approvers)) ∧
  (∀ i ∈ s.verified, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = Op.verify c i ∧ c ∈ E.verifiers))
def Claim : Prop :=
  (∀ E U ops s, BackPoint E U ops s ↔ OrigPredicatePoint E U ops s) ∧
  (∀ E (U : List ℕ) ops s, BackPoint E (fun c => c ∈ U) ops s ↔ OrigPoint E U ops s)
def Witness : Prop :=
  let ops : List (ℕ × Op) := [(1, .write 7 5), (1, .snapshot 7), (3, .verify 3 0),
    (1, .prepare 1 0 7), (2, .approve 2 0), (1, .commit 0 0)]
  let s := authRun (step E0 full) claim19 init ops
  (∀ c ∈ ([1] : List ℕ), c ∉ E0.approvers) ∧
  (∀ c ∈ ([1] : List ℕ), c ∉ E0.verifiers) ∧
  s.destroyed = [⟨0, 1, 7, 1, 5, 0⟩] ∧ s.approvals = [(0, 2, 1)] ∧ s.verified = [0]
''','''theorem back_shape : Back_sc19_safe_authenticated =
    (∀ E U ops, (∀ c, U c → c ∉ E.approvers) → (∀ c, U c → c ∉ E.verifiers) →
      BackPoint E U ops (authRun (step E full) claim19 init ops)) := rfl

theorem original_type (E : Env) (U : List ℕ) (ops : List (ℕ × Op))
    (ha : ∀ c ∈ U, c ∉ E.approvers) (hv : ∀ c ∈ U, c ∉ E.verifiers) :
    OrigPoint E U ops (authRun (step E full) claim19 init ops) := sc19_safe_authenticated E U ops ha hv

theorem point (E : Env) (U : ℕ → Prop) (ops : List (ℕ × Op)) (s : St) :
    BackPoint E U ops s ↔ OrigPredicatePoint E U ops s := by
  constructor
  · rintro ⟨hg, ha, hv⟩
    refine ⟨hg, ?_, ?_⟩
    · intro a ham
      obtain ⟨hm, hrole, hu⟩ := ha a ham
      exact ⟨a.2.1, .approve a.2.1 a.1, hm, hu, rfl, rfl, hrole⟩
    · intro i him
      obtain ⟨c, hm, hrole, hu⟩ := hv i him
      exact ⟨c, .verify c i, hm, hu, rfl, hrole⟩
  · rintro ⟨hg, ha, hv⟩
    refine ⟨hg, ?_, ?_⟩
    · intro a ham
      obtain ⟨c, o, hm, hu, ho, hc, hrole⟩ := ha a ham
      subst o
      subst c
      exact ⟨hm, hrole, hu⟩
    · intro i him
      obtain ⟨c, o, hm, hu, ho, hrole⟩ := hv i him
      subst o
      exact ⟨c, hm, hrole, hu⟩

theorem claim : Claim := by
  exact ⟨point, fun E U ops s => point E (fun c => c ∈ U) ops s⟩
theorem witness : Witness := by decide''')

save(9,'''open ControlStack.SC20 ControlStack.AuthInstances ControlStack.AuthenticatedLog
def BackPoint (E : Env) (U : ℕ → Prop) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good E s ∧ (∀ p ∈ s.promoted,
    (p.2.1, Op.promote p.2.1 p.1) ∈ ops ∧ p.2.1 ∈ E.reviewers ∧ ¬ U p.2.1)
def OrigPredicatePoint (E : Env) (U : ℕ → Prop) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good E s ∧ (∀ p ∈ s.promoted, ∃ c o, (c, o) ∈ ops ∧ ¬ U c ∧
    (o = Op.promote c p.1 ∧ c = p.2.1 ∧ c ∈ E.reviewers))
def OrigPoint (E : Env) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good E s ∧ (∀ p ∈ s.promoted, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
    (o = Op.promote c p.1 ∧ c = p.2.1 ∧ c ∈ E.reviewers))
def Claim : Prop :=
  (∀ E U ops s, BackPoint E U ops s ↔ OrigPredicatePoint E U ops s) ∧
  (∀ E (U : List ℕ) ops s, BackPoint E (fun c => c ∈ U) ops s ↔ OrigPoint E U ops s)
def Witness : Prop :=
  let ops : List (ℕ × Op) := [(1, .agentWrite 1 1 66), (2, .promote 2 1), (9, .freeze 9 [1]), (1, .train)]
  let s := authRun (step E0 full) claim20 init ops
  (∀ c ∈ ([1] : List ℕ), c ∉ E0.reviewers) ∧ s.trained = [[(1, 66)]] ∧ s.promoted = [(1, 2, 66)]
''','''theorem back_shape : Back_sc20_safe_authenticated =
    (∀ E U ops, (∀ c, U c → c ∉ E.reviewers) →
      BackPoint E U ops (authRun (step E full) claim20 init ops)) := rfl

theorem original_type (E : Env) (U : List ℕ) (ops : List (ℕ × Op))
    (hu : ∀ c ∈ U, c ∉ E.reviewers) :
    OrigPoint E U ops (authRun (step E full) claim20 init ops) := sc20_safe_authenticated E U ops hu

theorem point (E : Env) (U : ℕ → Prop) (ops : List (ℕ × Op)) (s : St) :
    BackPoint E U ops s ↔ OrigPredicatePoint E U ops s := by
  constructor
  · rintro ⟨hg, hp⟩
    refine ⟨hg, ?_⟩
    intro p hpm
    obtain ⟨hm, hrole, hu⟩ := hp p hpm
    exact ⟨p.2.1, .promote p.2.1 p.1, hm, hu, rfl, rfl, hrole⟩
  · rintro ⟨hg, hp⟩
    refine ⟨hg, ?_⟩
    intro p hpm
    obtain ⟨c, o, hm, hu, ho, hc, hrole⟩ := hp p hpm
    subst o
    subst c
    exact ⟨hm, hrole, hu⟩

theorem claim : Claim := by
  exact ⟨point, fun E U ops s => point E (fun c => c ∈ U) ops s⟩
theorem witness : Witness := by decide''')

# Certify that arbitrary predicate sets have the same observable content as lists on a finite trace.
for n,roles in [(5,['approvers','verifiers']),(9,['reviewers'])]:
    path=BASE/f'bg4n2_{n}.statement.lean'
    s=path.read_text()
    suffix=''' ∧
  (∀ E (U : ℕ → Prop) ops, ∃ V : List ℕ,
    (∀ c ∈ V, U c) ∧ (∀ s, BackPoint E U ops s ↔ OrigPoint E V ops s))'''
    boundary='\ndef Witness : Prop :='
    s=s.replace(boundary,suffix+boundary)
    path.write_text(s)
    path=BASE/f'bg4n2_{n}.proof.lean'
    s=path.read_text()
    if n==5:
        transport='''theorem transport (E : Env) (U V : ℕ → Prop) (ops : List (ℕ × Op)) (s : St)
    (same : ∀ c o, (c, o) ∈ ops → (U c ↔ V c)) :
    BackPoint E U ops s ↔ BackPoint E V ops s := by
  have dir (U V : ℕ → Prop) (same : ∀ c o, (c, o) ∈ ops → (U c ↔ V c)) :
      BackPoint E U ops s → BackPoint E V ops s := by
    rintro ⟨hg, ha, hv⟩
    refine ⟨hg, ?_, ?_⟩
    · intro a ham
      obtain ⟨hm, hrole, hu⟩ := ha a ham
      exact ⟨hm, hrole, fun hvc => hu ((same _ _ hm).mpr hvc)⟩
    · intro i him
      obtain ⟨c, hm, hrole, hu⟩ := hv i him
      exact ⟨c, hm, hrole, fun hvc => hu ((same _ _ hm).mpr hvc)⟩
  exact ⟨dir U V same, dir V U (fun c o hm => (same c o hm).symm)⟩
'''
    else:
        transport='''theorem transport (E : Env) (U V : ℕ → Prop) (ops : List (ℕ × Op)) (s : St)
    (same : ∀ c o, (c, o) ∈ ops → (U c ↔ V c)) :
    BackPoint E U ops s ↔ BackPoint E V ops s := by
  have dir (U V : ℕ → Prop) (same : ∀ c o, (c, o) ∈ ops → (U c ↔ V c)) :
      BackPoint E U ops s → BackPoint E V ops s := by
    rintro ⟨hg, hp⟩
    refine ⟨hg, ?_⟩
    intro p hpm
    obtain ⟨hm, hrole, hu⟩ := hp p hpm
    exact ⟨hm, hrole, fun hvc => hu ((same _ _ hm).mpr hvc)⟩
  exact ⟨dir U V same, dir V U (fun c o hm => (same c o hm).symm)⟩
'''
    finite='''
theorem finite_representation (E : Env) (U : ℕ → Prop) (ops : List (ℕ × Op)) :
    ∃ V : List ℕ, (∀ c ∈ V, U c) ∧ (∀ s, BackPoint E U ops s ↔ OrigPoint E V ops s) := by
  classical
  let V := (ops.map Prod.fst).filter (fun c => decide (U c))
  have memV (c : ℕ) : c ∈ V ↔ c ∈ ops.map Prod.fst ∧ U c := by simp [V]
  refine ⟨V, fun c hc => ((memV c).mp hc).2, ?_⟩
  intro s
  have same : ∀ c o, (c, o) ∈ ops → (U c ↔ c ∈ V) := by
    intro c o hm
    have hc : c ∈ ops.map Prod.fst := List.mem_map.mpr ⟨(c, o), hm, rfl⟩
    exact ⟨fun hu => (memV c).mpr ⟨hc, hu⟩, fun hv => ((memV c).mp hv).2⟩
  exact (transport E U (fun c => c ∈ V) ops s same).trans (point E (fun c => c ∈ V) ops s)
'''
    s=s.replace('theorem claim : Claim := by\n  exact ⟨point, fun E U ops s => point E (fun c => c ∈ U) ops s⟩',transport+finite+'''\ntheorem claim : Claim := by
  exact ⟨point, (fun E U ops s => point E (fun c => c ∈ U) ops s), finite_representation⟩''')
    path.write_text(s)

# This auxiliary fact explains why Claim 1 is qualified by reachability.
p=BASE/'bg4n2_1.proof.lean'
s=p.read_text()
s+='''
theorem unreachable_count_counterexample :
    let c : CSt := { cinit with ackd := [(0, 0)], released := [⟨0, 2, 0, 0⟩] }
    BackPoint 1 c ∧ ¬ OrigPoint 1 c := by
  simp [BackPoint, OrigPoint, α, cinit, Resume.RelOk]
'''
p.write_text(s)

# Keep computation logs clear of unused-definition warnings.
for n in range(1,11):
    if n not in (6,10):
        p=BASE/f'bg4n2_{n}.proof.lean'
        s=p.read_text()
        s=re.sub(r'simp only \[Witness, ControlStack\.[^\]]+\]; decide','simp only [Witness]; decide',s)
        p.write_text(s)
