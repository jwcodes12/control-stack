from pathlib import Path
import re
OUT=Path(__file__).resolve().parent

def save(n,defs,claim,proof,witness,wproof='by\n  decide'):
 p=next((OUT/'typed').glob(f'{n}-*.lean'))
 src=p.read_text()
 ns=re.search(r'namespace (\S+)',src)[1]
 full=src[src.index('def Back_'):src.rindex('\nend ')]
 full=re.sub(r'def Back_\w+', 'def BackFull',full,count=1)
 # Preserve the frozen back body, with namespace resolved by opens.
 opens='open ControlStack\nopen '+ns+'\n'
 if n in (5,6,7,8,9): opens+='open ControlStack ControlStack.SC28\n'
 if n in (5,6): opens+='open ControlStack.AuthenticatedLog\n'
 statement=f'namespace PL_bg7n2_{n}\n{opens}\n{full}\n\n{defs}\n\ndef Claim : Prop :=\n{claim}\n\ndef Witness : Prop :=\n{witness}\nend PL_bg7n2_{n}\n'
 (OUT/f'bg7n2_{n}.statement.lean').write_text(statement)
 (OUT/f'bg7n2_{n}.proof.lean').write_text(opens+f'theorem claim : Claim :=\n{proof}\n\ntheorem witness : Witness :=\n'+wproof.replace('by', 'by\n  unfold Witness', 1)+'\n')

scw='''  let t := run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0, .work 1 2 2]
  t.usage = [(1, 0, 2)] ∧ usedT t = 2'''
cw='''  let t := runC 10 cinit [.createLease 0 10, .launch 1 0, .consume 1 2]
  t.acct = [(1, 0, 2)] ∧ runCounter t = 2 ∧ t.outside = []'''
save(1,'''def BackResult (admins : List ℕ) (G : ℕ) (ops : List Op) : Prop :=
  Good G (run admins G full init ops)
def OrigResult (admins : List ℕ) (G : ℕ) (ops : List Op) : Prop :=
  Good G (run admins G full init ops)''',
'''  ∀ (admins : List ℕ) (G : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal o) → (BackResult admins G ops ↔ OrigResult admins G ops)''',
'by\n  intro admins G ops _\n  rfl',
'''  let ops : List Op := [.issue 9 0 10, .assignTo 9 1 0, .work 1 2 2]
  (∀ o ∈ ops, legal o) ∧ (run [9] 10 full init ops).usage = [(1, 0, 2)] ∧
    usedT (run [9] 10 full init ops) = 2''',
'''by
  constructor
  · simp [legal]
  · decide''')
save(2,'''def BackResult (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (lid : ℕ) (ops : List Op) : Prop :=
  usedL (run admins G C s ops) lid = usedL s lid
def OrigResult (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (lid : ℕ) (ops : List Op) : Prop :=
  usedL (run admins G C s ops) lid = usedL s lid''',
'''  ∀ (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (lid : ℕ) (ops : List Op),
    lid ∈ s.revoked → (BackResult admins G C s lid ops ↔ OrigResult admins G C s lid ops)''',
'by\n  intro admins G C s lid ops _\n  rfl',
'''  let s := run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0, .work 1 2 2, .revoke 9 0]
  0 ∈ s.revoked ∧ usedL s 0 = 2 ∧ usedL (run [9] 10 full s [.rollback 0, .work 1 3 3]) 0 = 2''')
save(3,'''def BackFresh (s : St) (child : ℕ) : Prop := leaseOf s child = none
def OrigFresh (s : St) (child : ℕ) : Prop := child ∉ s.assign.map Prod.fst
def BackResult (admins : List ℕ) (G : ℕ) (s : St) (c p ch nl lid : ℕ) : Prop :=
  leaseOf (step admins G full s (.fork c p ch nl)) ch = some lid
def OrigResult (admins : List ℕ) (G : ℕ) (s : St) (c p ch nl lid : ℕ) : Prop :=
  leaseOf (step admins G full s (.fork c p ch nl)) ch = some lid''',
'''  (∀ (s : St) (child : ℕ), BackFresh s child ↔ OrigFresh s child) ∧
  (∀ (admins : List ℕ) (G : ℕ) (s : St) (c p ch nl lid : ℕ),
    s.halted = false → leaseOf s p = some lid → BackFresh s ch →
    (BackResult admins G s c p ch nl lid ↔ OrigResult admins G s c p ch nl lid))''',
'''by
  constructor
  · intro s child
    simp [BackFresh, OrigFresh, leaseOf, Option.map_eq_none_iff, List.find?_eq_none,
      List.mem_map, not_exists, not_and]
    constructor
    · intro h b hb
      exact h child b hb rfl
    · intro h a b hab he
      subst a
      exact h b hab
  · intro admins G s c p ch nl lid _ _ _
    rfl''',
'''  let s := run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0]
  s.halted = false ∧ leaseOf s 1 = some 0 ∧ leaseOf s 2 = none ∧
    2 ∉ s.assign.map Prod.fst ∧ leaseOf (step [9] 10 full s (.fork 77 1 2 99)) 2 = some 0''')
save(4,'''def BackResult (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op) : Prop :=
  (run admins G full s ops).usage = s.usage
def OrigResult (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op) : Prop :=
  (run admins G full s ops).usage = s.usage''',
'''  ∀ (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op),
    s.halted = true → (BackResult admins G s ops ↔ OrigResult admins G s ops)''',
'by\n  intro admins G s ops _\n  rfl',
'''  let s := run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0, .work 1 2 2, .halt 9]
  s.halted = true ∧ usedT s = 2 ∧
    (run [9] 10 full s [.rollback 0, .work 1 3 3]).usage = s.usage ∧
    (run [9] 10 full s [.rollback 0]).ledger ≠ s.ledger''')
save(5,'''def BackResult (admins : List ℕ) (G : ℕ) (U : Set ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good G s ∧
    (∀ l ∈ s.leases, ∃ c, c ∈ admins ∧ c ∉ U ∧ (c, Op.issue c l.1 l.2) ∈ ops) ∧
    (∀ lid ∈ s.revoked, ∃ c, c ∈ admins ∧ c ∉ U ∧ (c, Op.revoke c lid) ∈ ops)
def OrigResult (admins : List ℕ) (G : ℕ) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good G s ∧
    (∀ l ∈ s.leases, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .issue c l.1 l.2 ∧ c ∈ admins)) ∧
    (∀ lid ∈ s.revoked, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ (o = .revoke c lid ∧ c ∈ admins))''',
'''  ∀ (admins : List ℕ) (G : ℕ) (Uset : Set ℕ) (Ulist : List ℕ) (ops : List (ℕ × Op)) (s : St),
    (∀ c ∈ admins, c ∉ Uset) → (∀ u ∈ Ulist, u ∉ admins) →
    (BackResult admins G Uset ops s ↔ OrigResult admins G Ulist ops s)''',
'''by
  intro admins G Uset Ulist ops s hs hl
  have excl : ∀ c ∈ admins, c ∉ Ulist := by
    intro c hc hu
    exact hl c hu hc
  constructor
  · rintro ⟨good, leases, revoked⟩
    refine ⟨good, ?_, ?_⟩
    · intro l hm
      obtain ⟨c, hc, _, hop⟩ := leases l hm
      exact ⟨c, .issue c l.1 l.2, hop, excl c hc, rfl, hc⟩
    · intro lid hm
      obtain ⟨c, hc, _, hop⟩ := revoked lid hm
      exact ⟨c, .revoke c lid, hop, excl c hc, rfl, hc⟩
  · rintro ⟨good, leases, revoked⟩
    refine ⟨good, ?_, ?_⟩
    · intro l hm
      obtain ⟨c, o, hop, _, he, hc⟩ := leases l hm
      exact ⟨c, hc, hs c hc, he ▸ hop⟩
    · intro lid hm
      obtain ⟨c, o, hop, _, he, hc⟩ := revoked lid hm
      exact ⟨c, hc, hs c hc, he ▸ hop⟩''',
'''  let ops : List (ℕ × Op) := [(9, .issue 9 0 10), (9, .assignTo 9 1 0), (1, .work 1 2 2), (9, .revoke 9 0)]
  let s := AuthenticatedLog.authRun (step [9] 10 full) claim28 init ops
  (∀ c ∈ ([9] : List ℕ), c ∉ ({1} : Set ℕ)) ∧
    (∀ u ∈ ([1] : List ℕ), u ∉ ([9] : List ℕ)) ∧
    (∀ io ∈ ops, legal io.2) ∧ s.leases = [(0, 10)] ∧ s.revoked = [0] ∧ s.usage = [(1, 0, 2)]''',
'''by
  dsimp
  constructor
  · simp
  constructor
  · simp
  constructor
  · simp [legal]
  decide''')
# Closed claim: retain literal full back; compare output predicates without computing truth of an iff.
save(6,'''def BackResult (unchecked checked : St) (applied : List Op) : Prop :=
  budgetOf unchecked 0 = some 100 ∧ leaseOf unchecked 1 = some 0 ∧
    usedL unchecked 0 = 5 ∧ applied = [.work 1 5 5] ∧ usedT checked = 0
def OrigResult (unchecked checked : St) : Prop :=
  unchecked.usage = [(1, 0, 5)] ∧ checked.usage = []
def uncheckedExample : St := ⟨[(0, 100)], [(1, 0)], [], [], [(2, 0, 5)], false⟩
def checkedExample : St := { init with usage := [(1, 0, 0)] }
def origExample : St := { init with usage := [(1, 0, 5)] }''',
'''  (BackResult uncheckedExample checkedExample [.work 1 5 5] ∧
    ¬ OrigResult uncheckedExample checkedExample) ∧
  (OrigResult origExample init ∧ ¬ BackResult origExample init [])''',
'''by
  unfold BackResult OrigResult
  constructor <;> decide''',
'''  let unchecked := run [9] 1000 full init (forged28.map Prod.snd)
  let checked := AuthenticatedLog.authRun (step [9] 1000 full) claim28 init forged28
  unchecked.usage = [(1, 0, 5)] ∧ checked.usage = [] ∧
    budgetOf unchecked 0 = some 100 ∧ leaseOf unchecked 1 = some 0''')
save(7,'''def BackResult (admins : List ℕ) (G : ℕ) (s : St) (w lid : ℕ) (units : List ℕ) : Prop :=
  (run admins G full s (units.map (fun a => Op.work w a a))).usage =
    s.usage ++ units.map (fun a => (w, lid, a))
def OrigResult (admins : List ℕ) (G : ℕ) (s : St) (w lid : ℕ) (units : List ℕ) : Prop :=
  (run admins G full s (units.map (fun a => Op.work w a a))).usage =
    s.usage ++ units.map (fun a => (w, lid, a))''',
'''  ∀ (admins : List ℕ) (G : ℕ) (s : St) (w lid b : ℕ) (units : List ℕ),
    s.halted = false → leaseOf s w = some lid → budgetOf s lid = some b → lid ∉ s.revoked →
    spentL s lid + charges units ≤ b → spentT s + charges units ≤ G →
    (BackResult admins G s w lid units ↔ OrigResult admins G s w lid units)''',
'by\n  intro admins G s w lid b units _ _ _ _ _ _\n  rfl',
'''  let s := run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0]
  s.halted = false ∧ leaseOf s 1 = some 0 ∧ budgetOf s 0 = some 10 ∧ 0 ∉ s.revoked ∧
    spentL s 0 + charges [2, 3, 1] ≤ 10 ∧ spentT s + charges [2, 3, 1] ≤ 10 ∧
    (run [9] 10 full s ([2, 3, 1].map (fun a => Op.work 1 a a))).usage = [(1, 0, 2), (1, 0, 3), (1, 0, 1)] ∧
    charge full 0 0 = 1 ∧
    (run [9] 1 full init [.issue 9 0 1, .assignTo 9 1 0, .work 1 0 0]).usage = [(1, 0, 0)] ∧
    (run [9] 1 full init [.issue 9 0 1, .assignTo 9 1 0, .work 1 0 0]).ledger = [(0, 1)]''')
save(8,'''def BackResult (admins : List ℕ) (G : ℕ) (s : St) (w lid a reported : ℕ) (p : List Op) : Prop :=
  let t := run admins G full s p
  (step admins G full t (.work w a reported)).usage = t.usage ++ [(w, lid, a)] ∨
    t.halted = true ∨ lid ∈ t.revoked ∨ leaseOf t w ≠ some lid ∨
    spentL s lid < spentL t lid ∨ spentT s < spentT t
def OrigResult (admins : List ℕ) (G : ℕ) (s : St) (w lid a : ℕ) (p : List Op) : Prop :=
  let t := run admins G full s p
  (step admins G full t (.work w a a)).usage = t.usage ++ [(w, lid, a)] ∨
    t.halted = true ∨ lid ∈ t.revoked ∨ leaseOf t w ≠ some lid ∨
    spentL s lid < spentL t lid ∨ spentT s < spentT t''',
'''  (∀ (s : St) (w lid b a reported G : ℕ),
    (spentL s lid + charge full a reported ≤ b ∧ spentT s + charge full a reported ≤ G) ↔
    (spentL s lid + charge full a a ≤ b ∧ spentT s + charge full a a ≤ G)) ∧
  (∀ (admins : List ℕ) (G : ℕ) (s : St) (w lid b a reported : ℕ) (p : List Op),
    leaseOf s w = some lid → budgetOf s lid = some b →
    spentL s lid + charge full a reported ≤ b → spentT s + charge full a reported ≤ G →
    (BackResult admins G s w lid a reported p ↔ OrigResult admins G s w lid a p))''',
'''by
  have step_report : ∀ (admins : List ℕ) (G : ℕ) (s : St) (w a r : ℕ),
      step admins G full s (.work w a r) = step admins G full s (.work w a a) := by
    intro admins G s w a r
    simp [step, charge, full]
  constructor
  · intro s w lid b a reported G
    simp [charge, full]
  · intro admins G s w lid b a reported p _ _ _ _
    dsimp only [BackResult, OrigResult]
    rw [step_report]''',
'''  let s := run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0]
  leaseOf s 1 = some 0 ∧ budgetOf s 0 = some 10 ∧
    spentL s 0 + charge full 2 999 ≤ 10 ∧ spentT s + charge full 2 999 ≤ 10 ∧
    (step [9] 10 full s (.work 1 2 999)).usage = [(1, 0, 2)]''')
save(9,'''def BackResult (s t : St) : Prop :=
  spentL s 0 = 0 ∧ t.usage = s.usage ∧ t.usage = [(2, 1, 10)]
def OrigResult (s t : St) : Prop :=
  t.usage = s.usage ∧ spentL s 0 = 0 ∧ s.usage = [(2, 1, 10)]''',
'''  ∀ (s t : St), BackResult s t ↔ OrigResult s t''',
'''by
  intro s t
  constructor
  · rintro ⟨hz, he, ht⟩
    exact ⟨he, hz, he.symm.trans ht⟩
  · rintro ⟨he, hz, hs⟩
    exact ⟨hz, he, he.trans hs⟩''',
'''  let s := run [9] 10 full init [.issue 9 0 10, .issue 9 1 10, .assignTo 9 1 0, .assignTo 9 2 1, .work 2 10 10]
  s.usage = [(2, 1, 10)] ∧ spentL s 0 = 0 ∧ spentT s = 10 ∧
    (step [9] 10 full s (.work 1 1 1)).usage = s.usage''')
save(10,'''def BackResult (admins : List ℕ) (G : ℕ)
    (t : RSt SC28.St {o : SC28.Op // SC28.legal o} (ℕ × ℕ × ℕ)) : Prop :=
  t.released = ((SC28.sys admins G).run SC28.init t.committed).usage ∧
    SC28.Good G ((SC28.sys admins G).run SC28.init t.committed)
def OrigResult (admins : List ℕ) (G : ℕ)
    (t : RSt SC28.St {o : SC28.Op // SC28.legal o} (ℕ × ℕ × ℕ)) : Prop :=
  t.released = (SC28.run admins G SC28.full SC28.init (t.committed.map Subtype.val)).usage ∧
    SC28.Good G (SC28.run admins G SC28.full SC28.init (t.committed.map Subtype.val))''',
'''  ∀ (admins : List ℕ) (G : ℕ)
    (t : RSt SC28.St {o : SC28.Op // SC28.legal o} (ℕ × ℕ × ℕ)),
    BackResult admins G t ↔ OrigResult admins G t''',
'''by
  have erun : ∀ (admins : List ℕ) (G : ℕ) (l : List {o : SC28.Op // SC28.legal o}) (s : SC28.St),
      (SC28.sys admins G).run s l = SC28.run admins G SC28.full s (l.map Subtype.val) := by
    intro admins G l
    induction l with
    | nil => intro s; rfl
    | cons o l ih => intro s; exact ih _
  intro admins G t
  unfold BackResult OrigResult
  rw [erun]''',
'''  (runR G28 true (rinit G28 SC28.init) spendTrace).released = [(1, 0, 10)] ∧
    (runR G28 true (rinit G28 SC28.init) spendTrace).halted = true ∧
    (runR G28 true (rinit G28 SC28.init) spendTrace).committed.length = 3''',
'by\n  set_option maxRecDepth 4096 in\n    decide')
save(11,'''def BackResult (G : ℕ) (s : CSt) : Prop :=
  runCounter s ≤ G ∧ (∀ lid, counter s lid ≤ (limitOf s lid).getD 0) ∧ s.acct.length ≤ G
def OrigResult (G : ℕ) (s : CSt) : Prop := SC28.Good G (α s)''',
'''  ∀ (G : ℕ) (s : CSt), BackResult G s ↔ OrigResult G s''',
'by\n  intro G s\n  rfl',cw)
save(12,'''def BackResult (G lid : ℕ) (first second : List COp) : Prop :=
  counter (runC G (runC G cinit first) second) lid = counter (runC G cinit first) lid
def OrigResult (G lid : ℕ) (first second : List COp) : Prop :=
  counter (runC G cinit (first ++ second)) lid = counter (runC G cinit first) lid''',
'''  ∀ (G lid : ℕ) (first second : List COp),
    lid ∈ (runC G cinit first).revoked → (BackResult G lid first second ↔ OrigResult G lid first second)''',
'by\n  intro G lid first second _\n  unfold BackResult OrigResult\n  rw [runC_append]',
'''  let first : List COp := [.createLease 0 10, .launch 1 0, .consume 1 2, .revoke 0]
  let s := runC 10 cinit first
  0 ∈ s.revoked ∧ counter s 0 = 2 ∧
    counter (runC 10 s [.fork 1 2, .consume 1 3, .launch 3 0, .consume 3 3]) 0 = 2''')
save(13,'''def BackResult (G : ℕ) (ops : List COp) : Prop :=
  let s := runC G cinit ops
  s.outside = [] ∧ realTotal s ≤ G
def OrigResult (G : ℕ) (ops : List COp) : Prop :=
  (runC G cinit ops).outside = [] ∧ realTotal (runC G cinit ops) ≤ G''',
'''  ∀ (G : ℕ) (ops : List COp), (∀ o ∈ ops, isUnplaced o = false) →
    (BackResult G ops ↔ OrigResult G ops)''',
'by\n  intro G ops _\n  rfl',
'''  let ops : List COp := [.createLease 0 10, .launch 1 0, .fork 1 2, .consume 1 2, .consume 2 3]
  (∀ o ∈ ops, isUnplaced o = false) ∧
    (runC 10 cinit ops).outside = [] ∧ realTotal (runC 10 cinit ops) = 5''',
'''by
  constructor
  · simp [isUnplaced]
  · decide''')
