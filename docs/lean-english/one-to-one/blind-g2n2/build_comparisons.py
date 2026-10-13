from pathlib import Path
OUT=Path(__file__).resolve().parent
DATA={}
DATA[1]=('ControlStack.SC12',r'''
def BackAt (admins : List ℕ) (s : St) (sess : ℕ) (ops : List Op) : Prop :=
  ((run admins full s ops).fired.filter (fun f => decide (f.2.1 = sess))) =
    (s.fired.filter (fun f => decide (f.2.1 = sess)))
def OrigAt (admins : List ℕ) (s : St) (sess : ℕ) (ops : List Op) : Prop :=
  (run admins full s ops).fired.filter (fun f => f.2.1 = sess) =
    s.fired.filter (fun f => f.2.1 = sess)
def Claim : Prop := ∀ (admins : List ℕ) (s : St) (sess : ℕ) (ops : List Op),
  Inv s → sess ∈ s.ended → (BackAt admins s sess ops ↔ OrigAt admins s sess ops)
def Witness : Prop := ∃ (s : St) (ops : List Op),
  Inv s ∧ 1 ∈ s.ended ∧ ops ≠ [] ∧ s.fired = [(5, 1, 0)] ∧
  (run [9] full s ops).fired = [(5, 1, 0), (6, 2, 1)]
''',r'''
open ControlStack ControlStack.SC12
example : FrozenBack = (∀ (admins : List ℕ) (s : St) (sess : ℕ) (ops : List Op),
    Inv s → sess ∈ s.ended → BackAt admins s sess ops) := rfl
example (admins : List ℕ) (s : St) (sess : ℕ) (ops : List Op)
    (h : Inv s) (hs : sess ∈ s.ended) : OrigAt admins s sess ops :=
  no_fire_after_end admins s ops h sess hs

theorem claim : Claim := by
  intro admins s sess ops h hs
  exact Iff.rfl

theorem witness : Witness := by
  let prior : List Op := [.start 9 1, .spawn 1 5 true 0, .fire 5, .endSession 9 1]
  refine ⟨run [9] full init prior, [.fire 5, .start 9 2, .spawn 2 6 true 0, .fire 6], ?_, ?_⟩
  · exact run_inv [9] init prior inv_init
  · decide
''')
DATA[2]=('ControlStack.SC12',r'''
def BackAt (admins : List ℕ) (s : St) (ops : List Op) : Prop := run admins full s ops = s
def OrigAt (admins : List ℕ) (s : St) (ops : List Op) : Prop := run admins full s ops = s
def Claim : Prop := ∀ (admins : List ℕ) (s : St) (ops : List Op),
  s.halted = true → (BackAt admins s ops ↔ OrigAt admins s ops)
def Witness : Prop := ∃ (s : St) (ops : List Op),
  s.halted = true ∧ s.fired = [(5, 1, 0)] ∧ ops ≠ [] ∧ run [9] full s ops = s
''',r'''
open ControlStack ControlStack.SC12
example : FrozenBack = (∀ (admins : List ℕ) (s : St) (ops : List Op),
    s.halted = true → BackAt admins s ops) := rfl
example (admins : List ℕ) (s : St) (ops : List Op) (hh : s.halted = true) :
    OrigAt admins s ops := halt_freezes admins s ops hh

theorem claim : Claim := by
  intro admins s ops hh
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨run [9] full init [.start 9 1, .spawn 1 5 true 0, .fire 5, .halt 9],
    [.start 9 2, .spawn 1 6 true 0, .fire 5, .endSession 9 1, .halt 9], ?_⟩
  decide
''')
DATA[3]=('ControlStack.AuthInstances',r'''
def BackAt (admins U : List ℕ) (ops : List (ℕ × SC12.Op)) (s : SC12.St) : Prop :=
  SC12.Good s ∧ ∀ e ∈ s.live, ∃ c : ℕ,
    c ∈ admins ∧ c ∉ U ∧ (c, SC12.Op.start c e.origin) ∈ ops
def OrigAt (admins U : List ℕ) (ops : List (ℕ × SC12.Op)) (s : SC12.St) : Prop :=
  SC12.Good s ∧ ∀ e ∈ s.live, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
    (o = SC12.Op.start c e.origin ∧ c ∈ admins)
def Claim : Prop := ∀ (admins U : List ℕ) (ops : List (ℕ × SC12.Op)) (s : SC12.St),
  BackAt admins U ops s ↔ OrigAt admins U ops s
def Witness : Prop :=
  let admins := [9]; let U := [1]
  let ops : List (ℕ × SC12.Op) := [(9, .start 9 5), (1, .spawn 5 6 true 0), (1, .fire 6)]
  let s := AuthenticatedLog.authRun (SC12.step admins SC12.full) claim12 SC12.init ops
  (∀ u ∈ U, u ∉ admins) ∧
  s.live = [⟨5, 5, 5, false, true⟩, ⟨6, 5, 5, true, true⟩] ∧
  s.fired = [(6, 5, 0)] ∧ (9, SC12.Op.start 9 5) ∈ ops ∧ 9 ∉ U
''',r'''
open ControlStack ControlStack.AuthInstances
example : FrozenBack = (∀ (admins U : List ℕ) (ops : List (ℕ × SC12.Op)),
    (∀ u ∈ U, u ∉ admins) → BackAt admins U ops
      (AuthenticatedLog.authRun (SC12.step admins SC12.full) claim12 SC12.init ops)) := rfl
example (admins U : List ℕ) (ops : List (ℕ × SC12.Op)) (hU : ∀ u ∈ U, u ∉ admins) :
    OrigAt admins U ops
      (AuthenticatedLog.authRun (SC12.step admins SC12.full) claim12 SC12.init ops) :=
  sc12_safe_authenticated admins U ops hU

theorem claim : Claim := by
  intro admins U ops s
  constructor
  · rintro ⟨hg, hp⟩
    refine ⟨hg, ?_⟩
    intro e he
    obtain ⟨c, hca, hcu, hco⟩ := hp e he
    exact ⟨c, SC12.Op.start c e.origin, hco, hcu, rfl, hca⟩
  · rintro ⟨hg, hp⟩
    refine ⟨hg, ?_⟩
    intro e he
    obtain ⟨c, o, hco, hcu, hoe, hca⟩ := hp e he
    subst o
    exact ⟨c, hca, hcu, hco⟩

theorem witness : Witness := by
  refine ⟨?_, ?_⟩
  · simp
  · decide
''')
DATA[4]=('ControlStack.AuthInstances',r'''
def Unguarded : SC12.St := AuthenticatedLog.authRun
  (SC12.step [9] SC12.full) (fun _ => (none : Option ℕ)) SC12.init forged12
def Guarded : SC12.St := AuthenticatedLog.authRun
  (SC12.step [9] SC12.full) claim12 SC12.init forged12
def BackAt (unguarded guarded : SC12.St) : Prop :=
  unguarded.live.length = 2 ∧ guarded = SC12.init
def OrigAt (unguarded guarded : SC12.St) : Prop :=
  unguarded.live.length = 2 ∧ guarded.live = []
def Claim : Prop :=
  (∀ unguarded guarded, BackAt unguarded guarded → OrigAt unguarded guarded) ∧
  (∃ unguarded guarded, OrigAt unguarded guarded ∧ ¬ BackAt unguarded guarded)
def Witness : Prop :=
  forged12 = [(1, SC12.Op.start 9 5), (1, SC12.Op.spawn 5 6 true 0)] ∧
  Unguarded.live.length = 2 ∧ Guarded = SC12.init
''',r'''
open ControlStack ControlStack.AuthInstances
example : FrozenBack = BackAt Unguarded Guarded := rfl
example : OrigAt Unguarded Guarded := forged12_spawns_without_auth

theorem claim : Claim := by
  constructor
  · intro unguarded guarded h
    refine ⟨h.1, ?_⟩
    rw [h.2]
    rfl
  · refine ⟨⟨[5], [], [⟨5, 5, 5, false, true⟩, ⟨6, 5, 5, true, true⟩], [], false⟩,
      { SC12.init with halted := true }, ?_⟩
    unfold OrigAt BackAt
    decide

theorem witness : Witness := by
  unfold Witness Unguarded Guarded
  decide
''')
DATA[5]=('ControlStack.AuditDispatch',r'''
def BackAt (s : St) (ops : List Op) : Prop := Inv (run s ops) ∧ s.audits <+: (run s ops).audits
def OrigAt (s : St) (ops : List Op) : Prop := Inv (run s ops) ∧ s.audits <+: (run s ops).audits
def Claim : Prop := ∀ (s : St) (ops : List Op), Inv s → (BackAt s ops ↔ OrigAt s ops)
def Witness : Prop := ∃ (s : St) (ops : List Op),
  Inv s ∧ s.effects = [1] ∧ ops ≠ [] ∧
  (run s ops).audits = [1, 2] ∧ (run s ops).effects = [1, 2]
''',r'''
open ControlStack ControlStack.AuditDispatch
example : FrozenBack = (∀ (s : St) (ops : List Op), Inv s → BackAt s ops) := rfl
example (s : St) (ops : List Op) (h : Inv s) : OrigAt s ops := trace_safe s ops h

theorem claim : Claim := by
  intro s ops h
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨⟨[1], [1], [1]⟩,
    [.request 2, .appEvent, .appSchema, .dispatch 2, .dispatch 2, .crash, .restart], ?_, ?_⟩
  · simp [ControlStack.AuditDispatch.Inv]
  · decide
''')
DATA[6]=('ControlStack.AuditDispatch',r'''
def BackAt (s : St) (o : Op) : Prop := (step s o).effects = s.effects
def OrigAt (s : St) (o : Op) : Prop := (step s o).effects = s.effects
def Claim : Prop := ∀ (s : St) (o : Op),
  (∀ id : ℕ, o ≠ Op.dispatch id) → (BackAt s o ↔ OrigAt s o)
def Witness : Prop := ∃ (s : St) (o : Op),
  (∀ id : ℕ, o ≠ Op.dispatch id) ∧ s.effects = [3] ∧
  (step s o).effects = [3] ∧ (step s o).requests = [4]
''',r'''
open ControlStack ControlStack.AuditDispatch
example : FrozenBack = (∀ (s : St) (o : Op),
    (∀ id : ℕ, o ≠ Op.dispatch id) → BackAt s o) := rfl
example (s : St) (o : Op) (happ : ∀ id : ℕ, o ≠ Op.dispatch id) :
    OrigAt s o := app_cannot_effect s o happ

theorem claim : Claim := by
  intro s o happ
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨⟨[], [3], [3]⟩, .request 4, ?_, rfl, rfl, rfl⟩
  intro id h
  cases h
''')
DATA[7]=('ControlStack.SC14',r'''
def BackAt (E : Env) (exp : ℕ) (ops : List Op) : Prop := Good E (run E full (init exp) ops)
def OrigAt (E : Env) (exp : ℕ) (ops : List Op) : Prop := Good E (run E full (init exp) ops)
def Claim : Prop := ∀ (E : Env) (exp : ℕ) (ops : List Op),
  (∀ o ∈ ops, legal o) → (BackAt E exp ops ↔ OrigAt E exp ops)
def Witness : Prop := ∃ ops : List Op,
  (∀ o ∈ ops, legal o) ∧
  (run E0 full (init 100) ops).usage = [((2, 2, 2), 0, 100), ((3, 3, 3), 1, 100)] ∧
  usedTotal (run E0 full (init 100) ops) = (5, 5, 5)
''',r'''
open ControlStack ControlStack.SC14
example : FrozenBack = (∀ (E : Env) (exp : ℕ) (ops : List Op),
    (∀ o ∈ ops, legal o) → BackAt E exp ops) := rfl
example (E : Env) (exp : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal o) :
    OrigAt E exp ops := sc14_safe E exp ops hops

theorem claim : Claim := by
  intro E exp ops hops
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨[.work (2, 2, 2) 0, .tick, .work (3, 3, 3) 0], ?_, ?_⟩
  · simp [legal]
  · decide
''')
DATA[8]=('ControlStack.SC14',r'''
def BackAt (E : Env) (s : St) (ops : List Op) : Prop := (run E full s ops).usage = s.usage
def OrigAt (E : Env) (s : St) (ops : List Op) : Prop := (run E full s ops).usage = s.usage
def Claim : Prop := ∀ (E : Env) (s : St) (ops : List Op),
  s.halted = true → (BackAt E s ops ↔ OrigAt E s ops)
def Witness : Prop := ∃ (s : St) (ops : List Op),
  s.halted = true ∧ s.usage = [((2, 2, 2), 0, 100)] ∧ s.spent = (2, 2, 2) ∧
  Op.rollback ∈ ops ∧ (run E0 full s ops).spent = 0 ∧ (run E0 full s ops).usage = s.usage
''',r'''
open ControlStack ControlStack.SC14
example : FrozenBack = (∀ (E : Env) (s : St) (ops : List Op),
    s.halted = true → BackAt E s ops) := rfl
example (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) :
    OrigAt E s ops := halt_freezes E s ops hh

theorem claim : Claim := by
  intro E s ops hh
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨⟨(2, 2, 2), (2, 2, 2), 0, 100, [((2, 2, 2), 0, 100)], true⟩,
    [.rollback, .work (1, 1, 1) 0, .tick, .setExpiry 9 200, .halt 9], ?_⟩
  decide
''')
for n,(ns,defs,proof) in DATA.items():
 p=next((OUT/'typed').glob(f'{n}-*.lean'))
 body=p.read_text().split('def Back_',1)[1].split(': Prop :=',1)[1].rsplit('end ',1)[0].strip()
 statement=f'namespace PL_bg2n2_{n}\n\nopen ControlStack {ns}\n\ndef FrozenBack : Prop :=\n{body}\n'+defs+f'\nend PL_bg2n2_{n}\n'
 (OUT/f'bg2n2_{n}.statement.lean').write_text(statement)
 (OUT/f'bg2n2_{n}.proof.lean').write_text(proof.lstrip())
