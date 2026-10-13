from pathlib import Path
P=Path(__file__).resolve().parent
opens='open ControlStack.SC26 ControlStack.SC26Refinement ControlStack.SC26Liveness ControlStack.SC26Liveness.Concrete ControlStack.SC26LossyLiveness ControlStack.SC26LossyHalt\n'
def save(n,body,proof,witness):
 cid=f'bg6n3_{n}'
 f=next((P/'typed').glob(f'{n}-*.lean'))
 frozen=f.read_text(); frozen=frozen[frozen.index('def Back_'):frozen.rindex('\nend ')]
 (P/f'{cid}.statement.lean').write_text(f'namespace PL_{cid}\n'+opens+'\n'+frozen+'\n\n'+body+f'\nend PL_{cid}\n')
 (P/f'{cid}.proof.lean').write_text(opens+'\n'+proof+'\n\n'+witness+'\n')
save(1,'''def BackAt (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req)
    (pre mid₁ mid₂ post : List Op) : Prop :=
  let beforeExecute := run R cap full s pre
  let final := run R cap full s
    (pre ++ [.execute r.requester k] ++ mid₁ ++ [.deliver k] ++ mid₂ ++ [.arrive k] ++ post)
  final.halted = true ∨ (k, r.tx) ∈ final.bank ∨
    (k ∉ beforeExecute.reserved ∧ cap < beforeExecute.spent + r.tx.amount)

def OrigAt (R : Roles) (cap : ℕ) (s : St) (c k : ℕ) (r : Req)
    (a0 a1 a2 a3 : List Op) : Prop :=
  let t := run R cap full s (a0 ++ .execute c k :: a1 ++ .deliver k :: a2 ++ .arrive k :: a3)
  t.halted = true ∨ (k, r.tx) ∈ t.bank ∨
    (k ∉ (run R cap full s a0).reserved ∧ cap < (run R cap full s a0).spent + r.tx.amount)

def Claim : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : St) (c k : ℕ) (r : Req) (pre mid₁ mid₂ post : List Op),
    Inv R cap s → reqOf s k = some r → Approved R s k r →
    (∀ o ∈ pre ++ mid₁ ++ mid₂ ++ post, legal R o) →
    (BackAt R cap s k r pre mid₁ mid₂ post ↔ OrigAt R cap s c k r pre mid₁ mid₂ post)

def setup : List Op := [.request 1 wTx, .approve 2 0 wTx]
def Witness : Prop :=
  let s := run R0 10 full init setup
  Inv R0 10 s ∧ reqOf s 0 = some ⟨0, 1, wTx⟩ ∧
    Approved R0 s 0 ⟨0, 1, wTx⟩ ∧ (∀ o ∈ setup, legal R0 o) ∧
    (∀ o ∈ ([] : List Op), legal R0 o) ∧
    (0, wTx) ∈ (run R0 10 full s [.execute 88 0, .deliver 0, .arrive 0]).bank
''','''theorem execute_identity (R : Roles) (cap : ℕ) (s : St) (c c' k : ℕ) :
    step R cap full s (.execute c k) = step R cap full s (.execute c' k) := rfl

theorem claim : Claim := by
  intro R cap s c k r pre mid₁ mid₂ post _ _ _ _
  unfold BackAt OrigAt
  simp only [List.append_assoc, List.cons_append, List.nil_append,
    ControlStack.SC26Refinement.run_append, ControlStack.SC26.run_cons]
  rfl
''','''theorem witness : Witness := by
  have hl : ∀ o ∈ setup, legal R0 o := by simp [setup, legal]
  refine ⟨run_inv R0 10 sound_full init setup hl (inv_init R0 10), by decide, ?_, hl, by simp, by decide⟩
  exact ⟨2, by decide, by decide, by decide⟩
''')
save(2,'''def BackAt (R : Roles) (cap k : ℕ) (ops₀ pre mid post : List COp) : Prop :=
  let start := runC R cap true cinit ops₀
  let final := runC R cap true start (pre ++ [.recover] ++ mid ++ [.bankProcess k] ++ post)
  (final.bank.map Prod.fst).count k = 1

def OrigAt (R : Roles) (cap k : ℕ) (ops0 pre mid post : List COp) : Prop :=
  k ∈ (runC R cap true (runC R cap true cinit ops0) (pre ++ .recover :: mid ++ .bankProcess k :: post)).bank.map Prod.fst ∧
  ((runC R cap true (runC R cap true cinit ops0) (pre ++ .recover :: mid ++ .bankProcess k :: post)).bank.map Prod.fst).count k = 1

def Claim : Prop :=
  ∀ (R : Roles) (cap k : ℕ) (ops₀ pre mid post : List COp) (d : DRow),
    (∀ o ∈ ops₀, legalC R o) → d ∈ (runC R cap true cinit ops₀).delivery → d.id = k →
    (∀ o ∈ pre ++ mid ++ post, legalC R o) →
    (runC R cap true (runC R cap true cinit ops₀) pre).halted = false →
    (BackAt R cap k ops₀ pre mid post ↔ OrigAt R cap k ops₀ pre mid post)

def setup : List COp := [.request 1 wTx, .approve 2 0 wTx, .execute 1 0, .deliver 0]
def Witness : Prop :=
  let s := runC R0 10 true cinit setup
  (∀ o ∈ setup, legalC R0 o) ∧ ⟨0, wTx, false⟩ ∈ s.delivery ∧
  (∀ o ∈ ([.crash] ++ [.crash] ++ [.crash] : List COp), legalC R0 o) ∧
  (runC R0 10 true s [.crash]).halted = false ∧
  ((runC R0 10 true s [.crash, .recover, .crash, .bankProcess 0, .crash]).bank.map Prod.fst).count 0 = 1
''','''theorem claim : Claim := by
  intro R cap k ops₀ pre mid post d _ _ _ _ _
  unfold BackAt OrigAt
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  constructor
  · intro h
    exact ⟨List.count_pos_iff.mp (by omega), h⟩
  · exact And.right
''','''theorem witness : Witness := by
  refine ⟨?_, by decide, ?_, by decide, by decide⟩
  · simp [setup, legalC]
  · simp [legalC]
''')
save(3,'''def BackAt (R : Roles) (cap : ℕ) (ops : List LOp) : Prop :=
  Good R cap (α (runL R cap true cinit ops))
def OrigAt (R : Roles) (cap : ℕ) (ops : List LOp) : Prop :=
  Good R cap (α (runL R cap true cinit ops))
def Claim : Prop :=
  ∀ (R : Roles) (cap : ℕ) (ops : List LOp), (∀ o ∈ ops, legalL R o) →
    (BackAt R cap ops ↔ OrigAt R cap ops)
def trace : List LOp := setupOps ++ [.base .recover, .dup 0, .drop 0, .deliverAt 0]
def Witness : Prop :=
  (∀ o ∈ trace, legalL R0 o) ∧
  (runL R0 10 true cinit trace).bank = [(0, wTx)] ∧
  (runL R0 10 true cinit trace).spent = 10
''','''theorem claim : Claim := by
  intro R cap ops _
  exact Iff.rfl
''','''theorem witness : Witness := by
  refine ⟨?_, by decide, by decide⟩
  simp [trace, setupOps, legalL, legalC]
''')
save(5,'''def BackAt (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (k : ℕ) : Prop :=
  k ∈ (runLH R cap true s ops).bank.map Prod.fst →
    k ∈ s.bank.map Prod.fst ∨ k ∈ s.wire.map Prod.fst

def OrigAt (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (k : ℕ) : Prop :=
  k ∈ (runL R cap true s ops).bank.map Prod.fst →
    k ∈ s.bank.map Prod.fst ∨ k ∈ s.wire.map Prod.fst

def Claim : Prop :=
  ∀ (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) (k : ℕ),
    s.halted = true → (∀ o ∈ ops, legalL R o) →
    (BackAt R cap s ops k ↔ OrigAt R cap s ops k)

def start : CSt := { strandedState with wire := [(0, wTx)] }
def trace : List LOp := [.dup 0, .drop 0, .base .crash, .base .recover, .deliverAt 0]
def Witness : Prop :=
  start.halted = true ∧ start.bank = [] ∧ 0 ∈ start.wire.map Prod.fst ∧
  (∀ o ∈ trace, legalL R0 o) ∧
  (runLH R0 10 true start trace).bank = [(0, wTx)]
''','''theorem runners (R : Roles) (cap : ℕ) (s : CSt) (ops : List LOp) :
    runLH R cap true s ops = runL R cap true s ops := by
  have hs : stepLH R cap true = stepL R cap true := by
    funext s o
    cases o <;> rfl
  simp only [runLH, runL, hs]

theorem claim : Claim := by
  intro R cap s ops k _ _
  unfold BackAt OrigAt
  rw [runners]
''','''theorem witness : Witness := by
  refine ⟨rfl, rfl, by decide, ?_, by decide⟩
  simp [trace, legalL, legalC]
''')
rounddefs='''def BackLegal (R : Roles) (rounds : List (List LOp × List LOp)) : Prop :=
  ∀ o ∈ (rounds.map roundOps).flatten, legalL R o
def OrigLegal (R : Roles) (rounds : List (List LOp × List LOp)) : Prop :=
  ∀ r ∈ rounds, ∀ o ∈ r.1 ++ r.2, legalL R o
'''
roundproof='''theorem legal_rounds (R : Roles) (rounds : List (List LOp × List LOp)) :
    BackLegal R rounds ↔ OrigLegal R rounds := by
  unfold BackLegal OrigLegal
  constructor
  · intro h r hr o ho
    apply h o
    apply List.mem_flatten.mpr
    refine ⟨roundOps r, List.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    simp only [roundOps, List.mem_append, List.mem_cons] at *
    rcases ho with ho | ho
    · exact Or.inl ho
    · exact Or.inr (Or.inr ho)
  · intro h o ho
    obtain ⟨l, hl, ho⟩ := List.mem_flatten.mp ho
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
    simp only [roundOps, List.mem_append, List.mem_cons] at ho
    rcases ho with ho | ho | ho
    · exact h r hr o (List.mem_append_left _ ho)
    · subst o; trivial
    · exact h r hr o (List.mem_append_right _ ho)
'''
save(4,rounddefs+'''def BackFair (k : ℕ) (rounds : List (List LOp × List LOp)) : Prop :=
  ∃ r ∈ rounds, Delivers k r
def OrigFair (k : ℕ) (rounds : List (List LOp × List LOp)) : Prop :=
  ∃ j, ∃ hj : j < rounds.length, Delivers k rounds[j]

def BackAt (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
    (rounds : List (List LOp × List LOp)) (post : List LOp) : Prop :=
  let start := runL R cap true cinit ops₀
  let final := runL R cap true start (rounds.map roundOps).flatten
  k ∈ final.bank.map Prod.fst ∧ ((runL R cap true final post).bank.map Prod.fst).count k = 1

def OrigAt (R : Roles) (cap k : ℕ) (ops0 : List LOp)
    (rounds : List (List LOp × List LOp)) (post : List LOp) : Prop :=
  k ∈ (runL R cap true (runL R cap true cinit ops0) (rounds.map roundOps).flatten).bank.map Prod.fst ∧
    ((runL R cap true (runL R cap true cinit ops0) ((rounds.map roundOps).flatten ++ post)).bank.map Prod.fst).count k = 1

def Claim : Prop :=
  (∀ R rounds, BackLegal R rounds ↔ OrigLegal R rounds) ∧
  (∀ k rounds, BackFair k rounds ↔ OrigFair k rounds) ∧
  (∀ (R : Roles) (cap k : ℕ) (ops₀ : List LOp) (d : DRow)
      (rounds : List (List LOp × List LOp)) (post : List LOp),
    (∀ o ∈ ops₀, legalL R o) → d ∈ (runL R cap true cinit ops₀).delivery → d.id = k →
    BackLegal R rounds → (∀ o ∈ post, legalL R o) → BackFair k rounds →
    (runL R cap true (runL R cap true cinit ops₀) (rounds.map roundOps).flatten).halted = false →
    (BackAt R cap k ops₀ rounds post ↔ OrigAt R cap k ops₀ rounds post))

def rounds : List (List LOp × List LOp) := [([], [.base (.bankProcess 0)])]
def Witness : Prop :=
  (∀ o ∈ setupOps, legalL R0 o) ∧
  ⟨0, wTx, false⟩ ∈ (runL R0 10 true cinit setupOps).delivery ∧
  BackLegal R0 rounds ∧ BackFair 0 rounds ∧
  (runL R0 10 true (runL R0 10 true cinit setupOps) (rounds.map roundOps).flatten).halted = false ∧
  (∀ o ∈ ([.dup 0, .deliverAt 0] : List LOp), legalL R0 o) ∧
  BackAt R0 10 0 setupOps rounds [.dup 0, .deliverAt 0]
''',roundproof+'''
theorem fair_rounds (k : ℕ) (rounds : List (List LOp × List LOp)) :
    BackFair k rounds ↔ OrigFair k rounds := by
  constructor
  · rintro ⟨r, hr, hd⟩
    obtain ⟨j, hj, he⟩ := List.getElem_of_mem hr
    exact ⟨j, hj, he.symm ▸ hd⟩
  · rintro ⟨j, hj, hd⟩
    exact ⟨rounds[j], List.getElem_mem hj, hd⟩

theorem claim : Claim := by
  refine ⟨legal_rounds, fair_rounds, ?_⟩
  intro R cap k ops₀ d rounds post _ _ _ _ _ _ _
  unfold BackAt OrigAt
  rw [runL_append]
''','''theorem witness : Witness := by
  refine ⟨?_, by decide, ?_, ?_, by decide, ?_, ?_⟩
  · simp [setupOps, legalL, legalC]
  · simp [BackLegal, rounds, roundOps, legalL, legalC]
  · refine ⟨([], [.base (.bankProcess 0)]), by simp [rounds], [], [], rfl, ?_⟩
    simp [DropFree]
  · simp [legalL]
  · constructor <;> decide
''')
save(6,rounddefs+'''def BackFair (R : Roles) (cap k : ℕ) (start : TSt)
    (rounds : List (List LOp × List LOp)) : Prop :=
  ∃ (before : List (List LOp × List LOp)) (r : List LOp × List LOp)
    (after : List (List LOp × List LOp)),
    rounds = before ++ r :: after ∧
      DeliversT R cap k (runT R cap start (before.map roundOps).flatten) r

def OrigFair (R : Roles) (cap k : ℕ) (start : TSt)
    (rounds : List (List LOp × List LOp)) : Prop :=
  ∃ j, ∃ hj : j < rounds.length,
    DeliversT R cap k (runT R cap start ((rounds.take j).map roundOps).flatten) rounds[j]

def BackAt (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
    (rounds : List (List LOp × List LOp)) (post : List LOp) : Prop :=
  let start := runT R cap tinit ops₀
  let final := runT R cap start (rounds.map roundOps).flatten
  k ∈ final.c.bank.map Prod.fst ∧ ((runT R cap final post).c.bank.map Prod.fst).count k = 1

def OrigAt (R : Roles) (cap k : ℕ) (ops0 : List LOp)
    (rounds : List (List LOp × List LOp)) (post : List LOp) : Prop :=
  k ∈ (runT R cap (runT R cap tinit ops0) (rounds.map roundOps).flatten).c.bank.map Prod.fst ∧
    ((runT R cap (runT R cap tinit ops0) ((rounds.map roundOps).flatten ++ post)).c.bank.map Prod.fst).count k = 1

def Claim : Prop :=
  (∀ R rounds, BackLegal R rounds ↔ OrigLegal R rounds) ∧
  (∀ R cap k start rounds, BackFair R cap k start rounds ↔ OrigFair R cap k start rounds) ∧
  (∀ (R : Roles) (cap k : ℕ) (ops₀ : List LOp)
      (rounds : List (List LOp × List LOp)) (post : List LOp),
    (∀ o ∈ ops₀, legalL R o) → BackLegal R rounds →
    (∀ o ∈ post, legalL R o) → BackFair R cap k (runT R cap tinit ops₀) rounds →
    (BackAt R cap k ops₀ rounds post ↔ OrigAt R cap k ops₀ rounds post))

def Witness : Prop :=
  (∀ o ∈ setupOps, legalL R0 o) ∧ BackLegal R0 [pcRound] ∧
  BackFair R0 10 0 (runT R0 10 tinit setupOps) [pcRound] ∧
  (∀ o ∈ ([.dup 0, .deliverAt 0] : List LOp), legalL R0 o) ∧
  BackAt R0 10 0 setupOps [pcRound] [.dup 0, .deliverAt 0]
''',roundproof+'''
theorem fair_rounds (R : Roles) (cap k : ℕ) (start : TSt)
    (rounds : List (List LOp × List LOp)) :
    BackFair R cap k start rounds ↔ OrigFair R cap k start rounds := by
  constructor
  · rintro ⟨before, r, after, hs, hd⟩
    subst rounds
    refine ⟨before.length, by simp, ?_⟩
    simpa using hd
  · rintro ⟨j, hj, hd⟩
    refine ⟨rounds.take j, rounds[j], rounds.drop (j + 1), ?_, hd⟩
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]

theorem claim : Claim := by
  refine ⟨legal_rounds, fair_rounds, ?_⟩
  intro R cap k ops₀ rounds post _ _ _ _
  unfold BackAt OrigAt
  rw [runT_append]
''','''theorem witness : Witness := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [setupOps, legalL, legalC]
  · simp [BackLegal, pcRound, roundOps, legalL, legalC]
  · refine ⟨[], pcRound, [], rfl, ?_⟩
    have hs : runT R0 10 tinit setupOps = tLogged := by decide
    change DeliversT R0 10 0 (runT R0 10 tinit setupOps) pcRound
    rw [hs]
    exact per_copy_weaker.2.1
  · simp [legalL]
  · constructor <;> decide
''')
