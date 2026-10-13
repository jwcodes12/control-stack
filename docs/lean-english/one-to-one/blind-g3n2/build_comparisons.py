from pathlib import Path
OUT=Path(__file__).resolve().parent

contexts={1:'ControlStack.AuthInstances',2:'ControlStack.SC16Refinement',3:'ControlStack.SC16Refinement',4:'ControlStack.SC17',5:'ControlStack.SC17',6:'ControlStack.SC17',7:'ControlStack.SC17Drift',8:'ControlStack.SC17Drift',9:'ControlStack.AuthInstances',10:'ControlStack.AuthInstances'}

def closed(n):
    p=next((OUT/'typed').glob(f'{n}-*.lean'))
    text=p.read_text()
    expr=text.split(': Prop :=',1)[1].rsplit('\nend ',1)[0].strip()
    return 'def BackClosed : Prop :=\n  '+expr+'\n'

def save(n,defs,claim,witness,proof):
    cid=f'bg3n2_{n}'
    opens='open '+contexts[n]+' ControlStack\n'
    if n in (2,3): opens+='open ControlStack.SC16\n'
    if n in (1,9,10): opens+='open ControlStack.AuthenticatedLog\n'
    origtypes={
      1:'OrigAt',
      2:'∀ R h ops, OrigAt R h ops',
      3:'∀ R h ops, OrigHyp h (α (runC R h false cinit ops)) → OrigAt R (α (runC R h false cinit ops))',
      4:'∀ E g0 ops, OrigAt E g0 ops',
      5:'∀ E s, s.halted = false → OrigAt E s',
      6:'∀ E s ops, s.halted = true → OrigAt E s ops',
      7:'∀ d W, 0 < W → ∀ desired ops, OrigAt d W desired ops',
      8:'∀ d W, 0 < W → ∀ desired ops, OrigAt d W desired ops',
      9:'∀ E g0 U ops, OrigHyp E U → OrigAt E U (authRun (SC17.step E SC17.full) claim17 (SC17.init g0) ops) ops',
      10:'OrigAt'}
    names={1:'forged16_deploys_without_auth',2:'concrete_safe',3:'concrete_reviewed_content',4:'sc17_safe',5:'reconcile_restores',6:'halt_freezes',7:'drift_bounded',8:'drift_lifetime',9:'sc17_safe_authenticated',10:'forged17_applies_without_auth'}
    orig_signature='\ndef OrigClosed : Prop := '+origtypes[n]+'\n'
    orig_signature+='def OriginalDeclaration : OrigClosed := @'+contexts[n]+'.'+names[n]+'\n'
    statement=f'namespace PL_{cid}\n{opens}\n'+closed(n)+'\n'+defs+orig_signature+'\ndef Claim : Prop :=\n'+claim+'\n\ndef Witness : Prop :=\n'+witness+f'\n\nend PL_{cid}\n'
    (OUT/f'{cid}.statement.lean').write_text(statement)
    proof='open ControlStack\nopen '+contexts[n]+'\n\n'+proof
    (OUT/f'{cid}.proof.lean').write_text(proof)

trace16='[.put 1 7, .review 2 7 5, .approve 3 0 7 5 0, .deploy 1 0 5]'
trace17='[.propose 1 0 dA, .approve 2 0, .apply 0]'

save(1,'''def OrigAt : Prop :=
  (authRun (SC16.step SC16.R0 id SC16.full) (fun _ => none) SC16.init forged16).deployed = [⟨0, 5, 7⟩] ∧
  (authRun (SC16.step SC16.R0 id SC16.full) claim16 SC16.init forged16).deployed = []
''','  BackClosed ↔ OrigAt','  BackClosed', '''theorem claim : Claim := Iff.rfl

theorem witness : Witness := by
  unfold Witness BackClosed
  decide
''')

save(2,'''def BackAt (R : Roles) (h : ℕ → ℕ) (ops : List COp) : Prop :=
  SC16.Good R h (α (runC R h false cinit ops))
def OrigAt (R : Roles) (h : ℕ → ℕ) (ops : List COp) : Prop :=
  Good R h (α (runC R h false cinit ops))
''','''  (BackClosed ↔ ∀ R h ops, BackAt R h ops) ∧
  (∀ R h ops, BackAt R h ops ↔ OrigAt R h ops)''',f'''  (α (runC R0 id false cinit {trace16})).deployed = [⟨0, 5, 7⟩] ∧
  OrigAt R0 id {trace16}''','''theorem claim : Claim := ⟨Iff.rfl, fun _ _ _ => Iff.rfl⟩

theorem witness : Witness := by
  unfold Witness OrigAt SC16.Good SC16.DepOk SC16.ReviewOk
  decide
''')

save(3,'''def BackHyp (h : ℕ → ℕ) (s : SC16.St) : Prop :=
  ∀ x ∈ s.deployed.map SC16.Dep.content ++ s.reviews.map SC16.Review.content,
    ∀ y ∈ s.deployed.map SC16.Dep.content ++ s.reviews.map SC16.Review.content,
      h x = h y → x = y
def OrigHyp (h : ℕ → ℕ) (s : SC16.St) : Prop :=
  Set.InjOn h {c | (∃ e ∈ s.deployed, e.content = c) ∨ ∃ rv ∈ s.reviews, rv.content = c}
def BackAt (R : Roles) (s : SC16.St) : Prop :=
  ∀ e ∈ s.deployed, ∃ rv ∈ s.reviews,
    e.content = rv.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager
def OrigAt (R : Roles) (s : SC16.St) : Prop :=
  ∀ e ∈ s.deployed, ∃ rv ∈ s.reviews,
    rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager
''','''  (BackClosed ↔ ∀ R h ops,
    BackHyp h (α (runC R h false cinit ops)) → BackAt R (α (runC R h false cinit ops))) ∧
  (∀ h s, BackHyp h s ↔ OrigHyp h s) ∧
  (∀ R s, BackAt R s ↔ OrigAt R s)''',f'''  let s := α (runC R0 id false cinit {trace16})
  BackHyp id s ∧ s.deployed ≠ [] ∧ s.reviews ≠ []''','''theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_, ?_⟩
  · intro h s
    have mem_iff (c : ℕ) :
        c ∈ s.deployed.map SC16.Dep.content ++ s.reviews.map SC16.Review.content ↔
        (∃ e ∈ s.deployed, e.content = c) ∨ ∃ rv ∈ s.reviews, rv.content = c := by
      simp [List.mem_map, eq_comm]
    constructor
    · intro hb x hx y hy hxy
      exact hb x ((mem_iff x).mpr hx) y ((mem_iff y).mpr hy) hxy
    · intro ho x hx y hy hxy
      exact ho ((mem_iff x).mp hx) ((mem_iff y).mp hy) hxy
  · intro R s
    constructor
    · intro hb e he
      obtain ⟨rv, hr, heq, hrole, hneq⟩ := hb e he
      exact ⟨rv, hr, heq.symm, hrole, hneq⟩
    · intro ho e he
      obtain ⟨rv, hr, heq, hrole, hneq⟩ := ho e he
      exact ⟨rv, hr, heq.symm, hrole, hneq⟩

theorem witness : Witness := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy heq
    exact heq
  · decide
''')

save(4,'''def BackAt (E : Env) (g0 : List G) (ops : List Op) : Prop :=
  Good E (run E full (init g0) ops)
def OrigAt (E : Env) (g0 : List G) (ops : List Op) : Prop :=
  Good E (run E full (init g0) ops)
''','''  (BackClosed ↔ ∀ E g0 ops, BackAt E g0 ops) ∧
  (∀ E g0 ops, BackAt E g0 ops ↔ OrigAt E g0 ops)''',f'''  (run E0 full (init []) {trace17}).applied.map AppRec.id = [0] ∧
  OrigAt E0 [] {trace17}''','''theorem claim : Claim := ⟨Iff.rfl, fun _ _ _ => Iff.rfl⟩

theorem witness : Witness := by
  unfold Witness OrigAt Good AppOk
  decide
''')

save(5,'''def BackAt (E : Env) (s : St) : Prop :=
  (step E full s Op.reconcile).live = (step E full s Op.reconcile).desired
def OrigAt (E : Env) (s : St) : Prop :=
  (step E full s .reconcile).live = (step E full s .reconcile).desired
''','''  (BackClosed ↔ ∀ E s, s.halted = false → BackAt E s) ∧
  (∀ E s, s.halted = false → (BackAt E s ↔ OrigAt E s))''','''  let s := { init [] with live := [(7, 7, 7)] }
  s.halted = false ∧ s.live ≠ s.desired ∧ BackAt E0 s''','''theorem claim : Claim := ⟨Iff.rfl, fun _ _ _ => Iff.rfl⟩

theorem witness : Witness := by
  unfold Witness BackAt
  decide
''')

save(6,'''def BackAt (E : Env) (s : St) (ops : List Op) : Prop :=
  (run E full s ops).applied = s.applied
def OrigAt (E : Env) (s : St) (ops : List Op) : Prop :=
  (run E full s ops).applied = s.applied
''','''  (BackClosed ↔ ∀ E s ops, s.halted = true → BackAt E s ops) ∧
  (∀ E s ops, s.halted = true → (BackAt E s ops ↔ OrigAt E s ops))''','''  let s := run E0 full (init []) [.propose 1 0 dA, .approve 2 0, .apply 0, .halt 9]
  s.halted = true ∧ s.applied ≠ [] ∧
  (run E0 full s [.oob (7, 7, 7), .apply 0]).live ≠ s.live ∧
  BackAt E0 s [.oob (7, 7, 7), .apply 0]''','''theorem claim : Claim := ⟨Iff.rfl, fun _ _ _ _ => Iff.rfl⟩

theorem witness : Witness := by
  unfold Witness BackAt
  decide
''')

save(7,'''def BackAt (d W : ℕ) (desired : List ℕ) (ops : List Op) : Prop :=
  let s := run d W true (init desired) ops
  (s.live.filter (fun g => decide (g ∉ s.desired))).length ≤ d * W
def OrigAt (d W : ℕ) (desired : List ℕ) (ops : List Op) : Prop :=
  ((run d W true (init desired) ops).live.filter
    (fun g => g ∉ (run d W true (init desired) ops).desired)).length ≤ d * W
''','''  (BackClosed ↔ ∀ d W desired ops, 0 < W → BackAt d W desired ops) ∧
  (∀ d W desired ops, 0 < W → (BackAt d W desired ops ↔ OrigAt d W desired ops))''','''  0 < (3 : ℕ) ∧ 0 < (1 : ℕ) ∧
  let s := run 1 3 true (init [1]) [.oob 7, .tick, .oob 7]
  (s.live.filter (fun g => decide (g ∉ s.desired))).length = 2 ∧
  s.drift.length = 2 ∧ BackAt 1 3 [1] [.oob 7, .tick, .oob 7]''','''theorem claim : Claim := ⟨Iff.rfl, fun _ _ _ _ _ => Iff.rfl⟩

theorem witness : Witness := by
  unfold Witness BackAt
  decide
''')

save(8,'''def BackAt (d W : ℕ) (desired : List ℕ) (ops : List Op) : Prop :=
  let s := run d W true (init desired) ops
  ∀ p ∈ s.drift, s.clock - p.2 < W
def OrigAt (d W : ℕ) (desired : List ℕ) (ops : List Op) : Prop :=
  ∀ p ∈ (run d W true (init desired) ops).drift,
    (run d W true (init desired) ops).clock - p.2 < W
''','''  (BackClosed ↔ ∀ d W desired ops, 0 < W → BackAt d W desired ops) ∧
  (∀ d W desired ops, 0 < W → (BackAt d W desired ops ↔ OrigAt d W desired ops))''','''  0 < (3 : ℕ) ∧
  let s := run 1 3 true (init []) [.oob 7, .tick]
  (7, 0) ∈ s.drift ∧ s.clock - 0 = 1 ∧ BackAt 1 3 [] [.oob 7, .tick]''','''theorem claim : Claim := ⟨Iff.rfl, fun _ _ _ _ _ => Iff.rfl⟩

theorem witness : Witness := by
  unfold Witness BackAt
  decide
''')

save(9,'''def BackHyp (E : SC17.Env) (U : Set ℕ) : Prop :=
  ∀ c ∈ U, c ∉ E.reviewers
def OrigHyp (E : SC17.Env) (U : List ℕ) : Prop :=
  ∀ c ∈ U, c ∉ E.reviewers
def BackAt (E : SC17.Env) (U : Set ℕ) (s : SC17.St) (ops : List (ℕ × SC17.Op)) : Prop :=
  SC17.Good E s ∧
  (∀ a ∈ s.approvals,
    (a.reviewer, SC17.Op.approve a.reviewer a.id) ∈ ops ∧
    a.reviewer ∈ E.reviewers ∧ a.reviewer ∉ U) ∧
  (∀ p ∈ s.props,
    (p.author, SC17.Op.propose p.author p.id p.diff) ∈ ops ∨
    (p.author, SC17.Op.amend p.author p.id p.diff) ∈ ops)
def OrigAt (E : SC17.Env) (U : List ℕ) (s : SC17.St) (ops : List (ℕ × SC17.Op)) : Prop :=
  SC17.Good E s ∧
  (∀ a ∈ s.approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
    (o = SC17.Op.approve c a.id ∧ c = a.reviewer ∧ c ∈ E.reviewers)) ∧
  (∀ p ∈ s.props, ∃ c o, (c, o) ∈ ops ∧
    (c = p.author ∧ (o = SC17.Op.propose c p.id p.diff ∨ o = SC17.Op.amend c p.id p.diff)))
''','''  (BackClosed ↔ ∀ E U g0 ops, BackHyp E U →
    BackAt E U (authRun (SC17.step E SC17.full) claim17 (SC17.init g0) ops) ops) ∧
  (∀ E (UL : List ℕ), BackHyp E {c | c ∈ UL} ↔ OrigHyp E UL) ∧
  (∀ E (US : Set ℕ) (UL : List ℕ) s ops,
    BackHyp E US → OrigHyp E UL → (BackAt E US s ops ↔ OrigAt E UL s ops))''','''  OrigHyp SC17.E0 [1] ∧ BackHyp SC17.E0 {c | c ∈ ([1] : List ℕ)} ∧
  let s := authRun (SC17.step SC17.E0 SC17.full) claim17 (SC17.init [])
    [(1, .propose 1 0 SC17.dA), (2, .approve 2 0), (1, .apply 0)]
  s.approvals.map SC17.Ap.reviewer = [2] ∧
  s.props.map SC17.Pr.author = [1] ∧ s.applied.map SC17.AppRec.id = [0]''','''theorem claim : Claim := by
  refine ⟨Iff.rfl, (fun _ _ => Iff.rfl), ?_⟩
  intro E US UL s ops hUS hUL
  constructor
  · rintro ⟨hgood, hap, hprop⟩
    refine ⟨hgood, ?_, ?_⟩
    · intro a ha
      obtain ⟨hi, hr, _⟩ := hap a ha
      refine ⟨a.reviewer, SC17.Op.approve a.reviewer a.id, hi, ?_, rfl, rfl, hr⟩
      exact fun hu => hUL a.reviewer hu hr
    · intro p hp
      rcases hprop p hp with hi | hi
      · exact ⟨p.author, SC17.Op.propose p.author p.id p.diff, hi, rfl, Or.inl rfl⟩
      · exact ⟨p.author, SC17.Op.amend p.author p.id p.diff, hi, rfl, Or.inr rfl⟩
  · rintro ⟨hgood, hap, hprop⟩
    refine ⟨hgood, ?_, ?_⟩
    · intro a ha
      obtain ⟨c, o, hi, _, ho, hc, hr⟩ := hap a ha
      subst c
      subst o
      exact ⟨hi, hr, fun hu => hUS a.reviewer hu hr⟩
    · intro p hp
      obtain ⟨c, o, hi, hc, ho⟩ := hprop p hp
      subst c
      rcases ho with ho | ho
      · exact Or.inl (ho ▸ hi)
      · exact Or.inr (ho ▸ hi)

theorem witness : Witness := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst c
    decide
  · intro c hc
    change c ∈ ([1] : List ℕ) at hc
    simp only [List.mem_singleton] at hc
    subst c
    decide
  · decide
''')

save(10,'''def OrigAt : Prop :=
  (authRun (SC17.step SC17.E0 SC17.full) (fun _ => none) (SC17.init []) forged17).live = [(1, 1, 1)] ∧
  (authRun (SC17.step SC17.E0 SC17.full) claim17 (SC17.init []) forged17).applied = []
''','  BackClosed ↔ OrigAt','  BackClosed','''theorem claim : Claim := Iff.rfl

theorem witness : Witness := by
  unfold Witness BackClosed
  decide
''')
