"""Save comparison statements; the frozen BackClosed bodies are copied verbatim."""
from pathlib import Path
import re

OUT = Path(__file__).resolve().parent

SC15_TRACE = '[.propose 1 0 7 [5] [5], .review 2 0 false, .runCI 0, .merge 0]'
SC16_TRACE = '[.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]'
AUTH15_TRACE = '[(1, .propose 1 0 7 [5] [5]), (2, .review 2 0 false), (1, .runCI 0), (1, .merge 0)]'
AUTH16_TRACE = '[(1, .stage 1 7), (2, .review 2 7), (3, .approve 3 0 7 5 0), (1, .deploy 1 0 5 7)]'

def save(n, opens, defs, claim, witness, proof, original_name):
    p = next((OUT/'typed').glob(f'{n}-*.lean'))
    raw = p.read_text()
    body = raw[raw.index('def Back_'):raw.rindex('\nend ')].strip()
    body = re.sub(r'^def Back_\w+', 'def BackClosed', body, count=1)
    cid = f'bg3n1_{n}'
    statement = f'namespace PL_{cid}\n\nopen ControlStack\n{opens}\n\n{body}\n\n{defs}\n\ndef Claim : Prop :=\n{claim}\n\ndef Witness : Prop :=\n{witness}\n\nend PL_{cid}\n'
    # OrigClosed is separately type-checked against the named source theorem.
    proof = proof.replace('theorem witness : Witness := by decide', 'theorem witness : Witness := by\n  decide')
    proof = proof.replace('theorem witness : Witness := by\n', 'theorem witness : Witness := by\n  unfold Witness\n')
    proof = f'open ControlStack\n{opens}\n\ntheorem original_type : OrigClosed := @{original_name}\n\n{proof}\n'
    (OUT/f'{cid}.statement.lean').write_text(statement)
    (OUT/f'{cid}.proof.lean').write_text(proof)

save(1, 'open ControlStack.SC15', '''def BackAt (E : Env) (s : St) : Prop :=
  ∀ c ∈ s.merged, MergeOk E s c
def OrigAt (E : Env) (s : St) : Prop :=
  ∀ c ∈ s.merged, MergeOk E s c
def OrigClosed : Prop := ∀ (E : Env) (ops : List Op),
  ∀ c ∈ (run E full init ops).merged, MergeOk E (run E full init ops) c''',
'''  (BackClosed ↔ ∀ E ops, BackAt E (run E full init ops)) ∧
  (OrigClosed ↔ ∀ E ops, OrigAt E (run E full init ops)) ∧
  (∀ E s, BackAt E s ↔ OrigAt E s)''',
f'''  let s := run E0 full init {SC15_TRACE}
  s.merged = [⟨0, 1, 7, [5], [5]⟩] ∧ s.reviews ≠ [] ∧ s.ci ≠ []''',
'''theorem claim : Claim := ⟨Iff.rfl, Iff.rfl, fun _ _ => Iff.rfl⟩
theorem witness : Witness := by decide''', 'ControlStack.SC15.sc15_safe')

save(2, 'open ControlStack.SC15', '''def BackAt (E : Env) (s : St) (ops : List Op) : Prop := run E full s ops = s
def OrigAt (E : Env) (s : St) (ops : List Op) : Prop := run E full s ops = s
def OrigClosed : Prop := ∀ (E : Env) (s : St) (ops : List Op),
  s.halted = true → run E full s ops = s''',
'''  (BackClosed ↔ ∀ E s ops, s.halted = true → BackAt E s ops) ∧
  (OrigClosed ↔ ∀ E s ops, s.halted = true → OrigAt E s ops) ∧
  (∀ E s ops, s.halted = true → (BackAt E s ops ↔ OrigAt E s ops))''',
'''  let s : St := { init with halted := true, merged := [⟨0, 1, 7, [5], [5]⟩] }
  let ops : List Op := [.propose 1 1 8 [] [], .review 2 0 false, .runCI 0, .merge 0, .halt 9]
  s.halted = true ∧ s.merged ≠ [] ∧ run E0 full s ops = s''',
'''theorem claim : Claim := ⟨Iff.rfl, Iff.rfl, fun _ _ _ _ => Iff.rfl⟩
theorem witness : Witness := by decide''', 'ControlStack.SC15.halt_freezes')

save(3, 'open ControlStack.SC15 ControlStack.AuthInstances ControlStack.AuthenticatedLog', '''def HypBack (E : Env) (U : List ℕ) : Prop := ∀ c ∈ U, c ∉ E.reviewers ∧ c ∉ E.security
def HypOrig (E : Env) (U : List ℕ) : Prop := ∀ c ∈ U, c ∉ E.reviewers ++ E.security
def BackAt (E : Env) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  (∀ c ∈ s.merged, MergeOk E s c) ∧
  (∀ r ∈ s.reviews, (r.reviewer, Op.review r.reviewer r.id r.sec) ∈ ops ∧
    r.reviewer ∉ U ∧ roleOk E r.sec r.reviewer = true)
def OrigAt (E : Env) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  (∀ c ∈ s.merged, MergeOk E s c) ∧
  (∀ r ∈ s.reviews, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
    (o = .review c r.id r.sec ∧ c = r.reviewer ∧ roleOk E r.sec c = true))
def OrigClosed : Prop := ∀ (E : Env) (U : List ℕ) (ops : List (ℕ × Op)),
  HypOrig E U → OrigAt E U ops (authRun (step E full) claim15 init ops)''',
'''  (BackClosed ↔ ∀ E U ops, HypBack E U → BackAt E U ops (authRun (step E full) claim15 init ops)) ∧
  (∀ E U, HypBack E U ↔ HypOrig E U) ∧
  (∀ E U ops s, BackAt E U ops s ↔ OrigAt E U ops s)''',
f'''  HypBack E0 [1] ∧
  let s := authRun (step E0 full) claim15 init {AUTH15_TRACE}
  s.merged = [⟨0, 1, 7, [5], [5]⟩] ∧ s.reviews ≠ []''',
'''theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_, ?_⟩
  · intro E U
    simp only [HypBack, HypOrig, List.mem_append, not_or]
  · intro E U ops s
    unfold BackAt OrigAt
    constructor
    · rintro ⟨hm, hr⟩
      refine ⟨hm, fun r h => ?_⟩
      obtain ⟨ho, hu, hp⟩ := hr r h
      exact ⟨r.reviewer, .review r.reviewer r.id r.sec, ho, hu, rfl, rfl, hp⟩
    · rintro ⟨hm, hr⟩
      refine ⟨hm, fun r h => ?_⟩
      obtain ⟨c, o, ho, hu, rfl, rfl, hp⟩ := hr r h
      exact ⟨ho, hu, hp⟩
theorem witness : Witness := by
  constructor
  · simp [HypBack, E0]
  · decide''', 'ControlStack.AuthInstances.sc15_safe_authenticated')

save(4, 'open ControlStack.SC15 ControlStack.AuthInstances ControlStack.AuthenticatedLog', '''def BackAt (unchecked checked : St) : Prop :=
  0 ∈ unchecked.merged.map Change.id ∧ checked.merged = []
def OrigAt (unchecked checked : St) : Prop :=
  unchecked.merged = [⟨0, 1, 7, [5], [5]⟩] ∧ checked.merged = []
def unchecked : St := authRun (step E0 full) (fun _ => none) init forged15
def checked : St := authRun (step E0 full) claim15 init forged15
def OrigClosed : Prop := OrigAt unchecked checked''',
'''  (BackClosed ↔ BackAt unchecked checked) ∧
  (∀ u c, OrigAt u c → BackAt u c) ∧
  (∃ u c, BackAt u c ∧ ¬ OrigAt u c)''',
'''  OrigAt unchecked checked ∧ unchecked.reviews ≠ [] ∧
  (∀ u c, OrigAt u c → BackAt u c)''',
'''theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_, ?_⟩
  · intro u c h
    obtain ⟨hu, hc⟩ := h
    exact ⟨by simp [hu], hc⟩
  · refine ⟨{ init with merged := [⟨0, 1, 999, [5], [5]⟩] }, init, ?_⟩
    unfold BackAt OrigAt
    decide
theorem witness : Witness := by
  refine ⟨by unfold OrigAt; decide, by decide, ?_⟩
  intro u c h
  obtain ⟨hu, hc⟩ := h
  exact ⟨by simp [hu], hc⟩''', 'ControlStack.AuthInstances.forged15_merges_without_auth')

save(5, 'open ControlStack.SC16', '''def BackAt (R : Roles) (h : ℕ → ℕ) (s : St) : Prop := Good R h s
def OrigAt (R : Roles) (h : ℕ → ℕ) (s : St) : Prop := Good R h s
def OrigClosed : Prop := ∀ (R : Roles) (h : ℕ → ℕ) (ops : List Op), Good R h (run R h full init ops)''',
'''  (BackClosed ↔ ∀ R h ops, BackAt R h (run R h full init ops)) ∧
  (OrigClosed ↔ ∀ R h ops, OrigAt R h (run R h full init ops)) ∧
  (∀ R h s, BackAt R h s ↔ OrigAt R h s)''',
f'''  let s := run R0 id full init {SC16_TRACE}
  s.deployed = [⟨0, 5, 7⟩] ∧ s.reviews ≠ [] ∧ s.approvals ≠ []''',
'''theorem claim : Claim := ⟨Iff.rfl, Iff.rfl, fun _ _ _ => Iff.rfl⟩
theorem witness : Witness := by decide''', 'ControlStack.SC16.sc16_safe')

INJ_DEFS = '''def Contents (s : St) : List ℕ := s.deployed.map Dep.content ++ s.reviews.map Review.content
def HypBack (h : ℕ → ℕ) (s : St) : Prop :=
  ∀ x y, x ∈ Contents s → y ∈ Contents s → h x = h y → x = y
def HypOrig (h : ℕ → ℕ) (s : St) : Prop :=
  Set.InjOn h {c | (∃ e ∈ s.deployed, e.content = c) ∨ ∃ rv ∈ s.reviews, rv.content = c}'''
INJ_PROOF = '''theorem hypotheses_iff (h : ℕ → ℕ) (s : St) : HypBack h s ↔ HypOrig h s := by
  have members (c : ℕ) : c ∈ Contents s ↔
      (∃ e ∈ s.deployed, e.content = c) ∨ ∃ rv ∈ s.reviews, rv.content = c := by
    simp [Contents, List.mem_map]
  unfold HypBack HypOrig Set.InjOn
  constructor
  · intro hb x hx y hy hxy
    exact hb x y ((members x).mpr hx) ((members y).mpr hy) hxy
  · intro ho x y hx hy hxy
    exact ho ((members x).mp hx) ((members y).mp hy) hxy'''

save(6, 'open ControlStack.SC16', INJ_DEFS + '''
def BackAt (R : Roles) (s : St) : Prop :=
  ∀ e ∈ s.deployed, ∃ rv ∈ s.reviews,
    rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager
def OrigAt (R : Roles) (s : St) : Prop :=
  ∀ e ∈ s.deployed, ∃ rv ∈ s.reviews,
    rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager
def OrigClosed : Prop := ∀ (R : Roles) (h : ℕ → ℕ) (ops : List Op),
  HypOrig h (run R h full init ops) → OrigAt R (run R h full init ops)''',
'''  (BackClosed ↔ ∀ R h ops, HypBack h (run R h full init ops) → BackAt R (run R h full init ops)) ∧
  (∀ h s, HypBack h s ↔ HypOrig h s) ∧
  (∀ R s, BackAt R s ↔ OrigAt R s)''',
f'''  let s := run R0 id full init {SC16_TRACE}
  HypBack id s ∧ s.deployed = [⟨0, 5, 7⟩] ∧ s.reviews ≠ []''',
INJ_PROOF + '''
theorem claim : Claim := ⟨Iff.rfl, hypotheses_iff, fun _ _ => Iff.rfl⟩
theorem witness : Witness := by
  refine ⟨fun _ _ _ _ h => h, ?_⟩
  decide''', 'ControlStack.SC16.sc16_reviewed_content')

save(7, 'open ControlStack.SC16', '''def BackAt (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op) : Prop := run R h full s ops = s
def OrigAt (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op) : Prop := run R h full s ops = s
def OrigClosed : Prop := ∀ (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op),
  s.halted = true → run R h full s ops = s''',
'''  (BackClosed ↔ ∀ R h s ops, s.halted = true → BackAt R h s ops) ∧
  (OrigClosed ↔ ∀ R h s ops, s.halted = true → OrigAt R h s ops) ∧
  (∀ R h s ops, s.halted = true → (BackAt R h s ops ↔ OrigAt R h s ops))''',
'''  let s : St := { init with halted := true, deployed := [⟨0, 5, 7⟩] }
  let ops : List Op := [.stage 1 8, .writeSlot 1 0 8, .review 2 7, .approve 3 1 7 5 0, .deploy 1 1 5 7, .halt 4]
  s.halted = true ∧ s.deployed ≠ [] ∧ run R0 id full s ops = s''',
'''theorem claim : Claim := ⟨Iff.rfl, Iff.rfl, fun _ _ _ _ _ => Iff.rfl⟩
theorem witness : Witness := by decide''', 'ControlStack.SC16.halt_freezes')

save(8, 'open ControlStack.SC16 ControlStack.SC16Disjoint', INJ_DEFS + '''
def HRev (R : Roles) : Prop := ∀ c ∈ R.reviewers, c ∉ R.agents
def HApp (R : Roles) : Prop := ∀ c ∈ R.approvers, c ∉ R.agents
def BackAt (R : Roles) (s : St) : Prop :=
  ∀ e ∈ s.deployed,
    (∃ rv ∈ s.reviews, rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧
      rv.reviewer ∉ R.agents ∧ rv.reviewer ≠ rv.stager) ∧
    (∃ ap ∈ s.approvals, ap.n = e.n ∧ ap.target = e.target ∧
      ap.approver ∈ R.approvers ∧ ap.approver ∉ R.agents)
def OrigAt (R : Roles) (s : St) : Prop :=
  ∀ e ∈ s.deployed,
    (∃ rv ∈ s.reviews, rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧
      rv.reviewer ∉ R.agents ∧ rv.reviewer ≠ rv.stager) ∧
    (∃ ap ∈ s.approvals, ap.n = e.n ∧ ap.target = e.target ∧
      ap.approver ∈ R.approvers ∧ ap.approver ∉ R.agents)
def OrigClosed : Prop := ∀ (R : Roles) (h : ℕ → ℕ) (ops : List Op),
  HRev R → HApp R → HypOrig h (run R h full init ops) → OrigAt R (run R h full init ops)''',
'''  (BackClosed ↔ ∀ R h ops, HRev R → HApp R → HypBack h (run R h full init ops) → BackAt R (run R h full init ops)) ∧
  (∀ h s, HypBack h s ↔ HypOrig h s) ∧
  (∀ R s, BackAt R s ↔ OrigAt R s)''',
f'''  HRev R0 ∧ HApp R0 ∧
  let s := run R0 id full init {SC16_TRACE}
  HypBack id s ∧ s.deployed = [⟨0, 5, 7⟩] ∧ s.reviews ≠ [] ∧ s.approvals ≠ []''',
INJ_PROOF + '''
theorem claim : Claim := ⟨Iff.rfl, hypotheses_iff, fun _ _ => Iff.rfl⟩
theorem witness : Witness := by
  refine ⟨?_, ?_, (fun _ _ _ _ h => h), ?_⟩
  · simp [HRev, R0]
  · simp [HApp, R0]
  · decide''', 'ControlStack.SC16Disjoint.sc16_safe_disjoint')

save(9, 'open ControlStack.SC16 ControlStack.SC16Disjoint', f'''def BackAt (s : St) : Prop :=
  (∃ e ∈ s.deployed, e.content = 7 ∧ e.target = 5) ∧
  s.reviews ≠ [] ∧ (∀ rv ∈ s.reviews, rv.reviewer ∈ Rov.agents)
def OrigAt (s : St) : Prop :=
  s.deployed = [⟨0, 5, 7⟩] ∧ s.reviews ≠ [] ∧ ∀ rv ∈ s.reviews, rv.reviewer ∈ Rov.agents
def observed : St := run Rov id full init {SC16_TRACE}
def OrigClosed : Prop := OrigAt observed''',
'''  (BackClosed ↔ BackAt observed) ∧
  (∀ s, OrigAt s → BackAt s) ∧
  (∃ s, BackAt s ∧ ¬ OrigAt s)''',
'''  observed.deployed = [⟨0, 5, 7⟩] ∧ observed.reviews = [⟨7, 2, 7, 1⟩] ∧
  (∀ s, OrigAt s → BackAt s)''',
'''theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_, ?_⟩
  · intro s h
    obtain ⟨hd, hr⟩ := h
    refine ⟨?_, hr⟩
    exact ⟨⟨0, 5, 7⟩, by simp [hd], rfl, rfl⟩
  · refine ⟨{ init with deployed := [⟨99, 5, 7⟩], reviews := [⟨7, 2, 7, 1⟩] }, ?_⟩
    constructor
    · refine ⟨⟨⟨99, 5, 7⟩, by simp, rfl, rfl⟩, by decide, ?_⟩
      intro rv h
      simp only [List.mem_singleton] at h
      subst rv
      decide
    · unfold OrigAt
      decide
theorem witness : Witness := by
  refine ⟨by decide, by decide, ?_⟩
  intro s h
  obtain ⟨hd, hr⟩ := h
  exact ⟨⟨⟨0, 5, 7⟩, by simp [hd], rfl, rfl⟩, hr⟩''', 'ControlStack.SC16Disjoint.overlap_reviewer_is_agent')

save(10, 'open ControlStack.SC16 ControlStack.AuthInstances ControlStack.AuthenticatedLog', '''def HypBack (R : Roles) (U : List ℕ) : Prop := ∀ c ∈ U, c ∉ R.reviewers ∧ c ∉ R.approvers
def HRev (R : Roles) (U : List ℕ) : Prop := ∀ c ∈ U, c ∉ R.reviewers
def HApp (R : Roles) (U : List ℕ) : Prop := ∀ c ∈ U, c ∉ R.approvers
def BackAt (R : Roles) (h : ℕ → ℕ) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good R h s ∧
  (∀ rv ∈ s.reviews, (rv.reviewer, Op.review rv.reviewer rv.d) ∈ ops ∧
    rv.reviewer ∉ U ∧ rv.reviewer ∈ R.reviewers) ∧
  (∀ ap ∈ s.approvals, (ap.approver, Op.approve ap.approver ap.n ap.d ap.target ap.slot) ∈ ops ∧
    ap.approver ∉ U ∧ ap.approver ∈ R.approvers)
def OrigAt (R : Roles) (h : ℕ → ℕ) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good R h s ∧
  (∀ rv ∈ s.reviews, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
    (o = .review c rv.d ∧ c = rv.reviewer ∧ c ∈ R.reviewers)) ∧
  (∀ ap ∈ s.approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
    (o = .approve c ap.n ap.d ap.target ap.slot ∧ c = ap.approver ∧ c ∈ R.approvers))
def OrigClosed : Prop := ∀ (R : Roles) (h : ℕ → ℕ) (U : List ℕ) (ops : List (ℕ × Op)),
  HRev R U → HApp R U → OrigAt R h U ops (authRun (step R h full) claim16 init ops)''',
'''  (BackClosed ↔ ∀ R h U ops, HypBack R U → BackAt R h U ops (authRun (step R h full) claim16 init ops)) ∧
  (∀ R U, HypBack R U ↔ (HRev R U ∧ HApp R U)) ∧
  (∀ R h U ops s, BackAt R h U ops s ↔ OrigAt R h U ops s)''',
f'''  HypBack R0 [1] ∧
  let s := authRun (step R0 id full) claim16 init {AUTH16_TRACE}
  s.deployed = [⟨0, 5, 7⟩] ∧ s.reviews ≠ [] ∧ s.approvals ≠ []''',
'''theorem hypotheses_iff (R : Roles) (U : List ℕ) : HypBack R U ↔ (HRev R U ∧ HApp R U) := by
  constructor
  · intro hb
    exact ⟨fun c hc => (hb c hc).1, fun c hc => (hb c hc).2⟩
  · rintro ⟨hr, ha⟩ c hc
    exact ⟨hr c hc, ha c hc⟩
theorem claim : Claim := by
  refine ⟨Iff.rfl, hypotheses_iff, ?_⟩
  intro R h U ops s
  unfold BackAt OrigAt
  constructor
  · rintro ⟨hg, hr, ha⟩
    refine ⟨hg, ?_, ?_⟩
    · intro rv hm
      obtain ⟨ho, hu, hp⟩ := hr rv hm
      exact ⟨rv.reviewer, .review rv.reviewer rv.d, ho, hu, rfl, rfl, hp⟩
    · intro ap hm
      obtain ⟨ho, hu, hp⟩ := ha ap hm
      exact ⟨ap.approver, .approve ap.approver ap.n ap.d ap.target ap.slot, ho, hu, rfl, rfl, hp⟩
  · rintro ⟨hg, hr, ha⟩
    refine ⟨hg, ?_, ?_⟩
    · intro rv hm
      obtain ⟨c, o, ho, hu, rfl, rfl, hp⟩ := hr rv hm
      exact ⟨ho, hu, hp⟩
    · intro ap hm
      obtain ⟨c, o, ho, hu, rfl, rfl, hp⟩ := ha ap hm
      exact ⟨ho, hu, hp⟩
theorem witness : Witness := by
  constructor
  · simp [HypBack, R0]
  · decide''', 'ControlStack.AuthInstances.sc16_safe_authenticated')
