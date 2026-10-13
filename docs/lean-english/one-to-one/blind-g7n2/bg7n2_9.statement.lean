namespace PL_bg7n2_9
open ControlStack
open ControlStack.SC28Liveness
open ControlStack ControlStack.SC28

def BackFull : Prop :=
  let s := run [9] 10 full init
    [Op.issue 9 0 10, Op.issue 9 1 10,
     Op.assignTo 9 1 0, Op.assignTo 9 2 1, Op.work 2 10 10]
  spentL s 0 = 0 ∧
    (step [9] 10 full s (.work 1 1 1)).usage = s.usage ∧
    (step [9] 10 full s (.work 1 1 1)).usage = [(2, 1, 10)]


def BackResult (s t : St) : Prop :=
  spentL s 0 = 0 ∧ t.usage = s.usage ∧ t.usage = [(2, 1, 10)]
def OrigResult (s t : St) : Prop :=
  t.usage = s.usage ∧ spentL s 0 = 0 ∧ s.usage = [(2, 1, 10)]

def OrigFull : Prop :=
  let s := run [9] 10 full init [.issue 9 0 10, .issue 9 1 10, .assignTo 9 1 0, .assignTo 9 2 1, .work 2 10 10]
  (step [9] 10 full s (.work 1 1 1)).usage = s.usage ∧ spentL s 0 = 0 ∧ s.usage = [(2, 1, 10)]

def BackSchema : Prop :=
    let s := run [9] 10 full init [.issue 9 0 10, .issue 9 1 10, .assignTo 9 1 0, .assignTo 9 2 1, .work 2 10 10]
    BackResult s (step [9] 10 full s (.work 1 1 1))

def OrigSchema : Prop :=
  let s := run [9] 10 full init [.issue 9 0 10, .issue 9 1 10, .assignTo 9 1 0, .assignTo 9 2 1, .work 2 10 10]
  OrigResult s (step [9] 10 full s (.work 1 1 1))


def Claim : Prop :=
  (BackFull ↔ BackSchema) ∧ (OrigFull ↔ OrigSchema) ∧
  ∀ (s t : St), BackResult s t ↔ OrigResult s t

def Witness : Prop :=
  let s := run [9] 10 full init [.issue 9 0 10, .issue 9 1 10, .assignTo 9 1 0, .assignTo 9 2 1, .work 2 10 10]
  s.usage = [(2, 1, 10)] ∧ spentL s 0 = 0 ∧ spentT s = 10 ∧
    (step [9] 10 full s (.work 1 1 1)).usage = s.usage
end PL_bg7n2_9
