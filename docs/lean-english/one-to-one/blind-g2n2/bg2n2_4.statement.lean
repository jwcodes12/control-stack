namespace PL_bg2n2_4

open ControlStack ControlStack.AuthInstances

def FrozenBack : Prop :=
let unguarded := ControlStack.AuthenticatedLog.authRun
    (SC12.step [9] SC12.full) (fun _ => (none : Option ℕ)) SC12.init forged12;
  let guarded := ControlStack.AuthenticatedLog.authRun
    (SC12.step [9] SC12.full) claim12 SC12.init forged12;
  unguarded.live.length = 2 ∧ guarded = SC12.init

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

end PL_bg2n2_4
