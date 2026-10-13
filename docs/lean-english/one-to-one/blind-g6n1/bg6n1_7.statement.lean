namespace PL_bg6n1_7

open ControlStack.AuthInstances ControlStack.SC25 ControlStack.AuthenticatedLog

def FrozenBack : Prop :=
  let plain := run R0 (fun x => x) cls0 full init (forged25.map Prod.snd)
  let guarded := authRun (step R0 (fun x => x) cls0 full) claim25 init forged25
  0 ∈ plain.executed.map Exec.id ∧ guarded.executed = []

def Back (ids : List ℕ) (guarded : List Exec) : Prop := 0 ∈ ids ∧ guarded = []
def Orig (ids : List ℕ) (guarded : List Exec) : Prop := ids = [0] ∧ guarded = []

def Claim : Prop :=
  (FrozenBack = (Back ((run R0 (fun x => x) cls0 full init (forged25.map Prod.snd)).executed.map Exec.id) (authRun (step R0 (fun x => x) cls0 full) claim25 init forged25).executed)) ∧
  (∀ (ids : List ℕ) (guarded : List Exec), ids.length = 1 → (Back ids guarded ↔ Orig ids guarded)) ∧
  (((run R0 (fun x => x) cls0 full init (forged25.map Prod.snd)).executed.map Exec.id).length = 1) ∧
  (Back ((run R0 (fun x => x) cls0 full init (forged25.map Prod.snd)).executed.map Exec.id) (authRun (step R0 (fun x => x) cls0 full) claim25 init forged25).executed ↔ Orig ((authRun (step R0 id cls0 full) (fun _ => none) init forged25).executed.map Exec.id) (authRun (step R0 (fun x => x) cls0 full) claim25 init forged25).executed)

def Witness : Prop :=
  ((run R0 (fun x => x) cls0 full init (forged25.map Prod.snd)).executed.map Exec.id) = [0] ∧ (authRun (step R0 (fun x => x) cls0 full) claim25 init forged25).executed = [] ∧
    (∀ io ∈ forged25, io.1 = 1) ∧ (1, Op.audit 2 0 true) ∈ forged25

end PL_bg6n1_7
