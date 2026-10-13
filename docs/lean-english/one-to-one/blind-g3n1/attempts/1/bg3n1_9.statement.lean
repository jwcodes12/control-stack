namespace PL_bg3n1_9

open ControlStack.SC16 ControlStack.SC16Disjoint

def BackClosed : Prop :=
  let ops : List Op :=
    [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]
  let s := run Rov (fun x => x) full init ops
  (∃ e ∈ s.deployed, e.content = 7 ∧ e.target = 5) ∧
  s.reviews ≠ [] ∧ (∀ rv ∈ s.reviews, rv.reviewer ∈ Rov.agents)

def BackAt (s : St) : Prop :=
  (∃ e ∈ s.deployed, e.content = 7 ∧ e.target = 5) ∧
  s.reviews ≠ [] ∧ (∀ rv ∈ s.reviews, rv.reviewer ∈ Rov.agents)
def OrigAt (s : St) : Prop :=
  s.deployed = [⟨0, 5, 7⟩] ∧ s.reviews ≠ [] ∧ ∀ rv ∈ s.reviews, rv.reviewer ∈ Rov.agents
def observed : St := run Rov id full init [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]
def OrigClosed : Prop := OrigAt observed

def Claim : Prop :=
  (BackClosed ↔ BackAt observed) ∧
  (∀ s, OrigAt s → BackAt s) ∧
  (∃ s, BackAt s ∧ ¬ OrigAt s)

def Witness : Prop :=
  observed.deployed = [⟨0, 5, 7⟩] ∧ observed.reviews = [⟨7, 2, 7, 1⟩] ∧
  (∀ s, OrigAt s → BackAt s)

end PL_bg3n1_9
