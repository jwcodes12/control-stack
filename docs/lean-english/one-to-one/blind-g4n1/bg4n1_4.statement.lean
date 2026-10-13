namespace PL_bg4n1_4
open ControlStack.AuthInstances

def Back_sc18_safe_authenticated : Prop :=
  ∀ (admins : List ℕ) (trusted T : ℕ) (U : ℕ → Prop)
    (ops : List (ℕ × ControlStack.SC18.Op)),
    (∀ a : ℕ, U a → a ∉ admins) →
    (∀ io ∈ ops, ¬ U io.1 → ControlStack.SC18.legal admins trusted io.2) →
    ControlStack.SC18.Good T
      (ControlStack.AuthenticatedLog.authRun
        (ControlStack.SC18.step admins trusted T ControlStack.SC18.full)
        claim18 (ControlStack.SC18.init trusted) ops)

def BackAt (admins : List ℕ) (trusted T : ℕ) (_U : ℕ → Prop)
    (ops : List (ℕ × ControlStack.SC18.Op)) : Prop :=
  ControlStack.SC18.Good T (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC18.step admins trusted T ControlStack.SC18.full)
    claim18 (ControlStack.SC18.init trusted) ops)

def OrigAt (admins : List ℕ) (trusted T : ℕ) (_U : List ℕ)
    (ops : List (ℕ × ControlStack.SC18.Op)) : Prop :=
  ControlStack.SC18.Good T (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC18.step admins trusted T ControlStack.SC18.full)
    claim18 (ControlStack.SC18.init trusted) ops)

def Claim : Prop :=
  (Back_sc18_safe_authenticated ↔ ∀ (admins : List ℕ) (trusted T : ℕ) (U : ℕ → Prop)
    (ops : List (ℕ × ControlStack.SC18.Op)),
    (∀ a : ℕ, U a → a ∉ admins) →
    (∀ io ∈ ops, ¬ U io.1 → ControlStack.SC18.legal admins trusted io.2) →
    BackAt admins trusted T U ops) ∧
  (∀ (admins : List ℕ) (trusted T : ℕ) (U : List ℕ)
    (ops : List (ℕ × ControlStack.SC18.Op)),
    (∀ a ∈ U, a ∉ admins) →
    (∀ io ∈ ops, io.1 ∉ U → ControlStack.SC18.legal admins trusted io.2) →
    (BackAt admins trusted T (fun a => a ∈ U) ops ↔ OrigAt admins trusted T U ops)) ∧
  (∀ (admins : List ℕ) (trusted T : ℕ) (U : ℕ → Prop)
    (ops : List (ℕ × ControlStack.SC18.Op)), ∃ V : List ℕ,
    ((∀ a, U a → a ∉ admins) ↔ (∀ a ∈ V, a ∉ admins)) ∧
    ((∀ io ∈ ops, ¬ U io.1 → ControlStack.SC18.legal admins trusted io.2) ↔
      (∀ io ∈ ops, io.1 ∉ V → ControlStack.SC18.legal admins trusted io.2)) ∧
    (BackAt admins trusted T U ops ↔ OrigAt admins trusted T V ops))

def Witness : Prop :=
  let ops : List (ℕ × ControlStack.SC18.Op) :=
    [(1, .setSink 9 66), (9, .setSink 9 0), (1, .request 0), (1, .logWrite 0), (1, .release 0)]
  (∀ a : ℕ, a = 1 → a ∉ [9]) ∧
  (∀ io ∈ ops, ¬ (io.1 = 1) → ControlStack.SC18.legal [9] 0 io.2) ∧
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC18.step [9] 0 2 ControlStack.SC18.full) claim18 (ControlStack.SC18.init 0) ops).cfg = 0 ∧
  (ControlStack.AuthenticatedLog.authRun
    (ControlStack.SC18.step [9] 0 2 ControlStack.SC18.full) claim18 (ControlStack.SC18.init 0) ops).released.map ControlStack.SC18.Rel.id = [0]

end PL_bg4n1_4
