namespace PL_bg7n2_10
open ControlStack
open ControlStack.AntiRollback

def BackFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ)
    (ops : List (ROp {o : SC28.Op // SC28.legal o})),
    let system := SC28.sys admins G
    let s := runR system true (rinit system SC28.init) ops
    let plain := system.run SC28.init s.committed
    s.released = plain.usage ∧ SC28.Good G plain


def BackResult (admins : List ℕ) (G : ℕ)
    (t : RSt SC28.St {o : SC28.Op // SC28.legal o} (ℕ × ℕ × ℕ)) : Prop :=
  t.released = ((SC28.sys admins G).run SC28.init t.committed).usage ∧
    SC28.Good G ((SC28.sys admins G).run SC28.init t.committed)
def OrigResult (admins : List ℕ) (G : ℕ)
    (t : RSt SC28.St {o : SC28.Op // SC28.legal o} (ℕ × ℕ × ℕ)) : Prop :=
  t.released = (SC28.run admins G SC28.full SC28.init (t.committed.map Subtype.val)).usage ∧
    SC28.Good G (SC28.run admins G SC28.full SC28.init (t.committed.map Subtype.val))

def OrigFull : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (ops : List (ROp {o : SC28.Op // SC28.legal o})),
    let t := runR (SC28.sys admins G) true (rinit (SC28.sys admins G) SC28.init) ops
    t.released = (SC28.run admins G SC28.full SC28.init (t.committed.map Subtype.val)).usage ∧
      SC28.Good G (SC28.run admins G SC28.full SC28.init (t.committed.map Subtype.val))

def BackSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ)
    (ops : List (ROp {o : SC28.Op // SC28.legal o})),
    BackResult admins G (runR (SC28.sys admins G) true (rinit (SC28.sys admins G) SC28.init) ops)

def OrigSchema : Prop :=
  ∀ (admins : List ℕ) (G : ℕ) (ops : List (ROp {o : SC28.Op // SC28.legal o})),
    OrigResult admins G (runR (SC28.sys admins G) true (rinit (SC28.sys admins G) SC28.init) ops)


def Claim : Prop :=
  (BackFull ↔ BackSchema) ∧ (OrigFull ↔ OrigSchema) ∧
  ∀ (admins : List ℕ) (G : ℕ)
    (t : RSt SC28.St {o : SC28.Op // SC28.legal o} (ℕ × ℕ × ℕ)),
    BackResult admins G t ↔ OrigResult admins G t

def Witness : Prop :=
  (runR G28 true (rinit G28 SC28.init) spendTrace).released = [(1, 0, 10)] ∧
    (runR G28 true (rinit G28 SC28.init) spendTrace).halted = true ∧
    (runR G28 true (rinit G28 SC28.init) spendTrace).committed.length = 3
end PL_bg7n2_10
