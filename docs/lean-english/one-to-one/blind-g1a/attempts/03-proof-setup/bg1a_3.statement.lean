namespace PL_bg1a_3
open ControlStack.Covert ControlStack.CovertNoGo Finset

-- Bool represents the secret bit; Fin 65536 represents the output alphabet.
-- The two functions induce point-mass encoder and decoder rows.
def Back_cap_does_not_prevent : Prop :=
  ∃ (send : Bool → Fin 65536) (decode : Fin 65536 → Bool),
    ControlStack.CovertNoGo.successView
      (fun t : Fin 65536 => t)
      (fun m t => if t = send m then (1 : ℝ) else 0)
      (fun t m => if decode t = m then (1 : ℝ) else 0) = 1

def pointEnc (send : Bool → Fin 65536) : Bool → Fin 65536 → ℝ :=
  fun m t => if t = send m then 1 else 0
def pointDec (decode : Fin 65536 → Bool) : Fin 65536 → Bool → ℝ :=
  fun t m => if decode t = m then 1 else 0

def BackAt (send : Bool → Fin 65536) (decode : Fin 65536 → Bool) : Prop :=
  successView id (pointEnc send) (pointDec decode) = 1

def OrigAt (enc : Bool → Fin 65536 → ℝ) (dec : Fin 65536 → Bool → ℝ) : Prop :=
  (∀ m, IsDist (enc m)) ∧ (∀ t, IsDist (dec t)) ∧ successView id enc dec = 1

def Original : Prop :=
  ∃ (enc : Bool → Fin 65536 → ℝ) (dec : Fin 65536 → Bool → ℝ), OrigAt enc dec

def Claim : Prop :=
  (Back_cap_does_not_prevent = (∃ send decode, BackAt send decode)) ∧
  (∀ send decode, BackAt send decode ↔ OrigAt (pointEnc send) (pointDec decode)) ∧
  (∀ enc dec, OrigAt enc dec → ∃ send decode,
    (∀ m, 0 < enc m (send m) ∧ dec (send m) m = 1) ∧
    (∀ m, decode (send m) = m) ∧ BackAt send decode) ∧
  (Back_cap_does_not_prevent ↔ Original)

def send01 : Bool → Fin 65536 := fun m => if m then 1 else 0
def decode01 : Fin 65536 → Bool := fun t => decide (t = 1)
def Witness : Prop :=
  send01 false ≠ send01 true ∧
  (∀ m, decode01 (send01 m) = m) ∧ BackAt send01 decode01
end PL_bg1a_3
