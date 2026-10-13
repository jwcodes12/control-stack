from pathlib import Path
out=Path(__file__).resolve().parent

def write(n, ns, at, params, hypotheses, signature, witness, wproof, extra=''):
 p=next((out/'typed').glob(f'{n}-*.lean'))
 body=p.read_text().split('namespace '+ns+'\n',1)[1].rsplit('end '+ns,1)[0].strip()
 backname=body.split('def ',1)[1].split(' :',1)[0]
 hyp=(' '+hypotheses) if hypotheses else ''
 stmt=f'namespace PL_bg1a_{n}\nopen {ns}\n\n{body}\n\n{extra}\ndef BackAt {params} : Prop :=\n  {at}\ndef OrigAt {params} : Prop :=\n  {at}\n\ndef Claim : Prop :=\n  ({backname} = (∀ {params}{hyp}, BackAt '+arguments[n]+')) ∧\n  (∀ '+params+hyp+', BackAt '+arguments[n]+' ↔ OrigAt '+arguments[n]+')\n\n'+witness+f'\nend PL_bg1a_{n}\n'
 proof=f'open {ns}\n\ntheorem claim : Claim := by\n  have originalSignature : ∀ {params}{hyp}, OrigAt {arguments[n]} := {signature}\n  exact ⟨rfl, by intros; exact Iff.rfl⟩\n\ntheorem witness : Witness := by\n  {wproof}\n'
 (out/f'bg1a_{n}.statement.lean').write_text(stmt)
 (out/f'bg1a_{n}.proof.lean').write_text(proof)
arguments={1:'p s a',2:'p s actions',4:'Ω M V ρ out dec',5:'forbidden ops',6:'P ops',7:'P s ops',8:'E ops',9:'K ops'}
egress_extra='''def peer : Peer := ⟨"peer", 443, "tcp"⟩
def policy : Policy := [⟨"authority", peer⟩]
def topology : Topology := ⟨true, true, true, true, true⟩
def start : State := ⟨true, topology, true, []⟩'''
ew='''def Witness : Prop :=
  Invariant policy start ∧
  (step policy start (.request "authority")).attempts = [⟨.gateway, peer⟩]'''
wp='constructor\n  · simp [Witness, Invariant, start, topology, safe]\n  · rfl'
for n, par, h, at, sig in [
 (1,'(p : Policy) (s : State) (a : Action)','(_h : Invariant p s)','Invariant p (step p s a)','@ControlStack.EgressGate.step_safe'),
 (2,'(p : Policy) (s : State) (actions : List Action)','(_h : Invariant p s)','Invariant p (run p s actions)','@ControlStack.EgressGate.trace_safe')]:
 write(n,'ControlStack.EgressGate',at,par,h,sig,ew,wp,egress_extra)
write(4,'ControlStack.SC05',
 'ControlStack.Covert.successProb ρ (fun ω _m v => out ω v) dec = (Fintype.card M : ℝ)⁻¹',
 '(Ω M V : Type) [Fintype Ω] [Fintype M] [Fintype V] (ρ : Ω → ℝ) (out : Ω → V → ℝ) (dec : Ω → V → M → ℝ)',
 '(_hρ : ControlStack.Covert.IsDist ρ) (_ho : ∀ ω, ControlStack.Covert.IsDist (out ω)) (_hd : ∀ ω v, ControlStack.Covert.IsDist (dec ω v))',
 '@ControlStack.SC05.zero_dependence_is_blind',
 '''def Witness : Prop :=
  ControlStack.Covert.IsDist (fun _ : Unit => (1 : ℝ)) ∧
  (∀ _ω : Unit, ControlStack.Covert.IsDist (fun _ : Bool => (1 : ℝ) / 2)) ∧
  (∀ (_ω : Unit) (_v : Bool), ControlStack.Covert.IsDist (fun _ : Bool => (1 : ℝ) / 2)) ∧
  ControlStack.Covert.successProb (fun _ : Unit => (1 : ℝ))
    (fun (_ : Unit) (_ : Bool) (_ : Bool) => (1 : ℝ) / 2)
    (fun (_ : Unit) (_ : Bool) (_ : Bool) => (1 : ℝ) / 2) = (1 : ℝ) / 2''',
 'norm_num [Witness, ControlStack.Covert.IsDist, ControlStack.Covert.successProb, Fintype.sum_bool]')
write(5,'ControlStack.SC05',
 '∀ a ∈ ControlStack.Gate.System.run (sys forbidden) [] ops, a ∉ forbidden',
 '(forbidden : List ℕ) (ops : List Op)','', '@ControlStack.SC05.forbidden_never_executes',
 '''def Witness : Prop :=
  ControlStack.Gate.System.run (sys [7]) [] [.act 3, .act 7] = [3] ∧
  ([Op.act 7].foldl (step [7] false) []) = [7]''', 'unfold Witness\n  decide')
write(6,'ControlStack.SC06','Good P (run P full init ops)', '(P : Policy) (ops : List Op)','', '@ControlStack.SC06.sc06_safe',
 '''def Witness : Prop :=
  (run P0 full init [.writeTyped 1 0 42 99, .read 2 0, .confirm 5 3 2 7 42, .act 2 7 42 3]).executed =
    [⟨2, 7, 42, true, some 3⟩]''','unfold Witness\n  decide')
write(7,'ControlStack.SC06','run P full s ops = s', '(P : Policy) (s : St) (ops : List Op)', '(_hh : s.halted = true)', '@ControlStack.SC06.halt_freezes',
 '''def Witness : Prop :=
  let s := run P0 full init [.writeTyped 2 0 42 99, .read 2 0, .halt 9]
  s.halted = true ∧ s.ctx ≠ [] ∧
    run P0 full s [.writeTyped 1 1 9 9, .read 2 1, .confirm 5 3 2 7 42, .act 2 7 42 3, .halt 9] = s''', 'unfold Witness\n  decide')
write(8,'ControlStack.SC07Liveness',
 '(∀ e ∈ (run E full init ops).log, e.dest ∈ E.allow) ∧ (∀ w : ℕ, wsum (run E full init ops) w ≤ E.q)',
 '(E : Env) (ops : List Op)','', '@ControlStack.SC07Liveness.sc07_safe',
 '''def Witness : Prop :=
  let s := run (⟨[1], 5, [0]⟩ : Env) full init [.send 1 5, .send 1 1, .send 2 0, .tick, .send 1 5]
  s.log = [⟨1, 5, 0⟩, ⟨1, 5, 1⟩] ∧ wsum s 0 = 5 ∧ wsum s 1 = 5 ∧ total s = 10''', 'unfold Witness\n  decide')
write(9,'ControlStack.SC07Refinement',
 '(∀ r ∈ (runC K cinit ops).fwd, (r.ip, r.port) ∈ K.allow) ∧ (∀ w : ℕ, payloadIn (runC K cinit ops).fwd w ≤ K.Q - 1)',
 '(K : CCfg) (ops : List COp)', '(_hK : K.quotaRule = true)',
 'fun K ops hK => ControlStack.SC07Refinement.concrete_safe K hK ops',
 '''def Witness : Prop :=
  (K0 true).quotaRule = true ∧
  let s := runC (K0 true) cinit [.pkt 1 8080 4 1, .pkt 1 8080 4 1, .pkt 1 8080 1 0, .pkt 2 8080 1 0]
  payloadIn s.fwd 0 = 4 ∧ wireIn s.fwd 0 = 5 ∧ s.quotaDrop = 2 ∧ s.denyDrop = 1''', 'unfold Witness\n  decide')
