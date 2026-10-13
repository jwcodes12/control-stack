from pathlib import Path
import json,hashlib
OUT=Path(__file__).resolve().parent
for f,h in json.loads((OUT/'typed/HASHES.json').read_text())['files'].items():
 assert hashlib.sha256((OUT/f).read_bytes()).hexdigest()==h
specs={
1:dict(module='SC07Exfil',params='(q : ℕ) (pr : ℝ) (c : ℕ → ℝ) (b : List ℕ)',quant='∀ (q : ℕ) (pr : ℝ) (c : ℕ → ℝ) (b : List ℕ), 0 < pr → (∀ i, pr ≤ c i ∧ c i ≤ 1) →',args='q pr c b',back='expLeak c (capped q b) 0 ≤ (q : ℝ) / pr',orig='expLeak c (capped q b) 0 ≤ q / pr',intro='q pr c b hpr hc',original='expected_leak_le q c pr hc hpr b',witness='(0 < (1 / 2 : ℝ)) ∧ (∀ i : ℕ, (1 / 2 : ℝ) ≤ (fun _ : ℕ => (1 / 2 : ℝ)) i ∧ (fun _ : ℕ => (1 / 2 : ℝ)) i ≤ 1) ∧ (capped 8 [8, 8]).sum = 16 ∧ expLeak (fun _ => (1 / 2 : ℝ)) (capped 8 [8, 8]) 0 = 12',wp='by norm_num [Witness, capped, expLeak]'),
2:dict(module='SC07Exfil',params='(q : ℕ)',quant='∀ q : ℕ, 0 < q →',args='q',back='let b : List ℕ := [0, q, 0, q]\n  let c : ℕ → ℝ := fun i => if i = 0 ∨ i = 2 then 1 else 0\n  b.sum = 2 * q ∧ survive c b 0 = 1',orig='let c : ℕ → ℝ := fun i => if i = 0 ∨ i = 2 then 1 else 0\n  (capped q [0, q, 0, q]).sum = 2 * q ∧ survive c (capped q [0, q, 0, q]) 0 = 1',intro='q hq',original='observable_schedule_exfil q hq',point='simp [BackAt, OriginalAt, capped]',witness='0 < (1 : ℕ) ∧ ([0, 1, 0, 1] : List ℕ).sum = 2 ∧ survive (fun i => if i = 0 ∨ i = 2 then 1 else 0) [0, 1, 0, 1] 0 = 1',wp='by norm_num [Witness, survive]'),
3:dict(module='SC07Exfil',params='(b : List ℕ) (c : ℕ → ℝ)',quant='∀ (b : List ℕ) (c : ℕ → ℝ), 800000000000 ≤ (capped 8000000000 b).sum → (∀ i, (5 / 100 : ℝ) ≤ c i ∧ c i ≤ 1) →',args='b c',back='ceilDiv 800000000000 8000000000 = 100 ∧ survive c (capped 8000000000 b) 0 ≤ (6 / 1000 : ℝ)',orig='ceilDiv 800000000000 8000000000 = 100 ∧ survive c (capped 8000000000 b) 0 ≤ (0.006 : ℝ)',intro='b c hS hc',original='datacenter_example c (by norm_num at hc ⊢; exact hc) b hS',point='norm_num [BackAt, OriginalAt]',witness='0 < (8000000000 : ℕ) ∧ (∀ i : ℕ, (5 / 100 : ℝ) ≤ (fun _ : ℕ => (1 : ℝ)) i ∧ (fun _ : ℕ => (1 : ℝ)) i ≤ 1) ∧ (capped 8000000000 (List.replicate 100 8000000000)).sum = 800000000000',wp='by norm_num [Witness, capped, List.sum_replicate]'),
4:dict(module='SC07Liveness',params='(E : Env) (s : St) (d : ℕ) (chunks : List ℕ)',quant='∀ (E : Env) (s : St) (d : ℕ) (chunks : List ℕ), s.halted = false → d ∈ E.allow → s.used + chunks.sum ≤ E.q →',args='E s d chunks',back='(run E full s (chunks.map (fun n => Op.send d n))).log = s.log ++ chunks.map (fun n => (⟨d, n, s.window⟩ : Fwd))',orig='(run E full s (chunks.map (fun n => .send d n))).log = s.log ++ chunks.map (fun n => ⟨d, n, s.window⟩)',intro='E s d chunks hh hd hq',original='upload_completes E s d chunks hh hd hq',witness='init.halted = false ∧ 10 ∈ E0.allow ∧ init.used + ([5, 3] : List ℕ).sum ≤ E0.q ∧ (run E0 full init [.send 10 5, .send 10 3]).log = [⟨10, 5, 0⟩, ⟨10, 3, 0⟩]',wp='by unfold Witness; decide'),
5:dict(module='SC07Liveness',params='(E : Env) (ops : List Op) (S : ℕ)',quant='∀ (E : Env) (ops : List Op) (S : ℕ), 0 < E.q → S ≤ total (run E full init ops) →',args='E ops S',back='ControlStack.SC07Exfil.ceilDiv S E.q ≤ (run E full init ops).window + 1',orig='ControlStack.SC07Exfil.ceilDiv S E.q ≤ (run E full init ops).window + 1',intro='E ops S hq hS',original='exfil_needs_windows E hq S ops hS',witness='0 < E0.q ∧ total (run E0 full init [.send 10 8, .tick, .send 10 8]) = 16 ∧ (run E0 full init [.send 10 8, .tick, .send 10 8]).window + 1 = 2 ∧ ControlStack.SC07Exfil.ceilDiv 16 E0.q = 2',wp='by unfold Witness; decide'),
6:dict(module='SC07Liveness',params='',quant='',args='',back='(run E0 full init [Op.send 10 6, Op.send 10 4]).log = [⟨10, 6, 0⟩] ∧ (run E0 full init [Op.send 10 6, Op.tick, Op.send 10 4]).log = [⟨10, 6, 0⟩, ⟨10, 4, 1⟩]',orig='(run E0 full init [.send 10 6, .send 10 4]).log = [⟨10, 6, 0⟩] ∧ (run E0 full init [.send 10 6, .tick, .send 10 4]).log = [⟨10, 6, 0⟩, ⟨10, 4, 1⟩]',intro='',original='shared_quota_blocks',witness='E0.allow = [10] ∧ E0.q = 8 ∧ BackAt',wp='by unfold Witness BackAt; decide'),
7:dict(module='SC07Refinement',params='(K : CCfg) (ops : List COp) (w : ℕ)',quant='∀ (K : CCfg) (ops : List COp) (w : ℕ), K.quotaRule = true → 0 < K.Q →',args='K ops w',back='wireIn (runC K cinit ops).fwd w < K.Q',orig='wireIn (runC K cinit ops).fwd w < K.Q',intro='K ops w hK hQ',original='concrete_wire_lt K hK hQ ops w',witness='(K0 true).quotaRule = true ∧ 0 < (K0 true).Q ∧ wireIn (runC (K0 true) cinit [.pkt 1 8080 4 1, .resetQuota, .pkt 1 8080 4 1]).fwd 0 = 5 ∧ wireIn (runC (K0 true) cinit [.pkt 1 8080 4 1, .resetQuota, .pkt 1 8080 4 1]).fwd 1 = 5',wp='by unfold Witness; decide'),
8:dict(module='SC07Refinement',params='(K : CCfg) (pre post : List COp)',quant='∀ (K : CCfg) (pre post : List COp), K.quotaRule = true → (runC K cinit pre).halted = true →',args='K pre post',back='(runC K cinit (pre ++ post)).fwd = (runC K cinit pre).fwd',orig='(runC K cinit (pre ++ post)).fwd = (runC K cinit pre).fwd',intro='K pre post hK hh',original='concrete_halt_freezes K hK pre post hh',witness='(K0 true).quotaRule = true ∧ (runC (K0 true) cinit [.pkt 1 8080 2 1, .halt]).halted = true ∧ (runC (K0 true) cinit [.pkt 1 8080 2 1, .halt]).fwd = [⟨1, 8080, 2, 3, 0⟩] ∧ (runC (K0 true) cinit [.pkt 1 8080 2 1, .halt, .resetQuota, .pkt 1 8080 2 1]).fwd = [⟨1, 8080, 2, 3, 0⟩]',wp='by unfold Witness; decide'),
9:dict(module='SC07Refinement',params='(K : CCfg) (ops : List COp) (w sink tolerance : ℕ)',quant='∀ (K : CCfg) (ops : List COp) (w sink tolerance : ℕ), K.quotaRule = true → sink ≤ payloadIn (runC K cinit ops).fwd w →',args='K ops w sink tolerance',back='sink ≤ K.Q - 1 ∧ sink ≤ K.Q + tolerance',orig='sink ≤ K.Q - 1 ∧ sink ≤ K.Q + tolerance',intro='K ops w sink tolerance hK hsink',original='sink_within_quota K hK ops w sink tolerance hsink',witness='(K0 true).quotaRule = true ∧ 0 < (4 : ℕ) ∧ 4 ≤ payloadIn (runC (K0 true) cinit [.pkt 1 8080 4 1]).fwd 0 ∧ 4 ≤ (K0 true).Q - 1 ∧ 4 ≤ (K0 true).Q + 1500',wp='by unfold Witness; decide')}
for n,s in specs.items():
 cid=f'bg1n3_{n}'
 typed=next((OUT/'typed').glob(f'{n}-*.lean')).read_text()
 frozen=typed[typed.index('def Back_'):typed.rindex('\nend ')].strip()
 frozen=frozen.replace(frozen.split()[1],'FrozenBack',1)
 if n==8: frozen=frozen.replace('«prefix»','pre').replace('continuation','post')
 at=s['args'];quant=s['quant'];space=' ' if at else ''
 stmt=f"namespace PL_{cid}\nopen ControlStack.{s['module']}\n\n{frozen}\n\ndef BackAt {s['params']} : Prop :=\n  {s['back']}\n\ndef OriginalAt {s['params']} : Prop :=\n  {s['orig']}\n\ndef Claim : Prop :=\n  (FrozenBack ↔ {quant} BackAt{space}{at}) ∧\n  ({quant} (BackAt{space}{at} ↔ OriginalAt{space}{at}))\n\ndef Witness : Prop :=\n  {s['witness']}\n\nend PL_{cid}\n"
 (OUT/f'{cid}.statement.lean').write_text(stmt)
 if n==3:
  reconstruction='''  refine ⟨?_, ?_⟩
  · constructor
    · intro h b c hS hc
      exact ⟨h.1, h.2 b c hS hc⟩
    · intro h
      refine ⟨by norm_num [ceilDiv], ?_⟩
      intro b c hS hc
      exact (h b c hS hc).2
  · intro b c hS hc
    norm_num [BackAt, OriginalAt]'''
 else:
  reconstruction='  refine ⟨Iff.rfl, ?_⟩\n'+('  intro '+s['intro']+'\n' if s['intro'] else '')+'  '+s.get('point','rfl')
 proof=f"open ControlStack.{s['module']}\n\ntheorem original_signature : {quant} OriginalAt{space}{at} := by\n"+('  intro '+s['intro']+'\n' if s['intro'] else '')+f"  exact {s['original']}\n\ntheorem claim : Claim := by\n{reconstruction}\n\ntheorem witness : Witness := {s['wp']}\n"
 (OUT/f'{cid}.proof.lean').write_text(proof)
