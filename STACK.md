# STACK: the capability-free control guarantee stack, status 2026-10-07

Each row is a machine-checked guarantee, or a planned one. Every verified row passed:
- a red team by two foreign model families;
- the proofledger Lean gate (standard axioms only);
- an orchestrator fidelity audit (`campaigns/<C>/forms/<CID>/fidelity-orchestrator.md`).

Statement sources are in `ledger/*.lean` and the model in `DESIGN.md` (v1).

Status legend:
- **verified**: kernel-checked, frozen statement;
- **pending**: frozen or draft, unproved;
- **open**: not yet formalised.

## Layer 1: collusion (untrusted monitoring with honeypots and a mediator)

| CID | plain-English guarantee | assumptions it needs (DESIGN §2.3) | protocols it speaks to | status |
|---|---|---|---|---|
| UMHSF1 | No monitor rule can pass attacks much more often than honeypots unless the mediated attack and honeypot laws differ. Precisely: pass(attack) ≤ e^η·pass(honeypot) + hs_η, attained. Mediation never increases distinguishability. A content-preserving mediator cannot reduce it below the content-level value (exact or approximate decoder). No honeypot law has a likelihood-ratio constant below the maximal leakage Σ_z max_x M(x,z). | finite laws | every untrusted-monitoring protocol (LASR, Greenblatt §3.4) | **verified** (frozen c4a262fd3de3; Sol-high + Flash pass; gate: standard axioms) |
| UMSURVF1 | The honeypot test's survival depends only on the monitor's honeypot pass rate h. It is a binomial CDF (hard slack) or (1−κh)^n (constant schedule), and h·survival ≤ (n_s+1)/(n_h+1). | A1–A3 (fresh contexts, iid honeypots) | Greenblatt upfront synthetic testing; LASR slack | **verified** (frozen 89139ffcfe63; Sol-high + Flash pass; gate: standard axioms) |
| UMPROTF1 | **For every colluding pair** (shared seed, stateless monitor, adaptive generator), the uncaught-catastrophe probability is at most (1−r) + r·L·(n_s+1)/(n_h+1) when every bad submission's view is L-dominated by the mediated honeypot law. The same holds in hockey-stick and soft-slack forms. The first bad submission decides; the trusted-only objective S(h)(1−r+r·a) is exactly attained. | A1–A10; L or δ is a hypothesis on the trusted mediator and honeypot law; r is STANDING | the halting variant of UM; LASR Eq. (1) with ε = 0 and shutdown in place of retraining | **verified** (frozen 1385777cdd90; Sol-high + Flash pass; gate: standard axioms) |
| UMSTRATF1 | With a content-only mediator, m honeypots per bad class and class-aware shutdown, every colluding pair has risk ≤ (1−r) + r(s_c+1)/(m+1), with no class-count factor. Attained by an explicit colluder. | A1–A10; content-only M; Blue can build honeypots per class | design recommendation for any honeypot protocol | TBD |
| UMNOGOF1 | If the mediator preserves a decodable content class and Bad has k distinct classes, **every** iid honeypot law loses to some colluding pair with probability ≥ (1−1/k)^{n_h}. This is the impossibility side. | free-submission model (lower bound) | why summarising/paraphrasing alone cannot give capability-free collusion safety | TBD |
| CANONF1 | A verified canonicaliser for a toy imperative language. It preserves semantics, and its output is a unique normal form modulo for→while, `;`-association and local renaming. Laws that agree on classes become identical after mediation, so markers carried only by those freedoms are erased. | (a verified trusted component) | LASR's For/While marker survived their minifier; this class is provably erased | **verified** (frozen d3d1dd97809f; Sol-high + Flash pass; gate: standard axioms) |

## Layer 2: actions (reference monitor), first step

| CID | guarantee | status |
|---|---|---|
| SANDBOXF1 (draft) | A model of the proofledger sandbox (bubblewrap mount table). (a) The current policy does **not** confine host writes to scratch: `~/.elan` (executed by the gate) is writable. (b) A read-only-root fixed policy confines host writes to scratch and the declared state directories. (c) The current policy does hide the hidden directories, except through the read-only Mathlib re-bind. Boundary assumption: no `/proc/<pid>/root` alias (needs `--unshare-pid`). | draft |

## Existing verified results that slot into the stack (earlier sessions)
- **Trusted monitoring (Redwood):**
  - N1/N1b (`~/research/control-tree/lean/ControlTree.lean`): the audit-game structure, a single-rate saddle point,
    and a dual certificate;
  - K5: noisy clocks.
- **Observables as clocks:**
  - CLKF1/CLKF2: a visible audit counter destroys the value of upfront auditing;
  - LUREF1/LUREF2: silent failures are a clock; erase the failure feedback.

  These are the stateful-adversary caveats to A1 and A4 here.

## Assumptions still unproved (what the stack does NOT give)
1. **That any deployed mediator satisfies the trusted-component hypothesis** (domination constant L, or
   hockey-stick δ, over every bad submission).
   - The theorems are parameterised by it.
   - For rich content-preserving mediators (LLM summarisers, semantics-preserving code transforms) it is false for
     every honeypot law: UMHSF1's maximal-leakage floor and UMNOGOF1.
   - Certifying it for a concrete mediator is open. CANONF1 is the only verified concrete mediator, and it removes only
     three named channels.
2. **Constructibility (A9).** Blue can enumerate a superset B̄ of Bad and build honeypots on it. The action layer
   should supply B̄ structurally.
3. **Worst-case audit recall r (A6, STANDING).** It needs human/U parity, as in Greenblatt et al. and LASR.
4. **Scaffold properties (A1–A4) are assumed, not verified:**
   - fresh monitor contexts;
   - fresh randomness;
   - the view z is the complete monitor input;
   - upfront honeypots.

   Verifying the scaffold is a code-level (Aeneas/hax) target.
5. **Fidelity of the recursions to the operational protocol** rests on an independent simulation, not a Lean bridge.
   The VCVio bridge is open.
6. **Out of model:**
   - stateful monitors and interleaved honeypots;
   - defer-on-exhaustion (it voids the guarantee; numerics only);
   - multi-step attacks;
   - composition with trusted monitoring (a min, not a product, absent conditional independence);
   - LASR's retraining slack (an assumption about U's learning dynamics).
