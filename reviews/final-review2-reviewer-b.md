# Final review 2 (Reviewer B): hostile review and novelty judgement, session 2, 2026-10-07

Scope: UMLOWERF1, SANDBOX2F1, UMUSEF1, UMDEFERF1, the VCVio operational refinement, the revised STACK.md, and directions (A) and (B).

Method:
- I read the brief, the frozen statements, `reviews/final-review2-reviewer-a.md`, the fidelity audits, `proofs/{SANDBOX2F1,SANDBOXF1}.lean`, the head of `ControlStack/RefinementProof.lean`, and DESIGN §2.3 and §5.
- I did not run Lean or lake.
- I re-implemented the recursions with exact `Fraction`s in `<scratch>/` and checked the statements against them. The checks are summarised in the appendix.
- I verified arXiv ids by fetching their abstract pages.

**Status change during the review.** The brief says UMDEFERF1 is "frozen, proof in progress". At 07:12 STACK.md was updated:
- The row now reads "**verified** (frozen ad82ec06fc48; ...; 714-line proof; gate: standard axioms)".
- `proofs/UMDEFERF1.lean` exists. It has 714 lines and contains no `sorry`, `axiom` or `native_decide`.
- The sha256 of `ledger/UMDEFER.lean` begins `ad82ec06fc48`, so it matches the frozen hash.
- I could not re-run the gate. I review the statement as frozen and treat "verified" as the orchestrator's report.

---

## 0. Verdict in one paragraph

No FATAL defect and no statement-level MAJOR defect in the five new items. Every Lean statement I could check says what its STACK row says, once the stated qualifications are read. The remaining problems are:

- **One positioning MAJOR.** UMUSEF1's "necessary lower constraint α₀·u ≤ X" is an instance of the view-blind attainment (UMPROTF1 T3*, UMUSEF1 (c')). It is dominated by an honest-free floor that the stack already proves but never states (§3.3).
- **One hygiene MAJOR.** HANDOFF.md, the next-session entry point, still carries five claims that STACK.md retracted after Reviewer A's review (§5).
- **A handful of MINOR overclaims.** Mostly UMDEFERF1 prose, plus one SANDBOX2F1 phrase and the coarse-regime scenario (§5).

Reviewer A's revisions largely suffice (§2). Two places where I disagree with Reviewer A: I rate (P) lower than Reviewer A does, and I find Reviewer A's "single most valuable next step" under-specified (§6).

Novelty: nothing here is "apparently open". UMLOWERF1 is classical technique with a modest result. SANDBOX2F1 is trivial mathematics with real engineering value. UMUSEF1 is classical in its lemmas and known in its core. UMDEFERF1 is known in its core (the win/continue/lose ratio), with a modest adaptive-generator formalisation. The refinement is a modest artifact over classical content.

---

## 1. Did Reviewer A's revisions suffice? (item by item against the current STACK.md)

| Reviewer A item | Revision in STACK.md | Suffices? | Residual |
|---|---|---|---|
| 1 UMLOWER "design-free" excludes adaptive designs | Row retitled "Converse for nonadaptive joint test designs"; adaptive counterexample quoted; the miss-tolerance contract and the inverse-honeypot caveat are stated | **Yes for STACK.md** | HANDOFF.md:61 still says "risk = Θ(k(n_s+1)/n) for every honeypot design". The SESSION.md/HANDOFF.md labels and `fidelity/UMLOWERF1.md` "Reading" still say "design-free" and "every honeypot design". I quantify adaptive power below (§3.1). |
| 2 UMUSE obstruction omits nonempty Bad and N ≥ 1 | Row and reading guide now say "nonempty Bad, N ≥ 1"; α₀ is a *test-pass* rate | **Yes** | The deeper problem is that (P) is dominated (§3.3). Reviewer A did not raise it. |
| 3 UMUSE presented as optimisation | "one-sided usefulness"; "NOT an optimisation or Pareto result" | **Yes in STACK.md** | `reviews/external-critique-2026-10-07.md` line 45 still says "UMUSE is the inf–sup objective for the hard-slack family". |
| 4 "gain over always-flag" | Absolute bounds; the sup-based worst-case baseline 1 − r | **Yes in STACK.md** | HANDOFF.md:54 still says "bound the adversarial gain over an always-flag protocol". |
| 5 UMSTRAT omits A11 | "A1–A11 (it reuses the absorbing `cat`)" | **Yes** | None. |
| 6 UMUSE operational bridge absent | Marked OPEN; the frozen docstring's overstatement is disclosed | **Yes as disclosure** | The fix Reviewer A asked for (an operational game with distinct terminal outcomes) is not done. I make it a next step (§6). |
| 7 UMDEFER floor does not construct a service | Trust-table rows for α and for replacement; "α = q·r is a separate service-construction obligation" | **Yes** | None beyond MINOR prose (§5). |
| 8 UMDEFER resource and reserve claims exceed Claim | "unmetered deferred-audit service"; "metered or reserve-limited deferred audits are not in Lean" | **Yes** | The frozen docstring still says "up to q(1−η) per round". It cannot be changed, and the STACK disclaimer suffices. |
| 9 direction B: complete mediation does not give A4/A5/A11 | The SOUNDGATE bullet now says the gate plus a verified driver plus an execution-order contract is needed | **Yes** | I agree with Reviewer A and add a stronger reason below (§6). |
| 10 Ctrl-Z undercounted; "none subsumes" too categorical | Ctrl-Z added as the closest neighbour of UMUSE/UMPROT; "an unmechanised result can subsume a CID's mathematical content" | **Yes** | The classical antecedents that actually subsume the lemmas are still unnamed (§4). |
| 11 SANDBOX2F1 parameter boundary | "(c) needs scratch W under /var/tmp. (b) allows ARBITRARY declared state directories" | **Yes** | One extra phrase to fix (§5, I9). |
| 12 thresholds and stale status | "labelled numerical scenario"; statuses synchronised; "A finite L exists only for a COVERING honeypot law" | **Mostly** | The scenario omits α₀, the parameter that dominates the table (§5, I7). |

**Where I disagree with Reviewer A:**

1. Reviewer A treats (P) as "the particular obstruction and its formalisation" and the "new contribution here". I judge it a restatement of mimicry (LASR App. B.3) that is dominated by an unconditional floor (§3.3).
2. Reviewer A calls UMDEFERF1 "modest". I put the core at known (Shlegeris) and the modest part at the adaptive-generator formalisation with a reachable conditional floor.
3. Reviewer A's recommended "single most valuable next formalisation" is a research programme, not a step: "every admissible history-dependent Red policy and every admissible conditional transition model". I give a concrete staged version in §6.
4. Reviewer A did not look at the satellite documents. They contradict STACK.md (§5, I2).

---

## 2. Cross-cutting findings (new, from my own checks)

**(i) The honest-free floor and an AOQL antecedent.** The view-blind pair at *any* h is a legitimate colluding pair. With nonempty Bad, N ≥ 1 and b ≥ 1 (or b = 0), UMPROT T3* and UMUSE (c') give

> sup-risk ≥ F*(n_h, n_s, r) := max_h survH(h)·(1 − r + r·h)

(b ≥ 1; take r = 1 for the b = 0 form). This needs no honest profile, no mediator and no L. For r = 1 and survival the binomial CDF, F* = max_h h·binCDF(n_h, n_s, h). That quantity is the **average outgoing quality limit (AOQL)** of the single-sampling plan (n_h, c = n_s) from acceptance sampling (Dodge–Romig, Bell Labs, 1940s). The honeypot test *is* an acceptance-sampling plan, and UMSURV's survival is its operating-characteristic curve. T3c, h·binCDF ≤ (n_s+1)/(n_h+1), is a standard binomial-moment bound on the AOQ curve.

Exact values (`useful.py`) for F*·(n_h+1)/(n_s+1):

| n_s | n_h | ratio |
|---|---|---|
| 0 | any | tends to 1/e (≈ 0.37 at n_h = 100) |
| 5 | 100 | 0.535 |
| 59 | 1000 | 0.764 |

So at L = 1 UMPROT's honeypot term is tight within a factor ≤ e, *unconditionally*. This is true, derivable from the existing Lean statements, and **not stated in STACK.md**. The "excess over the worst-case baseline" is therefore two-sided at L = 1.

**(ii) The decision-relevant quantity in the numerics is α₀, not k.** In DESIGN §5 at n_h = 30 and k = 4, risk rises 0.048 → 0.111 → 0.259 as α₀ goes 0 → 0.01 → 0.05. At n_h = 100 and k = 8, α₀ = 0 gives 0.029. The "k ≤ 4–8" caveat names the wrong dominant variable. The driver is the honest honeypot miss rate, through the slack that Cantelli (UMUSE (d)) forces. That is classical, and the stack's most decision-relevant content is the pair (UMUSE (d), UMPROT T3), not the converse.

**(iii) All review in the chain is LLM-based.** Reviewers A, B and C, the prover agents and the orchestrator are all models. "Specification fidelity" has not been checked by a human domain expert. STACK.md says "a red team by two foreign model families", which is accurate but invites a stronger reading.

---

## 3. New items

### 3.1 UMLOWERF1 (nonadaptive converse), verified

**Fidelity verdict: faithful to the stated, narrowed claim.**

What I re-derived. For seed ω and tuple xs, let N_ω(xs) be the number of positions with c(xs_i) = c(ω). Given the tuple, misses ~ Bin(N_ω, t).
- Survival is at least P(Bin ≤ n_s) ≥ 1 − t·N_ω/(n_s+1) by Markov, because `keep = 1` on all patterns with ≤ n_s misses.
- Averaging over the uniform seed on S, injectivity of c on S gives Σ_ω N_ω ≤ n.
- The first deployment PASS then gives catastrophe w.p. t, for every r, b and N ≥ 1.

Checks:
- The quantifier order (∃ decoder g, then ∀ design, then ∀ t) is right.
- The hypotheses are not vacuous: the Witness attains 1/4 exactly with a non-degenerate seed.
- `Setup` demands an exact decoder on *all* of X, not only on S. This is stronger than needed but harmless, because it only narrows the claim. It is load-bearing for honeypots outside S, which must not decode into a seed class.

**Adaptive testers: quantification of Reviewer A's point.** The reported nonadaptive scope is correct. I computed the exact optimal adaptive tester by dynamic programming over posterior states (`lower_adapt*.py`). The colluder is the Lean family (uniform seed, PASS the seed class w.p. t), and the tester picks each next class from earlier answers.

- Reviewer A's example is confirmed (k = 4, t = 1, n_s = 1, n = 5): survival is 0 against 3/8.
- It is not only a t = 1 corner. At the Lean-prescribed t, adaptive risk is far below the formula:

| (k, n_s, n) | t | adaptive risk | formula min(1/2, k(n_s+1)/(4n)) |
|---|---|---|---|
| (4, 1, 5) | 4/5 | exactly 3124/15625 ≈ 0.200 | 2/5 |
| (4, 6, 28) | 1/2 | exactly 21586293/536870912 ≈ 0.040 | 1/4 |

- After the colluder re-optimises t (grid), the adaptive tester still beats the maximum of the Lean curve:

| (k, n_s, n) | adaptive best-t risk | max of Lean curve |
|---|---|---|
| (4, 1, 5) | ≈ 0.309 | 0.40 |
| (4, 6, 28) | ≈ 0.176 | 0.25 |
| (6, 2, 18) | ≈ 0.159 | 0.25 |
| (5, 5, 30) | ≈ 0.152 | 0.25 |

  The gap is a factor of about 1.3–1.7 at these sizes. At n_s = 0 or k = 2 adaptivity did not help (ratio ≥ 1). So the formula is genuinely false for adaptive designs, not only in a corner.
- A converse that *does* cover adaptive designs is provable by an identical-until-bad argument (Shoup's difference lemma, eprint 2004/332). Along the all-FLAG path the tester's queries are a fixed sequence independent of the seed. Averaged over the uniform seed, the expected number of queries in the seed class is ≤ n/k, so P(at least one PASS) ≤ t·n/k. Hence survival ≥ 1 − t·n/k and

  > risk ≥ t(1 − t·n/k) for every adaptive (even randomised) tester, every n_s ≥ 0,

  so risk ≥ min(1/2, k/(4n)) at t = min(1, k/(2n)). This is the formula with the (n_s+1) factor removed. I checked 133 DP cells (various k, n_s, n, t), minimum slack 0.0057, no violation. It is a proof sketch only, not in Lean. It keeps the qualitative message (budget ∝ k) for adaptive testers and loses the n_s multiplier, which the numbers say can really be lost.

**Remaining overclaims in STACK.md:** none in the UMLOWERF1 row. The row is accurate. Residual items live outside STACK.md (§5, I2).

**Novelty: modest.** The technique is classical (averaging over a uniform seed plus Markov, i.e. Yao's minimax principle). The object is a converse for honeypot-test budget, and I found no source stating it.
- Qualitative precursor: Roger–Shlegeris, "Toy models of AI control for concentrated catastrophe prevention" (Alignment Forum/LessWrong, post id MDeGts4Aw9DktCkXw; I could not re-fetch the body, so I rely on the related-work audit's reading of the "audit a few examples from each category" passage).
- Technique: Yao 1977; Shoup, eprint.iacr.org/2004/332.

**Critique success criteria:**

| Criterion | Judgment |
|---|---|
| Non-vacuity | Met in the toy. |
| Fidelity | Met for the narrowed claim. |
| Necessary assumptions | The decoder and injectivity are load-bearing (Reviewer A, prose). The adaptive failure is a counterexample (Reviewer A, now confirmed numerically). Neither is a Lean theorem. |
| Decision relevance | Partial. Class-aware budgeting is lore. The quantification is new. |
| Honest scope | Met in STACK.md. |

---

### 3.2 SANDBOX2F1 (corrected sandbox fix), verified

**Fidelity verdict: faithful to the pathname-resolution model.**

- I read `ledger/SANDBOX.lean`, `ledger/SANDBOX2.lean` and the proof.
- (b) is a structural fact about the mount list: only two read-write host binds exist. It already held for `fixedPolicy`, so SANDBOX2F1's new content is (a) and (c).
- (c) is correct. The state binds come before the hiding tmpfs, so any path inside a hidden directory is covered by a later tmpfs, except the read-only Mathlib re-bind. The `["var","tmp"] <+: W` hypothesis is necessary, because W inside a hidden directory would reveal it through `/var/tmp/work`.

**Model-level gaps, all disclosed in the fidelity doc, some not in STACK.md:**
- **Hidden files** (e.g. a CLI history file inside a CLI state directory) are not modelled. With that state directory declared they are readable and writable.
- A declared state directory is exposed to the untrusted prover *by design*. The Witness shows a credential file in the declared state directory is writable, which means credential exposure to the prover, not only to the CLI.
- A declared state directory that is `/var/tmp` or one of its ancestors (for instance `["var","tmp"]` or `["var"]`) is bound after the scratch bind and the `/var/tmp` tmpfs. It re-exposes the host's `/var/tmp`, including every other session's scratch. (b) still holds, but "scratch confinement" is gone. This is another way the declared write set is "not a validated safe policy".
- These are model theorems; they make no claim about a running system. STACK.md says so.

**Remaining overclaim:** I9, "(c) ... hiding holds for **every** choice of state directories". It should read "for the 11 modelled hidden *directories*".

**Novelty: known/classical, trivial.** List-prefix reasoning over mount order. The value is operational: it caught a regression in the proposed fix, and SANDBOXF1(a) (a writable toolchain directory that a later, unsandboxed checker executes) is a concrete finding about the modelled policy. References: Bubblewrap (containers/bubblewrap); SOUNDGATE 2607.14166 and Alignment Contracts 2605.00081 as neighbouring effect-layer work.

I verified both arXiv ids by fetching their abstracts:
- 2607.14166: "Stop Means Stop", S. Khan, July 2026.
- 2605.00081: "Alignment Contracts for Agentic Security Systems", David–Guarnieri–Gervais, April 2026, with a Lean 4 artifact.

**Highest-value action on this item is not formal.** A short canary write test (or SOUNDGATE's canary self-test idea) is what converts a model fact like SANDBOXF1(a) into a system fact. It is outside the formal work, so I only flag it.

**Success criteria:**

| Criterion | Judgment |
|---|---|
| Non-vacuity | Met. The Witness is exercised. |
| Fidelity | Met for the model; correspondence to a running system is outside the model. |
| Necessary assumptions | (a) is the counterexample. |
| Decision relevance | High for sandbox policies of this shape. |
| Honest scope | Met. |

---

### 3.3 UMUSEF1 (usefulness companion and obstruction), verified

**Fidelity verdict: faithful. The identities are correct and the Witness reproduces.** Checks (`useful.py`):
- I re-implemented `haltP` and `cat` independently in exact `Fraction`s. The Witness numbers reproduce exactly: false halt 169/1600, α₀ = 9/40, f₀ = 13/40, completion 1375191/2560000, view-blind risk 47089/128000 (b = 1) and 8649/64000 (b = 0).
- The identities (a) and (c') and the accounting identity D·risk = q·completion held on 300 random small instances.
- The Cantelli inequalities (d) and (d') held on 20000 grid cells, and T3c on 5000, with no violation.
- The ROC statement (f) is UMHS T2 applied with P = M·μ, Q = M·P_H, so it is correct.

**The headline obstruction is dominated.**
- (P) says: for u ≤ completion, q·u ≤ D·X and α₀·u ≤ X. Its risk side is exactly "X ≥ risk of the view-blind pair at h = α₀", which is (c').
- Completion enters only through the identity D·risk = q·completion. Dropping the identity, X ≥ risk(view-blind, h) holds for *every* h with no honest profile. So the best form of the statement is X ≥ F*, and (P)'s floor is always ≤ F*.

Numbers (`useful.py`):

| n_h | n_s | α₀ | F* | (P) floor α₀·u | UMPROT H = (n_s+1)/(n_h+1) |
|---|---|---|---|---|---|
| 100 | 5 | 0.02 | 0.0318 | 0.0197 | 0.0594 |
| 100 | 0 | 0.001 | 0.00366 | 0.0009 | 0.0099 |
| 1000 | 59 | 0.05 | 0.0458 | 0.0457 | 0.0599 |

(P) is close to F* only when the slack is tuned to the honest profile. That is the composite of three facts:
- completion ≥ u forces n_s ≳ n_h·α₀ − O(√·) by Cantelli (d);
- UMPROT's term r·L(n_s+1)/(n_h+1) then cannot go below ≈ r·L·α₀;
- F* ≈ (n_s+1)/(n_h+1) up to the AOQL factor.

That composite is the real decision-relevant content. It is classical (Cantelli plus T3c) and is **not a Lean statement**.

**Remaining overclaims in STACK.md:**

- (I1, MAJOR positioning) Reading guide: "Usefulness is in Lean as honest full-run availability (UMUSEF1), with a necessary lower constraint α₀·u ≤ X on every universal certificate X at availability target u (nonempty Bad, N ≥ 1)."
  - The row's "a protocol that keeps the honest monitor's full-run completion ≥ u cannot certify risk below u × the honest rule's honeypot test-pass rate α₀" has the same problem.
  - Fix: "Usefulness is in Lean as honest full-run availability and exact honest-side identities (UMUSEF1). The only coupling to risk is mimicry: a view-blind colluder that passes honeypots at the honest rate α₀ is a colluding pair, so every universal certificate X satisfies X ≥ risk(view-blind, α₀) ≥ α₀·u (nonempty Bad, N ≥ 1). It is dominated by the honest-free floor max_h survH(h)·q(h), which the stack already proves (T3*, (c')). The usefulness-forced slack cost is Cantelli (d); its composition with UMPROT's honeypot term is not a Lean theorem."
  - Label (P) "mimicry floor (known: LASR App. B.3)".
- (MINOR) "For nonempty Bad, N ≥ 1 and b ≥ 1, the worst-case risk of always-FLAG is exactly 1 − r." This is correct but not a single Lean statement. It is T3a at A = 0 for "≤" and UMUSE (c') at h = 0 for "≥". Add "(corollary of T3a at A = 0 and UMUSEF1 (c'))".

**Novelty: classical (lemmas), known (core).**
- The honest-ability ceiling: LASR App. B.3 (2602.20628, "When can we trust untrusted monitoring? A safety case sketch across collusion strategies", Gardner-Challis et al., with Griffin and Abate, the Games for AI Control authors).
- Upfront validation, honest misses and shutdown thresholds: Ctrl-Z App. E (2504.10374).
- The framing: Games for AI Control (2409.07985).
- The honeypot test as acceptance sampling: Dodge–Romig AOQL.
- Cantelli's inequality (1928); Neyman–Pearson.

**Success criteria:**

| Criterion | Judgment |
|---|---|
| Non-vacuity | Met. The asymmetric Witness, with a blurring mediator. |
| Fidelity | Met, with two exceptions: the operational bridge is open, and the frozen docstring's "bridge for both" overstates (disclosed). |
| Necessary assumptions | The completion hypothesis is load-bearing (1/2 ≤ 1/3). N = 0 and Bad = ∅ are excluded. |
| Decision relevance | **Weak.** The obstruction is dominated. The decision-relevant slack cost is classical and unstated as a composition. |
| Honest scope | Met after Reviewer A's revision, modulo I1. |

---

### 3.4 UMDEFERF1 (audit, then defer), now reported verified

**Fidelity verdict: faithful to the frozen specification.**

I re-derived the Witness values by hand and by code:
- catV = 49/400, catD(α = 1/2) = 29/200, catD(α = 0) = 19/100, finiteCap = 29/200, catD(b = 1, n = 3) = 1/10, protocolCatV = 35721/400000, and the no-go value 3/16.
- The coarse bound follows from retry ≤ A/θ together with T3c.

Independent exact checks (`defer.py`, `defer_reach.py`):
- (b) catD ≤ finiteCap, with the true optimal history-dependent generator by dynamic programming: 1500 random instances (|X|, |Z| ≤ 3, n ≤ 4, b ≤ 2, various r, η, α), 0 violations. The bound was tight in 1447 of them.
- The floor bridge catV ≤ catD, with random history-dependent services ≥ α: 0 violations.
- The bridge when the floor is imposed *only on `Reach` states* (the service set to 0 elsewhere, `Reach` implemented from the inductive definition): 600 instances, 0 violations. 589 of those had unreachable low states, so `Reach` is neither too narrow nor too wide in these tests.
- The finite-certificate example (n_h = 10⁴, n_s = 5, ε = 10⁻³, b = 0, r = 1, η = 0, L = 1): minimal θ = 0.3165 (grid optimum, N ≥ 100), against the coarse H/ε = 0.600. This reproduces "θ ≈ 0.32".

**What the example really says.** At b = 0 the halting protocol already certifies risk ≤ H ≈ 6·10⁻⁴ with zero audits, but availability is [N ≤ 0] = 0. Deferral at risk 10⁻³ needs a conditional incrimination probability ≥ 0.32 on *every* deferred flag. In the unmetered service model that is an audit load of 32% of all deferred items, honest ones included. The model has no availability and no audit-resource accounting, so it cannot say whether deferral beats halting at equal total audits. Reviewer A's item 8 stands in spirit: the comparison that matters is missing. STACK.md already says "safety only"; the example's number should carry that caveat.

**Remaining overclaims in STACK.md:**

- (I3, MINOR) "(b) a finite retry certificate finiteCap ..., the exact worst case".
  - The Lean claim is an upper bound, with attainment only at an exhausted budget (c).
  - Before exhaustion, tightness holds only for the sup over (M, φ, π) with separated views (benign and bad views disjoint, so the monitor can flag benign items freely). That is numerically attested (Reviewer B's 4000 Bellman checks and my 1447/1500), not a Lean statement.
  - Fix: "an upper bound that is attained at an exhausted budget (Lean) and, numerically, before exhaustion when benign and bad views are separable".
- (I4, MINOR) "decides whether layer 1 survives defer-style routing: only with a uniform stopping hazard". The docstring itself says this is not a necessity theorem (finite horizons and permanent switching avoid the no-go). Fix: "the proved guarantee requires a uniform stopping hazard; (e) is a no-go only for the benign-flag-guard-free free-submission model".
- (I5, MINOR) "(e) ... a burn-then-attack colluder's risk tends to 1 over long horizons against every two-point honeypot law". The tuned t_K = 1/√(K+1) depends on the horizon K. Fix: add "tuned to the horizon".
- (I6, MINOR) Add the example number and the audit-load caveat above.
- The row says "the floor bridge catV ≤ catD is a theorem". That is now acceptable (verified status).

**Novelty: known core, modest formalisation.**
- The per-attempt stopping ratio A/(θ + A(1−θ)) is Shlegeris's win/continue/lose (Redwood blog, Nov 2024; verified to exist) and LASR's B.6 (u/(c+u)).
- The no-go is classical arithmetic: (1−t)^{n_h} → 1 and 1 − (1−t)^K → 1 with t_K = 1/√(K+1).
- What is new, and modest: the adaptive-generator bound with a *reachable conditional* floor (which separates "fresh coins" from a conditional recall floor), the budget-sensitive `finiteCap`, and the composition with the honeypot test.
- Neighbours: Games for AI Control (the Defer action; I confirmed that the paper does not model collusion or honeypots); Ctrl-Z (resampling and incrimination).

**Success criteria:**

| Criterion | Judgment |
|---|---|
| Non-vacuity | Met. A history-dependent service is witnessed. |
| Fidelity | Met. |
| Necessary assumptions | Met in Lean for the stopping hazard (the no-go). The average-vs-conditional floor counterexample (371/2000 > 2/11) is prose and numerics only. |
| Decision relevance | Partial. See the audit-load point. |
| Honest scope | Met except I3–I6. |

---

### 3.5 VCVio operational refinement (`Refinement.lean` / `RefinementProof.lean`), proved, not ledger-gated

**Fidelity verdict: faithful for the catastrophe event.**

- The game has a shared seed, a binomial honeypot test through the Bridge, a stateless monitor with fresh coins, an adaptive generator that sees the whole history including PASS/FLAG bits (a stronger adversary than needed), and an audit kernel with history-dependent recall.
- Absorbing shutdown and halt-on-exhaustion are built into `deploy`.
- `ProbComp` has no failure here (the proof sums outputs to 1), so `toReal` is well-behaved.
- The quantifier order (colluding pair and audit kernel universally quantified after H and M) is the adversary-favourable one.
- It is *more* general than the ledger's T3 in one respect (recall may depend on (h, x, z)) and narrower in two (hard slack and the domination form only; rational probabilities).

**Gaps:**
- There is no operational honest-completion event (Reviewer A #6), and the Boolean outcome merges completion, caught shutdown, test rejection and budget halt. The STACK row says "honest-completion (`haltP`) event in the game" is open, which is correct.
- It is an *adequacy* theorem between a trace-level program and the Bellman recursion, not a refinement of a deployed scaffold. STACK assumption 5 already says "abstract operational-model correspondence".

**Remaining overclaims in STACK.md:**
- (I10, MINOR) The row title "Operational refinement". In formal methods "refinement" implies an implementation relation. Fix: "operational adequacy".
- (MINOR) "This is the first operational bridge to UMSURVF1's quantity". It is a priority-flavoured claim. Replace with "an operational bridge (no comparable ProbComp-level protocol model found in this search)".

**Novelty: modest artifact over classical content.** The content is the standard adequacy of a Bellman recursion for a probabilistic program. The artifact is useful infrastructure. References: VCVio (Tuma–Hopper, eprint.iacr.org/2024/1819, verified); SSProve (eprint 2021/397; I did not re-fetch it).

**Success criteria:**

| Criterion | Judgment |
|---|---|
| Non-vacuity | Met. The Witness is 27/256 < 1/4. |
| Fidelity | Met for catastrophe; open for availability. |
| Necessary assumptions | Statelessness is load-bearing, and the call-counting monitor reaches 1 trivially. |
| Decision relevance | Low. It is a correspondence result. |
| Honest scope | Met. |

---

## 4. Positioning against prior art and the critique

STACK.md now positions the work honestly in its main claims.

**What is right.**
- The defensible claim is "no comparable machine-checked artifact found in this search", not a priority claim. A "first Lean formalisation of control protocols" claim is explicitly banned.
- "Machine checking changes the evidential status, not the novelty."
- The informal anticipations (Roger–Shlegeris, LASR, Ctrl-Z, Greenblatt App. G, Shlegeris) are named.
- The four obligations are mapped to what discharges them.

**Gaps.**

1. *Classical antecedents that subsume the lemmas are unnamed.* "Classical" is asserted without referents. Add:
   - acceptance sampling and AOQL (Dodge–Romig), for UMSURV, T3c and the view-blind sup;
   - cut-and-choose in secure computation (Lindell–Pinkas), and the exchangeability or conformal rank bound (Angelopoulos–Bates, arXiv 2107.07511, verified; I did not check the cut-and-choose reference);
   - Yao's averaging principle and the Shoup/Bellare–Rogaway difference lemma, for UMLOWER;
   - Cantelli and Neyman–Pearson;
   - Schneider, "Enforceable security policies" (2000): A4, A5 and A11 are prefix-closed trace properties, so execution-monitor enforceability is the classical frame for direction (B).
2. *Same-group lineage.* LASR (2602.20628) and Games for AI Control (2409.07985) share Griffin and Abate. LASR is the successor that does cover untrusted monitoring, and GAC does not (confirmed: GAC "does not model collusion or honeypots"). Say so, so the reader does not expect GAC to contain UM.
3. *Safety-case and guaranteed-safe-AI neighbours.* Missing from the prior-art section: Korbak et al., "A sketch of an AI control safety case" (arXiv 2501.17315, verified), Towards Guaranteed Safe AI (2405.06624, verified), Out of Control (2506.17846, verified), Reliability Theory for AI Control (Molnar, 2609.26419, verified, 22 Sept 2026). The critique cites them. The audit file covers six sources only.
4. *The critique's "decision relevance already met" is generous* (`external-critique-2026-10-07.md`, disposition). Class-aware versus global slack is Roger–Shlegeris lore. Incrimination for defer is Shlegeris. What is new is the quantification, and the quantified UMLOWER is nonadaptive. Call it "partially met".
5. *LASR eq (1) and UMSURV soft slack.* UMSURV's soft-slack survival (1−κh)^{n_h} is the exact discrete form of LASR's e^{−n_h(1−s_θ)(1−ε)/n_s} (LASR App. B.5). The STACK row says no reduction to LASR eq (1) is proved. Add "the survival term is the exact form of LASR's Poisson expression".

**Critique success criteria, package-level:**

| Criterion | Judgment |
|---|---|
| Non-vacuity | Technical non-vacuity yes. Realistic non-vacuity no, and honestly stated ("coarse-regime caveat"). The honest-miss rate α₀ is the dominant driver, not k (§2 (ii)). |
| Specification fidelity | LLM-only audits, none human. Catastrophe correspondence is proved. Availability correspondence is not. |
| Necessary assumptions by counterexample | Mixed. The counterexamples for A11 (3/4 > 1/2), the average-versus-conditional floor (371/2000 > 2/11) and the call-counting monitor are prose and numerics, not Lean. The decoder, the stopping hazard and the completion hypothesis are exercised in Lean. |
| Decision relevance | Weak to partial. The numerics say α₀, slack and class-aware design matter. Those are classical, and the composite statement is not in Lean. |
| Honest scope | Largely met. See §5. |

---

## 5. Consolidated remaining issues (severity, exact phrase, fix)

**MAJOR**

- **I1 (UMUSEF1 positioning).** Exact phrases: "Usefulness is in Lean as honest full-run availability (UMUSEF1), with a necessary lower constraint α₀·u ≤ X on every universal certificate X at availability target u"; "a protocol that keeps the honest monitor's full-run completion ≥ u cannot certify risk below u × the honest rule's honeypot test-pass rate α₀". Fix: as in §3.3.
- **I2 (stale satellite documents).** HANDOFF.md carries five claims STACK.md retracted:
  - line 61: "With UMLOWERF1 and UMSTRATF1, risk = Θ(k(n_s+1)/n) for every honeypot design";
  - line 54: "they bound the adversarial gain over an always-flag protocol, and usefulness is not in Lean";
  - line 68 (finding 3): "this is shown in numerics only" (UMDEFERF1 is now frozen and reported verified);
  - line 58 (finding 1): "k ≲ 4–8 at realistic n_h ≤ 100" (no α₀);
  - the labels "design-free converse" in SESSION.md:60, HANDOFF.md:48 and the title of `fidelity/UMLOWERF1.md`, whose "Reading" bullets also say "Against every honeypot design" and "necessary and sufficient up to constants".
  - `reviews/external-critique-2026-10-07.md` line 45 still says "UMUSE is the inf–sup objective for the hard-slack family".

  HANDOFF.md is the next session's entry point, so these will be re-read as current. Fix: rewrite or delete them. The Θ claim holds for (iid uniform honeypots, global slack) and, as a lower bound only, for nonadaptive designs.

**MINOR**

- **I3** UMDEFER "the exact worst case": fix in §3.4.
- **I4** UMDEFER "only with a uniform stopping hazard": fix in §3.4.
- **I5** UMDEFER (e) "tends to 1 over long horizons": add "tuned to the horizon".
- **I6** UMDEFER (d) example: add "θ ≈ 0.32 is a 32% conditional audit load on deferred items in an unmetered service; compare halting at b = 0, risk ≤ H ≈ 6·10⁻⁴ with no audits and no availability".
- **I7 (coarse regime).** Exact phrase: "(a labelled numerical scenario, DESIGN §5: r = 1, δ = 0, content-only M, honest false shutdown ≤ 10%, n_h ≤ 100). Risk X ≲ 0.1 needs about k ≤ 4–8".
  - Omits α₀. The table gives 0.068 at α₀ = 0.01, k = 8, but 0.163 at α₀ = 0.05, k = 8, and 0.26–0.41 with global slack.
  - "honest false shutdown" is ambiguous. It is the honeypot-test false shutdown, not UMUSE's false halt P(Bin(N, f₀) > b).
  - The values are sups of the one-class colluder family, i.e. lower bounds on the true worst case (for r = 1 they equal the exact sup of the class-aware design, but the Lean certificate is the looser (s_c+1)/(m+1) = 0.154 at m = 12, s_c = 1).
  - Fix: add α₀ ≤ 0.01, name the false-shutdown notion, and say the "needs" side is a necessary condition while the certified side is the Markov bound.
- **I8** Reading guide: "The adversary is universally quantified, which is what makes it capability-independent." Fix: "which makes the bounds independent of the adversary's strategy within the modelled class (stateless fresh-context monitor, shared seed, single-step Bad); capability re-enters through L, r, α, the scaffold and the model class".
- **I9** SANDBOX2F1 "(c) ... hiding holds for **every** choice of state directories". Fix: "for the 11 modelled hidden directories (not hidden files; a hidden file inside a declared state directory is exposed; the Mathlib re-bind is an explicit read-only hole)".
- **I10** "Operational refinement": rename to "operational adequacy". "This is the first operational bridge": soften.
- **I11** A1–A11 are never defined in STACK.md; the trust table lists only A1–A4 and A11. Add "(A1–A11 are defined in DESIGN §2.3)" or a one-line list.
- **I12** "the worst-case risk of always-FLAG is exactly 1 − r": cite T3a at A = 0 plus UMUSE (c').
- **I13** Add the AOQL (§2 (i)) and tightness-within-e remark, and the unnamed classical antecedents (§4).
- **I14** Reading guide: "Every verified row passed: a red team by two foreign model families; ...; an orchestrator fidelity audit." Add "no human expert review yet".

---

## 6. Ranking the next directions

**Ranking: (A), rescoped, first; (B) last; better-per-effort precursors proposed.**

**(A) Lean-check a Games-for-AI-Control trusted-monitoring certificate, merged with N1b.**

- *Value.* This is the only proposal that speaks to the audience that wrote the prior art, and it is the critique's own item 7 ("an optimiser produces protocol + bound; Lean checks the certificate").
- *Reviewer A's rescoping is correct.* GAC restricts Red to a memoryless policy: "memoryless (its actions depend only on the last observation)", with a fixed backdoor probability β (verified in GAC v2, May 2026). Prop 4.1 is a dynamic-programming recursion for memoryless threshold protocols. Checking the Red best response over β certifies safety against that adversary class only. A literal transcription would be known infrastructure.
- *Novelty lives in the rescoping.* A Bellman-supersolution certificate (a value function V on a finite stateful model with budget, feedback, observations and shutdown, satisfying per-state inequalities for every admissible Red action) is checkable per state and covers every history-dependent Red. N1b's dual certificate is of that form. The decisive deliverable is a theorem and a counterexample:
  1. the fixed-β certificate is sound against every history-dependent Red *exactly when* Red's observations are independent of budget state and audit outcomes;
  2. otherwise it fails. The visible-audit-counter results (CLKF1/CLKF2) and the LUREF silent-failure results are the existing seeds.
  That is "necessary assumptions shown by counterexample" plus "decision relevance" (which observables to hide), which is exactly what the package lacks.
- *Risks.*
  - Kernel arithmetic with high-degree polynomials in β needs a Bernstein-coefficient certificate. Avoid `native_decide`, since the gate allows standard axioms only.
  - Reproducing a published Beta-fixture number needs explicit approximation bounds, as Reviewer A says. Start with a small M and C toy, and treat the paper-number reproduction as optional.
- *Novelty if done as rescoped:* modest. *If only transcribed:* known.

**(B) Port SOUNDGATE's admission gate to Lean; prove A4/A5/A11 follow from complete mediation.**

- *Reviewer A's objection is correct.* Complete mediation does not give test-before-deploy, halt-on-exhaustion or catch-to-cancel. SOUNDGATE's own cancellation excludes rollback of released effects.
- *A further reason.* A4, A5 and A11 are prefix-closed trace properties (the bad thing happens at a finite prefix). By Schneider's enforceability theorem they are enforceable by a security automaton, so the theorem is nearly immediate. The substance is entirely the driver contract plus the execution-order contract, which restates A4/A5/A11 as driver postconditions. The assumption moves; it does not shrink.
- *Correspondence.* SOUNDGATE's model-to-code link is differential testing. A Lean port verifies a re-model, not the Rust.
- *One real use.* It would discharge part of UMDEFER's "replacement" trust-table row (no effect before the decision; immediate shutdown), not the "replacement cannot cause the catastrophe" half.
- *Novelty:* classical (reference monitors, Schneider). *Value:* clarity, not depth.

**A better order of work.** Three small precursors are each cheaper and more valuable than (B), and they de-risk (A).

1. **Certificate form for UMPROT and UMSTRAT** (about 100 lines). State "if ∀ t ∈ [0,1], binCDF(n_h, n_s, t)·(1 − r + r·min(1, L·t)) ≤ U, then every colluding pair has risk ≤ U". UMDEFER (d) already has this shape. This lets the DESIGN §5 numerics enter as Lean-checked rational certificates and removes the Markov slack (0.154 versus 0.068 at m = 12, s_c = 1). It is the minimal instance of (A)'s certificate workflow on the existing stack, and it exercises the polynomial-bound tooling (A) needs. It also gives the AOQL two-sidedness at L = 1.
2. **Adaptive converse (UMLOWER-ADAPT)** (about 150 lines). Prove risk ≥ t(1 − t·n/k) for adaptive testers (§3.1). It closes Reviewer A's item 1 for every ordering of the test and gives the honest "k/(4n)" statement.
3. **Outcome-valued operational game** (about 300–500 lines in VCVio). Return one of {completion, catastrophe, caught shutdown, test rejection, budget halt}, and prove the full outcome distribution equals the recursions. This closes Reviewer A's item 6 and makes safety and availability two marginals of one experiment. It is a prerequisite for any honest Pareto or "operational" claim.

I would not put (B) before these. If a single step must be named: **(A) rescoped, staged so that precursor 1 is its first milestone.**

---

## 7. Per-CID table (new items)

| CID | Fidelity verdict | Novelty | References |
|---|---|---|---|
| UMLOWERF1 | Faithful to the narrowed claim (nonadaptive joint designs). The formula is false for adaptive testers, by a factor up to 1.7 at the colluder's best t on my instances; an adaptive converse with the n_s factor removed is provable on paper. | **modest** (classical technique) | Roger–Shlegeris "Toy models ..." (AF post MDeGts4Aw9DktCkXw; body not re-fetched); Yao 1977; Shoup eprint 2004/332 (verified) |
| SANDBOX2F1 | Faithful to the pathname model. It is a model theorem, not a system test. Hidden files are outside the model. | **known/classical (trivial)** | bubblewrap; SOUNDGATE 2607.14166 (verified); Alignment Contracts 2605.00081 (verified) |
| UMUSEF1 | Faithful. Identities and Witness reproduced exactly. (P) is dominated by the honest-free floor. The operational bridge is open. | **classical** (lemmas); **known** (core) | LASR 2602.20628 App. B.3, B.5 (verified id); Ctrl-Z 2504.10374 App. E (verified); GAC 2409.07985 (verified); Dodge–Romig AOQL; Cantelli; Neyman–Pearson |
| UMDEFERF1 | Faithful to the frozen spec. 1500 + 600 exact checks, 0 counterexamples. Reported verified (proof present, not re-run). | **modest** (adaptive formalisation); core **known** | Shlegeris, "Win/continue/lose scenarios and execute/replace/audit protocols" (Redwood blog, Nov 2024; verified to exist); LASR App. B.6; GAC 2409.07985; Ctrl-Z 2504.10374 |
| VCVio refinement | Faithful for the catastrophe event. The availability event is absent. | **modest** (artifact over classical content) | VCVio eprint 2024/1819 (verified); SSProve eprint 2021/397 (not re-fetched); Greenblatt et al. 2312.06942 (verified) |

**Overall verdict.** The Lean statements are sound and their plain-English rows are accurate. The package remains classical and modest formal infrastructure with quantitative negative results. Significance for AI control is unestablished. It exposes assumptions L, r, α and the scaffold, and gives quantitative reasons to stratify honeypots, to track the honest miss rate, and to avoid deferral without incrimination, all of which were known informally. STACK.md needs minor edits (I3–I14) and one positioning edit (I1). The satellite documents need the I2 sweep. Nothing earns "apparently open".

---

## Appendix: scratch checks (`<scratch>/`)

| Script | What it checks | Result |
|---|---|---|
| `defer.py` | `catD ≤ finiteCap` with the optimal history-dependent generator; floor bridge with random services (1500 instances) | 0 violations; tight in 1447 |
| `defer_reach.py` | Bridge with the floor only on `Reach` states (600 instances, 589 with unreachable low states) | 0 violations |
| `defer_ex.py` | UMDEFER (d) example (n_h = 10⁴, n_s = 5, ε = 10⁻³) | θ_min = 0.3165; coarse H/ε = 0.600 |
| `useful.py` | UMUSE Witness numbers; (a), (c'), (P) identity (300 random instances); Cantelli (20000 cells); T3c (5000); F* and AOQL ratio table | exact match; 0 failures |
| `lower_adapt.py`, `lower_adapt2.py`, `lower_adapt3.py` | Exact optimal adaptive tester by DP; Reviewer A's counterexample; adaptive vs the Lean curve; adaptive-converse survival ≥ 1 − t·n/k (133 cells) | counterexample confirmed (survival ≈ 0 against 3/8); formula beaten at best t by 1.3–1.7× in the listed cells; no violation of the adaptive converse |
