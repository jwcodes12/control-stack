# English corrections proposed by the one-to-one blind checks: owner decision list

**Status of this file.** Model-written and model-reviewed; there has been **no independent human review**. Everything below is a set of **PROPOSED** corrections for the owner to accept or reject. **NONE has been applied to the English part files** (nothing under `docs/lean-english/` other than this new file was touched). Quoted replacement sentences are copied from the "## Corrections to the English" sections of `blind-*/RESULTS.md` (and, for the old G0 pass, `RESULTS.md`); a quote that begins with a bold label or "Replace ..." instruction keeps the source's own framing. Claim references are `batch#N`, where N is the claim's number inside that batch as listed in [BLIND-INDEX.md](BLIND-INDEX.md); the Lean name is the one in that index (namespace `ControlStack.` omitted).

## 1. Summary by verdict class

Counts cover the 160 claims actually run (BLIND-INDEX.md totals: EQUIVALENT 151, ENGLISH_STRONGER 4, ENGLISH_WEAKER 3, UNDECIDED 2).

| Class | Claims | Count | How derived |
|---|---:|---:|---|
| EQUIVALENT, no correction proposed | 151 minus the 73 below | **78** | **Approximate.** 151 minus the claims named in any batch's "Corrections to the English" section. A claim mentioned only in a "Does NOT say" audit or "Ambiguities exposed" list is not counted as corrected. |
| EQUIVALENT, correction proposed | see sections 3B and 4 | **73** | Tallied by hand from the corrections sections: 9 in section 3B (the source says the English prose is wrong, over-claims, or needs a "substantive" fix) plus 64 in section 4 (wording-only). The 9/64 split is my reading of the sources and is a judgement call; the 73 total is the more reliable figure. |
| ENGLISH_STRONGER | g1n2#10, g2n1#2, g2n2#4, v1#1 | **4** | Exact (matches BLIND-INDEX.md). |
| ENGLISH_WEAKER | g3n1#4, g3n1#9, g5n1#7 | **3** | Exact. |
| UNDECIDED | g6n2#4, g6n2#8 | **2** | Exact. |
| **Total run** | | **160** | 78 + 73 + 4 + 3 + 2 = 160. |

Other tallies: 82 claims have at least one proposed correction (73 EQUIVALENT-verdict plus the 9 non-EQUIVALENT ones). Section 2 covers the older G0 pass.

Meaning of the non-EQUIVALENT verdicts (per the sources): ENGLISH_STRONGER means the frozen blind back-translation of the English asserts the conclusion for strictly more instances or with a stronger output contract than the original Lean; ENGLISH_WEAKER means the Lean original implies the back-translation but not conversely; UNDECIDED means no reverse implication was certified. None of these is a claim that the Lean is false or that the deployed system misbehaves.

## 2. Older G0 pass (RESULTS.md): superseded, listed for completeness

`RESULTS.md` (26 deployment-stack blocks, not blind) has a "Corrections to the English" section with seven bullets for G0 claims 1, 2, 3, 5, 12, 16 and 20 (Accepted, exclusive_sink, database_custody, agent_not_receiver_uid, accepted_no_avoided_path, deployment_broker_safe, halted_absorbing). The source itself says those old verdicts are **STALE** and that the English for claims 1, 2, 3, 5, 12, 16, 20, 23 was reworded after those inputs. Blind-v1 then re-checked those eight (7 EQUIVALENT, claim 1 ENGLISH_STRONGER) and the corrections below in section 3A (v1#1) and section 4 (v1#5, v1#12) are the current ones. Two old bullets are not repeated elsewhere and are kept here as the owner may want them:

- **deployment_broker_safe (G0 claim 16):** "The published nonce count is **at most** the cap," with no duplicates and used approvals. Exactly filling the cap is permitted.
- **halted_absorbing (G0 claim 20):** if reproducing the original displayed conclusion, say "the halted flag remains true and the release count is unchanged." Full-state identity is additionally derivable in this model, as the gated comparison proves, but is not the displayed theorem statement.

(Both were re-checked EQUIVALENT in blind-v1, claims 16 and 20, which listed "no substantive replacement" for them.)

## 3A. Substantive corrections: claims with a non-EQUIVALENT verdict (9)

### v1#1 `Deployment.Accepted` (blind-v1): ENGLISH_STRONGER
- **English says:** the identity check is over "distinct nodes" (equal UIDs hold only for the broker/receiver pair).
- **Lean proves:** the original identity check is guarded by `a.id ≠ b.id`, so it imposes nothing on two entries with the same id. The frozen blind reading guards by `a ≠ b` (record inequality). Gate: Back -> Orig proved; a model instance (`collision`, a reviewer and approver sharing id 6 and UID 23703) is accepted by the original and refuted by the Back. Model counterexample only, not evidence about a deployed system.
- **Proposed replacements (v1, corrections 1 to 5):**
  > **Claim 1, identities — replace "distinct nodes" with:** "For any two entries in `d.nodes` whose **IDs differ**, their UID fields are equal if and only if their IDs are the broker and receiver IDs, in either order. Entries with the same ID are exempt from this identity check."

  > **Claim 1, role counts/topology — replace "There are exactly six nodes" with:** "The node list has length six, with two role-0 entries and one entry for each of roles 1–4; the stated flag and broker/receiver ID equivalences also hold. These checks do not require all six node IDs to be distinct." Replace "fixes the topology to exactly six nodes" with "fixes the node-list length and role counts to this six-entry, two-agent slice."

  > **Claim 1, writers — replace the set/list wording with:** "Counting list entries, the sources of write edges into the sink form exactly the singleton list `[receiver]`. There are exactly two write-edge entries into the database, including a broker-source entry and a receiver-source entry; their list order is irrelevant."

  > **Claim 1, Does NOT say (a) — replace the mediation sentence with:** "The avoided-path computation stops when an edge would land on the broker or receiver. Listed edges still undergo the basic and applicable writer checks; the broker's and receiver's actual forwarding behavior is outside this predicate."

  > **Claim 1, decidability note — replace "its decidability instance is by infer_instance" with:** "Each finite check group is decidable; the `Accepted` instance uses `decidable_of_iff` to assemble those checks into the structure predicate."

### g1n2#10 `SC07Exfil.sc07_fixed_budget` (blind-g1n2): ENGLISH_STRONGER
- **English says:** (traffic-law premise) a schedule-independent certificate with row mass bounded, allowing mass <= 1.
- **Lean proves:** the original requires the certificate row mass to **equal one**. Same payoff and bound otherwise. Strictness witness: N=2, B=1, r=1/2, sigma(g,a)=1/4 (row mass 1/2); a normalized original instance is also witnessed. The original `hrec` constrains the non-caught marginal; it does not assert sigma equals the full action marginal including caught branches.
- **Proposed replacement:**
  > **Claim 10, missing normalization and traffic-law interpretation.** Replace the traffic-law premise with: "There is a schedule-independent certificate sigma on traffic decisions at each visible history g, with non-negative entries and sum_a sigma(g,a)=1. For every size-B audit schedule and every full history, the non-caught marginal for action a is bounded by sigma(g,a) times 1-r when that action sends traffic in an audited window, and by sigma(g,a) otherwise." The original requires equality to one, not merely an upper bound. Its `hrec` constrains the non-caught marginal; it does not separately assert that sigma equals the complete action marginal of K, including caught branches.

### g2n1#2 `SC08.safe_of_sound` (blind-g2n1): ENGLISH_STRONGER
- **English says:** the same safety statement from "any initial files with no runs", with either initial halted flag admitted.
- **Lean proves:** the original declaration fixes the initial state as `⟨files, [], false⟩` (halted = false). The Back quantifies over arbitrary `halted`. "ENGLISH_STRONGER here means strictly broader parameter/hypothesis coverage"; it is not a counterexample to safety. No original conclusion exists for the initial-`true` case.
- **Proposed replacement:**
  > **Claim 2 — initial state.** Replace "The same safety statement … from any initial files with no runs" and its hypothesis description with: "For any environment and checks with digest checking and script checking on, start with arbitrary files, an empty run list, and the halted flag set to false. After any trace, every recorded run has an allowlisted program digest and every listed-interpreter run has an allowlisted script digest. The noexec and halt switches may have either value." This matches the named original declaration. If either initial halted flag is intended, name and prove that extension separately.

### g2n2#4 `AuthInstances.forged12_spawns_without_auth` (blind-g2n2): ENGLISH_STRONGER
- **English says:** with the forged trace and no authentication, both operations do nothing / guarded state equals init (whole-state equality).
- **Lean proves:** original's output predicate is `unguarded.live.length = 2 ∧ guarded.live = []`; Back's is `unguarded.live.length = 2 ∧ guarded = SC12.init`. Back -> Orig certified; the converse fails at the observation level (a guarded state `{ SC12.init with halted := true }`), but that counterexample is not claimed reachable. The fixed-trace witness confirms the actual guarded result is init, so the English is not false of the concrete run; it states a stronger output contract.
- **Proposed replacement:**
  > **Claim 4 — match the original's observed output.** Replace its Says sentence with: "With admin list [9], full checks and initial state SC12.init, run the fixed trace in which issuer 1 requests start 9 5 and then spawn 5 6 true 0. With the authentication claim function constantly none, the final live list has length two. With claim12, the final live list is empty." The whole-state equality in the back is also true for this trace, as the gated Witness shows, but it is stronger than the original's live-list conclusion. If John wants to retain "both operations do nothing," identify it as an additional fact about this concrete run rather than the exact stated conclusion of forged12_spawns_without_auth.

### g3n1#4 `AuthInstances.forged15_merges_without_auth` (blind-g3n1): ENGLISH_WEAKER
- **English says:** (Says sentence) the merged log contains a change with id 0 under the forged trace.
- **Lean proves:** the original gives the **exact** one-element merged log (id 0, author 1, content 7, paths `[5]`, declared paths `[5]`). Orig -> Back only; membership of id 0 does not determine content, author, paths or log cardinality. Checked (claim15) empty-log conclusion identical. Strictness counterexample is a log-level observation, not a claim about the fixed trace's output.
- **Proposed replacement:**
  > **Claim 4 — replace the Says sentence with:** "In `E0`, run exactly `[(1, propose 1 0 7 [5] [5]), (1, review 2 0 false), (1, runCI 0), (1, merge 0)]` from the empty state under `full`. With a claim function that always returns `none`, the final merged log is exactly the one-element list whose change has id 0, author 1, content 7, paths `[5]` and declared paths `[5]`. With `claim15`, the final merged log is empty." This states the original exact-list conclusion and fills in the ordinary-review flag and declared paths. The existing limitations about this one trace and trusted issuer identity can remain.

### g3n1#9 `SC16Disjoint.overlap_reviewer_is_agent` (blind-g3n1): ENGLISH_WEAKER
- **English says:** the deployment log has an entry at target 5 with content 7 (existence).
- **Lean proves:** exact deployment log `[⟨0,5,7⟩]` (nonce 0, singleton cardinality). Orig -> Back only; existence omits nonce 0 and cardinality. Review conclusions identical.
- **Proposed replacement:**
  > **Claim 9 — replace the Says sentence with:** "With `Rov` (agents `[1,2]`, reviewers `[2]`, approvers `[3]`, admins `[4]`) and the identity hash, run exactly `[stage 1 7, review 2 7, approve 3 0 7 5 0, deploy 1 0 5 7]` from the empty state under `full`. The deployment log is exactly the one-element list `[(nonce 0, target 5, content 7)]`, the review log is nonempty, and every recorded reviewer belongs to `Rov.agents`." This fixes nonce, slot and deploy caller and retains the original exact deployment-log conclusion. It deliberately leaves the review-log conclusion at nonempty/all-agent, as in the source theorem.

### g5n1#7 `EvalIntegrityAdaptive.sc21_adaptive_recall` (blind-g5n1): ENGLISH_WEAKER
- **English says:** a "conditional recall" kernel condition reading the premise as a conditional detection probability.
- **Lean proves:** the original constrains only the per-history joint **no-catch mass**, allowing arbitrary already-caught mass subject to the total-mass bound. The Back adds a non-redundant full-choice marginal premise, so Orig -> Back by restricting the rule's domain; conclusions equivalent on the common domain. Strictness certificate: N=2, B=k=1, r=1/2, hidden type Unit, kernel assigning probability 1 to "corrupt and caught". Does not refute the original survival bound.
- **Proposed replacements:**
  > **Claim 7 — replace the "same kernel conditions" passage:** "Let the hidden component have a finite type. The kernel is nonnegative and has total mass at most 1 at every history for each allowed sample. A reference rule σ is a distribution at every visible history. Assume that the joint mass of choice a and no catch is at most σ(visible history)(a), multiplied by 1−r when the current round is sampled and a is corruption. Then the uniformly averaged probability mass of at least k corruptions and no catches is at most `hypMiss N B k r`. Unlike claim 6, this theorem requires no bound on the full choice marginal summed over both catch flags."

  > **Claim 7 — replace the opening conditional-recall wording:** "The recall assumption is the stated per-history joint no-catch mass inequality. Reading r as an actual conditional detection probability requires an additional correspondence between σ and the kernel's choice probabilities."

### g6n2#4 `SC26.halt_freezes` (blind-g6n2): UNDECIDED
- **English says:** the "set" of in-flight messages is unchanged after halt; an authentic admin halt is implied as a hypothesis.
- **Lean proves:** the original gives exact **list** equality of `net` (order and multiplicity). Orig -> Back (set equality) is certified; the converse is not (diagnostic symbolic states `net = [(0,tx1)]` vs `[(0,tx1),(0,tx1)]`), and the source stresses this is not a counterexample to any legal run, so neither DIFFERENT nor ENGLISH_WEAKER is certified. The theorem assumes only the halted flag, not an admin-halt history.
- **Proposed replacement:**
  > **Claim 4 — replace the main sentence:** "For any starting state `s` with `s.halted = true`, after any legal continuation under the deployed checks, the entire ordered message list `net` is exactly equal to `s.net`, including multiplicities. Every final bank entry belongs to `s.bank` or `s.net`. Previously transmitted messages may still be recorded in the bank." This matches the original list equality rather than only its set-valued consequence. Remove the suggestion that an authentic admin halt is a formal hypothesis of this theorem: the theorem assumes the flag, without requiring a history that explains it.

### g6n2#8 `SC26Authenticated.forged_approval_pays_without_auth` (blind-g6n2): UNDECIDED
- **English says:** (Back) the bank holds the entry (membership) and no approver issued **anything** in the trace.
- **Lean proves:** original gives the exact singleton bank `[(0, tx1)]` and excludes **one exact self-issued approval** (`approve a 0 tx1` for `a` in approvers). Orig -> Back certified; the fixed-trace converse is not (a duplicated-bank observation satisfies Back and fails Orig; a script `[(2, deliver 0)]` satisfies Orig's conjunct but fails Back's). On the actual five-operation trace both hold, but the source declines to turn that into an iff.
- **Proposed replacement:**
  > **Claim 8 — replace the main sentence:** "For the specified five-operation trace, the run with identity checking disabled has bank list exactly `[(0, tx1)]`; the trace contains no `approve a 0 tx1` issued by that same `a` for any `a` in the approvers list; and the identity-checked run has an empty bank." Add separately, if desired: "In this particular trace every issuer is agent 1, so no approver issues any operation." The latter is an additional true fact about the trace, stronger than the provenance conjunct in the original declaration. Membership alone omits the original's exact singleton-bank conclusion.

## 3B. Substantive corrections: EQUIVALENT-verdict claims whose English prose itself is wrong or over-claims (9)

The principal Lean statement matches; the sources say the accompanying English sentence needs a real fix.

### g0n2#1 `Deployment.indexed_receipts_sound`
- **English says:** "A shorter list also passes."
- **Lean/witness:** only a valid prefix (first nine receipts) passes; deleting the middle release or the denial does not.
  > Replace with: **"A valid prefix can also pass: in this transcript the first nine receipts are accepted. Arbitrary deletions need not pass, because the remaining state ids may no longer form a chain."**

### g0n2#4 `TrustedBroker.committed_nonce_unusable`
- **English says:** a different nonce for the same digest can be approved and released again, "limited only by lease and global budget". Source: "The parenthetical is wrong."
  > Replace with: **"This theorem does not rule out another release of the same digest under a different nonce. Such a release still has to satisfy the entire `Allowed` guard, including a matching unused approval, the role and expiry checks, artifact and review checks, and lease and global budgets."** It is permission left open by this result, not an unconditional existence claim or a sink guarantee.

### g1a#4 `SC05.zero_dependence_is_blind`
- Source verdict row: "Partly — (a), (c) yes; (b) needs correction". The "Does NOT say" (b) wrongly excluded a bit alphabet: `M = Bool` is permitted (blind rate 1/2).
  > **Claim 4 — replace "Does NOT say" (b):** "It applies to a uniformly random secret in any finite secret alphabet, including a bit, for which the blind success rate is 1/2. It does not give the same blind rate for a nonuniform secret, and it does not model whether a decoded value causes an action to execute."

### g1n2#5 `ChannelInstances.rekey_epoch`
- **English says:** any secret-carrying persistent cache necessarily violates the premise (categorical); source: "too broad".
  > **Claim 5, persistent state and the other rounds.** Replace the categorical cache claim with: "The bound includes all n rounds provided the same secret-independent certificate has mass at most one outside the window. Persistent hidden state violates this premise only when its effect on visible outputs prevents such a certificate; hidden correlation by itself does not force a violation." Replace "whatever happens in the other rounds" with "for any other-round kernels satisfying the outside-window domination and mass premises."

### g1n2#6 `ChannelInstances.log_channel`
- **English says:** "if a free-text field exists the bound is void" (overgeneralization).
  > **Claim 6, free-text qualification.** Replace "if a free-text field exists the bound is void" with: "A visible field outside the stated finite record alphabet must be counted or certified separately. A field large enough to carry the entire secret can permit exact recovery with probability one." The neighboring theorem is a full-secret-capacity example, not a claim about every field described as free text.

### g1n2#7 `ChannelInstances.canonical_seq`
- **English says:** "Does NOT say" (b) excludes m = 1; source: "incorrectly excludes m=1".
  > **Claim 7, Does NOT say (b).** Replace it with: "The bound is for any fixed number m of items, including m=1. It does not cover unbounded or observation-dependent sequence lengths without modeling those observations." Replace the bit-capacity gloss in (c) with: "The formal conclusion concerns exact recovery. For Kc ≥ 1, the number of possible fixed-length visible sequences is Kc^m, whose log2 cardinality is m log2 Kc."

### g4n1#1 `SC18.sc18_safe`
- **English says:** the protection list includes "fail-closed on sink outage". Source witness (claim 7): a release happens with `sinkUp = false`.
  > **Claim 1, protection-list wording: replace "fail-closed on sink outage" with:** "no fail-open exception for unacknowledged requests during a sink outage; a watchdog that halts after more than T silent model ticks; and a halt check." Add: "A sink outage does not immediately forbid releases: a previously acknowledged request may be released before the watchdog halts the node."

### g5n2#12 `MonitorCollusion.phase_learning`
- **English says:** repeatedly calls the formal scalar a probability while noting Lean imposes no kernel mass bound. Source witness: scalar is **3/2 > 1** (kernel and certificate of 3, L = 3, m = 1). The inequality remains correct.
  > **Claim 12 — replace the probability wording under the existing formal hypotheses:** "For finite hidden-state and visible-output sets, nonnegative round kernels dominated at every history by a phase-independent certificate of mass at most L, with L nonnegative, give a uniform-prior correct-guess weighted mass at most L^m/2. If every round kernel is also a probability distribution, this weighted mass is the probability of a correct final guess."

### g6n3#6 `SC26LossyHalt.tagged_rounds`
- Source calls this "a substantive correction": the English's auxiliary strict-weakening assertion (per-copy premise vs drop-free `Delivers`) is wrong as stated; the two raw predicates are not ordered by implication. The principal theorem and Back remain equivalent.
  > **Claim 6 — replace the strict-weakening sentence.** "The per-copy premise allows some delivery traces with earlier drops that the drop-free `Delivers` premise excludes; `per_copy_weaker` supplies one such example. The two raw predicates are not ordered by implication: `Delivers` can hold even when the intent is already acknowledged and this recovery emits no new tagged copy."

  The source also gives (wording): "A new transmission produced by `transmit` or `recover` receives a fresh tag. Network duplication preserves the tag, and a drop removes one occurrence. Per-copy delivery requires an occurrence with the chosen tag to remain available at the indexed bank-processing step."

## 4. Wording-only clarifications (64 claims, all EQUIVALENT verdicts)

Each row is a short summary; the full replacement sentence is in the cited batch's `RESULTS.md`, section "Corrections to the English". Where a row quotes, the quote is verbatim. The source files describe none of these as changing a verdict.

| Claim | Lean name | Batch | Proposed change (summary or quote) |
|---|---|---|---|
| #5 | Deployment.gate_contract | g0n1 | Cap caveat: replace "It says nothing about spend cap here" with "The acceptability predicate has no cap clause. The invariant conjunct includes `spent ≤ cap`, so the theorem does carry a spending-cap guarantee through that invariant."; also append-only wording (final bank extends initial; prefix conclusion vacuous between intermediate states) |
| #6 | Deployment.broker_contract | g0n1 | Cap reference: "`Safe t` bounds spending by the cap stored in `t`; every model step preserves that cap ..." |
| #8 | Deployment.accepted_path_safety_monotone | g0n1 | State that an `AvoidedPath` may have zero steps; steps follow any listed edge whose target is neither broker nor receiver, no filter on authority/write/unknown flags |
| #9 | Deployment.path_edge_subset | g0n1 | Same avoided-path wording; under edge inclusion and matching broker/receiver IDs every such path in the smaller graph is one in the larger |
| #10 | Deployment.requested_monotonicity_counterexample | g0n1 | Kind: concrete counterexample to downward monotonicity of acceptance, produced by deleting required database-write edges; not evidence the reduced graph gains a bypass path |
| #6 | Deployment.TranscriptReplay.final_safe | g0n2 | Kind label: concrete-instance theorem derived from a checked model trace; `s10` is `Safe` via `runtime_trace` + `trace_preserves`; spent = cap = 2 are separate facts |
| #7 | Deployment.TranscriptReplay.replay_was_not_allowed | g0n2 | "This is a direct instance of `committed_nonce_unusable`; the required equality between the two request nonces is proved by `rfl`." |
| #8 | Deployment.TranscriptReplay.omitted_tail_is_accepted | g0n2 | "Both the full transcript and this nine-receipt prefix return acceptance. Acceptance alone therefore does not establish that all real events were recorded." |
| #3 | SC05.cap_does_not_prevent | g1a | Make the 65536-value alphabet and identity observation explicit; deterministic code suffices, so the cap does not preclude conveying a bit |
| #9 | SC07Refinement.concrete_safe | g1a | Accounting description: halted/non-allowlisted packets are dropped without incrementing `consumed`; each window's forwarded payload is at most Q - 1 |
| #2 | GatewayCore.core_bound | g1n2 | Transition description: blanking happens only before the first close; first close freezes the delivered view; if no close occurs the final view is delivered |
| #3 | Covert.covert_bound_lifetime | g1n2 | Independence wording: success expression averages over a uniform secret independently of the shared seed; the decoder's view tuple may depend on the secret |
| #4 | ChannelInstances.sc02_accumulated | g1n2 | Probability/kernel wording: only non-negativity and certificate domination required; kernel mass may be below or above one (witness gains mass) |
| #1 | SC07Exfil.expected_leak_le | g1n3 | Catch parameter applied only when the quota-capped window carries positive traffic; zero-count windows contribute no catch factor |
| #2 | SC07Exfil.observable_schedule_exfil | g1n3 | Negative control: the plan evades the schedule because traffic windows have catch probability zero, so the positive catch-lower-bound premise is unavailable |
| #3 | SC07Exfil.datacenter_example | g1n3 | Whole-plan survival statement (through every traffic-bearing window), not survival only until first completion |
| #5 | SC07Liveness.exfil_needs_windows | g1n3 | "At least ceil(S/q) windows have been opened, counting the initial window and allowing empty windows." No elapsed-time or audit-probability bound from this alone |
| #7 | SC07Refinement.concrete_wire_lt | g1n3 | Model assumptions: `runC` from `cinit`, natural lengths, `quotaRule = true` and Q > 0; deployment correspondence is separate |
| #9 | SC07Refinement.sink_within_quota | g1n3 | Sink premise is an input: measured sink count at most forwarded payload bytes of window w; gateway model does not establish TCP delivery |
| #1 | SC08.sc08_safe | g2n1 | Missing interpreter entry: binary treated as non-interpreter, script argument unchecked, run recorded with no script |
| #5 | SC09.spawn_attenuates | g2n1 | Sub-collection: every capability in a spawned process's list occurs in the parent's list just before the spawn; membership inclusion, not counts or order |
| #7 | SC10.sc10_safe | g2n1 | Decision records store a policy-version index and value at it; writer on admin list; index + 1 equals store length at decision time |
| #10 | SC12.sc12_safe | g2n1 | Claimed session labels apply to registered spawns; bypass attempts carry parent, child id and job flag but no claimed session label |
| #3 | AuthInstances.sc12_safe_authenticated | g2n2 | Specify the start state SC12.init (empty active/ended/live/firing lists, not halted) and the issuer-number drop rule |
| #5 | AuditDispatch.trace_safe | g2n2 | Remove temporal attribution: the theorem says every final effect id appears in the audit list, not a before/after order of writes |
| #6 | SC16.sc16_reviewed_content | g3n1 | "The reviewer differs from the stager id stored in that review record, which comes from the first content-store entry whose hash matches the reviewed digest." |
| #8 | SC16Disjoint.sc16_safe_disjoint | g3n1 | Same stager-phrase clarification; also keep the conclusion that reviewer and approver are not members of `R.agents` |
| #2 | SC16Refinement.concrete_safe | g3n2 | Nonce scope: `Good` concerns deployment nonces, not a blanket uniqueness of every nonce-bearing field |
| #4 | SC17.sc17_safe | g3n2 | List semantics: arbitrary initial grant lists and ceiling predicate; apply record has equal live/desired lists, passes ceiling, has final-log approval; proposal ids no repeats |
| #5 | SC17.reconcile_restores | g3n2 | "From any state with `halted = false`, one reconcile with the deployed checks makes the model's live grant list exactly equal to its desired grant list." |
| #7 | SC17Drift.drift_bounded | g3n2 | Unit counted: at most `d * W` live entries absent from desired, repeated entries counted separately |
| #8 | SC17Drift.drift_lifetime | g3n2 | Ghost-record scope: every `(grant, birthTick)` in the final ghost list has `clock - birthTick < W` |
| #9 | AuthInstances.sc17_safe_authenticated | g3n2 | Concrete representation: U as a finite list of adversary issuer ids disjoint from reviewers; no cryptographic issuer-source theorem |
| #3 | SC18.halt_freezes | g4n1 | Replace "Does NOT say" (1): halted ticks leave the whole state unchanged so the clock does not advance; sink-down/restore can still change `sinkUp` |
| #4 | AuthInstances.sc18_safe_authenticated | g4n1 | "every release's request id was in the trusted log at release time" (not the record) |
| #6 | SC18Liveness.honest_release | g4n1 | Append: an id already released remains in the list; no new release or repair of an earlier record required |
| #8 | SC18Liveness.silent_ticks_halt | g4n1 | "After exactly n tick operations" counts trace operations; after the watchdog halts further ticks are ignored, so the clock need not advance by n |
| #10 | SC18Liveness.Resume.resume_progress | g4n1 | Replace "Does NOT say" (3): only membership in final released-id list; `resume_safe` gives log/timing guarantees only for runs from `init`; also the "already released" append |
| #1 | SC18Refinement.concrete_safe | g4n2 | Make the acknowledgement prefix and count explicit (`r.llen`, `r.lastAck`); the count clause is redundant for these runs, not for arbitrary states |
| #2 | SC18Refinement.concrete_durable | g4n2 | Use the same explicit description of `r.lastAck` to avoid confusing its historical value with the final acknowledgement clock |
| #3 | SC19.sc19_safe | g4n2 | Distinguish safety predicate from verifier provenance: `Good` stores a verified index, not a record naming its issuer |
| #5 | AuthInstances.sc19_safe_authenticated | g4n2 | Specify U as a list interpreted through membership, disjoint from trusted roles; duplicates/order irrelevant |
| #7 | SC20.sc20_safe | g4n2 | State the final-state digest predicate precisely (registry digest equals `h` of content, or a promotion record with a listed reviewer) |
| #9 | AuthInstances.sc20_safe_authenticated | g4n2 | Same U-representation precision as claim 5 |
| #10 | AuthInstances.forged20_trains_without_auth | g4n2 | Make `E0` self-contained: allowlist [50], reviewers [2], admin [9], `h` identity, registry `some 7` at id 0; forged trace records exactly `[[(1, 66)]]`, claim-checked run records no run |
| #2 | EvalIntegrity.sc21_undetected_prob | g5n1 | Probability reading needs B <= N (uniform sample among size-B subsets): ratio `C(N−k,B)/C(N,B)`; for B > N the family is empty and the ratio is 0 by real division |
| #6 | EvalIntegrityAdaptive.sc21_adaptive_content | g5n1 | State finite scope: hidden component from a finite type (`[Fintype Y]`, `Y : Type`); infinite alphabets are not covered |
| #8 | EvalIntegrity.sc22_unreplicated_misreport | g5n1 | Same B <= N probability qualification as claim 2 |
| #2 | SC23Isolation.w1_impossible | g5n2 | Make the concrete operation explicit (`act 5 [1] 0`: tool 5, planner-value index 1, nonce 0); replace the "general laundering impossibility" parenthetical with a pointer to the separate noninterference theorem |
| #5 | SC23IsolationV2.w1_impossible_v2 | g5n2 | Make the concrete operation explicit (`act 5 [1] 0`) |
| #11 | MonitorCollusion.canon_channel | g5n2 | Replace the "i.e. ... bits" sentence: exact-decoding probability is at most K divided by number of messages; no information-measure bound in bits is proved; also state the shared finite seed convention |
| #2 | SC25.expired_never_executes | g6n1 | Expiry provenance is not a hypothesis: "For any starting state, if an operation id is in its expired list and absent from its execution-id list, every continuation under the deployed configuration keeps that id absent from the execution-id list." |
| #3 | SC25.halt_freezes | g6n1 | Only the starting halted flag is assumed; in runs from the initial state it first becomes true only via an admin halt operation |
| #5 | SC25Content.digest_only_executes_unaudited | g6n1 | Specify the witness (agents 1,2,3,4; operation 0, content 7, declared false; amend to 50) and exact logs: execution-content `[50]`, ghost-audit `[(0, 7, PASS, 2)]` |
| #7 | AuthInstances.forged25_executes_without_auth | g6n1 | "Ignoring claimed identities, the final execution-id list is exactly [0]. Applying the claim25 authentication guard instead, the final execution list is empty." |
| #8 | SC25Refinement.concrete_safe | g6n1 | Simulation summary: an executing concrete fire is check then fire; a blocked fire is no abstract operations; expire is timeout; restart is no operations |
| #10 | SC26.sc26_safe | g6n1 | Replace "Does NOT say" (3): the theorem does not establish that a real bank authenticates the gate or deduplicates request ids; those are modeled by `bankAuth`/`bankDedup`; call the payload field a "memo-digest field" |
| #6 | SC26Refinement.concrete_halt | g6n2 | Tighten unsent-intent qualification: "After halt, no new entry absent from both the initial bank and the initial wire can appear in the bank. Recovery and transmit cannot add to the wire." |
| #10 | SC26Liveness.honest_progress | g6n2 | Carry the listed premise in the main sentence (invariant-satisfying, non-halted state; unreserved request; non-requester approval; cap headroom); keep the note that the proof does not use unreservedness |
| #1 | SC26Liveness.progress_interleaved | g6n3 | The designated honest step is `execute c k` for any caller identity `c`; the model's execute transition ignores that identity, so `c` need not be the requester |
| #3 | SC26LossyLiveness.lossy_safe | g6n3 | Optionally spell out all of `Good` (bank entries match reserved requests with exact non-requester approvals; unique keys; total within cap) |
| #4 | SC26LossyLiveness.lossy_rounds | g6n3 | Make the suffix explicit: some round's post-list is `nd ++ [bankProcess k] ++ rest` with `nd` containing no drop and `rest` an arbitrary legal suffix |
| #5 | Deployment.agent_not_receiver_uid | v1 | "Every agent node's UID field differs from the UID field of any listed receiver node; interpreting that as a fact about process identities requires faithful UID extraction." |
| #12 | Deployment.accepted_no_avoided_path | v1 | Add: "A zero-step path from the starting ID to itself also counts." |

## 5. Caveats

- **Not yet run:** claims in batches **g7n1 and g7n2 (23 claims)** have not been run through the one-to-one blind process, so this document says nothing about them.
- **All verdicts are model-generated.** Each verdict comes from a Codex-written (Phase A) blind back-translation of the English, compared with the original Lean and gate-checked by the deterministic gate in a Phase B pass. Gate receipts (`*.receipt.json`, `*.witness.receipt.json`, statement/proof files) sit under each batch directory (`blind-<batch>/`); BLIND-INDEX.md's `re-gated` column says the orchestrator re-ran the batch's gates (`n/a` for blind-g1a and blind-v1, verified by hand per `blind-v1/SUMMARY.md`). No independent human has reviewed any of it.
- **A verdict is about the stated model formula,** not the real deployment, world assumptions, or the whole narrative (per `RESULTS.md`). EQUIVALENT means the frozen back-translation and the original Lean agree pointwise under the same hypotheses; it does not certify every informal sentence of the English, which is why sections 3B and 4 exist.
- **Counts:** the 78 "no correction" figure and the 9/64 split between sections 3B and 4 are approximate (see section 1). The per-class totals for non-EQUIVALENT verdicts and the 160 total are exact.
- **Nothing was applied.** No English part file was edited; each correction above remains a proposal for the owner.
