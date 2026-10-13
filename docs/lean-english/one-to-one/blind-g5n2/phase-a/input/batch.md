# English statements under test

### Claim 1
## `ControlStack.SC23Isolation.noninterference`

- **Says (plain English):** Take two lists of operations that are identical except that some tool-result operations carry different content values (position by position, the lists have the same length and the same operations; only the contents of tool results differ). Run both from the empty state under the full checks. Then the two final states agree on: the list of user inputs, the planner's list of values (trusted values and handle indices), the number of quarantined values, and the halted flag. So injected content cannot change anything the planner holds.
- **Under these hypotheses:** The environment (users, admins, sensitive tools, the planner program `plan`, the quarantined transformer `qf`) is arbitrary but identical for both runs. The planner's derivation is a function of the trusted user inputs and a step counter only (it cannot inspect handles or content), tool results enter a separate quarantine and the planner receives only an index, and the operation that would let the planner read quarantine content is a no-op in the full configuration. World assumptions: the real planner really is restricted to its own state (no side channel from quarantined processing into the planner, e.g. shared context, logs or error messages); user input is authentic (in this version `userInput` has no caller).
- **Does NOT say:** That the executed action list is the same across the two runs: resolved argument values of quarantined handles do differ, and the theorem does not compare them; that the planner's own program is good; anything about the confirmation channel.
- **Kind:** general theorem (a relational invariant over pairs of traces; structural isolation is a property of the model's types).

### Claim 2
## `ControlStack.SC23Isolation.w1_impossible`

- **Says (plain English):** For one concrete environment (one user with id 1, admin 9, sensitive tool 5, a planner that returns 40 plus the number of user inputs plus the step index, a quarantined transformer that adds 1): the trace "a tool result with content 66, then a planner derivation, then a sensitive action on the derived value with no confirmation" executes exactly the same actions as the trace with content 0 in place of 66, and the single executed action has argument value 41, marked untainted. So the review's laundering trace (injected 66 reaching the sensitive tool as trusted) does not occur.
- **Under these hypotheses:** The fixed example environment `E0`, full checks, one specific trace. Nothing is quantified over environments or traces.
- **Does NOT say:** That laundering is impossible in general (that is `noninterference`); that this specific planner is sensible. It is a decided finite computation.
- **Kind:** finite computation (decide/native), a concrete instance of the general noninterference theorem.

### Claim 3
## `ControlStack.SC23Isolation.sc23_isolated_safe`

- **Says (plain English):** After any list of operations from the empty state, every executed action on a sensitive tool whose arguments include at least one quarantined handle (flagged "tainted" in the log) has a recorded user confirmation with the same tool, the same nonce as the one used, exactly the resolved argument values, and made by a caller on the user list.
- **Under these hypotheses:** Full checks (taint check on, isolation on, halt check on). The environment is arbitrary. Confirmations may only be added by users and each nonce is added once. World assumptions: confirmations come from real users and the UI shows exact values; planner isolation holds as in `noninterference`.
- **Does NOT say:** That a confirmation backs only one action: this model has no used-nonce list, so one confirmation can approve the same tool-and-values action repeatedly (the first model, `SC23.sc23_safe`, does track one-use). That an action with untainted arguments is safe; that the planner's values are correct; anything about non-sensitive tools. Note that the combination with `noninterference` (as the docstring says) is what excludes laundering; this theorem alone is about handle arguments.
- **Kind:** general theorem (inductive invariant).

### Claim 4
## `ControlStack.SC23IsolationV2.noninterference_authed`

- **Says (plain English):** Each operation now comes with its true issuer (a number). An operation that claims an identity (user input, confirm, halt) is applied only if the claimed identity equals the issuer; otherwise it is ignored. Take two traces of issued operations with the same issuers at each position and the same operations except for tool-result contents. Then the final states agree on user inputs, the planner's values, the quarantine size and the halted flag, even though in this version the planner program can read its own state (a view of trusted values and handle indices).
- **Under these hypotheses:** Full checks including an opaque planner view (the view shows handle indices, not contents); the planner program is arbitrary over (user inputs, view, step index); issuers are per-operation inputs not chosen by the claimed identity. World assumptions: the platform-reported issuer is the true issuer; no side channel from quarantined processing into the planner.
- **Does NOT say:** That the two runs execute the same actions or that confirmations coincide; that the platform really authenticates issuers; anything about tool results themselves being authentic.
- **Kind:** general theorem (the unauthenticated version `noninterference` for raw traces plus a lemma that authentication commutes with the content change).

### Claim 5
## `ControlStack.SC23IsolationV2.w1_impossible_v2`

- **Says (plain English):** For one concrete environment (user 1, admin 9, sensitive tool 5, a planner that returns the sum of the trusted values in its view, a quarantine transformer adding 1): the trace "tool result with content 66, planner derivation, sensitive action on the derived value, no confirmation" executes the same actions as with tool-result content 0, and the single executed action has argument value 0, marked untainted. The planner sees only the handle, whose trusted sum is 0.
- **Under these hypotheses:** Fixed example environment `E0`, full checks including the opaque view, one specific trace; nothing quantified.
- **Does NOT say:** That laundering is impossible in general; that the planner is useful. Concrete computation only.
- **Kind:** finite computation (decide/native).

### Claim 6
## `ControlStack.SC23IsolationV2.sc23v2_safe_authenticated`

- **Says (plain English):** Given a list `U` of untrusted issuer numbers disjoint from the user list, and any list of issued operations, every executed action on a sensitive tool with a quarantined (tainted) argument is backed by a confirm operation in the issued trace that was issued by some user c, not in `U`, naming exactly the action's tool and resolved values.
- **Under these hypotheses:** Full checks, opaque view; the authentication guard (identity claimed on user input, confirm and halt must equal the issuer); `U` and the user list disjoint (so "c not in U" is immediate from "c is a user"). World assumptions: the platform-reported issuer is the true issuer (the single premise left from credential separation); the planner is isolated as in `noninterference`; confirmation UI shows exact values.
- **Does NOT say:** That the confirmation occurred before the action in the trace order, or was used only once (this model has no one-use tracking); that the issuer's confirmation was informed; that confirmations of non-tainted actions are needed.
- **Kind:** refinement/bridge (lifts the unauthenticated invariant to issued traces by the issuer-authentication wrapper, and extracts the issuer).

### Claim 7
## `ControlStack.AuthInstances.sc23_safe_authenticated`

- **Says (plain English):** For the first (label-based) SC-23 model wrapped with authenticated issuers (only confirm and halt claim an identity; user input, tool results, derive and act claim none), given untrusted issuers `U` disjoint from the users and any list of issued operations: (1) the safety property of `SC23.sc23_safe` holds for the resulting state; and (2) every confirmation present in the final state came from an operation in the issued trace issued by a user c not in `U`, which was a confirm with exactly that nonce, tool and values, with c equal to the recorded confirming principal.
- **Under these hypotheses:** The first model's full checks, the authentication guard on confirm and halt, and the disjointness of `U` and the users. World assumptions: platform-reported issuer is the true issuer; provenance_truthful as in `SC23.sc23_safe`. Note that user input is not authenticated in this instance (claim is none), so the premise that user inputs are the user's is still outside the theorem.
- **Does NOT say:** That forged identities for user input or tool results are impossible; that the issuer-reported identity is real; that the confirmation preceded the action.
- **Kind:** refinement/bridge (reduces to `SC23.sc23_safe` on the authenticated sub-trace, plus a generic log-origin lemma).

### Claim 8
## `ControlStack.AuthInstances.forged23_acts_without_auth`

- **Says (plain English):** One concrete trace: an untrusted principal 7 delivers a tool result of 66, then submits a confirmation claiming to be user 1 (nonce 7, tool 5, values [66]), then performs the sensitive action. Without authentication (no operation claims any identity), the tainted sensitive action executes with that forged confirmation. With the authenticated guard (confirmation claims user 1 but issuer is 7), the forged confirmation is ignored and nothing executes.
- **Under these hypotheses:** Policy `P0` (user 1, admin 9, sensitive tool 5), full checks, this one trace of three issued operations.
- **Does NOT say:** Anything beyond this trace; it is a negative control showing the authentication wrapper is what blocks a forged confirmation in this model.
- **Kind:** negative control (shows a weakened model, without authentication, fails); finite computation (decide).

### Claim 9
## `ControlStack.MonitorCollusion.pass_transfer`

- **Says (plain English):** Let the honeypot views and the real-attack views each follow a probability distribution over a finite set of possible views. Let the monitor, on seeing a view v, pass it with probability β(v) between 0 and 1 (any randomised rule that depends only on the view). Then the monitor's pass rate on real attacks and its pass rate on honeypots differ by at most the total variation distance (half the sum of absolute differences of the two distributions).
- **Under these hypotheses:** Both view laws are genuine probability distributions (non-negative, sum 1); the decision rule depends on the view only (no other input such as timing, ordering or memory of other items), with pass probability in [0,1]; the view set is finite. A false-negative rate is the pass rate on attacks, so this is the bound on the difference of the real and honeypot false-negative rates. World assumptions: the monitor's decision really depends only on the stated (canonicalised) view; TV between the real distribution of views and the honeypot distribution is small (it must be estimated or enforced; nothing here bounds it).
- **Does NOT say:** That honeypot measurements are valid: if a colluding generator makes real attacks distinguishable from honeypots then TV is large and the bound is vacuous (`stego_fools_honeypots` has TV = 1). That honeypot-measured recall is within TV for a monitor that sees side information not in the view. That the bound holds across a stream of dependent items; it is one decision, per item, with the view laws fixed.
- **Kind:** general theorem (a standard inequality: expectation of a [0,1]-valued function under two distributions differs by at most TV).

### Claim 10
## `ControlStack.MonitorCollusion.collusion_uniform`

- **Says (plain English):** Pick a phase uniformly at random: with probability 1/2 the item is a real attack, with probability 1/2 it is a honeypot. A view is drawn from the real-attack distribution or the honeypot distribution accordingly; the monitor (a randomised rule depending only on the view) outputs pass or flag. The colluder succeeds on this item if it passes a real attack or flags a honeypot. Then its success probability is at most (1 plus TV between the two view distributions) divided by 2; equivalently its advantage over a coin flip is at most TV/2.
- **Under these hypotheses:** Both view laws are distributions; the monitor's output on a view v is a distribution over pass/flag; the prior on phase is exactly uniform; a single item (one-shot); the decision depends only on the view v. World assumptions: complete mediated view (no side input to the monitor); TV is bounded or estimated; fresh phase per item.
- **Does NOT say:** (a) That the colluder cannot pass every real attack in a long stream and flag every honeypot: the bound is for one item with a 50/50 prior (the general-prior form `collusion_ml` is a separate theorem), not a bound on a joint event over many items. (b) That TV is small: the colluding generator chooses the real-attack view law, so TV is the quantity the adversary tries to maximise; at TV = 1 the bound is 1. (c) Anything about shared secrets or adaptivity across items (see `phase_learning` for streams).
- **Kind:** general theorem (an instance of the one-shot maximal-leakage transfer `collusion_ml`, with sum of pointwise maxima equal to 1 + TV).

### Claim 11
## `ControlStack.MonitorCollusion.canon_channel`

- **Says (plain English):** A generator and a monitor share a codebook (an encoder and decoder fixed in advance, possibly randomised). The generator embeds a message drawn uniformly from a finite set M into the view. A trusted canonicalisation maps each view to one of K classes, and the monitor decodes from the class only. Then the probability that the decoded message is correct is at most K divided by the number of messages, i.e. at most log base 2 of K bits of covert information per item get through.
- **Under these hypotheses:** M finite and nonempty; the encoder gives a distribution over views for each message; the decoder gives a distribution over messages for each class; the canonicalisation is a fixed function into K classes; the message is uniform. World assumptions: the canonicalisation is trusted and actually erases everything else (the monitor sees the canonical class only, complete mediation), and the generator and monitor have no other channel (e.g. timing, ordering, metadata).
- **Does NOT say:** That K is small (it only bounds signalling by log K bits; the semantic content of an attack may itself need many bits); that canonicalisation keeps the attack detectable; that the shared codebook is the only form of collusion; anything about the monitor's detection quality. The bound is vacuous when K is at least the number of messages.
- **Kind:** general theorem (counting bound for a covert channel pushed through the K-class map; reduces to the unmapped covert bound).

### Claim 12
## `ControlStack.MonitorCollusion.phase_learning`

- **Says (plain English):** A hidden phase, test or deployment, is chosen uniformly and then fixed for a stream of m items. In each round the model produces a visible output (views, the monitor's actions, feedback) and possibly hidden state, with arbitrary dependence on the whole history so far (hidden and visible). Suppose that in every round, whatever the phase and the history, the probability of each visible output (summed over hidden state) is at most the value of a phase-independent certificate, and the certificate's total mass over outputs is at most L. Then any final guess of the phase, which may be randomised and depend on the visible transcript, is correct with probability at most L to the power m, divided by 2.
- **Under these hypotheses:** Kernel entries non-negative; a certificate c that dominates every phase's round law at every history; L at least 0 and an upper bound on the total mass of the certificate at every visible history; the guess is a distribution over phases for each visible transcript; uniform prior; the phase is constant across the stream. World assumption: the per-item leakage bound L is valid for every history (worst case over history) and phases are re-randomised before L^m reaches 1 (about 1/λ items for L = 2^λ). L itself must be estimated or enforced; this theorem does not bound it.
- **Does NOT say:** That the phase cannot be learned: L^m grows exponentially and the bound is at least 1 (vacuous) once L^m ≥ 2; nothing about a phase kept fixed for a long deployment; nothing about adaptive signal search by a colluding generator beyond what L captures (the scenario notes this is untested at runtime). The Lean statement does not require the kernel sum to be at most 1.
- **Kind:** general theorem (an instance of the sequential maximal-leakage transfer `Leakage.seq_transfer_const` plus a bound on the certificate's mass).
