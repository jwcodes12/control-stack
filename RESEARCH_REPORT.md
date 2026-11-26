# One mathematical statement worth proving for AI safety

**Research assessment: 26 November 2026**  
**Scope:** interpretability, AI control, and alignment; a small team with strong Lean skills, about one week, models at most 10B parameters, and modest GPU resources.  
**Publishing note:** `control-stack` is the requested destination, not a constraint on the research topic.

## Recommendation

**Spend the first day trying to obtain a non-vacuous certificate for finite SAE feature-set interventions. If that experiment passes, formalize the certificate and its connection to the actual intervention objective.** Use vector or multiple-token responses, but do not assume that increasing the number of output coordinates fixes the scalar-readout problem.

The proposed result would let a circuit tool say one of three useful things:

1. This feature set is optimal, or has bounded regret, for a precisely specified finite intervention and candidate pool.
2. This explicit competing feature set is better.
3. The available evidence does not resolve the selection.

That is a meaningful change from returning an attribution ranking whose finite-edit reliability is unknown. It builds on the user's strongest empirical result instead of starting with an attractive mathematical abstraction and hoping to find an application afterward.

**The qualification is substantial:** the quadratic optimization algebra below is classical. A new Lean proof of that algebra alone would not meet the requested significance threshold. The potential contribution is a tight, checkable connection to actual finite model interventions, demonstrated on real cases where the certificate changes a circuit-selection decision. I estimate a 20–35% chance of that complete outcome within a week, assuming the existing SAE code and caches are available. I would not advertise any candidate in this report as a guaranteed one-week moonshot.

The strongest alternative is a sharp counterexample to restricting an adversarial monitor to extreme scores when the protocol also has a deferral action. Its mathematical separation is clean; its practical value is conditional on finding the relevant semantics in an actual protocol. The other candidates have higher risks of reproducing classical mathematics or known empirical failure modes.

## Evidence and claim status

This report distinguishes four things:

- **Published evidence:** cited to primary papers, proceedings, author project pages, or author research posts. Abstract-only verification is marked where full text could not be inspected.
- **User-reported work:** the prior experiments and Lean results in the request. Their correctness is not independently re-established here.
- **Proposed statements:** exact targets and proof sketches developed for this assessment. No new Lean proof is claimed.
- **Checks performed for this report:** small CPU numerical or exact-rational calculations, described in Section 7. No pretrained-model intervention experiment, adapter training run, or SGLD study on a learned model was run for this report.

Searches were current through the assessment date. Absence of a located theorem is not evidence that the theorem is new. In particular, the report does not convert a paper's explicit limitation into a claim that its authors asserted a universal guarantee.

## 1. What methods rely on, and what would actually settle the reliance

The most useful research targets concern **the inference a practitioner makes from a measurement**, not whether an informal slogan is universally true. Several of these extrapolations are already recognized limitations in the original papers.

| Working reliance | Precise theorem or counterexample that would matter | Current evidence and implication |
|---|---|---|
| SAE reconstruction quality supports using features as causal units | For a stated class of interventions, bound downstream behavioral discrepancy from measurable reconstruction and intervention geometry; alternatively construct equal-reconstruction models with sharply different intervention behavior under the same specified readout. | Sparse Feature Circuits uses approximate effects and actual ablations [R1]. Circuit Tracing explicitly discusses replacement-model faithfulness and freezes some nonlinearities [R2]. Reconstruction error alone is not an adequate intervention specification. |
| A discovered feature has a stable identity across fits | Prove identification up to stated symmetries under assumptions that can be checked on learned dictionaries; or exhibit equally good fitted dictionaries with conflicting intervention semantics. | iSAE already studies identifiability using dictionary-learning conditions [R3]. A generic RIP theorem is not a fresh project. Identification of codes and identification of interventions are different questions. |
| Re-encoding or reranking after an edit improves feature selection | Certify actual finite-loss optimality/regret over a declared family of masks, or produce a better competing mask and a structural failure mechanism. | The user's threshold-jump result supplies unusually good motivation. Candidate 1 targets the remaining decision, rather than reproving discontinuity. |
| First-order or integrated attribution remains useful for finite group edits | Bound the error uniformly over the candidate group interventions, not just at the unedited point or for isolated features. | EAP-IG already prioritizes faithfulness [R4]. New 2026 work explicitly studies second-order error and corrections using exact measurements [R5], [R6] (abstracts verified). A Taylor expansion alone is not enough novelty. |
| Stable circuit membership implies a faithful mechanism | Separately certify stability under dataset edits and behavioral accuracy under activation edits. Neither implication should be assumed. | Certified Circuits proves the former type of guarantee [R7]. Candidate 1 concerns the latter objective and selection optimality. |
| A linear probe that works in distribution will remain informative under composition changes | Characterize the representation/inference assumptions under which recovery survives a specified shift; or prove a counterexample within that shift class. | Stop Probing, Start Coding already studies compositional failures and the gap introduced by a fixed SAE encoder [R8]. Generic OOD impossibilities would add little. |
| A collection of activation monitors constrains behavior-changing directions | Quantify behavior change possible within the monitor's nullspace and within a feasible perturbation class, including finite nonlinear error. | Obfuscated Activations already demonstrates substantial evasion and some performance costs [R9]. Candidate 6 asks whether a computable local quantity predicts that cost, not whether evasion is possible at all. |
| Extreme suspiciousness scores suffice when modeling a malicious monitor | Prove an endpoint-policy reduction for the exact protocol, or give a family where an intermediate score adds a strategically different continuation outcome. | The 2026 untrusted-monitoring analysis explicitly flags binary scores as an unresolved simplification [R10] (Appendix B.3). Candidate 2 isolates a specific failure condition. |
| Several monitor ROC curves can be combined as if failures were independent | Compute sharp risk over admissible joint laws, with the law required conditionally on the attacker's information and history. | The same analysis flags score dependence [R10] (Appendix B.7). Candidate 3 is useful only if it changes an actual frontier or protocol decision; its probability machinery is established. |
| Evaluation results transfer to deployment, including rare adaptive attacks | State an identifiable transfer class, such as a history-conditional uncertainty set, and prove a risk bound uniform over that class. A counterexample outside the class is not a refutation of the theorem. | AI Control evaluates concrete threat models [R11]. With unrestricted deployment shift, unseen behavior can be changed while preserving every evaluated sample. That elementary no-free-lunch observation is not the desired research result. |
| Static low-rank adapter statistics remain adequate against adaptive poisoning | Show detector completeness under a trusted specification and explicit clean-baseline geometry, or construct a collision in the detector's actual complete features with different specified behavior. | The inspected LoRA detector assumes non-adaptive attacks and includes entrywise kurtosis as well as spectral features [R12]. Candidate 5 therefore uses column permutations, not an invalid arbitrary-rotation argument. |
| LLC changepoints identify changes in learned computation | Separate true local geometry, finite-temperature resolution, localization, and sampling error; derive a usable finite-scale diagnostic. | Finite-temperature resolution effects are already explicit in Chen–Murfet [R14]. Candidate 4 supplies a sharp calibration family, but must change a learned-model interpretation to be significant. |
| Good task performance gives a positive weight radius for algorithmic behavior | Produce a checkable condition that passes on ordinary task-trained weights and controls the claimed input/length class. | Length-generalization theory is already substantial [R22], [R23]. The user's failure on task-trained attention is a useful empirical warning; a new generic invariant lemma would not resolve it. |

The common trap is to prove a theorem with the desired conclusion hidden in an uncheckable premise: uniform intervention error, conditional monitor recall, reachable-state coverage, or a trusted latent specification. A worthwhile project must explain how its premise is measured or verified, and where it remains an assumption.

## 2. Ranking: impact multiplied by probability of a useful result in one week

These are **subjective planning estimates**, not statistical forecasts. “Useful result” means a correct formal core **plus** a demonstrated change to a real methodological decision. It is deliberately stricter than “some Lean file compiles.” Impact is on a five-point relative scale, conditional on clearing that bar.

| Rank | Candidate | Impact | Approximate probability of a clean formal core | Probability of a useful one-week outcome | Illustrative impact × probability | Funding decision |
|---:|---|---:|---:|---:|---:|---|
| 1 | Finite-edit SAE selection certificate | 5 | 70–85% | 25% central; 20–35% plausible range | 1.25 | Run the first-day non-vacuity test. Main recommendation. |
| 2 | Intermediate scores defeat an endpoint-only monitor analysis | 4 | 85–95% | 20% | 0.80 | First audit a real protocol's semantics. |
| 3 | Joint-score certificates for adaptive deployment risk | 4 | 75–90% | 15% | 0.60 | Continue only after a material frontier or policy change. |
| 4 | Exact LLC thermal crossover and calibration | 3 | 60–75% for the restricted case | 15% | 0.45 | Good supporting work for the existing SGLD project. |
| 5 | Collisions in a concrete low-rank weight detector | 3 | 90% for the toy family | 10% | 0.30 | Requires a realistic clean-performance-preserving collision. |
| 6 | Quantitative probe coverage under feasible changes | 3 | 75–90% for the local theorem | 5% | 0.15 | Low priority; high classicality risk. |

Candidates 2 and 3 share data and protocol-analysis work, so they are not independent bets. The lower-ranked items are included to make the alternatives and their failure conditions explicit, not because six equally strong opportunities were found.

**Blunt assessment:** I would allocate the research week to Candidate 1 only after its day-one gate. I would not spend it proving Candidates 3, 5, or 6 in the abstract. Those would likely reproduce the user's previous experience of obtaining correct, narrow lemmas without changing practice.

## 3. Candidate statements

### Candidate 1 — Certifying a finite SAE feature-set intervention

#### Exact statement

For every pair of positive integers $m,p$, every integer $0<k<m$, and every matrix $V\in\mathbb R^{p\times m}$ and vector $b\in\mathbb R^p$, define

$$
\Omega_k=\{s\in\{0,1\}^m:\mathbf1^\top s=k\},
\qquad Q(s)=\|b-Vs\|_2^2,
\qquad G=V^\top V.
$$

Let $H:\Omega_k\to\mathbb R$ be the actual finite-intervention loss. For every candidate $s_0\in\Omega_k$, vector $d\in\mathbb R^m$, number $\epsilon\ge0$, and number $\gamma\in\mathbb R$, set

$$
g=2V^\top(Vs_0-b).
$$

Assume all three conditions:

1. **Quadratic lower bound on the fixed-cardinality subspace:**

   $$
   \forall u\in\mathbb R^m,
   \quad\mathbf1^\top u=0
   \Longrightarrow
   u^\top(G-\operatorname{diag}(d))u\ge0.
   $$

2. **Every selected/unselected exchange has sufficient certified margin:**

   $$
   \forall i,j,
   \quad s_{0i}=1\land s_{0j}=0
   \Longrightarrow
   g_j+d_j-g_i+d_i\ge\gamma.
   $$

3. **The surrogate error is bounded over the entire declared candidate family:**

   $$
   \forall s\in\Omega_k,\qquad |H(s)-Q(s)|\le\epsilon.
   $$

Then, writing $r(s,s_0)=|\{j:s_j=1,\ s_{0j}=0\}|$,

$$
\boxed{\forall s\in\Omega_k,\quad
H(s)-H(s_0)\ge r(s,s_0)\gamma-2\epsilon.}
$$

In particular, **if $\gamma>2\epsilon$, $s_0$ is the unique global minimizer of $H$ on $\Omega_k$**. A more forgiving conclusion is

$$
H(s_0)-\min_{s\in\Omega_k}H(s)
\le
2\epsilon+\min(k,m-k)\max(0,-\gamma).
$$

This is global optimality over the specified pool and budget, not over an omitted dictionary, all possible intervention types, or all prompts.

#### Why it is plausible; what is actually difficult

The displayed implication has a short derivation. For $u=s-s_0$, expand

$$
Q(s)-Q(s_0)=g^\top u+u^\top Gu.
$$

Use the quadratic lower bound. Each removed coordinate contributes $d_i-g_i$, each added coordinate $d_j+g_j$. Pair the equally many additions and removals, then account for two surrogate errors. This is a target for formalization, not a conjecture that needs a GPU to discover whether its algebra is true.

**The open research question is whether a useful instance satisfies the premises at a reasonable cost.** The $d_i$ may be signed. Scalar rank deficiency therefore does not imply that every such certificate is impossible. Conversely, stacking outputs can add redundant coordinates, shrink a relevant decision margin, or worsen nonlinear error. Raw output dimension is not effective response rank.

To define the actual intervention, retain the SAE residual and fixed features:

$$
h=e+\sum_{i=1}^m u_i,
\qquad h_s=e+\sum_i s_i u_i,
\qquad H(s)=\|W(f(h_s)-f(h))\|_2^2.
$$

Here $f$ is the actual downstream model and $W$ is a fixed, preregistered response map. It can select multiple logit contrasts or output positions reached by the same intervention. If stacking prompts, the support must mean the same intervention across those prompts. This is a teacher-forced output objective unless a generation objective is explicitly modeled.

One surrogate takes $V_i=WJ_f(h)u_i$ and $b=\sum_iV_i$. If the downstream remainder has a valid bound

$$
\forall s\in\Omega_k,\quad
\|W(f(h_s)-f(h))-WJ_f(h)(h_s-h)\|\le\eta(s),
$$

then

$$
|H(s)-Q(s)|\le 2\sqrt{Q(s)}\,\eta(s)+\eta(s)^2.
$$

A uniform upper bound on the right supplies $\epsilon$. Bounding only isolated single-feature edits does not establish this premise for group interventions. Nor does the largest Hessian value sampled at a few interpolation points establish a uniform Hessian bound.

#### Decision changed, and value of either outcome

Users of sparse-feature circuits could accept a set with an explicit objective guarantee, reject it with a competing intervention, or abstain. This separates bad optimization from inaccurate modeling of finite effects. A positive result would justify an operational certificate. A negative result is valuable only if it identifies a systematic obstruction—such as interaction structure or unavoidable surrogate error—and changes the selection method. Failure of one sufficient condition alone is not an impossibility theorem.

#### Closest prior work and novelty boundary

Sparse Feature Circuits and EAP-IG establish a real use case for intervention-based selection [R1], [R4]. Certified Circuits concerns dataset-edit stability, a different guarantee [R7]. The recent attribution-correction papers are direct novelty threats to generic Taylor/HVP proposals [R5], [R6].

The optimization backbone is established quadratic convex reformulation: diagonal and more general perturbations with semidefinite bounds are explicitly studied by Pörn et al. [R17]. **Do not call the quadratic certificate a new optimization theorem.** The research contribution must be a non-vacuous finite-model bridge and a useful certification procedure. A recent intervention-identifiability submission was also located, but its primary full text could not be verified; see the unresolved novelty lead in the bibliography.

#### Cheap experiment and one-day kill test

Reuse existing SAE checkpoints and intervention code. On a small declared pool, say $m=12,k=3$, enumerate all 220 masks. On 32 development and 32 held-out examples that is 14,080 intervention forward passes, often cheaper with cached prefixes and batched downstream runs. Compare scalar, vector, and multiple-token objectives without tuning the response metric on held-out results.

For each candidate selection, calculate its certificate margin and the maximum observed surrogate discrepancy over the entire enumerated pool. This is a strong falsification test; ordinary floating-point evaluations are not a formal numerical enclosure. Record certification coverage, true enumerated regret, explicit counterexamples, and runtime.

**Proposed engineering gate:** continue only if at least 10% of held-out examples have a positive error-adjusted margin, or meet a preregistered useful regret tolerance, and the resulting decisions improve or correct a relevant baseline. The 10% figure is a project-management threshold, not a scientific constant. This small held-out batch measures pilot coverage, not a population certification rate. Kill sooner for a false certificate or a mismatch in residual/intervention semantics.

Enumeration already gives the empirical optimum. Therefore, by day two there must also be a credible, cheaper way to establish the finite-edit error bound. Otherwise this becomes an expensive restatement of exhaustive search.

#### Lean feasibility and hardest lemma

The finite-dimensional core is plausible in two to four days for a strong team. Use finite types, finite sums, real inner products, binary masks, and a certificate for positivity on the sum-zero subspace. For a rational basis matrix $T$ spanning that subspace, check a supplied factorization of

$$
T^\top(G-\operatorname{diag}(d))T=L\Lambda L^\top,
\qquad \Lambda_{ii}\ge0.
$$

Here $\Lambda$ must be diagonal with nonnegative entries. An external optimizer can find the witness; Lean need only check it. Rational LDL-style witnesses avoid requiring a rational square root for every pivot.

The hardest finite-algebra lemma is the paired-exchange lower bound. The hardest substantive obligation is the actual-model remainder bound. A proof about a rounded matrix does not automatically certify the original floating-point transformer. Input/output rounding and extraction error need an explicit budget, or the claim must remain conditional.

---

### Candidate 2 — Intermediate scores can invalidate endpoint-only monitor evaluation

#### Exact statement

For every $0<\varepsilon<1$ and every integer $N\ge1$, define the following finite game. Waiting consumes a round and leaves the live state unchanged. When the generator submits an attack, it does so before receiving the current private recognition signal. Independently of history, the submitted candidate is replaced by a known bad honeypot with probability $1-\varepsilon$; otherwise it is the live attack.

The monitor sees `clear` on a live attack with probability $\varepsilon$; otherwise it sees `ambiguous`. Honeypots always yield `ambiguous`. These signals are the monitor's only current observation; neither agent observes the hidden honeypot/live label. Fresh type and signal draws obey the stated conditional laws given the entire permitted history and the agents' private randomization. Scores route as follows:

- $s<1/3$: execute.
- $1/3\le s<2/3$: defer, blocking this attempt while continuing.
- $s\ge2/3$: audit.

Executing a live attack causes catastrophe; auditing it catches the attacker and halts. A honeypot passes the test exactly when $s\ge1/3$; otherwise the monitor is caught and the game halts. Thus a deferred honeypot passes. There is no additional score-calibration test or binding deferral quota. Policies may depend on all permitted past observations and private randomness.

Then the proposed exact values are

$$
\boxed{\sup_{\pi:\ s\in\{0,1\}}
\Pr_\pi(\text{catastrophe by }N)=\varepsilon,}
$$

$$
\boxed{\sup_{\pi:\ s\in[0,1]}
\Pr_\pi(\text{catastrophe by }N)
=1-(1-\varepsilon)(1-\varepsilon^2)^{N-1}.}
$$

The endpoint restriction includes randomized mixtures of endpoints. The separation is not obtained by comparing a randomized policy against an artificially deterministic baseline.

#### Why the statement is likely true

Execute on `clear`. The three possible reports on `ambiguous` have these unconditional outcomes:

| Report | Catastrophe | Caught and halted | Continue |
|---|---:|---:|---:|
| 0 | $\varepsilon$ | $1-\varepsilon$ | 0 |
| $1/2$ | $\varepsilon^2$ | 0 | $1-\varepsilon^2$ |
| 1 | $\varepsilon^2$ | $\varepsilon(1-\varepsilon)$ | $1-\varepsilon$ |

Both endpoint actions have catastrophe/(catastrophe + catch) equal to $\varepsilon$. Their mixtures cannot beat that eventual-risk bound. An intermediate report supplies a new continuation outcome. The unrestricted optimum defers ambiguous cases for the first $N-1$ rounds and executes on the last round. Bellman induction yields the formula.

For $\varepsilon=1/4,N=2$, the two values are $1/4$ and $19/64$. As $\varepsilon\to0$, allowing sufficiently many rounds makes the unrestricted value approach one while the endpoint value approaches zero.

#### Decision changed and exact scope

A monitor evaluator would either include intermediate score actions or prove that they can be reduced to endpoints under the actual protocol's tests and resource limits.

The decisive assumptions are **accepting a deferred honeypot** and allowing continuation after deferral. If honeypots require audit-level detection, or graded calibration or a binding quota changes continuation, the example may disappear. Even the large separation needs sufficient rounds and resources. This game does not itself model honest-task usefulness, and a large honeypot fraction is not evidence of affordability.

This is not a refutation of the exact LASR protocol: its simplified analysis uses upfront honeypots/retraining. It is a candidate family exposing when an endpoint reduction can fail. The family's relevance must be established by an implementation audit.

#### Closest prior work, cheap experiment, and kill

The explicit research opening is the binary-score simplification in [R10] (Appendix B.3). AI-Control Games already supplies general stochastic-game machinery [R18]. The possible new contribution is a missing action that materially changes an evaluation, not Bellman recursion itself.

On day one, inspect one real implementation's routing thresholds, honeypot acceptance, private observations, quotas, and shutdown rules. Build its finite action table, and solve endpoint-only and full score-bin versions with the same budgets and information timing. A small model is optional: logged score distributions can suffice.

**Kill if no relevant protocol has the crucial semantics, or the gap vanishes under its real calibration tests and quotas.** Do not promote a deliberately vulnerable toy protocol into a broad conclusion about untrusted monitoring.

#### Lean feasibility and hardest lemma

Two to four days should suffice for the finite game, explicit rational example, and induction. The key lemma is the upper bound for every randomized history-dependent endpoint strategy, respecting what the monitor and generator can observe. A proof of the displayed closed-form recurrence without that strategy-to-recurrence connection would be incomplete.

---

### Candidate 3 — Dependence-robust risk from joint monitor scores

#### Exact statement

For every finite joint-score alphabet $\Omega$, every nonempty compact polytope $\mathcal P\subseteq\Delta(\Omega)$, every integer horizon $N\ge0$, and every fixed routing policy, let $w(p)$ and $c(p)$ be linear functions giving the probabilities of catastrophic release and absorbing catch, with $w(p),c(p)\ge0$ and $w(p)+c(p)\le1$.

Assume that at every surviving history the next **conditional** score distribution belongs to $\mathcal P$. For exactness, additionally assume every such next distribution is available independently of previous choices; this is the usual rectangular uncertainty assumption. Set

$$
V_0=0,
\qquad
V_{n+1}=\max_{p\in\mathcal P}
\left[w(p)+(1-w(p)-c(p))V_n\right].
$$

Then

$$
\boxed{\sup_{\text{admissible adaptive strategies}}
\Pr(\text{catastrophe before catch by }N)=V_N.}
$$

Without full attainability/rectangularity, the same recurrence is still an upper bound if every conditional law is contained in the set, but need not be tight. Remaining audit and deferral budgets must be added to the state when they affect routing.

An implementation-oriented theorem would verify rational upper bounds $U_n$: if $U_0\ge0$, $U_n\in[0,1]$, and each supplied certificate proves

$$
\forall p\in\mathcal P,
\quad w(p)+(1-w(p)-c(p))U_n\le U_{n+1},
$$

then the specified finite model's risk is at most $U_N$. The numerical optimizer is outside the trusted checker.

#### Why true, what changes, and the empirical question

Condition on the next outcome and induct on the remaining horizon. Compactness supplies a maximizer for the exact recurrence. This is established robust dynamic programming, not new probability theory [R19], [R20].

The practical question is whether replacing product-of-marginal assumptions with a feasible joint-law set changes which monitors, thresholds, or audit allocations look adequate. Pairwise correlation tests do not establish mutual independence. But another counterexample to that elementary implication would not meet the research bar.

The crucial risk is promoting an unconditional held-out score table into a history-conditional guarantee. That promotion requires an explicit modeling or transfer assumption. A statistical confidence interval for a fixed joint distribution does not establish uniform validity against a deployment adversary selecting different situations.

#### Prior work and why the candidate is not already finished

The modeling assumption is explicit in [R10] (Appendix B.7). The mathematical reduction is already covered by robust MDP work [R19], [R20] and related AI-Control Games [R18]. What remains is an empirically consequential, assumption-transparent instantiation with a small verified checker. It may be a valuable methodological artifact; it is not a new general theorem about monitoring.

#### Cheap experiment, one-day kill, and Lean difficulty

Recalculate a single published safety/usefulness frontier three ways: independent marginals, observed joint scores, and admissible coupling intervals. Hold routing and resource budgets fixed. Prespecify a practical change worth continuing for, such as a reversed monitor/threshold recommendation or a risk bound crossing the team's chosen tolerance. Do not select that criterion after seeing the result.

**Kill if the relevant joint data are unavailable, the uncertainty set makes every useful policy uncertifiable, no material decision changes, or the only claimed deployment bridge is marginal calibration.**

A finite rational checker and adaptive induction are feasible in a week. Avoid formalizing a general-purpose LP solver or strong-duality library. The hardest lemma connects the accepted inequalities to the law of an adaptive history-dependent process. This is where a silent independence assumption would otherwise return.

---

### Candidate 4 — Exact thermal crossover with an unchanged asymptotic LLC

#### Exact statement

For every integer $k\ge2$, $a>0$, and $t>0$, define

$$
K_a(x)=x^{2k}+ax^2,
\qquad p_{a,t}(x)=Z_{a,t}^{-1}e^{-tK_a(x)},\quad x\in\mathbb R.
$$

This is an exact Gibbs distribution without localization. The local learning coefficient at the minimum is $1/2$ for every $a>0$, and $1/(2k)$ at $a=0$, under a smooth positive local prior.

Let

$$
z=a t^{1-1/k},\qquad
q_z(u)\propto e^{-u^{2k}-zu^2},\qquad
F_k(z)=\mathbb E_{q_z}[u^{2k}+zu^2].
$$

The target is the following explicit crossover theorem:

$$
t\mathbb E_{p_{a,t}}K_a=F_k(z),
$$

with $F_k$ strictly increasing on $z>0$, limits $1/(2k)$ at zero and $1/2$ at infinity, and bounds

$$
0\le F_k(z)-\frac1{2k}
\le
\left(1-\frac1k\right)z
\frac{\Gamma(3/(2k))}{\Gamma(1/(2k))},
$$

$$
0\le\frac12-F_k(z)
\le
(k-1)\frac{\Gamma(k+1/2)}{\Gamma(1/2)}z^{-k}.
$$

Also,

$$
t^2\operatorname{Var}_{p_{a,t}}(K_a)
=F_k(z)-\left(1-\frac1k\right)zF_k'(z).
$$

Consequently, the finite-temperature mean and variance diagnostics change around $t\asymp a^{-k/(k-1)}$ even though the asymptotic coefficient stays $1/2$ throughout $a>0$.

#### Why likely true and cheap evidence

The variable change $x=t^{-1/(2k)}u$ gives the scaling. Integration by parts gives

$$
1=2k\mathbb E_z u^{2k}+2z\mathbb E_z u^2,
$$

so

$$
F_k(z)=\frac1{2k}+\left(1-\frac1k\right)z\mathbb E_z u^2
=\frac12-(k-1)\mathbb E_z u^{2k}.
$$

Rescaling by $v=\sqrt z\,u$ and comparing monotone moments yields the bounds and monotonicity. Differentiating the exact Gibbs mean gives the variance identity. These are proposed derivations; the report does not claim a completed formal proof.

CPU quadrature during this assessment for $k=2$ gave:

| $z$ | Mean diagnostic | Variance diagnostic | Asymptotic LLC for $a>0$ |
|---:|---:|---:|---:|
| 0.01 | 0.25168318 | 0.25084496 | 0.5 |
| 0.1 | 0.26623956 | 0.25844046 | 0.5 |
| 1 | 0.36697998 | 0.32806068 | 0.5 |
| 10 | 0.49303596 | 0.48655242 | 0.5 |

#### Decision changed and novelty risk

An LLC user should separate a geometric transition from a diagnostic moving across its resolution scale. Longer sampling can reduce Monte Carlo error while leaving this discrepancy intact. The positive contribution would be a quantitative calibration procedure that changes how an actual training trajectory is interpreted.

However, the qualitative warning is already known. Lau et al. introduce the practical LLC estimator [R13]; Chen–Murfet explicitly explain finite-temperature resolution [R14]; Epifano's author research post discusses localization and hyperparameter confounds [R15]. A new exact two-dimensional RLCT algorithm offers additional ground-truth fixtures [R16]. The elementary crossover family does not supersede this literature. The SIVE research repository also explicitly distinguishes finite-path variance probes from intrinsic LLC/RLCT and includes scale diagnostics [R27]. A variance-based version of the same warning is therefore not a fresh contribution by itself.

#### One-day kill test and Lean feasibility

Compare exact quadrature against SGLD on this family and on the user's existing tractable examples. Vary temperature, localization, and step size separately. Test whether the scaling predicts an already observed checkpoint change. **Kill as a headline project if it merely reproduces known sensitivity or needs an unverified normal-form assumption to connect to a neural checkpoint.** Keep it as a calibration fixture in the ongoing finite-sample project.

The $k=2$ case is plausible in a week for an analysis specialist. All $k$, Gamma identities, differentiation under the integral, and a finite-sample SGLD confidence theorem are too much for one week. The hardest lemma is justified integration/differentiation on the real line, not the scaling algebra. More GPU time does not establish mixing or resolve localization bias.

---

### Candidate 5 — Exact collisions in a concrete weight-only LoRA detector

#### Exact counterexample family

For every $d\ge3$, output dimension $q\ge1$, $\alpha>0$, and unit vector $u\in\mathbb R^q$, let

$$
C=\operatorname{span}(e_3,\ldots,e_d),
\qquad
A_{\mathrm{bad}}=\alpha u e_1^\top,
\qquad
A_{\mathrm{good}}=\alpha u e_2^\top.
$$

Take a fixed trusted specification requiring zero update on $C\cup\{e_1\}$, with behavior at $e_2$ unrestricted. Then:

1. Both updates have rank one and agree with the specification on every clean input in $C$.
2. $A_{\mathrm{good}}e_1=0$, but $\|A_{\mathrm{bad}}e_1\|=\alpha$.
3. They have the same singular values and the same multiset of matrix entries.
4. Therefore every deterministic detector whose adapter features depend only on those quantities returns the same output for both, including after conditioning on any fixed benign calibration bank. A randomized detector has the same output distribution.

For a multi-projection detector, hold all other projections identical. A column permutation preserves both the spectral statistics and entrywise kurtosis used in [R12]. Arbitrary orthogonal rotations generally do not preserve kurtosis and would be an invalid argument against that complete feature set.

#### What it would change and what it would not show

The useful research target is a realistic counterpart: an adapter pair that is indistinguishable to the published feature implementation while one violates a fixed harmless sentinel specification and both retain clean performance. That would change reliance on static spectral screening against adaptive adapters.

The displayed family only proves a limitation of an invariant feature representation. It does not rule out arbitrary weight-based detectors, and a detector that knows the protected direction can distinguish the matrices immediately. A large calibration bank cannot recover information that the detector's representation has discarded.

#### Prior work and experiment

The inspected v3 of Detecting Backdoored LoRAs from Weights Alone explicitly assumes a non-adaptive attacker and uses a calibrated reference bank [R12]. The counterexample would therefore test an extension of its threat model, not contradict its stated evaluation. Cryptographic undetectability results already establish much broader impossibility phenomena under different model classes and computational assumptions [R21]; they do not by themselves establish a practical rank-one transformer collision.

Use a frozen small model, a public implementation of the complete detector, a benign classification task, and a harmless trigger-controlled label. Search only after fixing the protected behavior and clean-performance tolerance. Check all detector features and its actual threshold; matching only singular values is insufficient.

**One-day kill:** the collision exists only in the toy subspace, clean features remove the necessary freedom, or realistic candidates lose ordinary task performance. The toy theorem itself is too easy and unsurprising to justify a research week.

#### Lean feasibility

The rank-one and permutation statements are straightforward finite linear algebra. Proving equality of the exact feature implementation, including stabilized definitions at degenerate values, is the most relevant formal detail. Establishing the neural-model/specification correspondence is the hard research step. Formalizing a vague label such as “malicious” without the fixed specification would make the result meaningless.

---

### Candidate 6 — Quantifying probe coverage in a feasible perturbation space

#### Exact local statement

For every pair of positive integers $p,q$, let the coordinates $\theta\in\mathbb R^p$ parametrize the actual permitted changes, for example the factors of a fixed adapter architecture. Let $f:\mathbb R^p\to\mathbb R$ be a chosen behavior score, and $c:\mathbb R^p\to\mathbb R^q$ collect protected monitor scores and clean-task outputs on a specified finite evaluation set.

For every center $\theta$, radius $R>0$, and constants $L_f,L_c\ge0$, suppose differentiability at $\theta$ and, for every $v$ with $\|v\|\le R$,

$$
|f(\theta+v)-f(\theta)-\nabla f(\theta)^\top v|
\le \tfrac12 L_f\|v\|^2,
$$

$$
\|c(\theta+v)-c(\theta)-J_c(\theta)v\|
\le \tfrac12 L_c\|v\|^2.
$$

Define $a=P_{\ker J_c(\theta)}\nabla f(\theta)$. Then

$$
\boxed{
R\|a\|-\tfrac12L_fR^2
\le
\sup_{\substack{\|v\|\le R\\J_c(\theta)v=0}}
[f(\theta+v)-f(\theta)]
\le
R\|a\|+\tfrac12L_fR^2,}
$$

and every perturbation in that supremum changes the protected vector by at most $L_cR^2/2$.

For $a\ne0$, the lower bound uses $v=Ra/\|a\|$; for $a=0$, the zero perturbation suffices for the stated lower inequality. These quantifiers concern the declared parameter ball and evaluation set. They do not certify unseen prompts or perturbations outside the model.

#### Why true, and why the idea is weak

The proof is orthogonal projection plus a finite Taylor remainder. It turns a vague claim about “monitor coverage” into a quantity, but the elementary result is not a mathematical breakthrough. Its potential empirical use is to predict which monitor placements or combinations impose a real behavior-change cost under an actually feasible parameter change.

Defining $v$ in adapter coordinates addresses one weakness of an arbitrary hidden-state theorem: those coordinates correspond to changes the experiment can perform. Fix the parameterization or perturbation metric before comparing costs: rescaling bilinear LoRA factors can preserve the model while changing their Euclidean distances and projected gradients. The theorem does not solve the uniform remainder problem, guarantee generalization, or make finite protected examples a complete task specification.

#### Prior work, experiment, kill, and Lean

Obfuscated Activations already demonstrates evasions and an empirical performance cost on some tasks [R9]. Stop Probing, Start Coding already shows that linear representation and accessible concept recovery differ [R8]. The gap here is a quantitatively predictive, intervention-specific bound, not another existence proof that probes can fail.

On a small harmless classification task, compare projected-gradient magnitudes across monitor sets against the finite parameter change needed to shift the target label while preserving protected outputs. Prespecify held-out prompts and include a nonlinear check. **Kill if the quantity predicts only infinitesimal changes, requires uncertified curvature estimates, fails to predict practical cost, or simply recovers known evasion.**

Lean feasibility is high for the conditional local theorem. The hardest mathematical step is a clean projection/optimization formulation; the hardest scientific step is obtaining finite, useful remainder bounds in the feasible parameterization. I would not allocate the week to this unless existing experiments already show a surprising separation.

## 4. Reassessment of every direction already tried

| Previous direction | What the current evidence supports | New angle or resource that could change the verdict |
|---|---|---|
| ARC no-coincidence, restricted verifiers | The reported partial-input barrier is not a result about the full ARC conjecture. The conjecture's quantifiers concern a verifier receiving a reversible circuit and polynomial advice, with a random-circuit rejection requirement [R24]. | Spend several days with a complexity/proof-complexity specialist and choose one distribution and verifier class carefully. More GPU compute or another round of unconstrained model attempts is unlikely to address the central obstruction. Keep open, but not this week's bet. |
| Prover–estimator debate | There is a material version update: the current v2 corrects the stability definition from conditional to marginal probabilities. Stability is used for completeness/usefulness, not soundness. Appendix A.4 already connects it to fractional block sensitivity [R25]. | Audit the existing formal statement against v2. This does not imply the user's proof is wrong; it may formalize a different statement. A new result needs a new decomposition class, a way to find stable decompositions, or a protocol change. A generic LP certificate would duplicate the revised paper. |
| ReLU free energy / SGLD LLC estimation | The user's anomaly and multi-input result remain useful starting points. Exact Gibbs bias, localization, and sampler error are separate obstacles. | Use Candidate 4 and exact two-dimensional RLCT fixtures [R16] to calibrate the ongoing finite-sample project. A sampling/mixing specialist and tractable normal forms are more valuable than simply running longer chains. |
| Low-rank backdoor detectability | Rank and trigger effect alone still do not specify a detectable anomaly. The inspected detector does not claim adaptive security. | Test invariances of its complete feature implementation against a fixed trusted specification, as in Candidate 5. The new resource is an actual calibrated adapter bank and clean utility evaluation. |
| SAE selection after intervention | This has the strongest supplied empirical mechanism and an explicit missing practical guarantee. | Candidate 1: signed, instance-specific quadratic bounds, vector/multiple-token effects, exact small-pool falsification, and a finite-edit bridge. Additional GPU time helps enumerate interventions; more algebra about the threshold jump is not the missing resource. |
| Robustness radii for learned recurrence/attention | Certification-trained successes and task-trained failures should not be conflated. There is already direct length-generalization theory [R22], [R23]. | Try two additional tasks and small GPU-trained models; use task-specific sufficient statistics or short counterexample searches. If ordinary task-trained weights still fail, investigate whether the behavior is genuinely fragile or the certificate conservative. I cannot responsibly invent a new exact condition before that discovery. |
| Control, audit, sequential testing, preference identification | Classical results remain valuable infrastructure, but the user's originality concern is justified. | Candidates 2 and 3 attach the mathematics to a specific disputed modeling choice and a decision-changing test. Without that connection, do not spend another week on a lemma. |

The debate update deserves a small, separate audit even if Candidate 1 is chosen. It should not silently displace the main project or be described as a demonstrated defect in the user's existing formalization.

## 5. The single best project: first two days

### Goal and success statement

**Goal:** build a certificate that passes on meaningful finite SAE interventions and exposes when a proposed selection is wrong or unresolved.

**Successful one-week result:** a checked theorem for selection optimality/regret, a documented way to establish its finite-edit premises for a useful model/objective class, and preregistered examples where the resulting decision is better supported than a coefficient-based ranking. A proof about an affine surrogate, accompanied only by plots of downstream agreement, is a partial result.

### Day 1: discover whether there is anything worth proving

| Time block | Work | Required output |
|---|---|---|
| Hours 0–1 | Freeze the model, SAE version, site, residual treatment, mask convention, feature pool rule, budget, response map, and development/held-out split. | A one-page experiment contract. The actual objective is defined before choosing the most favorable metric. |
| Hours 1–3 | Reproduce the supplied original-versus-recomputed ranking failure on a small batch. Reuse existing artifacts. | A few reproducible examples and a check that both methods perform the same intervention. |
| Hours 3–5 | Enumerate $m=12,k=3$ supports on development examples. Build scalar and vector-response surrogates and optimize a signed diagonal certificate. | Exact mask identities, exhaustive floating-point losses, Gram matrices, certificate margins, and the worst observed surrogate discrepancy. |
| Hours 5–7 | Freeze the chosen design and run the held-out batch. Compare with the original selection, recomputed selection, greedy local swaps, and the enumerated optimum. | Coverage, regret, failures, runtime, and representative witnesses. No metric tuning on this batch. |
| Hours 7–8 | Diagnose failure mode and decide whether to proceed. | A go/stop decision tied to the predeclared gate, with a written reason. |

Use a small model first—an already working Pythia/Gemma setup is more valuable than downloading the largest allowed model. A single downstream vector should retain fixed semantic meaning. Expanding the output vector solely until the certificate passes would change the research question.

Record whether failure comes from the selected support, the quadratic relaxation, output-response collinearity, nonlinear finite effects, or numerical error. Only the second and third are directly addressed by a stronger quadratic certificate. If the actual finite loss reverses the surrogate ordering, proving the surrogate more carefully will not repair the method.

**Day-one stop rule:** zero or negligible useful adjusted coverage on the small pool is enough reason to stop this particular certificate. Do not infer that all certification is impossible. If it passes only after discarding every hard example or using held-out data to redefine the metric, the test has failed.

### Day 2: establish the bridge and start the proof

Three people can work in parallel:

| Workstream | Concrete tasks | End-of-day acceptance condition |
|---|---|---|
| Formal core | Define masks, $Q,H$, exchange count, certificate, and error budget. Prove the quadratic expansion, binary-coordinate identities, equal addition/removal counts, and the exchange bound. | The central finite inequality is checked, or the remaining lemma is small and explicit. No `sorry` in claimed results; inspect theorem axioms. |
| Model connection | Find a conservative finite-edit bound for the demonstrated model/objective class. Where useful, handle known output normalization exactly instead of bounding an entire transformer by one global Lipschitz constant. Account for frozen attention, reconstruction residuals, and floating-point/extraction error separately. | A sound bound that actually fits inside the observed margin on at least some cases, and a cost estimate below exhaustive downstream evaluation. |
| Adversarial review and reproduction | Try near-threshold edits, nearly duplicate response columns, altered budgets, different magnitudes, and another available SAE family or layer. Construct competing masks whenever a claim fails. | A compact set of successful cases, honest abstentions, and counterexamples; no false acceptance. |

The first algebraic target should be the margin inequality, not a polished optimizer. External numerical optimization can search for a witness; the formal checker should verify what the witness establishes.

For the model connection, sampled derivatives are useful diagnostics, not proof premises verified by sampling. If the only practical regime is a final-layer objective with tractable normalization, state that restriction prominently. Do not describe it as a guarantee for arbitrary mid-layer circuits.

**Day-two stop rule:** if the project can certify only a frozen surrogate or requires evaluating every candidate support to bound its error, it has not yet met the intended practical bar. Preserve the diagnostic result, but do not spend days three through seven polishing a claim with that unresolved gap.

### Days 3–7, if the gates pass

Finish the certificate checker and actual-objective bridge; reproduce on a second setup; document one failure family; and have a reviewer check the English-to-Lean quantifiers and extraction assumptions. The final artifact should state the candidate universe, objective, budget, numerical model, certificate coverage, and abstention rate. The theorem's conclusion is about intervention loss, not the semantic purity of every SAE feature or the absence of hidden unsafe behavior.

## 6. Attractive ideas that should not be mistaken for fresh results

Several short derivations looked promising but failed the novelty or usefulness test:

- **Generic SAE identifiability under RIP:** directly overlaps current dictionary-learning work [R3].
- **A Taylor remainder for attribution patching:** direct 2026 overlap [R5], [R6]. The group-selection and non-vacuity problem remains the possible contribution.
- **A stability LP for prover–estimator debate:** already in the corrected paper [R25].
- **A finite-temperature LLC confound:** already discussed theoretically [R14]. A sharp calibration result needs a consequential application.
- **A rank-one perturbation invisible on a calibration subspace:** immediate linear algebra. Candidate 5 becomes interesting only through a realistic collision in a concrete detector.
- **Combining marginal monitor failures by independence:** disproving this in general is elementary. Candidate 3 requires changed operational conclusions and a defensible conditional model.
- **A sharp softmax-drift bound:** for $p=\operatorname{softmax}(z)$, $q=\operatorname{softmax}(z+\delta)$, the bound $\operatorname{TV}(p,q)\le\tanh((\max\delta-\min\delta)/4)$ is a known Hilbert-metric consequence [R26]. It may help bound frozen-attention error, but should not be marketed as a new theorem.
- **Commuting SAE deletion operators:** generic impossibilities for too many distinct commuting rank-one projectors are classical. The practical question is which features are simultaneously reachable/coactive and whether the pipeline re-encodes between edits. Global overcompleteness alone does not answer it.

## 7. Checks performed during this assessment

These checks are formulation sanity tests, not substitutes for the proposed real-model work.

1. **Candidate 1:** generated 100 random least-squares instances with 8 features, budget 3, and 12 output coordinates; checked all 56 supports per instance against a valid constant-diagonal lower bound. Across 5,600 comparisons, minimum floating-point slack was approximately $-7.1\times10^{-15}$, consistent with roundoff. This checks signs and exchange factors. It says nothing about SAE non-vacuity.
2. **Candidate 2:** checked the Bellman recurrence with Python rational arithmetic, including the exact $19/64$ two-round example and the closed form at larger horizons. No neural recognition model was tested.
3. **Candidate 4:** numerical integration of the Gibbs family produced the table above. No learned-checkpoint transition was explained or disproved.
4. **Softmax bound:** 10,000 random finite-dimensional cases had no positive numerical violation; the largest ratio to the bound was approximately 0.999995. This is a sanity check of a known inequality, not a novelty claim.

The following compact code reproduces the first three types of checks. It is included as research provenance, not as a test suite for the repository.

```python
import itertools
from fractions import Fraction
import numpy as np
from scipy.integrate import quad

rng = np.random.default_rng(20261126)
min_slack = float("inf")
for _ in range(100):
    m, k, p = 8, 3, 12
    V, b = rng.normal(size=(p, m)), rng.normal(size=p)
    masks = np.array([
        np.eye(m, dtype=int)[list(S)].sum(axis=0)
        for S in itertools.combinations(range(m), k)
    ])
    loss = ((masks @ V.T - b) ** 2).sum(axis=1)
    s0 = masks[loss.argmin()]
    G, g = V.T @ V, 2 * V.T @ (V @ s0 - b)
    d = np.linalg.eigvalsh(G)[0] - 1e-9
    gamma = min(g[s0 == 0] + d) - max(g[s0 == 1] - d)
    for s, value in zip(masks, loss):
        exchanges = ((s == 1) & (s0 == 0)).sum()
        slack = value - ((V @ s0 - b) ** 2).sum() - exchanges * gamma
        min_slack = min(min_slack, slack)
print("C1 minimum floating-point slack:", min_slack)

e = Fraction(1, 4)
for N in (1, 2, 5):
    value = Fraction(0)
    for _ in range(N):
        value = max(e, e*e + (1-e*e)*value,
                    e*e + (1-e)*value, value)
    assert value == 1 - (1-e)*(1-e*e)**(N-1)
    print("C2", N, value)

k = 2
for z in (0.01, 0.1, 1, 10):
    def integral(power):
        return quad(lambda u: (u**(2*k)+z*u*u)**power
                    * np.exp(-u**(2*k)-z*u*u), 0, np.inf)[0]
    Z = integral(0)
    mean = integral(1) / Z
    variance = integral(2) / Z - mean**2
    print("C4", z, mean, variance)
```

## 8. Sources and verification notes

The numbered references are evidence for the literature positioning, not attributions of the proposed statements to those authors. Primary proceedings/author pages and accessible papers were preferred. This bibliography intentionally avoids relying on secondary summaries for theorem details.

1. **[R1] Marks et al., _Sparse Feature Circuits: Discovering and Editing Interpretable Causal Graphs in Language Models_, ICLR 2025.** [Author project page](https://features.baulab.info/). Primary method description inspected.
2. **[R2] Ameisen et al., _Circuit Tracing: Revealing Computational Graphs in Language Models_, 2025.** [Primary technical report](https://transformer-circuits.pub/2025/attribution-graphs/methods.html). Method and limitations inspected.
3. **[R3] Nelson, Karaletsos, Locatello, _Toward Identifiable Sparse Autoencoders_, ICML 2026.** [PMLR](https://proceedings.mlr.press/v306/nelson26a.html). Primary proceedings abstract inspected; no claim here to have rechecked every theorem.
4. **[R4] Hanna, Pezzelle, Belinkov, _Have Faith in Faithfulness: Going Beyond Circuit Overlap When Finding Model Mechanisms_, COLM 2024.** [arXiv](https://arxiv.org/abs/2403.17806). Primary abstract inspected.
5. **[R5] Zhang and Wang, _When Attribution Patching Lies: Diagnosis and a Second-Order Correction_, 2026.** [arXiv:2606.09899](https://arxiv.org/abs/2606.09899). Indexed primary abstract verified; direct full-text retrieval unavailable. Used as a novelty warning about error bounds/HVP correction, not as a fully audited theorem.
6. **[R6] Zhang, Zheng, Wang, _Correcting Attribution Patching with a Few Exact Measurements_, 2026.** [arXiv:2610.27393](https://arxiv.org/abs/2610.27393). Indexed primary abstract verified; full-text theorem audit unavailable.
7. **[R7] Anani et al., _Certified Circuits: Stability Guarantees for Mechanistic Circuits_, ICML 2026.** [PMLR](https://proceedings.mlr.press/v306/anani26a.html). Primary proceedings page inspected; the stated guarantee concerns concept-dataset edits.
8. **[R8] Barin-Pacela et al., _Stop Probing, Start Coding: Why Linear Probes and Sparse Autoencoders Fail at Compositional Generalization_, UAI 2026.** [PMLR](https://proceedings.mlr.press/v337/barin-pacela26a.html). Primary proceedings abstract inspected.
9. **[R9] Bailey et al., _Obfuscated Activations Bypass LLM Latent-Space Defenses_.** [arXiv:2412.09565](https://arxiv.org/abs/2412.09565); [author project](https://obfuscated-activations.github.io/). Primary indexed claims verified. Version/venue labels are not used to make novelty claims here.
10. **[R10] Gardner-Challis et al., _When can we trust untrusted monitoring? A safety case sketch across collusion strategies_, 2026.** [Primary HTML, v1](https://arxiv.org/html/2602.20628v1). Sections on binary scores, score dependence, and protocol scope inspected directly.
11. **[R11] Greenblatt et al., _AI Control: Improving Safety Despite Intentional Subversion_, 2023/2024.** [arXiv](https://arxiv.org/abs/2312.06942). Primary abstract inspected.
12. **[R12] Puertolas Merenciano et al., _Detecting Backdoored LoRAs from Weights Alone_, v3, 7 April 2026.** [Primary HTML](https://arxiv.org/html/2602.15195v3). Threat model and full detector feature definitions inspected. Older metadata may use _Weight space Detection of Backdoors in LoRA Adapters_.
13. **[R13] Lau, Furman, Wang, Murfet, Wei, _The Local Learning Coefficient: A Singularity-Aware Complexity Measure_, AISTATS 2025.** [PMLR](https://proceedings.mlr.press/v258/lau25a.html). Primary proceedings page inspected.
14. **[R14] Chen and Murfet, _Modes of Sequence Models and Learning Coefficients_, 2025.** [arXiv:2504.18048](https://arxiv.org/abs/2504.18048). Primary abstract and paper consulted in the research pass; finite-temperature resolution is explicit.
15. **[R15] Jacob Epifano, _Linear does not mean regular: Jacobian rank limits the learning coefficient_.** [Author research post](https://jrepifano.github.io/research/llc-jacobian-rank/), with linked companion on hyperparameters. A primary research post, not a peer-reviewed paper; inspected for the localization-confound discussion.
16. **[R16] Sergeant-Perthuis, Tsigaridas, Tsukahara, _Exact Algebraic Computation of Learning Coefficients for Two-Dimensional Singular Models_, v2, 21 November 2026.** [arXiv:2608.20183](https://arxiv.org/abs/2608.20183). Primary abstract verified; detailed algorithm claims beyond that scope are not used.
17. **[R17] Pörn, Nissfolk, Skjäl, Westerlund, _Solving 0–1 quadratic programs by reformulation techniques_, 2017.** [Author-institution publication page](https://research.abo.fi/en/publications/solving-01-quadratic-programs-by-reformulation-techniques/). Confirms the established diagonal/semidefinite reformulation machinery.
18. **[R18] Griffin, Thomson, Shlegeris, Abate, _Games for AI Control: Models of Safety Evaluations of AI Deployment Protocols_, arXiv:2409.07985, current v2 May 2026.** [Primary abstract](https://arxiv.org/abs/2409.07985). General game framework is prior work.
19. **[R19] Iyengar, _Robust Dynamic Programming_, 2005.** [Primary journal page](https://pubsonline.informs.org/doi/abs/10.1287/moor.1040.0129). The conditional uncertainty/rectangularity issue is explicit.
20. **[R20] Nilim and El Ghaoui, _Robust Control of Markov Decision Processes with Uncertain Transition Matrices_, 2005.** [Author-hosted paper](https://people.eecs.berkeley.edu/~elghaoui/Pubs/RobMDP_OR2005.pdf). Primary text inspected.
21. **[R21] Goldwasser, Kim, Vaikuntanathan, Zamir, _Planting Undetectable Backdoors in Machine Learning Models_.** [arXiv:2204.06974](https://arxiv.org/abs/2204.06974). Primary abstract inspected; its black-box and white-box constructions have different scopes.
22. **[R22] Huang et al., _A Formal Framework for Understanding Length Generalization in Transformers_, ICLR 2025.** [arXiv:2410.02140](https://arxiv.org/abs/2410.02140). Primary abstract inspected.
23. **[R23] Izzo, Nichani, Lee, _Quantitative Bounds for Length Generalization in Transformers_, 2025.** [arXiv:2510.27015](https://arxiv.org/abs/2510.27015). Primary abstract and paper consulted; do not interpret its assumptions as guarantees for arbitrary trained weights.
24. **[R24] Eric Neyman, _A computational no-coincidence principle_, ARC, 14 February 2025.** [Primary statement](https://www.alignment.org/blog/a-computational-no-coincidence-principle/). Exact conjecture inspected.
25. **[R25] Brown-Cohen, Irving, Piliouras, Chen, Li, Xun, _Avoiding Obfuscation with Prover-Estimator Debate_, v2, July 2026.** [Primary PDF](https://arxiv.org/pdf/2506.13609). The definition correction, usefulness/soundness distinction, and Appendix A.4 were checked in the research pass.
26. **[R26] Cohen and Fausti, _Hyperbolic contractivity and the Hilbert metric on probability measures_, 2023/2024.** [arXiv:2309.02413](https://arxiv.org/abs/2309.02413). Primary abstract verified; cited to avoid rediscovering the sharp metric comparison.

27. **[R27] Yingjia Cai, _SIVE finite-scale local-probe experiments_, research code.** [Author repository README](https://github.com/yingjiacai/SIVE/blob/main/README.md). Primary README inspected; it explicitly scopes its variance statistic as a finite-path, finite-scale probe. The associated paper was located but its full primary text was not available for a theorem audit, so this report relies only on the repository statements.

**Additional checked novelty lead:** _What Do Sparse Autoencoder Feature Discovery Scores Identify? From Activations to Interventions_, [arXiv:2610.15850](https://arxiv.org/abs/2610.15850). Its indexed primary abstract describes observational/interventional identification limitations. Full text was not available for a theorem audit, so it is a reason to investigate overlap, not a basis for stronger claims here.

**Unresolved novelty lead:** _Identifiable Interventions from Nonidentifiable Sparse Codes_, [OpenReview submission](https://openreview.net/forum?id=zRMBPEX4fo). The primary page/PDF hit an access-verification wall. Secondary summaries suggest close overlap, but their detailed claims are not treated as verified. Resolve this before claiming priority for any intervention-identifiability result.

[R1]: https://features.baulab.info/
[R2]: https://transformer-circuits.pub/2025/attribution-graphs/methods.html
[R3]: https://proceedings.mlr.press/v306/nelson26a.html
[R4]: https://arxiv.org/abs/2403.17806
[R5]: https://arxiv.org/abs/2606.09899
[R6]: https://arxiv.org/abs/2610.27393
[R7]: https://proceedings.mlr.press/v306/anani26a.html
[R8]: https://proceedings.mlr.press/v337/barin-pacela26a.html
[R9]: https://arxiv.org/abs/2412.09565
[R10]: https://arxiv.org/html/2602.20628v1
[R11]: https://arxiv.org/abs/2312.06942
[R12]: https://arxiv.org/html/2602.15195v3
[R13]: https://proceedings.mlr.press/v258/lau25a.html
[R14]: https://arxiv.org/abs/2504.18048
[R15]: https://jrepifano.github.io/research/llc-jacobian-rank/
[R16]: https://arxiv.org/abs/2608.20183
[R17]: https://research.abo.fi/en/publications/solving-01-quadratic-programs-by-reformulation-techniques/
[R18]: https://arxiv.org/abs/2409.07985
[R19]: https://pubsonline.informs.org/doi/abs/10.1287/moor.1040.0129
[R20]: https://people.eecs.berkeley.edu/~elghaoui/Pubs/RobMDP_OR2005.pdf
[R21]: https://arxiv.org/abs/2204.06974
[R22]: https://arxiv.org/abs/2410.02140
[R23]: https://arxiv.org/abs/2510.27015
[R24]: https://www.alignment.org/blog/a-computational-no-coincidence-principle/
[R25]: https://arxiv.org/pdf/2506.13609
[R26]: https://arxiv.org/abs/2309.02413
[R27]: https://github.com/yingjiacai/SIVE/blob/main/README.md
