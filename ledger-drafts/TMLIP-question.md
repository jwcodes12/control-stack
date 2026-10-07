# Parameter-Lipschitz extension of finite trusted-monitoring certificates

Build a non-vacuous, kernel-checkable extension of TMCERTF1 that turns a certificate on a finite grid of models into a risk bound for every model in a rational parameter confidence box.

Definitions to formalise in the new statement:

- A row distance between finite games `G` and `H`, at `(n,s,a)`, is `|G.cat n s a - H.cat n s a| + sum_s' |G.K n s a s' - H.K n s a s'|`.
- `RowClose N G H eps` means this distance is at most `eps` for every row before horizon N.
- A finite grid covers a parameter set when every parameter in the set is within distance `h` of some grid point. A coordinatewise or abstract nonnegative distance is acceptable, but the assumptions relating it to row distance must be explicit.
- If each row of a parameterized game is L-Lipschitz in parameter distance, a certificate V for a grid point should transfer to a nearby model by inflating the horizon-n value by `n*L*h`. State all lawfulness, nonnegativity, and `[0,1]` value-range assumptions that the proof actually needs.

Claim should include the one-step certificate-transfer lemma and its finite-grid corollary: if every grid model has a certificate bounded by U, then every model in the box has a certificate/risk bound no larger than `U + N*L*h`. Reuse `PL_TMCERTF1.RiskCertUpTo`, `LawfulUpTo`, and the existing soundness result; do not redefine the game semantics.

Witness should give an exact small instance showing the dependence on row error/horizon is nontrivial (and ideally sharp at N=1), plus a finite grid covering example. The formulation must not claim a statistical confidence level or infer parameter coverage from sampled data; the statistical band and coverage argument remain external inputs. Do not edit or restate any frozen campaign.
