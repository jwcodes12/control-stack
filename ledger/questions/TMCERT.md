QUESTION (campaign TMCERT, v2 after two design-review rounds: a certificate checker for finite-horizon stateful control
games; trusted-monitoring layer, direction A). Game: Blue's controller folded into rows (catastrophe cat n s a,
continuation K n s a s'); model index theta; row-local admissibility adm n s a theta; nature selects admissible rows per
cell after every history (rectangular). Claims: (S) a horizon-N Bellman supersolution V bounds risk for every randomised
history-dependent Red and every selector admissible below N; (P) risk in [0,1] for lawful rows; (S') finite seeded
mixtures; (Fx) fixed-model certificate; (FxGap) rectangular is strictly more conservative (3/4 vs 1/2); (Obs) observation
lift; (T) single-model tightness: Vstar least certificate, in [0,1], attained by a deterministic time-dependent Markov Red;
(TR) robust tightness for finite model sets; (U) usefulness sub-solution for the same controller; (Q) computable rational
checker (decide +kernel) with soundness bridge (certificate, V >= 0, Lawful at all horizons; guards t, k > 0); (Vx) vertex
certificates certify the convex-hull family; (Abs) deployment through an abstraction: CoveredV (each concrete row's value
against V dominated by an admissible abstract row) => every concrete history-dependent Red bounded; equality coverage is a
special case. Witness: checker on the FxGap tables, consumed bound 3/4 attained, equality and interior-row coverage.
Brute force and two reviewers' exact checks: all conjuncts true. Classical infrastructure (MDP verification theorem,
robust DP, simulation by abstraction).
