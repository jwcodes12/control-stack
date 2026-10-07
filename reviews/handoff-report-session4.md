# Session 4 handoff report

- Added `DESIGN-A2.md`: finite-sample simultaneous-band pipeline, discretised threshold and tie handling, interval-to-vertex model, TMCERT checker route, assumptions, limits, and cost estimate.
- Added `numerics/design_a2_certificate.py`, generating exact-rational JSON inputs and a 101-row CSV table for `N=100`, two coins, three states, two actions, and two illustrative ROC vertices. It computed 1,200 risk inequalities.
- Fixture outputs: full-information rectangular upper bound about 0.45051; fixed-rate witness beta `37/50`, risk about 0.33281; clocked final-50 witness risk about 0.31822; honest expected used solutions about 52.464/100. Exact values are in the generated artifacts.
- The ROC vertices `[2q,3q]` are synthetic and not based on samples. No confidence statement, `decide +kernel` run, new theorem, or frozen CID was produced.
- Next: acquire the labelled validation sample, freeze the threshold grid, derive simultaneous rational bands, regenerate the table, and measure the concrete Lean checker cost.
