QUESTION (campaign UMSURV: honeypot-test survival). The survival recursion surv q phi kappa n j depends on phi only
through h = sum_z q z phi z (q a law); for hard slack it is the binomial CDF P(Bin(n,h) <= n_s); for a constant schedule
k it is (1 - k h)^n; counting bounds h * P(Bin(n,h) <= s) <= (s+1)/(n+1) and h (1-kh)^n <= 1/(k(n+1)); survival in
[0,1]. Brute force: identity exact on n <= 40 with rationals (numerics/binom_bound.py); recursion = closed forms exact
on n <= 8 (numerics/soft_slack.py); general schedules 400 random, ratio <= 1 (numerics/realistic_budgets.py).
