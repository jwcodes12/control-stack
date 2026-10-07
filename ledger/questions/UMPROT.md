QUESTION (campaign UMPROT: protocol safety). For the protocol recursion `cat`/`protocolCat` (definitions in the
statement; honeypot survival from UMSURV): (T3a) first bad submission decides, budget-sensitive: if every bad
submission's attack pass probability is <= A then for every history and adaptive generator, cat <= 1 - r + rA while an
audit is available and <= A otherwise; (T3*) a generator that submits a fixed bad x at once attains
surv * (1 - r + r E_{M x} phi); (T3) closed forms: domination form (1-r) + r L (n_s+1)/(n_h+1), hockey-stick form
(1-r) + r(delta + e^eta (n_s+1)/(n_h+1)), soft form (1-r) + r L n_s/(n_h+1). Brute force: exact DP over adaptive
generators equals the formula to 4e-16 on 300 instances with budget, recall and halting
(numerics/simulate_protocol.py; Reviewer B's independent exact-Fraction DP: 0 mismatches); the recurrence equals an
independent sampling simulation of the operational protocol within Monte Carlo error.
