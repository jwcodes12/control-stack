QUESTION (campaign TMGAC, v1 after a design review: Games for AI Control, arXiv 2409.07985 v2, trusted monitoring with a
perfect auditor, as an instance of PL_TMCERTF1). gac: state = coins c; zones TA (backdoor audit), TD (backdoor
audit-or-defer), FA (safe audit); audit with a coin catches; with no coin runs; defer continues. gacQ: ROC f, FPRs qa <= qd,
index m = n + 1; c = 0 convention qa m 0 = 0, f 0 = 0. Claims: (L) lawful; (LQ) adapter lawful for valid thresholds and
monotone ROC; (Z) 1 - risk(constRed beta) = zGAC (App. C.1 case analysis; algebraic identity); (UZ) honest used-solution
reward 1 - qd + [c>0] qa gives uGAC (App. C.2: run or audited-and-safe count, deferred does not); (M) finite mixtures of
constant rates; (Lip) |risk(b) - risk(b')| <= N|b - b'|; (Grid) grid j/J bounds every rate up to N/(2J); (W) at C = 0 always
backdooring attains Vstar; (T5) three problems, one coin: constant rates <= 13/50 (equality at 4/5); a round-index-only Red
11/32 = Vstar; a coin-count-only Red 9/32. Witness: exG3 = gacQ (genuine ROC), certificate exV3 consumed (every Red <= 11/32),
usefulness 19/8; adapter instance safety 63/64, usefulness 3/2; audited-only usefulness 1. Exact numerics: 2400 bridge
comparisons with monotone ROC tables and unrestricted algebra, 0 mismatches. A sensitivity result against GAC's explicit
null-observation assumption, not a refutation.
