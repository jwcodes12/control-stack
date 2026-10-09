# SC-07 egress quota run (evidence, PREREG-SC07-EGRESSQ-v1)

- commit: `5b7d2d7e3e3e3f712dec97737a1fc8942a7b5a59` (harness/prereg status: `clean`)
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`, nftables v1.0.9 (Old Doc Yak #3)
- started 2026-10-09T05:32:28.143888Z, finished 2026-10-09T05:33:12.965190Z, wall 44.8 s
- host unchanged: {"links": true, "sysctls": true, "routes4_sha256": true, "routes6_sha256": true, "nft_ruleset_stateless_sha256": true, "netns": true}
- overall: **PASS**

| hypothesis | reps passed | verdict |
|---|---|---|
| H1 | 5/5 | PASS |
| H2 | 5/5 | PASS |
| H3 | 5/5 | PASS |
| H4 | 5/5 | PASS |
| H5 | 5/5 | PASS |
| H6 | 5/5 | PASS |

## Key measurements per repetition

- H2 rep 1: {"fwd_up_minus_quota": -39164, "fwd_up_minus_sink": 8172, "fwd_up_packets": 157, "quota_drop_packets": 23, "sink_minus_quota": -47336}
- H4 rep 1: {"after_halt_end": 0, "after_halt_start": 65536, "halt_latency_s": 0.018552, "sink_total": 1179648}
- H2 rep 2: {"fwd_up_minus_quota": -56280, "fwd_up_minus_sink": 9368, "fwd_up_packets": 180, "quota_drop_packets": 47, "sink_minus_quota": -65648}
- H4 rep 2: {"after_halt_end": 0, "after_halt_start": 65536, "halt_latency_s": 0.029678, "sink_total": 1245184}
- H2 rep 3: {"fwd_up_minus_quota": -6828, "fwd_up_minus_sink": 8380, "fwd_up_packets": 161, "quota_drop_packets": 34, "sink_minus_quota": -15208}
- H4 rep 3: {"after_halt_end": 0, "after_halt_start": 65536, "halt_latency_s": 0.025917, "sink_total": 1179648}
- H2 rep 4: {"fwd_up_minus_quota": -41524, "fwd_up_minus_sink": 8692, "fwd_up_packets": 167, "quota_drop_packets": 33, "sink_minus_quota": -50216}
- H4 rep 4: {"after_halt_end": 0, "after_halt_start": 65536, "halt_latency_s": 0.017888, "sink_total": 1179648}
- H2 rep 5: {"fwd_up_minus_quota": -46112, "fwd_up_minus_sink": 9472, "fwd_up_packets": 182, "quota_drop_packets": 56, "sink_minus_quota": -55584}
- H4 rep 5: {"after_halt_end": 0, "after_halt_start": 65536, "halt_latency_s": 0.020189, "sink_total": 1179648}

## Failed checks

none
