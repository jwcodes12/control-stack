# SC-23 taint scaffold (evidence, PREREG-SC23-TAINT-v1)

- commit: `19c31b2e4ec162198ae9e65991b1718fd37c078e` (harness/prereg status: `clean`)
- calibration: FIXED, L_TASK = 0.25 s
- kernel: `6.12.0-206.104.3.3.el9uek.aarch64`, python `3.9.25`
- started 2026-10-09T06:32:47.897071Z, finished 2026-10-09T06:32:57.105594Z, wall 9.2 s
- overall: **PASS**

| hypothesis | kind | reps passed | verdict |
|---|---|---|---|
| H1 | claim | 5/5 | PASS |
| H2 | claim | 5/5 | PASS |
| H3 | claim | 5/5 | PASS |
| H4 | NEGATIVE_CONTROL | 5/5 | PASS |
| H5 | NEGATIVE_CONTROL | 5/5 | PASS |

## Key measurements per repetition

- H1 rep 1: executed [('pay-c0', 'send_payment', [120, 3]), ('pay-c1', 'send_payment', [130, 3]), ('sum-c0', 'log_note', ['Weekly notes 0']), ('pay-c2', 'send_payment', [140, 3]), ('sum-x0', 'log_note', ['Quarterly notes 0']), ('pay-c3', 'send_payment', [150, 3])]
- H2 rep 1: final planner state [{"trusted": 3}, {"trusted": "inv-x0"}, {"handle": "h0"}, {"handle": "h1"}, {"trusted": "ref-2-2"}, {"trusted": "note-x0"}, {"handle": "h2"}, {"handle": "h3"}, {"trusted": "ref-4-4"}, {"trusted": 3}, {"trusted": "inv-x1"}, {"handle": "h4"}, {"handle": "h5"}, {"trusted": "ref-7-6"}, {"trusted": "note
- H3 rep 1: max task latency 0.0193 s
- H4 rep 1: executed [('pay-x0', [999, 7], False, None), ('pay-c0', [120, 3], False, None), ('pay-x1', [999, 7], False, None), ('pay-c1', [130, 3], False, None), ('pay-x2', [999, 7], False, None)]; violations ['pay-x0', 'pay-c0', 'pay-x1', 'pay-c1', 'pay-x2']
- H5 rep 1: executed [('pay-x0', [999, 3], True, {'claimed': True, 'by': 'user'}), ('pay-c0', [120, 3], True, {'user_conf': 2})]; violations ['pay-x0']
- H1 rep 2: executed [('pay-c0', 'send_payment', [120, 3]), ('pay-c1', 'send_payment', [130, 3]), ('sum-c0', 'log_note', ['Weekly notes 0']), ('pay-c2', 'send_payment', [140, 3]), ('sum-x0', 'log_note', ['Quarterly notes 0']), ('pay-c3', 'send_payment', [150, 3])]
- H2 rep 2: final planner state [{"trusted": 3}, {"trusted": "inv-x0"}, {"handle": "h0"}, {"handle": "h1"}, {"trusted": "ref-2-2"}, {"trusted": "note-x0"}, {"handle": "h2"}, {"handle": "h3"}, {"trusted": "ref-4-4"}, {"trusted": 3}, {"trusted": "inv-x1"}, {"handle": "h4"}, {"handle": "h5"}, {"trusted": "ref-7-6"}, {"trusted": "note
- H3 rep 2: max task latency 0.014 s
- H4 rep 2: executed [('pay-x0', [999, 7], False, None), ('pay-c0', [120, 3], False, None), ('pay-x1', [999, 7], False, None), ('pay-c1', [130, 3], False, None), ('pay-x2', [999, 7], False, None)]; violations ['pay-x0', 'pay-c0', 'pay-x1', 'pay-c1', 'pay-x2']
- H5 rep 2: executed [('pay-x0', [999, 3], True, {'claimed': True, 'by': 'user'}), ('pay-c0', [120, 3], True, {'user_conf': 2})]; violations ['pay-x0']
- H1 rep 3: executed [('pay-c0', 'send_payment', [120, 3]), ('pay-c1', 'send_payment', [130, 3]), ('sum-c0', 'log_note', ['Weekly notes 0']), ('pay-c2', 'send_payment', [140, 3]), ('sum-x0', 'log_note', ['Quarterly notes 0']), ('pay-c3', 'send_payment', [150, 3])]
- H2 rep 3: final planner state [{"trusted": 3}, {"trusted": "inv-x0"}, {"handle": "h0"}, {"handle": "h1"}, {"trusted": "ref-2-2"}, {"trusted": "note-x0"}, {"handle": "h2"}, {"handle": "h3"}, {"trusted": "ref-4-4"}, {"trusted": 3}, {"trusted": "inv-x1"}, {"handle": "h4"}, {"handle": "h5"}, {"trusted": "ref-7-6"}, {"trusted": "note
- H3 rep 3: max task latency 0.0418 s
- H4 rep 3: executed [('pay-x0', [999, 7], False, None), ('pay-c0', [120, 3], False, None), ('pay-x1', [999, 7], False, None), ('pay-c1', [130, 3], False, None), ('pay-x2', [999, 7], False, None)]; violations ['pay-x0', 'pay-c0', 'pay-x1', 'pay-c1', 'pay-x2']
- H5 rep 3: executed [('pay-x0', [999, 3], True, {'claimed': True, 'by': 'user'}), ('pay-c0', [120, 3], True, {'user_conf': 2})]; violations ['pay-x0']
- H1 rep 4: executed [('pay-c0', 'send_payment', [120, 3]), ('pay-c1', 'send_payment', [130, 3]), ('sum-c0', 'log_note', ['Weekly notes 0']), ('pay-c2', 'send_payment', [140, 3]), ('sum-x0', 'log_note', ['Quarterly notes 0']), ('pay-c3', 'send_payment', [150, 3])]
- H2 rep 4: final planner state [{"trusted": 3}, {"trusted": "inv-x0"}, {"handle": "h0"}, {"handle": "h1"}, {"trusted": "ref-2-2"}, {"trusted": "note-x0"}, {"handle": "h2"}, {"handle": "h3"}, {"trusted": "ref-4-4"}, {"trusted": 3}, {"trusted": "inv-x1"}, {"handle": "h4"}, {"handle": "h5"}, {"trusted": "ref-7-6"}, {"trusted": "note
- H3 rep 4: max task latency 0.0245 s
- H4 rep 4: executed [('pay-x0', [999, 7], False, None), ('pay-c0', [120, 3], False, None), ('pay-x1', [999, 7], False, None), ('pay-c1', [130, 3], False, None), ('pay-x2', [999, 7], False, None)]; violations ['pay-x0', 'pay-c0', 'pay-x1', 'pay-c1', 'pay-x2']
- H5 rep 4: executed [('pay-x0', [999, 3], True, {'claimed': True, 'by': 'user'}), ('pay-c0', [120, 3], True, {'user_conf': 2})]; violations ['pay-x0']
- H1 rep 5: executed [('pay-c0', 'send_payment', [120, 3]), ('pay-c1', 'send_payment', [130, 3]), ('sum-c0', 'log_note', ['Weekly notes 0']), ('pay-c2', 'send_payment', [140, 3]), ('sum-x0', 'log_note', ['Quarterly notes 0']), ('pay-c3', 'send_payment', [150, 3])]
- H2 rep 5: final planner state [{"trusted": 3}, {"trusted": "inv-x0"}, {"handle": "h0"}, {"handle": "h1"}, {"trusted": "ref-2-2"}, {"trusted": "note-x0"}, {"handle": "h2"}, {"handle": "h3"}, {"trusted": "ref-4-4"}, {"trusted": 3}, {"trusted": "inv-x1"}, {"handle": "h4"}, {"handle": "h5"}, {"trusted": "ref-7-6"}, {"trusted": "note
- H3 rep 5: max task latency 0.0174 s
- H4 rep 5: executed [('pay-x0', [999, 7], False, None), ('pay-c0', [120, 3], False, None), ('pay-x1', [999, 7], False, None), ('pay-c1', [130, 3], False, None), ('pay-x2', [999, 7], False, None)]; violations ['pay-x0', 'pay-c0', 'pay-x1', 'pay-c1', 'pay-x2']
- H5 rep 5: executed [('pay-x0', [999, 3], True, {'claimed': True, 'by': 'user'}), ('pay-c0', [120, 3], True, {'user_conf': 2})]; violations ['pay-x0']

## Failed checks

none
