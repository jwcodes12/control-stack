# Lean dependencies for 187 headline claims

Generated from elaborated Lean declarations, not source-text grep. Model-written/model-reviewed; no independent human review.

Claims: 187 (duplicates retained).

The JSON stores direct and transitive project declarations and the transitive Lean axiom set.

| # | Lean name | Direct project deps | Transitive project deps | Axioms | Standard |
|---|---|---:|---:|---|---|
| 1 | ControlStack.Deployment.Accepted | 2 | 31 | Quot.sound, propext | yes |
| 2 | ControlStack.Deployment.exclusive_sink | 20 | 33 | Quot.sound, propext | yes |
| 3 | ControlStack.Deployment.database_custody | 20 | 33 | Quot.sound, propext | yes |
| 4 | ControlStack.Deployment.runtime_exclusive | 11 | 37 | Quot.sound, propext | yes |
| 5 | ControlStack.Deployment.agent_not_receiver_uid | 20 | 33 | Quot.sound, propext | yes |
| 6 | ControlStack.Deployment.agent_call_legal | 13 | 54 | Quot.sound, propext | yes |
| 7 | ControlStack.Deployment.protocol_safe | 8 | 110 | Quot.sound, propext | yes |
| 8 | ControlStack.Deployment.one_use | 7 | 68 | Quot.sound, propext | yes |
| 9 | ControlStack.Deployment.gate_contract | 14 | 125 | Quot.sound, propext | yes |
| 10 | ControlStack.Deployment.broker_contract | 7 | 67 | Quot.sound, propext | yes |
| 11 | ControlStack.Deployment.deployment_safe | 49 | 162 | Quot.sound, propext | yes |
| 12 | ControlStack.Deployment.accepted_no_avoided_path | 18 | 38 | Quot.sound, propext | yes |
| 13 | ControlStack.Deployment.accepted_path_safety_monotone | 15 | 40 | Quot.sound, propext | yes |
| 14 | ControlStack.Deployment.path_edge_subset | 11 | 15 | (none) | yes |
| 15 | ControlStack.Deployment.requested_monotonicity_counterexample | 15 | 77 | Quot.sound, propext | yes |
| 16 | ControlStack.Deployment.deployment_broker_safe | 44 | 125 | Quot.sound, propext | yes |
| 17 | ControlStack.Deployment.indexed_receipts_sound | 15 | 73 | propext | yes |
| 18 | ControlStack.TrustedBroker.transaction_preserves | 56 | 59 | Quot.sound, propext | yes |
| 19 | ControlStack.TrustedBroker.transaction_coherent | 51 | 57 | Quot.sound, propext | yes |
| 20 | ControlStack.TrustedBroker.halted_absorbing | 52 | 56 | propext | yes |
| 21 | ControlStack.TrustedBroker.committed_nonce_unusable | 41 | 43 | propext | yes |
| 22 | ControlStack.TrustedBroker.trace_preserves | 7 | 64 | Quot.sound, propext | yes |
| 23 | ControlStack.Deployment.TranscriptReplay.runtime_trace | 11 | 113 | Quot.sound, propext | yes |
| 24 | ControlStack.Deployment.TranscriptReplay.final_safe | 7 | 123 | Quot.sound, propext | yes |
| 25 | ControlStack.Deployment.TranscriptReplay.replay_was_not_allowed | 12 | 62 | propext | yes |
| 26 | ControlStack.Deployment.TranscriptReplay.omitted_tail_is_accepted | 5 | 103 | Quot.sound, propext | yes |
| 27 | ControlStack.SafetyCaseSC01.sc01_case | 18 | 51 | Classical.choice, Quot.sound, propext | yes |
| 28 | ControlStack.GatewayCore.core_bound | 16 | 50 | Classical.choice, Quot.sound, propext | yes |
| 29 | ControlStack.Covert.covert_bound_lifetime | 3 | 4 | Classical.choice, Quot.sound, propext | yes |
| 30 | ControlStack.ChannelInstances.sc02_accumulated | 4 | 19 | Classical.choice, Quot.sound, propext | yes |
| 31 | ControlStack.ChannelInstances.rekey_epoch | 5 | 25 | Classical.choice, Quot.sound, propext | yes |
| 32 | ControlStack.EgressGate.step_safe | 34 | 72 | Quot.sound, propext | yes |
| 33 | ControlStack.EgressGate.trace_safe | 7 | 74 | Quot.sound, propext | yes |
| 34 | ControlStack.ChannelInstances.log_channel | 3 | 20 | Classical.choice, Quot.sound, propext | yes |
| 35 | ControlStack.ChannelInstances.canonical_seq | 3 | 20 | Classical.choice, Quot.sound, propext | yes |
| 36 | ControlStack.SC05.cap_does_not_prevent | 3 | 6 | Classical.choice, Quot.sound, propext | yes |
| 37 | ControlStack.SC05.zero_dependence_is_blind | 3 | 3 | Classical.choice, Quot.sound, propext | yes |
| 38 | ControlStack.SC05.forbidden_never_executes | 8 | 23 | Quot.sound, propext | yes |
| 39 | ControlStack.SC06.sc06_safe | 17 | 81 | Quot.sound, propext | yes |
| 40 | ControlStack.SC06.halt_freezes | 9 | 62 | Quot.sound, propext | yes |
| 41 | ControlStack.SC07Exfil.windows_needed | 4 | 8 | Quot.sound, propext | yes |
| 42 | ControlStack.SC07Exfil.sc07_mixed | 4 | 17 | Classical.choice, Quot.sound, propext | yes |
| 43 | ControlStack.SC07Exfil.sc07_fixed_budget | 11 | 70 | Classical.choice, Quot.sound, propext | yes |
| 44 | ControlStack.SC07Exfil.expected_leak_le | 5 | 7 | Classical.choice, Quot.sound, propext | yes |
| 45 | ControlStack.SC07Exfil.observable_schedule_exfil | 3 | 5 | Classical.choice, Quot.sound, propext | yes |
| 46 | ControlStack.SC07Exfil.datacenter_example | 4 | 17 | Classical.choice, Quot.sound, propext | yes |
| 47 | ControlStack.SC07Liveness.sc07_safe | 22 | 52 | Classical.choice, Quot.sound, propext | yes |
| 48 | ControlStack.SC07Liveness.upload_completes | 22 | 31 | Quot.sound, propext | yes |
| 49 | ControlStack.SC07Liveness.exfil_needs_windows | 11 | 57 | Classical.choice, Quot.sound, propext | yes |
| 50 | ControlStack.SC07Liveness.shared_quota_blocks | 11 | 42 | Quot.sound, propext | yes |
| 51 | ControlStack.SC07Refinement.concrete_safe | 31 | 116 | Classical.choice, Quot.sound, propext | yes |
| 52 | ControlStack.SC07Refinement.concrete_wire_lt | 34 | 46 | Classical.choice, Quot.sound, propext | yes |
| 53 | ControlStack.SC07Refinement.concrete_halt_freezes | 40 | 98 | Classical.choice, Quot.sound, propext | yes |
| 54 | ControlStack.SC07Refinement.sink_within_quota | 14 | 118 | Classical.choice, Quot.sound, propext | yes |
| 55 | ControlStack.SC08.sc08_safe | 8 | 47 | Quot.sound, propext | yes |
| 56 | ControlStack.SC08.safe_of_sound | 9 | 44 | Quot.sound, propext | yes |
| 57 | ControlStack.SC08.halt_freezes | 9 | 39 | Quot.sound, propext | yes |
| 58 | ControlStack.SC09.sc09_safe | 8 | 67 | Quot.sound, propext | yes |
| 59 | ControlStack.SC09.spawn_attenuates | 17 | 47 | Quot.sound, propext | yes |
| 60 | ControlStack.SC09.halt_freezes | 9 | 52 | Quot.sound, propext | yes |
| 61 | ControlStack.SC10.sc10_safe | 15 | 63 | Quot.sound, propext | yes |
| 62 | ControlStack.SC10.policy_admin_only | 13 | 61 | Quot.sound, propext | yes |
| 63 | ControlStack.SC10.halt_freezes | 9 | 44 | Quot.sound, propext | yes |
| 64 | ControlStack.SC10.sc10_safe | 15 | 63 | Quot.sound, propext | yes |
| 65 | ControlStack.SC10.policy_admin_only | 13 | 61 | Quot.sound, propext | yes |
| 66 | ControlStack.SC12.sc12_safe | 8 | 56 | Classical.choice, Quot.sound, propext | yes |
| 67 | ControlStack.SC12.no_fire_after_end | 11 | 51 | Classical.choice, Quot.sound, propext | yes |
| 68 | ControlStack.SC12.halt_freezes | 8 | 37 | Quot.sound, propext | yes |
| 69 | ControlStack.AuthInstances.sc12_safe_authenticated | 20 | 93 | Classical.choice, Quot.sound, propext | yes |
| 70 | ControlStack.AuthInstances.forged12_spawns_without_auth | 10 | 48 | Quot.sound, propext | yes |
| 71 | ControlStack.AuditDispatch.trace_safe | 8 | 22 | Quot.sound, propext | yes |
| 72 | ControlStack.AuditDispatch.app_cannot_effect | 12 | 30 | Quot.sound, propext | yes |
| 73 | ControlStack.SC14.sc14_safe | 10 | 66 | Classical.choice, Quot.sound, propext | yes |
| 74 | ControlStack.SC14.halt_freezes | 11 | 40 | Quot.sound, propext | yes |
| 75 | ControlStack.AntiRollback.rollback_transfer | 23 | 69 | Quot.sound, propext | yes |
| 76 | ControlStack.SC15.sc15_safe | 11 | 66 | Quot.sound, propext | yes |
| 77 | ControlStack.SC15.halt_freezes | 9 | 56 | Quot.sound, propext | yes |
| 78 | ControlStack.AuthInstances.sc15_safe_authenticated | 26 | 104 | Quot.sound, propext | yes |
| 79 | ControlStack.AuthInstances.forged15_merges_without_auth | 13 | 80 | Quot.sound, propext | yes |
| 80 | ControlStack.SC16.sc16_safe | 9 | 107 | Quot.sound, propext | yes |
| 81 | ControlStack.SC16.sc16_reviewed_content | 27 | 108 | Quot.sound, propext | yes |
| 82 | ControlStack.SC16.halt_freezes | 9 | 57 | Quot.sound, propext | yes |
| 83 | ControlStack.SC16Disjoint.sc16_safe_disjoint | 29 | 109 | Quot.sound, propext | yes |
| 84 | ControlStack.SC16Disjoint.overlap_reviewer_is_agent | 18 | 68 | Quot.sound, propext | yes |
| 85 | ControlStack.AuthInstances.sc16_safe_authenticated | 30 | 148 | Quot.sound, propext | yes |
| 86 | ControlStack.AuthInstances.forged16_deploys_without_auth | 13 | 79 | Quot.sound, propext | yes |
| 87 | ControlStack.SC16Refinement.concrete_safe | 14 | 176 | Quot.sound, propext | yes |
| 88 | ControlStack.SC16Refinement.concrete_reviewed_content | 22 | 177 | Quot.sound, propext | yes |
| 89 | ControlStack.SC17.sc17_safe | 10 | 93 | Quot.sound, propext | yes |
| 90 | ControlStack.SC17.reconcile_restores | 17 | 69 | Quot.sound, propext | yes |
| 91 | ControlStack.SC17.halt_freezes | 11 | 72 | Quot.sound, propext | yes |
| 92 | ControlStack.SC17Drift.drift_bounded | 8 | 43 | Classical.choice, Quot.sound, propext | yes |
| 93 | ControlStack.SC17Drift.drift_lifetime | 12 | 40 | Classical.choice, Quot.sound, propext | yes |
| 94 | ControlStack.AuthInstances.sc17_safe_authenticated | 30 | 138 | Quot.sound, propext | yes |
| 95 | ControlStack.AuthInstances.forged17_applies_without_auth | 13 | 85 | Quot.sound, propext | yes |
| 96 | ControlStack.SC18.sc18_safe | 15 | 60 | Classical.choice, Quot.sound, propext | yes |
| 97 | ControlStack.SC18.config_untampered | 9 | 59 | Classical.choice, Quot.sound, propext | yes |
| 98 | ControlStack.SC18.halt_freezes | 10 | 38 | Quot.sound, propext | yes |
| 99 | ControlStack.AuthInstances.sc18_safe_authenticated | 22 | 79 | Classical.choice, Quot.sound, propext | yes |
| 100 | ControlStack.AuthInstances.forged18_redirects_without_auth | 9 | 49 | Quot.sound, propext | yes |
| 101 | ControlStack.SC18Liveness.honest_release | 22 | 47 | Quot.sound, propext | yes |
| 102 | ControlStack.SC18Liveness.progress_interleaved | 26 | 52 | Quot.sound, propext | yes |
| 103 | ControlStack.SC18Liveness.silent_ticks_halt | 23 | 41 | Quot.sound, propext | yes |
| 104 | ControlStack.SC18Liveness.Resume.resume_safe | 12 | 45 | Classical.choice, Quot.sound, propext | yes |
| 105 | ControlStack.SC18Liveness.Resume.resume_progress | 19 | 27 | Quot.sound, propext | yes |
| 106 | ControlStack.SC18Refinement.concrete_safe | 18 | 111 | Classical.choice, Quot.sound, propext | yes |
| 107 | ControlStack.SC18Refinement.concrete_durable | 21 | 114 | Classical.choice, Quot.sound, propext | yes |
| 108 | ControlStack.SC19.sc19_safe | 9 | 79 | Quot.sound, propext | yes |
| 109 | ControlStack.SC19.halt_freezes | 9 | 58 | Quot.sound, propext | yes |
| 110 | ControlStack.AuthInstances.sc19_safe_authenticated | 21 | 121 | Quot.sound, propext | yes |
| 111 | ControlStack.AuthInstances.forged19_destroys_without_auth | 13 | 83 | Quot.sound, propext | yes |
| 112 | ControlStack.SC20.sc20_safe | 9 | 67 | Quot.sound, propext | yes |
| 113 | ControlStack.SC20.halt_freezes | 9 | 52 | Quot.sound, propext | yes |
| 114 | ControlStack.AuthInstances.sc20_safe_authenticated | 17 | 105 | Quot.sound, propext | yes |
| 115 | ControlStack.AuthInstances.forged20_trains_without_auth | 10 | 62 | Quot.sound, propext | yes |
| 116 | ControlStack.EvalIntegrity.sc21_safe | 11 | 49 | Quot.sound, propext | yes |
| 117 | ControlStack.EvalIntegrity.sc21_undetected_prob | 4 | 7 | Classical.choice, Quot.sound, propext | yes |
| 118 | ControlStack.EvalIntegrity.sc21_undetected_le_pow | 4 | 15 | Classical.choice, Quot.sound, propext | yes |
| 119 | ControlStack.EvalIntegrity.observable_sample_nogo | 2 | 2 | Classical.choice, Quot.sound, propext | yes |
| 120 | ControlStack.EvalIntegrityAdaptive.sc21_adaptive | 7 | 48 | Classical.choice, Quot.sound, propext | yes |
| 121 | ControlStack.EvalIntegrityAdaptive.sc21_adaptive_content | 7 | 43 | Classical.choice, Quot.sound, propext | yes |
| 122 | ControlStack.EvalIntegrityAdaptive.sc21_adaptive_recall | 10 | 69 | Classical.choice, Quot.sound, propext | yes |
| 123 | ControlStack.EvalIntegrity.sc22_unreplicated_misreport | 4 | 8 | Classical.choice, Quot.sound, propext | yes |
| 124 | ControlStack.EvalIntegrity.observable_sample_nogo | 2 | 2 | Classical.choice, Quot.sound, propext | yes |
| 125 | ControlStack.SC23.sc23_safe | 9 | 82 | Quot.sound, propext | yes |
| 126 | ControlStack.SC23.halt_freezes | 9 | 56 | Quot.sound, propext | yes |
| 127 | ControlStack.SC23Isolation.noninterference | 17 | 69 | Classical.choice, Quot.sound, propext | yes |
| 128 | ControlStack.SC23Isolation.w1_impossible | 12 | 70 | Quot.sound, propext | yes |
| 129 | ControlStack.SC23Isolation.sc23_isolated_safe | 11 | 72 | Quot.sound, propext | yes |
| 130 | ControlStack.SC23IsolationV2.noninterference_authed | 18 | 90 | Classical.choice, Quot.sound, propext | yes |
| 131 | ControlStack.SC23IsolationV2.w1_impossible_v2 | 12 | 75 | Quot.sound, propext | yes |
| 132 | ControlStack.SC23IsolationV2.sc23v2_safe_authenticated | 34 | 96 | Quot.sound, propext | yes |
| 133 | ControlStack.AuthInstances.sc23_safe_authenticated | 22 | 119 | Quot.sound, propext | yes |
| 134 | ControlStack.AuthInstances.forged23_acts_without_auth | 13 | 79 | Quot.sound, propext | yes |
| 135 | ControlStack.MonitorCollusion.pass_transfer | 4 | 4 | Classical.choice, Quot.sound, propext | yes |
| 136 | ControlStack.MonitorCollusion.collusion_uniform | 4 | 6 | Classical.choice, Quot.sound, propext | yes |
| 137 | ControlStack.MonitorCollusion.canon_channel | 2 | 3 | Classical.choice, Quot.sound, propext | yes |
| 138 | ControlStack.MonitorCollusion.phase_learning | 6 | 18 | Classical.choice, Quot.sound, propext | yes |
| 139 | ControlStack.SC25.sc25_safe | 9 | 114 | Quot.sound, propext | yes |
| 140 | ControlStack.SC25.expired_never_executes | 12 | 67 | Quot.sound, propext | yes |
| 141 | ControlStack.SC25.halt_freezes | 11 | 63 | Quot.sound, propext | yes |
| 142 | ControlStack.SC25Content.sc25_content_safe | 39 | 138 | Quot.sound, propext | yes |
| 143 | ControlStack.SC25Content.digest_only_executes_unaudited | 17 | 73 | Quot.sound, propext | yes |
| 144 | ControlStack.AuthInstances.sc25_safe_authenticated | 28 | 158 | Quot.sound, propext | yes |
| 145 | ControlStack.AuthInstances.forged25_executes_without_auth | 13 | 76 | Quot.sound, propext | yes |
| 146 | ControlStack.SC25Refinement.concrete_safe | 14 | 191 | Quot.sound, propext | yes |
| 147 | ControlStack.SC25Refinement.concrete_content_safe | 49 | 201 | Quot.sound, propext | yes |
| 148 | ControlStack.SC26.sc26_safe | 9 | 109 | Quot.sound, propext | yes |
| 149 | ControlStack.SC26.safe_of_sound | 11 | 106 | Quot.sound, propext | yes |
| 150 | ControlStack.SC26.sc26_safe_disjoint | 19 | 110 | Quot.sound, propext | yes |
| 151 | ControlStack.SC26.sc26_once | 10 | 67 | Quot.sound, propext | yes |
| 152 | ControlStack.SC26.halt_freezes | 13 | 70 | Quot.sound, propext | yes |
| 153 | ControlStack.SC26Refinement.concrete_safe | 18 | 184 | Quot.sound, propext | yes |
| 154 | ControlStack.SC26Refinement.concrete_halt | 11 | 73 | Quot.sound, propext | yes |
| 155 | ControlStack.SC26Authenticated.sc26_safe_authenticated | 38 | 144 | Quot.sound, propext | yes |
| 156 | ControlStack.SC26Authenticated.forged_approval_pays_without_auth | 16 | 162 | Quot.sound, propext | yes |
| 157 | ControlStack.AuthenticatedAdv.sc26_consent_from_honest_script | 19 | 152 | Quot.sound, propext | yes |
| 158 | ControlStack.SC26Liveness.honest_progress | 42 | 122 | Classical.choice, Quot.sound, propext | yes |
| 159 | ControlStack.SC26Liveness.progress_interleaved | 42 | 125 | Classical.choice, Quot.sound, propext | yes |
| 160 | ControlStack.SC26Liveness.Concrete.crash_tolerant_progress | 65 | 209 | Classical.choice, Quot.sound, propext | yes |
| 161 | ControlStack.SC26LossyLiveness.lossy_safe | 18 | 206 | Quot.sound, propext | yes |
| 162 | ControlStack.SC26LossyLiveness.lossy_rounds | 27 | 248 | Classical.choice, Quot.sound, propext | yes |
| 163 | ControlStack.SC26LossyHalt.lossy_halt_keys | 10 | 94 | Quot.sound, propext | yes |
| 164 | ControlStack.SC26LossyHalt.tagged_rounds | 23 | 279 | Classical.choice, Quot.sound, propext | yes |
| 165 | ControlStack.SC27Chain.sc27_safe | 14 | 44 | Quot.sound, propext | yes |
| 166 | ControlStack.SC27Chain.tamper_after_anchor_detected | 10 | 35 | Quot.sound, propext | yes |
| 167 | ControlStack.SC27Chain.halt_freezes | 9 | 37 | Quot.sound, propext | yes |
| 168 | ControlStack.SC27ExtensionOnly.sc27_ext_safe | 16 | 38 | Quot.sound, propext | yes |
| 169 | ControlStack.SC27ExtensionOnly.tampered_never_anchored | 26 | 35 | Quot.sound, propext | yes |
| 170 | ControlStack.SC27ExtensionOnly.anchors_chain | 11 | 38 | Quot.sound, propext | yes |
| 171 | ControlStack.SC27ExtensionOnly.alarm_iff | 15 | 24 | propext | yes |
| 172 | ControlStack.SC27Refinement.concrete_ext_safe | 24 | 98 | Classical.choice, Quot.sound, propext | yes |
| 173 | ControlStack.SC27Refinement.concrete_tampered_never_anchored | 25 | 103 | Classical.choice, Quot.sound, propext | yes |
| 174 | ControlStack.SC28.sc28_safe | 9 | 64 | Quot.sound, propext | yes |
| 175 | ControlStack.SC28.revoked_lease_stops | 9 | 38 | Quot.sound, propext | yes |
| 176 | ControlStack.SC28.fork_shares_lease | 17 | 35 | Quot.sound, propext | yes |
| 177 | ControlStack.SC28.halt_freezes | 9 | 38 | Quot.sound, propext | yes |
| 178 | ControlStack.AuthInstances.sc28_safe_authenticated | 20 | 109 | Quot.sound, propext | yes |
| 179 | ControlStack.AuthInstances.forged28_consumes_without_auth | 9 | 49 | Quot.sound, propext | yes |
| 180 | ControlStack.SC28Liveness.honest_steps_progress | 27 | 45 | Quot.sound, propext | yes |
| 181 | ControlStack.SC28Liveness.progress_interleaved | 24 | 47 | Classical.choice, Quot.sound, propext | yes |
| 182 | ControlStack.SC28Liveness.global_cap_blocks_honest | 11 | 37 | Quot.sound, propext | yes |
| 183 | ControlStack.AntiRollback.rollback_transfer | 23 | 69 | Quot.sound, propext | yes |
| 184 | ControlStack.AntiRollback.sc28_rollback_safe | 29 | 257 | Quot.sound, propext | yes |
| 185 | ControlStack.SC28Refinement.concrete_safe | 15 | 161 | Quot.sound, propext | yes |
| 186 | ControlStack.SC28Refinement.concrete_revoked_stops | 19 | 137 | Quot.sound, propext | yes |
| 187 | ControlStack.SC28Refinement.exclusive_placement_safe | 17 | 169 | Quot.sound, propext | yes |

Dependencies do not establish runtime correspondence, environment truth or English statement fidelity.
