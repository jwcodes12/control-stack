import ControlStack.Scenarios.SC26Transaction
import ControlStack.Scenarios.SC28Budget
import ControlStack.Scenarios.SC16Deploy
import ControlStack.Scenarios.SC25Audit
import ControlStack.Scenarios.SC23Injection
import ControlStack.Scenarios.SC12Persistence
import ControlStack.Scenarios.SC18Logging
import ControlStack.Scenarios.SC08Exec
import ControlStack.Scenarios.SC09Priv
import ControlStack.Scenarios.SC10Policy
import ControlStack.Scenarios.SC17Infra
import ControlStack.Scenarios.SC19Prod
import ControlStack.Scenarios.SC27Chain
import ControlStack.Families.F6.ReservedAudit
import ControlStack.Families.F6.ReservedRecall
import ControlStack.Families.F6.DamageBound
import ControlStack.Families.F3.DistributedHalt
import ControlStack.Families.F6.MonitorCollusion
import ControlStack.Families.F2.ChannelInstances
import ControlStack.Core.Compose
set_option pp.all false
set_option linter.all false

#eval IO.println "### CHECK ControlStack.SC26.sc26_safe"
#check @ControlStack.SC26.sc26_safe
#eval IO.println "### AXIOMS ControlStack.SC26.sc26_safe"
#print axioms ControlStack.SC26.sc26_safe
#eval IO.println "### CHECK ControlStack.SC26.safe_of_sound"
#check @ControlStack.SC26.safe_of_sound
#eval IO.println "### AXIOMS ControlStack.SC26.safe_of_sound"
#print axioms ControlStack.SC26.safe_of_sound
#eval IO.println "### CHECK ControlStack.SC26.sc26_safe_disjoint"
#check @ControlStack.SC26.sc26_safe_disjoint
#eval IO.println "### AXIOMS ControlStack.SC26.sc26_safe_disjoint"
#print axioms ControlStack.SC26.sc26_safe_disjoint
#eval IO.println "### CHECK ControlStack.SC26.sc26_once"
#check @ControlStack.SC26.sc26_once
#eval IO.println "### AXIOMS ControlStack.SC26.sc26_once"
#print axioms ControlStack.SC26.sc26_once
#eval IO.println "### CHECK ControlStack.SC26.halt_freezes"
#check @ControlStack.SC26.halt_freezes
#eval IO.println "### AXIOMS ControlStack.SC26.halt_freezes"
#print axioms ControlStack.SC26.halt_freezes
#eval IO.println "### CHECK ControlStack.SC26.honest_trace_pays"
#check @ControlStack.SC26.honest_trace_pays
#eval IO.println "### AXIOMS ControlStack.SC26.honest_trace_pays"
#print axioms ControlStack.SC26.honest_trace_pays
#eval IO.println "### PRINT ControlStack.SC26.Good"
#print ControlStack.SC26.Good
#eval IO.println "### PRINT ControlStack.SC26.Approved"
#print ControlStack.SC26.Approved
#eval IO.println "### PRINT ControlStack.SC26.reqOf"
#print ControlStack.SC26.reqOf
#eval IO.println "### PRINT ControlStack.SC26.legal"
#print ControlStack.SC26.legal
#eval IO.println "### PRINT ControlStack.SC26.full"
#print ControlStack.SC26.full
#eval IO.println "### PRINT ControlStack.SC26.Sound"
#print ControlStack.SC26.Sound
#eval IO.println "### PRINT ControlStack.SC26.Checks"
#print ControlStack.SC26.Checks
#eval IO.println "### PRINT ControlStack.SC26.init"
#print ControlStack.SC26.init
#eval IO.println "### PRINT ControlStack.SC26.Roles"
#print ControlStack.SC26.Roles
#eval IO.println "### PRINT ControlStack.SC26.Tx"
#print ControlStack.SC26.Tx
#eval IO.println "### PRINT ControlStack.SC26.Req"
#print ControlStack.SC26.Req
#eval IO.println "### PRINT ControlStack.SC26.St"
#print ControlStack.SC26.St
#eval IO.println "### CHECK ControlStack.SC28.sc28_safe"
#check @ControlStack.SC28.sc28_safe
#eval IO.println "### AXIOMS ControlStack.SC28.sc28_safe"
#print axioms ControlStack.SC28.sc28_safe
#eval IO.println "### CHECK ControlStack.SC28.honest_trace_works"
#check @ControlStack.SC28.honest_trace_works
#eval IO.println "### AXIOMS ControlStack.SC28.honest_trace_works"
#print axioms ControlStack.SC28.honest_trace_works
#eval IO.println "### PRINT ControlStack.SC28.Good"
#print ControlStack.SC28.Good
#eval IO.println "### PRINT ControlStack.SC28.legal"
#print ControlStack.SC28.legal
#eval IO.println "### PRINT ControlStack.SC28.full"
#print ControlStack.SC28.full
#eval IO.println "### PRINT ControlStack.SC28.init"
#print ControlStack.SC28.init
#eval IO.println "### PRINT ControlStack.SC28.St"
#print ControlStack.SC28.St
#eval IO.println "### PRINT ControlStack.SC28.Op"
#print ControlStack.SC28.Op
#eval IO.println "### CHECK ControlStack.SC16.sc16_safe"
#check @ControlStack.SC16.sc16_safe
#eval IO.println "### AXIOMS ControlStack.SC16.sc16_safe"
#print axioms ControlStack.SC16.sc16_safe
#eval IO.println "### CHECK ControlStack.SC16.sc16_reviewed_content"
#check @ControlStack.SC16.sc16_reviewed_content
#eval IO.println "### AXIOMS ControlStack.SC16.sc16_reviewed_content"
#print axioms ControlStack.SC16.sc16_reviewed_content
#eval IO.println "### CHECK ControlStack.SC16.honest_trace_deploys"
#check @ControlStack.SC16.honest_trace_deploys
#eval IO.println "### AXIOMS ControlStack.SC16.honest_trace_deploys"
#print axioms ControlStack.SC16.honest_trace_deploys
#eval IO.println "### PRINT ControlStack.SC16.Good"
#print ControlStack.SC16.Good
#eval IO.println "### PRINT ControlStack.SC16.full"
#print ControlStack.SC16.full
#eval IO.println "### PRINT ControlStack.SC16.init"
#print ControlStack.SC16.init
#eval IO.println "### PRINT ControlStack.SC16.Roles"
#print ControlStack.SC16.Roles
#eval IO.println "### PRINT ControlStack.SC16.St"
#print ControlStack.SC16.St
#eval IO.println "### CHECK ControlStack.SC25.sc25_safe"
#check @ControlStack.SC25.sc25_safe
#eval IO.println "### AXIOMS ControlStack.SC25.sc25_safe"
#print axioms ControlStack.SC25.sc25_safe
#eval IO.println "### CHECK ControlStack.SC25.honest_reversible"
#check @ControlStack.SC25.honest_reversible
#eval IO.println "### AXIOMS ControlStack.SC25.honest_reversible"
#print axioms ControlStack.SC25.honest_reversible
#eval IO.println "### CHECK ControlStack.SC25.honest_irreversible_with_crash"
#check @ControlStack.SC25.honest_irreversible_with_crash
#eval IO.println "### AXIOMS ControlStack.SC25.honest_irreversible_with_crash"
#print axioms ControlStack.SC25.honest_irreversible_with_crash
#eval IO.println "### PRINT ControlStack.SC25.Good"
#print ControlStack.SC25.Good
#eval IO.println "### PRINT ControlStack.SC25.ExecOk"
#print ControlStack.SC25.ExecOk
#eval IO.println "### PRINT ControlStack.SC25.full"
#print ControlStack.SC25.full
#eval IO.println "### PRINT ControlStack.SC25.Checks"
#print ControlStack.SC25.Checks
#eval IO.println "### PRINT ControlStack.SC25.init"
#print ControlStack.SC25.init
#eval IO.println "### PRINT ControlStack.SC25.Roles"
#print ControlStack.SC25.Roles
#eval IO.println "### PRINT ControlStack.SC25.St"
#print ControlStack.SC25.St
#eval IO.println "### CHECK ControlStack.SC23.sc23_safe"
#check @ControlStack.SC23.sc23_safe
#eval IO.println "### AXIOMS ControlStack.SC23.sc23_safe"
#print axioms ControlStack.SC23.sc23_safe
#eval IO.println "### CHECK ControlStack.SC23.honest_untainted"
#check @ControlStack.SC23.honest_untainted
#eval IO.println "### AXIOMS ControlStack.SC23.honest_untainted"
#print axioms ControlStack.SC23.honest_untainted
#eval IO.println "### CHECK ControlStack.SC23.honest_confirmed"
#check @ControlStack.SC23.honest_confirmed
#eval IO.println "### AXIOMS ControlStack.SC23.honest_confirmed"
#print axioms ControlStack.SC23.honest_confirmed
#eval IO.println "### PRINT ControlStack.SC23.Good"
#print ControlStack.SC23.Good
#eval IO.println "### PRINT ControlStack.SC23.ActOk"
#print ControlStack.SC23.ActOk
#eval IO.println "### PRINT ControlStack.SC23.full"
#print ControlStack.SC23.full
#eval IO.println "### PRINT ControlStack.SC23.init"
#print ControlStack.SC23.init
#eval IO.println "### PRINT ControlStack.SC23.Policy"
#print ControlStack.SC23.Policy
#eval IO.println "### PRINT ControlStack.SC23.St"
#print ControlStack.SC23.St
#eval IO.println "### CHECK ControlStack.SC12.sc12_safe"
#check @ControlStack.SC12.sc12_safe
#eval IO.println "### AXIOMS ControlStack.SC12.sc12_safe"
#print axioms ControlStack.SC12.sc12_safe
#eval IO.println "### CHECK ControlStack.SC12.honest_session_lifecycle"
#check @ControlStack.SC12.honest_session_lifecycle
#eval IO.println "### AXIOMS ControlStack.SC12.honest_session_lifecycle"
#print axioms ControlStack.SC12.honest_session_lifecycle
#eval IO.println "### PRINT ControlStack.SC12.Good"
#print ControlStack.SC12.Good
#eval IO.println "### PRINT ControlStack.SC12.full"
#print ControlStack.SC12.full
#eval IO.println "### PRINT ControlStack.SC12.init"
#print ControlStack.SC12.init
#eval IO.println "### PRINT ControlStack.SC12.St"
#print ControlStack.SC12.St
#eval IO.println "### CHECK ControlStack.SC18.sc18_safe"
#check @ControlStack.SC18.sc18_safe
#eval IO.println "### AXIOMS ControlStack.SC18.sc18_safe"
#print axioms ControlStack.SC18.sc18_safe
#eval IO.println "### CHECK ControlStack.SC18.honest_logged_release"
#check @ControlStack.SC18.honest_logged_release
#eval IO.println "### AXIOMS ControlStack.SC18.honest_logged_release"
#print axioms ControlStack.SC18.honest_logged_release
#eval IO.println "### PRINT ControlStack.SC18.Good"
#print ControlStack.SC18.Good
#eval IO.println "### PRINT ControlStack.SC18.RelOk"
#print ControlStack.SC18.RelOk
#eval IO.println "### PRINT ControlStack.SC18.legal"
#print ControlStack.SC18.legal
#eval IO.println "### PRINT ControlStack.SC18.full"
#print ControlStack.SC18.full
#eval IO.println "### PRINT ControlStack.SC18.Checks"
#print ControlStack.SC18.Checks
#eval IO.println "### PRINT ControlStack.SC18.init"
#print ControlStack.SC18.init
#eval IO.println "### PRINT ControlStack.SC18.St"
#print ControlStack.SC18.St
#eval IO.println "### CHECK ControlStack.SC08.sc08_safe"
#check @ControlStack.SC08.sc08_safe
#eval IO.println "### AXIOMS ControlStack.SC08.sc08_safe"
#print axioms ControlStack.SC08.sc08_safe
#eval IO.println "### CHECK ControlStack.SC08.safe_of_sound"
#check @ControlStack.SC08.safe_of_sound
#eval IO.println "### AXIOMS ControlStack.SC08.safe_of_sound"
#print axioms ControlStack.SC08.safe_of_sound
#eval IO.println "### CHECK ControlStack.SC08.honest_execs"
#check @ControlStack.SC08.honest_execs
#eval IO.println "### AXIOMS ControlStack.SC08.honest_execs"
#print axioms ControlStack.SC08.honest_execs
#eval IO.println "### PRINT ControlStack.SC08.Good"
#print ControlStack.SC08.Good
#eval IO.println "### PRINT ControlStack.SC08.RunOk"
#print ControlStack.SC08.RunOk
#eval IO.println "### PRINT ControlStack.SC08.full"
#print ControlStack.SC08.full
#eval IO.println "### PRINT ControlStack.SC08.Env"
#print ControlStack.SC08.Env
#eval IO.println "### PRINT ControlStack.SC08.St"
#print ControlStack.SC08.St
#eval IO.println "### CHECK ControlStack.SC09.sc09_safe"
#check @ControlStack.SC09.sc09_safe
#eval IO.println "### AXIOMS ControlStack.SC09.sc09_safe"
#print axioms ControlStack.SC09.sc09_safe
#eval IO.println "### CHECK ControlStack.SC09.honest_privileged_work"
#check @ControlStack.SC09.honest_privileged_work
#eval IO.println "### AXIOMS ControlStack.SC09.honest_privileged_work"
#print axioms ControlStack.SC09.honest_privileged_work
#eval IO.println "### PRINT ControlStack.SC09.Good"
#print ControlStack.SC09.Good
#eval IO.println "### PRINT ControlStack.SC09.full"
#print ControlStack.SC09.full
#eval IO.println "### PRINT ControlStack.SC09.init"
#print ControlStack.SC09.init
#eval IO.println "### PRINT ControlStack.SC09.Policy"
#print ControlStack.SC09.Policy
#eval IO.println "### PRINT ControlStack.SC09.St"
#print ControlStack.SC09.St
#eval IO.println "### CHECK ControlStack.SC10.sc10_safe"
#check @ControlStack.SC10.sc10_safe
#eval IO.println "### AXIOMS ControlStack.SC10.sc10_safe"
#print axioms ControlStack.SC10.sc10_safe
#eval IO.println "### CHECK ControlStack.SC10.honest_enforcement_and_build"
#check @ControlStack.SC10.honest_enforcement_and_build
#eval IO.println "### AXIOMS ControlStack.SC10.honest_enforcement_and_build"
#print axioms ControlStack.SC10.honest_enforcement_and_build
#eval IO.println "### PRINT ControlStack.SC10.Good"
#print ControlStack.SC10.Good
#eval IO.println "### PRINT ControlStack.SC10.full"
#print ControlStack.SC10.full
#eval IO.println "### PRINT ControlStack.SC10.init"
#print ControlStack.SC10.init
#eval IO.println "### PRINT ControlStack.SC10.Env"
#print ControlStack.SC10.Env
#eval IO.println "### PRINT ControlStack.SC10.St"
#print ControlStack.SC10.St
#eval IO.println "### CHECK ControlStack.SC17.sc17_safe"
#check @ControlStack.SC17.sc17_safe
#eval IO.println "### AXIOMS ControlStack.SC17.sc17_safe"
#print axioms ControlStack.SC17.sc17_safe
#eval IO.println "### CHECK ControlStack.SC17.honest_apply"
#check @ControlStack.SC17.honest_apply
#eval IO.println "### AXIOMS ControlStack.SC17.honest_apply"
#print axioms ControlStack.SC17.honest_apply
#eval IO.println "### PRINT ControlStack.SC17.Good"
#print ControlStack.SC17.Good
#eval IO.println "### PRINT ControlStack.SC17.AppOk"
#print ControlStack.SC17.AppOk
#eval IO.println "### PRINT ControlStack.SC17.full"
#print ControlStack.SC17.full
#eval IO.println "### PRINT ControlStack.SC17.init"
#print ControlStack.SC17.init
#eval IO.println "### PRINT ControlStack.SC17.Env"
#print ControlStack.SC17.Env
#eval IO.println "### CHECK ControlStack.SC19.sc19_safe"
#check @ControlStack.SC19.sc19_safe
#eval IO.println "### AXIOMS ControlStack.SC19.sc19_safe"
#print axioms ControlStack.SC19.sc19_safe
#eval IO.println "### CHECK ControlStack.SC19.honest_destructive_change"
#check @ControlStack.SC19.honest_destructive_change
#eval IO.println "### AXIOMS ControlStack.SC19.honest_destructive_change"
#print axioms ControlStack.SC19.honest_destructive_change
#eval IO.println "### PRINT ControlStack.SC19.Good"
#print ControlStack.SC19.Good
#eval IO.println "### PRINT ControlStack.SC19.DestroyOk"
#print ControlStack.SC19.DestroyOk
#eval IO.println "### PRINT ControlStack.SC19.full"
#print ControlStack.SC19.full
#eval IO.println "### PRINT ControlStack.SC19.init"
#print ControlStack.SC19.init
#eval IO.println "### PRINT ControlStack.SC19.Env"
#print ControlStack.SC19.Env
#eval IO.println "### CHECK ControlStack.SC27Chain.sc27_safe"
#check @ControlStack.SC27Chain.sc27_safe
#eval IO.println "### AXIOMS ControlStack.SC27Chain.sc27_safe"
#print axioms ControlStack.SC27Chain.sc27_safe
#eval IO.println "### CHECK ControlStack.SC27Chain.honest_accept"
#check @ControlStack.SC27Chain.honest_accept
#eval IO.println "### AXIOMS ControlStack.SC27Chain.honest_accept"
#print axioms ControlStack.SC27Chain.honest_accept
#eval IO.println "### PRINT ControlStack.SC27Chain.full"
#print ControlStack.SC27Chain.full
#eval IO.println "### PRINT ControlStack.SC27Chain.init"
#print ControlStack.SC27Chain.init
#eval IO.println "### PRINT ControlStack.SC27Chain.Env"
#print ControlStack.SC27Chain.Env
#eval IO.println "### PRINT ControlStack.SC27Chain.St"
#print ControlStack.SC27Chain.St
#eval IO.println "### CHECK ControlStack.ReservedAudit.reserved_policy_bound"
#check @ControlStack.ReservedAudit.reserved_policy_bound
#eval IO.println "### AXIOMS ControlStack.ReservedAudit.reserved_policy_bound"
#print axioms ControlStack.ReservedAudit.reserved_policy_bound
#eval IO.println "### CHECK ControlStack.ReservedRecall.adaptive_recall_bound"
#check @ControlStack.ReservedRecall.adaptive_recall_bound
#eval IO.println "### AXIOMS ControlStack.ReservedRecall.adaptive_recall_bound"
#print axioms ControlStack.ReservedRecall.adaptive_recall_bound
#eval IO.println "### CHECK ControlStack.ReservedRecall.hypMiss"
#check @ControlStack.ReservedRecall.hypMiss
#eval IO.println "### AXIOMS ControlStack.ReservedRecall.hypMiss"
#print axioms ControlStack.ReservedRecall.hypMiss
#eval IO.println "### CHECK ControlStack.DamageBound.damage_bound"
#check @ControlStack.DamageBound.damage_bound
#eval IO.println "### AXIOMS ControlStack.DamageBound.damage_bound"
#print axioms ControlStack.DamageBound.damage_bound
#eval IO.println "### CHECK ControlStack.DamageBound.tail_bound"
#check @ControlStack.DamageBound.tail_bound
#eval IO.println "### AXIOMS ControlStack.DamageBound.tail_bound"
#print axioms ControlStack.DamageBound.tail_bound
#eval IO.println "### CHECK ControlStack.DamageBound.ucX"
#check @ControlStack.DamageBound.ucX
#eval IO.println "### AXIOMS ControlStack.DamageBound.ucX"
#print axioms ControlStack.DamageBound.ucX
#eval IO.println "### CHECK ControlStack.DistributedHalt.fenced_after_eps"
#check @ControlStack.DistributedHalt.fenced_after_eps
#eval IO.println "### AXIOMS ControlStack.DistributedHalt.fenced_after_eps"
#print axioms ControlStack.DistributedHalt.fenced_after_eps
#eval IO.println "### CHECK ControlStack.DistributedHalt.landed_after_le"
#check @ControlStack.DistributedHalt.landed_after_le
#eval IO.println "### AXIOMS ControlStack.DistributedHalt.landed_after_le"
#print axioms ControlStack.DistributedHalt.landed_after_le
#eval IO.println "### CHECK ControlStack.DistributedHalt.accepts"
#check @ControlStack.DistributedHalt.accepts
#eval IO.println "### AXIOMS ControlStack.DistributedHalt.accepts"
#print axioms ControlStack.DistributedHalt.accepts
#eval IO.println "### CHECK ControlStack.DistributedHalt.sinkRun"
#check @ControlStack.DistributedHalt.sinkRun
#eval IO.println "### AXIOMS ControlStack.DistributedHalt.sinkRun"
#print axioms ControlStack.DistributedHalt.sinkRun
#eval IO.println "### CHECK ControlStack.DistributedHalt.Rate"
#check @ControlStack.DistributedHalt.Rate
#eval IO.println "### AXIOMS ControlStack.DistributedHalt.Rate"
#print axioms ControlStack.DistributedHalt.Rate
#eval IO.println "### CHECK ControlStack.DistributedHalt.HaltAbsorbs"
#check @ControlStack.DistributedHalt.HaltAbsorbs
#eval IO.println "### AXIOMS ControlStack.DistributedHalt.HaltAbsorbs"
#print axioms ControlStack.DistributedHalt.HaltAbsorbs
#eval IO.println "### CHECK ControlStack.DistributedHalt.Delivered"
#check @ControlStack.DistributedHalt.Delivered
#eval IO.println "### AXIOMS ControlStack.DistributedHalt.Delivered"
#print axioms ControlStack.DistributedHalt.Delivered
#eval IO.println "### CHECK ControlStack.DistributedHalt.Latency"
#check @ControlStack.DistributedHalt.Latency
#eval IO.println "### AXIOMS ControlStack.DistributedHalt.Latency"
#print axioms ControlStack.DistributedHalt.Latency
#eval IO.println "### CHECK ControlStack.DistributedHalt.HoldsOld"
#check @ControlStack.DistributedHalt.HoldsOld
#eval IO.println "### AXIOMS ControlStack.DistributedHalt.HoldsOld"
#print axioms ControlStack.DistributedHalt.HoldsOld
#eval IO.println "### CHECK ControlStack.DistributedHalt.landedAfter"
#check @ControlStack.DistributedHalt.landedAfter
#eval IO.println "### AXIOMS ControlStack.DistributedHalt.landedAfter"
#print axioms ControlStack.DistributedHalt.landedAfter
#eval IO.println "### CHECK ControlStack.MonitorCollusion.pass_transfer"
#check @ControlStack.MonitorCollusion.pass_transfer
#eval IO.println "### AXIOMS ControlStack.MonitorCollusion.pass_transfer"
#print axioms ControlStack.MonitorCollusion.pass_transfer
#eval IO.println "### CHECK ControlStack.MonitorCollusion.collusion_uniform"
#check @ControlStack.MonitorCollusion.collusion_uniform
#eval IO.println "### AXIOMS ControlStack.MonitorCollusion.collusion_uniform"
#print axioms ControlStack.MonitorCollusion.collusion_uniform
#eval IO.println "### CHECK ControlStack.ChannelInstances.gpu_bound"
#check @ControlStack.ChannelInstances.gpu_bound
#eval IO.println "### AXIOMS ControlStack.ChannelInstances.gpu_bound"
#print axioms ControlStack.ChannelInstances.gpu_bound
#eval IO.println "### CHECK ControlStack.ChannelInstances.log_channel"
#check @ControlStack.ChannelInstances.log_channel
#eval IO.println "### AXIOMS ControlStack.ChannelInstances.log_channel"
#print axioms ControlStack.ChannelInstances.log_channel
#eval IO.println "### CHECK ControlStack.ChannelInstances.sc02_accumulated"
#check @ControlStack.ChannelInstances.sc02_accumulated
#eval IO.println "### AXIOMS ControlStack.ChannelInstances.sc02_accumulated"
#print axioms ControlStack.ChannelInstances.sc02_accumulated
#eval IO.println "### CHECK ControlStack.Compose.bridgeSpec"
#check @ControlStack.Compose.bridgeSpec
#eval IO.println "### AXIOMS ControlStack.Compose.bridgeSpec"
#print axioms ControlStack.Compose.bridgeSpec
#eval IO.println "### CHECK ControlStack.Compose.bridge_breaks_joint"
#check @ControlStack.Compose.bridge_breaks_joint
#eval IO.println "### AXIOMS ControlStack.Compose.bridge_breaks_joint"
#print axioms ControlStack.Compose.bridge_breaks_joint
#eval IO.println "### CHECK ControlStack.Compose.BridgeAdmissible"
#check @ControlStack.Compose.BridgeAdmissible
#eval IO.println "### AXIOMS ControlStack.Compose.BridgeAdmissible"
#print axioms ControlStack.Compose.BridgeAdmissible
#eval IO.println "### CHECK ControlStack.Compose.withBridge"
#check @ControlStack.Compose.withBridge
#eval IO.println "### AXIOMS ControlStack.Compose.withBridge"
#print axioms ControlStack.Compose.withBridge
