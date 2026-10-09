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

#eval IO.println "### PRINT ControlStack.SC16.DepOk"
#print ControlStack.SC16.DepOk
#eval IO.println "### PRINT ControlStack.SC16.step"
#print ControlStack.SC16.step
#eval IO.println "### PRINT ControlStack.SC16.Review"
#print ControlStack.SC16.Review
#eval IO.println "### PRINT ControlStack.SC16.Appr"
#print ControlStack.SC16.Appr
#eval IO.println "### PRINT ControlStack.SC10.DecOk"
#print ControlStack.SC10.DecOk
#eval IO.println "### PRINT ControlStack.SC09.UseOk"
#print ControlStack.SC09.UseOk
#eval IO.println "### PRINT ControlStack.SC09.step"
#print ControlStack.SC09.step
#eval IO.println "### PRINT ControlStack.SC28.usedT"
#print ControlStack.SC28.usedT
#eval IO.println "### PRINT ControlStack.SC28.usedL"
#print ControlStack.SC28.usedL
#eval IO.println "### PRINT ControlStack.SC28.budgetOf"
#print ControlStack.SC28.budgetOf
#eval IO.println "### PRINT ControlStack.SC28.step"
#print ControlStack.SC28.step
#eval IO.println "### PRINT ControlStack.SC12.step"
#print ControlStack.SC12.step
#eval IO.println "### PRINT ControlStack.SC23.step"
#print ControlStack.SC23.step
#eval IO.println "### PRINT ControlStack.SC23.Val"
#print ControlStack.SC23.Val
#eval IO.println "### PRINT ControlStack.SC25.step"
#print ControlStack.SC25.step
#eval IO.println "### PRINT ControlStack.SC18.step"
#print ControlStack.SC18.step
#eval IO.println "### PRINT ControlStack.SC17.step"
#print ControlStack.SC17.step
#eval IO.println "### PRINT ControlStack.SC19.step"
#print ControlStack.SC19.step
#eval IO.println "### PRINT ControlStack.SC27Chain.step"
#print ControlStack.SC27Chain.step
#eval IO.println "### PRINT ControlStack.SC27Chain.chainHead"
#print ControlStack.SC27Chain.chainHead
#eval IO.println "### PRINT ControlStack.SC27Chain.Op"
#print ControlStack.SC27Chain.Op
#eval IO.println "### PRINT ControlStack.SC26.step"
#print ControlStack.SC26.step
#eval IO.println "### PRINT ControlStack.SC08.step"
#print ControlStack.SC08.step
#eval IO.println "### PRINT ControlStack.SC10.step"
#print ControlStack.SC10.step
#eval IO.println "### PRINT ControlStack.DistributedHalt.accepts"
#print ControlStack.DistributedHalt.accepts
#eval IO.println "### PRINT ControlStack.DistributedHalt.sinkStep"
#print ControlStack.DistributedHalt.sinkStep
#eval IO.println "### PRINT ControlStack.DistributedHalt.sinkRun"
#print ControlStack.DistributedHalt.sinkRun
#eval IO.println "### PRINT ControlStack.DistributedHalt.Rate"
#print ControlStack.DistributedHalt.Rate
#eval IO.println "### PRINT ControlStack.DistributedHalt.HaltAbsorbs"
#print ControlStack.DistributedHalt.HaltAbsorbs
#eval IO.println "### PRINT ControlStack.DistributedHalt.Delivered"
#print ControlStack.DistributedHalt.Delivered
#eval IO.println "### PRINT ControlStack.DistributedHalt.Latency"
#print ControlStack.DistributedHalt.Latency
#eval IO.println "### PRINT ControlStack.DistributedHalt.HoldsOld"
#print ControlStack.DistributedHalt.HoldsOld
#eval IO.println "### PRINT ControlStack.DistributedHalt.landedAfter"
#print ControlStack.DistributedHalt.landedAfter
#eval IO.println "### PRINT ControlStack.DistributedHalt.initiatedAfter"
#print ControlStack.DistributedHalt.initiatedAfter
#eval IO.println "### PRINT ControlStack.Compose.BridgeAdmissible"
#print ControlStack.Compose.BridgeAdmissible
#eval IO.println "### PRINT ControlStack.MonitorCollusion.passRate"
#print ControlStack.MonitorCollusion.passRate
#eval IO.println "### PRINT ControlStack.MonitorCollusion.tv"
#print ControlStack.MonitorCollusion.tv
#eval IO.println "### PRINT ControlStack.ChannelInstances.gpuK"
#print ControlStack.ChannelInstances.gpuK
#eval IO.println "### PRINT ControlStack.ChannelInstances.wmax"
#print ControlStack.ChannelInstances.wmax
#eval IO.println "### PRINT ControlStack.ReservedAudit.successInd"
#print ControlStack.ReservedAudit.successInd
#eval IO.println "### PRINT ControlStack.ReservedAudit.reservedK"
#print ControlStack.ReservedAudit.reservedK
#eval IO.println "### PRINT ControlStack.ReservedAudit.pU"
#print ControlStack.ReservedAudit.pU
#eval IO.println "### PRINT ControlStack.ReservedRecall.recallSucc"
#print ControlStack.ReservedRecall.recallSucc
#eval IO.println "### PRINT ControlStack.ReservedRecall.hypMiss"
#print ControlStack.ReservedRecall.hypMiss
#eval IO.println "### PRINT ControlStack.DamageBound.ucX"
#print ControlStack.DamageBound.ucX
#eval IO.println "### PRINT ControlStack.DamageBound.pre"
#print ControlStack.DamageBound.pre
#eval IO.println "### PRINT ControlStack.Leakage.AOut"
#print ControlStack.Leakage.AOut
#eval IO.println "### PRINT ControlStack.Leakage.val"
#print ControlStack.Leakage.val
#eval IO.println "### PRINT ControlStack.Leakage.Dominated"
#print ControlStack.Leakage.Dominated
