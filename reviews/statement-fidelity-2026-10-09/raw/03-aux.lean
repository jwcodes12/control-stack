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
#eval IO.println "### PRINT Leakage.survInd"
#check @ControlStack.Leakage.survInd
#print ControlStack.Leakage.survInd
#eval IO.println "### PRINT Leakage.liveInd"
#check @ControlStack.Leakage.liveInd
#print ControlStack.Leakage.liveInd
#eval IO.println "### PRINT Leakage.caughtFlag"
#check @ControlStack.Leakage.caughtFlag
#print ControlStack.Leakage.caughtFlag
#eval IO.println "### PRINT Leakage.attackSet"
#check @ControlStack.Leakage.attackSet
#print ControlStack.Leakage.attackSet
#eval IO.println "### PRINT Leakage.memN"
#check @ControlStack.Leakage.memN
#print ControlStack.Leakage.memN
#eval IO.println "### PRINT SC16.ReviewOk"
#check @ControlStack.SC16.ReviewOk
#print ControlStack.SC16.ReviewOk
#eval IO.println "### PRINT SC16.casLookup"
#check @ControlStack.SC16.casLookup
#print ControlStack.SC16.casLookup
#eval IO.println "### PRINT SC12.Ent"
#check @ControlStack.SC12.Ent
#print ControlStack.SC12.Ent
#eval IO.println "### PRINT ChannelInstances.sc02_example"
#check @ControlStack.ChannelInstances.sc02_example
#print ControlStack.ChannelInstances.sc02_example
#eval IO.println "### PRINT ChannelInstances.gpu_example"
#check @ControlStack.ChannelInstances.gpu_example
#print ControlStack.ChannelInstances.gpu_example
#eval IO.println "### PRINT DamageBound.example_r1"
#check @ControlStack.DamageBound.example_r1
#print ControlStack.DamageBound.example_r1
#eval IO.println "### PRINT ReservedRecall.recall_instance_bound"
#check @ControlStack.ReservedRecall.recall_instance_bound
#print ControlStack.ReservedRecall.recall_instance_bound
#eval IO.println "### PRINT DistributedHalt.example_fenced"
#check @ControlStack.DistributedHalt.example_fenced
#print ControlStack.DistributedHalt.example_fenced
#eval IO.println "### PRINT MonitorCollusion.phase_example"
#check @ControlStack.MonitorCollusion.phase_example
#print ControlStack.MonitorCollusion.phase_example
