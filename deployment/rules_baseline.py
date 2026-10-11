"""Small hand-written Compose rules; no OPA installation or runtime inspection."""
import re
CREDENTIAL=re.compile(r'TOKEN|SECRET|KEY|PASSWORD|PASS|PASSWD|AUTH|COOKIE|PRIVATE',re.I)
def assess(compose):
    findings=[]
    for name,service in compose.get('services',{}).items():
        if service.get('privileged'):findings.append(name+':privileged')
        if service.get('network_mode')=='host':findings.append(name+':host-network')
        if service.get('pid')=='host' or service.get('ipc')=='host':findings.append(name+':host-namespace')
        if service.get('user') in ('0','root','0:0',0):findings.append(name+':root-user')
        if service.get('cap_add'):findings.append(name+':extra-capabilities')
        environment=service.get('environment',{})
        names=environment if isinstance(environment,dict) else [str(item).split('=',1)[0] for item in environment] if isinstance(environment,list) else []
        if any(CREDENTIAL.search(key) for key in names):findings.append(name+':credential-name')
        for mount in service.get('volumes',[]):
            if isinstance(mount,dict) and mount.get('source') in ('/','/var/run/docker.sock','/run/docker.sock','/proc','/sys','/dev','/etc'):findings.append(name+':host-system-bind')
    return {'verdict':'REJECT' if findings else 'ALLOW','findings':findings,'scope':'Common declaration-only deny rules; no identity separation, writer graph, required writers, inventory correspondence or completeness claim.'}
