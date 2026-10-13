# Conftest policy: Compose checks taken from the published OWASP Docker Security Cheat Sheet rules
# (https://cheatsheetseries.owasp.org/cheatsheets/Docker_Security_Cheat_Sheet.html) and the CIS Docker Benchmark topics they cite.
# Written for the Tier 11 held-out baseline comparison. It reads declared Compose fields only: no identity separation, writer
# graph, required writers, runtime inventory correspondence or completeness claim. NOT independent of this repository's authors:
# the rule selection and the Rego are model-written; the rule SOURCE is public.
package main

import rego.v1

services contains name if some name, _ in input.services

svc(name) := input.services[name]

mounts(name) := [m | some m in svc(name).volumes]

sensitive_sources := {"/", "/var/run/docker.sock", "/run/docker.sock", "/proc", "/sys", "/dev", "/etc", "/boot", "/var/lib/docker", "/root"}

mount_source(m) := m.source if is_object(m)
mount_source(m) := split(m, ":")[0] if is_string(m)

# RULE #1 do not expose the Docker daemon socket
deny contains msg if {
	some name in services
	some m in mounts(name)
	mount_source(m) in {"/var/run/docker.sock", "/run/docker.sock"}
	msg := sprintf("%s: mounts the Docker socket (OWASP #1)", [name])
}

# RULE #2 set a user / do not run as root
deny contains msg if {
	some name in services
	not svc(name).user
	msg := sprintf("%s: no user set, runs as root (OWASP #2)", [name])
}

deny contains msg if {
	some name in services
	svc(name).user in {"0", "root", "0:0", 0}
	msg := sprintf("%s: runs as root (OWASP #2)", [name])
}

# RULE #3 limit capabilities
deny contains msg if {
	some name in services
	not "ALL" in svc(name).cap_drop
	msg := sprintf("%s: does not drop all capabilities (OWASP #3)", [name])
}

deny contains msg if {
	some name in services
	count(svc(name).cap_add) > 0
	msg := sprintf("%s: adds capabilities (OWASP #3)", [name])
}

# RULE #4 prevent in-container privilege escalation
deny contains msg if {
	some name in services
	not "no-new-privileges:true" in svc(name).security_opt
	msg := sprintf("%s: no-new-privileges not set (OWASP #4)", [name])
}

# RULE #8 do not use privileged containers
deny contains msg if {
	some name in services
	svc(name).privileged == true
	msg := sprintf("%s: privileged (OWASP #8)", [name])
}

# RULE #5 / #7 isolate: no host network or host namespaces
deny contains msg if {
	some name in services
	svc(name).network_mode == "host"
	msg := sprintf("%s: host network (OWASP #5)", [name])
}

deny contains msg if {
	some name in services
	some key in ["pid", "ipc", "uts", "userns_mode"]
	svc(name)[key] == "host"
	msg := sprintf("%s: host %s namespace (OWASP #5)", [name, key])
}

# RULE #12 read-only root filesystem
deny contains msg if {
	some name in services
	not svc(name).read_only
	msg := sprintf("%s: root filesystem is writable (OWASP #8)", [name])
}

# RULE #7 resource limits
deny contains msg if {
	some name in services
	not svc(name).mem_limit
	not svc(name).deploy.resources.limits.memory
	msg := sprintf("%s: no memory limit (OWASP #7)", [name])
}

# sensitive host directories bound into a container
deny contains msg if {
	some name in services
	some m in mounts(name)
	src := mount_source(m)
	src in sensitive_sources
	not src in {"/var/run/docker.sock", "/run/docker.sock"}
	msg := sprintf("%s: binds sensitive host path %s", [name, src])
}
