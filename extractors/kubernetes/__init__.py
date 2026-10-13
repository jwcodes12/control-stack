"""Collector for a deliberately restricted normalized Kubernetes JSON profile (gate G4, static extractor only).

It translates a `v1/List` of bare Pods plus one default-deny NetworkPolicy into the SAME normalized profile the Compose
extractor already understands, then runs that extractor, so every authority rule (mounts, UIDs, hardening, credentials, unknown
features) lives in one place and the intermediate Compose JSON is written next to the result for inspection. The translation
is the part under test; it is a faithfulness premise that kubelet semantics match the Compose ones it maps to:

  Pod            -> service        (labels['cstack.io/role'] is the role, default deputy)
  runAsUser      -> user           allowPrivilegeEscalation:false -> security_opt no-new-privileges:true
  capabilities.drop:[ALL] -> cap_drop:[ALL]        privileged -> privileged        hostNetwork -> network_mode: host
  hostPath volume + volumeMount -> bind mount (type/source/target/read_only); any other volume kind -> unsupported
  env[].name -> environment names (values are not examined; valueFrom/envFrom -> unsupported)
  default-deny NetworkPolicy (podSelector {}, Ingress+Egress, no rules) -> the internal 'isolated' network; without it every
  service gets an unsupported network and the verdict cannot be CONDITIONAL
  automountServiceAccountToken must be false (the Kubernetes default hands the pod an API credential)

Anything else on a Pod, container, securityContext or top-level object becomes an unsupported feature, which the Compose
extractor turns into an UNKNOWN authority edge (never a silent pass). NOT implemented: a runtime collector. There is no
`kubectl`/cluster capture here; a runtime inventory must be supplied in the normalized shape (see deployment/collect_docker.py),
and without one every non-broker service has `runtime facts missing`. No cluster has been run. Controllers (Deployment,
StatefulSet, DaemonSet, Job), Services, Ingress, RBAC, admission policy and CNI behaviour are out of the profile.
"""
import hashlib
import json
import re
from pathlib import Path

from extractors.compose import collect as compose_collect, sha
from security_ir import validate

ROLE_LABEL = "cstack.io/role"
CLAIM_ANNOTATION = "cstack.io/claim"
POD_SPEC_KEYS = {"containers", "volumes", "securityContext", "automountServiceAccountToken", "hostNetwork", "restartPolicy"}
POD_SC_KEYS = {"runAsUser"}
CONTAINER_KEYS = {"name", "image", "env", "volumeMounts", "securityContext"}
CONTAINER_SC_KEYS = {"runAsUser", "allowPrivilegeEscalation", "capabilities", "privileged"}
UNSUPPORTED_VOLUME = {"type": "volume"}  # not a bind: the Compose extractor reports 'unsupported volume feature'


def deny_all(policy):
    """A NetworkPolicy that selects every pod and allows nothing in either direction."""
    spec = policy.get("spec", {}) if isinstance(policy, dict) else {}
    return (policy.get("kind") == "NetworkPolicy" and spec.get("podSelector") == {}
            and sorted(spec.get("policyTypes", [])) == ["Egress", "Ingress"]
            and not spec.get("ingress") and not spec.get("egress") and set(spec) <= {"podSelector", "policyTypes"})


def convert(manifest):
    """Return (normalized compose dict, list of reasons for unsupported top-level objects)."""
    top_unsupported = []
    if manifest.get("kind") != "List" or manifest.get("apiVersion") != "v1" or not isinstance(manifest.get("items"), list):
        raise ValueError("manifest must be a v1 List")
    if set(manifest) - {"apiVersion", "kind", "items", "metadata"}:
        top_unsupported.append("list-field")
    claim = {}
    meta = manifest.get("metadata", {})
    raw = meta.get("annotations", {}).get(CLAIM_ANNOTATION) if isinstance(meta, dict) and isinstance(meta.get("annotations"), dict) else None
    if isinstance(raw, str):
        claim = json.loads(raw)
    pods, policies = [], []
    for item in manifest["items"]:
        kind = item.get("kind") if isinstance(item, dict) else None
        if kind == "Pod":
            pods.append(item)
        elif kind == "NetworkPolicy":
            policies.append(item)
        else:
            top_unsupported.append("object-kind:" + str(kind))
    isolated = len(policies) == 1 and deny_all(policies[0])
    if policies and not isolated:
        top_unsupported.append("network-policy-not-default-deny")
    services = {}
    for pod in pods:
        services.update(convert_pod(pod, isolated))
    compose = {"services": services,
               "networks": {"isolated": {"internal": True}} if isolated else {"default": {}},
               "x-cstack": claim}
    return compose, top_unsupported


def convert_pod(pod, isolated):
    name = pod.get("metadata", {}).get("name")
    if not isinstance(name, str) or not re.fullmatch(r"[a-z0-9]([-a-z0-9]*[a-z0-9])?", name):
        raise ValueError("pod needs a DNS-label name")
    extra = sorted("pod-field:" + k for k in set(pod) - {"apiVersion", "kind", "metadata", "spec"})
    spec = pod.get("spec", {})
    labels = pod.get("metadata", {}).get("labels", {})
    svc = {"x-cstack-role": labels.get(ROLE_LABEL, "deputy") if isinstance(labels, dict) else "deputy",
           "networks": ["isolated"] if isolated else ["default"]}
    extra += ["spec-field:" + k for k in sorted(set(spec) - POD_SPEC_KEYS)]
    extra += ["pod-metadata-field:" + k for k in sorted(set(pod.get("metadata", {})) - {"name", "labels", "namespace"})]
    containers = spec.get("containers", [])
    if not isinstance(containers, list) or len(containers) != 1 or not isinstance(containers[0], dict):
        extra.append("container-count-not-one")
        containers = containers[:1] if isinstance(containers, list) and containers and isinstance(containers[0], dict) else [{}]
    c = containers[0]
    extra += ["container-field:" + k for k in sorted(set(c) - CONTAINER_KEYS)]
    svc["image"] = c.get("image", "")
    pod_sc = spec.get("securityContext", {}) if isinstance(spec.get("securityContext", {}), dict) else {}
    extra += ["pod-securityContext-field:" + k for k in sorted(set(pod_sc) - POD_SC_KEYS)]
    sc = c.get("securityContext", {}) if isinstance(c.get("securityContext", {}), dict) else {}
    extra += ["securityContext-field:" + k for k in sorted(set(sc) - CONTAINER_SC_KEYS)]
    uid = sc.get("runAsUser", pod_sc.get("runAsUser"))
    svc["user"] = str(uid) if type(uid) is int else ""
    if sc.get("allowPrivilegeEscalation") is False:
        svc["security_opt"] = ["no-new-privileges:true"]
    caps = sc.get("capabilities")
    if isinstance(caps, dict) and set(caps) == {"drop"} and caps["drop"] == ["ALL"]:
        svc["cap_drop"] = ["ALL"]
    elif caps is not None:
        extra.append("capabilities-not-drop-ALL")
        svc["cap_drop"] = ["unsupported"]
    if "privileged" in sc:
        svc["privileged"] = sc["privileged"]
    if spec.get("hostNetwork") is True:
        svc["network_mode"] = "host"
    elif "hostNetwork" in spec:
        extra.append("hostNetwork-not-true")
    if spec.get("automountServiceAccountToken") is not False:
        extra.append("service-account-token-not-disabled")
    env = {}
    for e in c.get("env", []) if isinstance(c.get("env", []), list) else [None]:
        if isinstance(e, dict) and isinstance(e.get("name"), str) and set(e) == {"name", "value"} and isinstance(e["value"], str):
            env[e["name"]] = e["value"]
        elif isinstance(e, dict) and isinstance(e.get("name"), str):
            env[e["name"]] = ""
            extra.append("env-valueFrom:" + e["name"])
        else:
            extra.append("env-syntax")
    svc["environment"] = env
    host_paths = {}
    volumes = spec.get("volumes", [])
    for v in volumes if isinstance(volumes, list) else []:
        if isinstance(v, dict) and set(v) == {"name", "hostPath"} and isinstance(v["hostPath"], dict) and set(v["hostPath"]) <= {"path", "type"}:
            host_paths[v["name"]] = v["hostPath"].get("path")
        else:
            host_paths[v.get("name") if isinstance(v, dict) else None] = None  # non-hostPath volume
    binds = []
    for m in c.get("volumeMounts", []) if isinstance(c.get("volumeMounts", []), list) else []:
        src = host_paths.get(m.get("name")) if isinstance(m, dict) else None
        if (isinstance(m, dict) and isinstance(src, str) and set(m) <= {"name", "mountPath", "readOnly"}
                and isinstance(m.get("mountPath"), str) and type(m.get("readOnly", False)) is bool):
            binds.append({"type": "bind", "source": src, "target": m["mountPath"], "read_only": m.get("readOnly", False)})
        else:
            binds.append(dict(UNSUPPORTED_VOLUME))
    svc["volumes"] = binds
    for reason in extra:  # an unknown service key makes the Compose extractor report an unsupported feature (UNKNOWN edge)
        svc["k8s-" + reason.split(":")[0] + "-" + hashlib.sha256(reason.encode()).hexdigest()[:8]] = reason
    return {name: svc}


def collect(manifest, runtime, expected_sha256, workdir, replay=False):
    manifest, runtime, workdir = Path(manifest), Path(runtime), Path(workdir)
    if sha(manifest) != expected_sha256:
        raise ValueError("Kubernetes manifest pin mismatch")
    compose, top_unsupported = convert(json.loads(manifest.read_text()))
    if top_unsupported:
        compose["x-cstack-k8s-unsupported"] = top_unsupported  # unknown top-level key: the extractor adds an UNKNOWN edge
    workdir.mkdir(parents=True, exist_ok=True)
    converted = workdir / "converted.compose.json"
    converted.write_text(json.dumps(compose, sort_keys=True, indent=2) + "\n")
    ir = compose_collect(converted, runtime, sha(converted), replay=replay)
    ir["sources"].append({"source": str(manifest), "sha256": sha(manifest), "kind": "DECLARED"})
    return validate(ir)
