#!/usr/bin/env python3
"""Static Kubernetes extractor (gate G4): differential against the Compose extractor plus a sealed set of single-fault mutants.

The oracle is the Compose hardened reference example (examples/compose-two-agent-hardened/clean.*). A Kubernetes manifest is
generated from it by an independent translator written here; the extractor under test must yield the same authority graph.
No cluster is run. The runtime inventory is the Compose one, reused because the normalized runtime shape is identical: this
tests the manifest mapping, not a kubelet."""
import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from extractors.compose import collect as compose_collect, sha  # noqa: E402
from extractors.kubernetes import collect, convert  # noqa: E402
from security_ir.verifier import verify  # noqa: E402

EX = ROOT / "examples/compose-two-agent-hardened"


def pods_from_compose(compose):
    items = []
    for name, s in sorted(compose["services"].items()):
        vols, mounts = [], []
        for i, v in enumerate(s["volumes"]):
            vols.append({"name": "v%d" % i, "hostPath": {"path": v["source"]}})
            mounts.append({"name": "v%d" % i, "mountPath": v["target"], "readOnly": v["read_only"]})
        sc = {"runAsUser": int(s["user"])}
        if s.get("security_opt") == ["no-new-privileges:true"]:
            sc["allowPrivilegeEscalation"] = False
        if s.get("cap_drop") == ["ALL"]:
            sc["capabilities"] = {"drop": ["ALL"]}
        items.append({"apiVersion": "v1", "kind": "Pod",
                      "metadata": {"name": name, "labels": {"cstack.io/role": s["x-cstack-role"]}},
                      "spec": {"automountServiceAccountToken": False, "volumes": vols,
                               "containers": [{"name": "main", "image": s["image"], "securityContext": sc,
                                               "env": [{"name": k, "value": v} for k, v in sorted(s["environment"].items())],
                                               "volumeMounts": mounts}]}})
    items.append({"apiVersion": "networking.k8s.io/v1", "kind": "NetworkPolicy", "metadata": {"name": "default-deny"},
                  "spec": {"podSelector": {}, "policyTypes": ["Ingress", "Egress"]}})
    return {"apiVersion": "v1", "kind": "List", "items": items,
            "metadata": {"annotations": {"cstack.io/claim": json.dumps(compose["x-cstack"], sort_keys=True)}}}


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.dir = Path(self.tmp.name)
        self.compose = json.loads((EX / "clean.compose.json").read_text())
        self.runtime = EX / "clean.runtime.json"

    def run_k8s(self, manifest, tag="k"):
        path = self.dir / (tag + ".json")
        path.write_text(json.dumps(manifest, sort_keys=True, indent=2))
        return collect(path, self.runtime, sha(path), self.dir / ("work-" + tag))

    @staticmethod
    def graph(ir):
        nodes = sorted((n["id"], n["type"], json.dumps(n["facts"], sort_keys=True)) for n in ir["nodes"])
        edges = sorted((e["from"], e["to"], e["capability"], e["reachability"], e["authorization"]) for e in ir["edges"])
        return nodes, edges

    def unknown_edges(self, ir):
        return [e for e in ir["edges"] if e["reachability"] == "UNKNOWN"]


class Differential(Base):
    def test_translated_reference_deployment_has_the_same_authority_graph_as_compose(self):
        path = self.dir / "oracle.compose.json"
        path.write_text(json.dumps(self.compose, sort_keys=True, indent=2))
        want = self.graph(compose_collect(path, self.runtime, sha(path)))
        got = self.graph(self.run_k8s(pods_from_compose(self.compose)))
        self.assertEqual(got, want)
        self.assertEqual([e for e in want[1] if e[3] == "UNKNOWN"], [], "the reference deployment has no unknown authority")
        refuted = [o["premise"] for o in verify(self.run_k8s(pods_from_compose(self.compose), "again"))["obligations"] if o["status"] == "REFUTED"]
        self.assertEqual(refuted, [])

    def test_the_manifest_digest_is_a_recorded_source_and_a_wrong_pin_is_refused(self):
        ir = self.run_k8s(pods_from_compose(self.compose))
        self.assertTrue(any(s["source"].endswith("k.json") and s["kind"] == "DECLARED" for s in ir["sources"]))
        bad = self.dir / "bad.json"
        bad.write_text(json.dumps(pods_from_compose(self.compose)))
        with self.assertRaises(ValueError):
            collect(bad, self.runtime, "0" * 64, self.dir / "w")


class Mutants(Base):
    """Each mutation changes one thing and must make the authority graph UNKNOWN or PRESENT-forbidden where the baseline is clean."""

    def mutate(self, fn):
        m = pods_from_compose(self.compose)
        fn(m)
        return self.run_k8s(m, "mut")

    def pod(self, m, name):
        return next(i for i in m["items"] if i["kind"] == "Pod" and i["metadata"]["name"] == name)

    def assert_flagged(self, ir, service):
        self.assertTrue([e for e in ir["edges"] if e["from"] == service and e["reachability"] in ("UNKNOWN", "PRESENT")
                         and e["authorization"] == "FORBIDDEN"], service)

    def test_privileged_agent(self):
        self.assert_flagged(self.mutate(lambda m: self.pod(m, "agent-a")["spec"]["containers"][0]["securityContext"].update(privileged=True)), "agent-a")

    def test_host_network(self):
        self.assert_flagged(self.mutate(lambda m: self.pod(m, "agent-a")["spec"].update(hostNetwork=True)), "agent-a")

    def test_docker_socket_hostpath(self):
        def f(m):
            p = self.pod(m, "agent-a")
            p["spec"]["volumes"].append({"name": "sock", "hostPath": {"path": "/var/run/docker.sock"}})
            p["spec"]["containers"][0]["volumeMounts"].append({"name": "sock", "mountPath": "/var/run/docker.sock"})
        self.assert_flagged(self.mutate(f), "agent-a")

    def test_agent_gets_the_sink_writable(self):
        def f(m):
            p = self.pod(m, "agent-a")
            sink = self.compose["x-cstack"]["sink_source"]
            p["spec"]["volumes"].append({"name": "sink", "hostPath": {"path": sink}})
            p["spec"]["containers"][0]["volumeMounts"].append({"name": "sink", "mountPath": "/output", "readOnly": False})
        self.assert_flagged(self.mutate(f), "agent-a")

    def test_missing_capability_drop_and_privilege_escalation_flag(self):
        for field in ("capabilities", "allowPrivilegeEscalation"):
            self.assert_flagged(self.mutate(lambda m: self.pod(m, "agent-a")["spec"]["containers"][0]["securityContext"].pop(field)), "agent-a")

    def test_partial_capability_drop_is_not_accepted(self):
        self.assert_flagged(self.mutate(lambda m: self.pod(m, "agent-a")["spec"]["containers"][0]["securityContext"].update(
            capabilities={"drop": ["NET_RAW"]})), "agent-a")

    def test_tag_instead_of_digest(self):
        self.assert_flagged(self.mutate(lambda m: self.pod(m, "agent-a")["spec"]["containers"][0].update(image="python:3.12")), "agent-a")

    def test_service_account_token_not_disabled(self):
        self.assert_flagged(self.mutate(lambda m: self.pod(m, "agent-a")["spec"].pop("automountServiceAccountToken")), "agent-a")

    def test_unsupported_pod_fields(self):
        for field, value in (("hostPID", True), ("hostIPC", True), ("serviceAccountName", "admin"), ("initContainers", [{"name": "x"}]),
                             ("shareProcessNamespace", True)):
            self.assert_flagged(self.mutate(lambda m: self.pod(m, "agent-a")["spec"].__setitem__(field, value)), "agent-a")

    def test_secret_and_emptydir_volumes_are_unsupported_not_ignored(self):
        def f(m):
            p = self.pod(m, "agent-a")
            p["spec"]["volumes"].append({"name": "s", "secret": {"secretName": "x"}})
            p["spec"]["containers"][0]["volumeMounts"].append({"name": "s", "mountPath": "/secret"})
        self.assert_flagged(self.mutate(f), "agent-a")

    def test_env_from_secret_and_envfrom(self):
        self.assert_flagged(self.mutate(lambda m: self.pod(m, "agent-a")["spec"]["containers"][0]["env"].append(
            {"name": "TOKEN", "valueFrom": {"secretKeyRef": {"name": "s", "key": "k"}}})), "agent-a")

    def test_second_container_and_run_as_root(self):
        self.assert_flagged(self.mutate(lambda m: self.pod(m, "agent-a")["spec"]["containers"].append({"name": "side", "image": "x"})), "agent-a")
        # a root agent is not an authority edge: the obligations catch it (identity separation, and the running UID no longer matches)
        ir = self.mutate(lambda m: self.pod(m, "agent-a")["spec"]["containers"][0]["securityContext"].update(runAsUser=0))
        refuted = {o["premise"] for o in verify(ir)["obligations"] if o["status"] == "REFUTED"}
        self.assertTrue({"identity-separation", "runtime-snapshot:agent-a"} <= refuted, refuted)

    def test_missing_or_weakened_network_policy_leaves_every_service_unknown(self):
        weak = self.mutate(lambda m: m["items"].__setitem__(-1, {**m["items"][-1], "spec": {"podSelector": {}, "policyTypes": ["Ingress"]}}))
        none = self.mutate(lambda m: m["items"].pop())
        for ir in (weak, none):
            self.assertTrue(self.unknown_edges(ir))
            for svc in ("agent-a", "broker", "receiver"):
                self.assertTrue([e for e in ir["edges"] if e["from"] == svc and e["reachability"] == "UNKNOWN"], svc)

    def test_unsupported_object_kinds_make_the_deployment_unknown(self):
        ir = self.mutate(lambda m: m["items"].append({"apiVersion": "apps/v1", "kind": "Deployment", "metadata": {"name": "d"}, "spec": {}}))
        self.assertTrue([e for e in ir["edges"] if e["from"] == "unknown" and e["reachability"] == "UNKNOWN"])

    def test_converter_is_deterministic(self):
        m = pods_from_compose(self.compose)
        m["items"][0]["spec"]["hostPID"] = True
        self.assertEqual(json.dumps(convert(m), sort_keys=True), json.dumps(convert(copy.deepcopy(m)), sort_keys=True))


if __name__ == "__main__":
    unittest.main()
