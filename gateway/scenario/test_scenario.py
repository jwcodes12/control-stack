"""Fault-catalog oracle and assurance-evidence mutation controls; no runtime claim."""
import copy
import json
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

from run import HERE, ROOT, channels, oracle, source_hashes, summarize
from check_receipt import check
sys.path.insert(0, str(ROOT / "gateway"))
from gateway import GatewayError
from harness import run_episode


class ScenarioTests(unittest.TestCase):
    def setUp(self):
        self.contract = json.loads((HERE / "contract.json").read_text())

    def test_oracle_rejects_all_wrong_catalog_repairs(self):
        for fault in range(8):
            for repair in range(8):
                actual = oracle(self.contract, fault, {"repair": repair})
                self.assertEqual(actual["passed"], fault == repair)
        for reply in [None, {"repair": True}, {"repair": 9}, {"repair": 0, "extra": 1}]:
            self.assertFalse(oracle(self.contract, 0, reply)["passed"])

    def test_diagnostic_probes_distinguish_all_faults(self):
        signatures = [tuple(eval(expr, {"__builtins__": {}}, {"a": a, "b": b})
                            for a, b in self.contract["diagnostic_inputs"])
                      for expr in self.contract["fault_expressions"]]
        self.assertEqual(len(set(signatures)), 8)

    def test_certified_harness_refuses_before_agent_launch(self):
        with patch("harness.sandboxed_result") as launch:
            with self.assertRaises(GatewayError):
                run_episode(Path("unused"), Path("unused"), 0, channels(self.contract), certified=True)
            launch.assert_not_called()

    def receipt_fixture(self):
        """Synthetic evidence solely for checker mutation tests; never published as a run."""
        c = self.contract
        records = []
        for lineage in range(c["lineages"]):
            episodes = []
            for i in range(5):
                b = {"repair": i, "passed": True, "spec_checks": len(c["oracle_inputs"]),
                     "sender_ok": True, "receiver_ok": True, "elapsed_seconds": 1.0}
                m = {**b, "false_blank": False, "view": {"repair": [[i]]}, "alerts": []}
                episodes.append({"episode": i, "fault": i, "order": ["baseline", "mediated"], "baseline": b, "mediated": m})
            records.append({"lineage": str(lineage), "episodes": episodes, "ledger_product": 9 ** 5,
                            "admissions": 5, "sixth_episode_rejected": True})
        return {"contract": c, "contract_id": c["id"], "hashes": source_hashes(), "mode": "full", "status": "pass",
                "verdict": "CONDITIONAL", "unresolved": ["complete_receiver_observation", "shared_kernel_channels",
                "python_model_refinement", "host_integrity_and_no_snapshot_rollback", "statistical_runtime_independence", "workload_transport"],
                "preflight": {"netns": 2, "pidns": 3, "host_netns": 1, "host_pidns": 1,
                    "effective_capabilities": "0", "no_new_privileges": "1", "interfaces": ["lo"], "routes4": "header\n"},
                "records": records, "summary": summarize(c, records)}

    def test_receipt_promotions_and_missing_evidence_are_rejected(self):
        report = self.receipt_fixture()
        check(report)
        mutations = [lambda r: r.update(verdict="DEPLOYMENT-GRADE"),
                     lambda r: r["unresolved"].remove("shared_kernel_channels"),
                     lambda r: r["hashes"].pop("gateway/harness.py"),
                     lambda r: r["summary"]["mediated"].update(completion_interval=["1", "1"]),
                     lambda r: r["records"][0]["episodes"][0]["mediated"].update(repair=7),
                     lambda r: r["records"][0].update(sixth_episode_rejected=False),
                     lambda r: r["records"][0].update(ledger_product=1),
                     lambda r: r["preflight"].update(netns=1),
                     lambda r: r.update(mode="smoke")]
        for mutate in mutations:
            bad = copy.deepcopy(report); mutate(bad)
            with self.assertRaises(AssertionError):
                check(bad)

    def test_episode_counts_cannot_hide_lifetime_failure(self):
        report = self.receipt_fixture()
        # 63 successful lifetimes, despite 319/320 successful episodes.
        failed = report["records"][0]["episodes"][0]["mediated"]
        failed.update(repair=None, passed=False, spec_checks=0, false_blank=True, view={"repair": [None]})
        report["summary"] = summarize(self.contract, report["records"])
        self.assertEqual(report["summary"]["mediated"]["completed_lifetimes"], 63)
        self.assertEqual(report["summary"]["mediated"]["completed_episodes"], 319)
        check(report)


if __name__ == "__main__":
    unittest.main()
