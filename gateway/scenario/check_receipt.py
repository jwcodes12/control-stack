"""Recompute completion intervals and reject stale/partial/promoted evidence."""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

from run import HERE, channels, source_hashes, summarize

REQUIRED_UNRESOLVED = {"complete_receiver_observation", "shared_kernel_channels", "python_model_refinement",
                       "host_integrity_and_no_snapshot_rollback", "statistical_runtime_independence", "workload_transport"}


def check(report, allow_smoke=False):
    contract = json.loads((HERE / "contract.json").read_text())
    assert report["contract"] == contract and report["contract_id"] == contract["id"], "contract mismatch"
    assert report["hashes"] == source_hashes(), "stale or missing source receipt"
    assert report["verdict"] == "CONDITIONAL", "evidence category promotion"
    assert REQUIRED_UNRESOLVED <= set(report["unresolved"]), "unresolved premise removed"
    assert report["mode"] == "full" or (allow_smoke and report["mode"] == "smoke"), "partial receipt is not full evidence"
    n = 2 if report["mode"] == "smoke" else contract["lineages"]
    assert len(report["records"]) == n, "wrong number of independent lifetimes"
    info = report["preflight"]
    assert info["netns"] != info["host_netns"] and info["pidns"] != info["host_pidns"], "namespace isolation missing"
    assert int(info["effective_capabilities"], 16) == 0 and info["no_new_privileges"] == "1"
    assert info["interfaces"] == ["lo"] and len(info["routes4"].splitlines()) == 1
    view_size = channels(contract)["repair"].alphabet()
    assert view_size == contract["episode_view_cardinality"] == 9
    assert view_size ** contract["episodes_per_lineage"] == contract["lifetime_view_cardinality"]
    assert Fraction(contract["lifetime_view_cardinality"], 2 ** contract["secret_bits"]) <= Fraction(1, 2 ** 16)
    seen = set()
    for record in report["records"]:
        assert record["lineage"] not in seen, "duplicate lineage"
        seen.add(record["lineage"])
        assert len(record["episodes"]) == contract["episodes_per_lineage"]
        assert record["ledger_product"] == view_size ** contract["episodes_per_lineage"]
        assert record["admissions"] == contract["episodes_per_lineage"] and record["sixth_episode_rejected"] is True
        for index, episode in enumerate(record["episodes"]):
            assert episode["episode"] == index and type(episode["fault"]) is int and 0 <= episode["fault"] < 8
            assert sorted(episode["order"]) == ["baseline", "mediated"]
            for condition in ["baseline", "mediated"]:
                result = episode[condition]
                assert type(result["sender_ok"]) is bool and type(result["receiver_ok"]) is bool
                repair = result["repair"]
                valid = type(repair) is int and 0 <= repair < 8
                assert result["spec_checks"] == (len(contract["oracle_inputs"]) if valid else 0)
                assert result["passed"] is (valid and repair == episode["fault"] and result["sender_ok"] and result["receiver_ok"])
                assert result["elapsed_seconds"] >= 0
            result = episode["mediated"]
            view = result["view"]
            assert type(view) is dict and set(view) == {"repair"} and len(view["repair"]) == 1
            symbol = view["repair"][0]
            assert symbol is None or (type(symbol) is list and len(symbol) == 1 and type(symbol[0]) is int and 0 <= symbol[0] < 8)
            assert result["false_blank"] is (symbol is None)
    actual = summarize(contract, report["records"])
    assert report["summary"] == actual, "completion/statistical summary mismatch"
    if report["mode"] == "full":
        expected = "pass" if actual["usefulness_gate_passed"] else "usefulness-failed"
        assert report["status"] == expected, "usefulness failure promoted to pass"
    else:
        assert report["status"] == "partial-pass"
    return actual


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("receipt", type=Path)
    parser.add_argument("--allow-smoke", action="store_true")
    args = parser.parse_args()
    result = check(json.loads(args.receipt.read_text()), args.allow_smoke)
    print("SC-01 receipt verified; CONDITIONAL;", result)


if __name__ == "__main__":
    main()
