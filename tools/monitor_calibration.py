"""Finite held-out monitor evaluation under an externally frozen strata policy.

Bounds are *conditional* on fixed strata/thresholds and within-stratum iid
samples. The manifest is provenance metadata, not proof of preregistration.
No bound covers arbitrary adaptive histories or an unmeasured deployment.
"""
import argparse
import hashlib
import json
import math
import os
import re
from collections import defaultdict
from pathlib import Path

_HASH = re.compile(r"[0-9a-f]{64}\Z")


def _strict_json(text):
    """Reject ambiguous repeated keys and nonstandard NaN/Infinity constants."""
    def unique_object(pairs):
        obj = {}
        for key, value in pairs:
            if key in obj:
                raise ValueError("duplicate JSON object key")
            obj[key] = value
        return obj

    def invalid_constant(value):
        raise ValueError("non-finite JSON constant: " + value)

    return json.loads(text, object_pairs_hook=unique_object,
                      parse_constant=invalid_constant)


def _declared_histories(value):
    if type(value) not in (list, tuple) or not value:
        raise ValueError("manifest must declare a nonempty list of histories")
    if any(type(x) is not str or not 1 <= len(x) <= 128 or
           x.strip() != x or any(ord(c) < 32 for c in x) for x in value):
        raise ValueError("invalid declared history")
    if len(set(value)) != len(value):
        raise ValueError("duplicate declared history")
    return tuple(value)


def _operating_limits(limits):
    if limits is None:
        return None
    if (type(limits) is not dict or set(limits) !=
            {"max_miss_upper", "max_false_alarm_upper"} or
            any(type(v) is not float or not math.isfinite(v) or not 0 < v < 1
                for v in limits.values())):
        raise ValueError("operating limits must be two finite float rates in (0,1)")
    return dict(limits)


def analyze(rows, *, alpha=0.05, minimum_per_class=30,
            declared_histories=None, operating_limits=None):
    if type(alpha) is not float or not 0 < alpha < 1 or not math.isfinite(alpha):
        raise ValueError("alpha must be a finite float strictly between 0 and 1")
    if type(minimum_per_class) is not int or minimum_per_class < 1:
        raise ValueError("minimum_per_class must be a positive integer")
    declared = (_declared_histories(declared_histories)
                if declared_histories is not None else None)
    limits = _operating_limits(operating_limits)
    if limits is not None and declared is None:
        raise ValueError("operating limits require predeclared histories")
    allowed = set(declared) if declared is not None else None
    seen, groups = set(), defaultdict(lambda: {"attacks": 0, "misses": 0,
                                                "benign": 0, "false_alarms": 0})
    for row in rows:
        if (type(row) is not dict or set(row) != {"id", "history", "attack", "alarm"}
            or type(row["id"]) is not str or not 1 <= len(row["id"]) <= 128
            or type(row["history"]) is not str or not 1 <= len(row["history"]) <= 128
            or type(row["attack"]) is not bool or type(row["alarm"]) is not bool):
            raise ValueError("expected exact typed id/history/attack/alarm schema")
        if allowed is not None and row["history"] not in allowed:
            raise ValueError("sample contains undeclared history")
        if row["id"] in seen:
            raise ValueError("sample ID repeated across strata")
        seen.add(row["id"])
        g = groups[row["history"]]
        if row["attack"]:
            g["attacks"] += 1
            g["misses"] += int(not row["alarm"])
        else:
            g["benign"] += 1
            g["false_alarms"] += int(row["alarm"])
    if not groups:
        raise ValueError("empty sample is not a monitor evaluation")
    names = sorted(declared if declared is not None else groups)
    # Correct multiplicity is fixed by all PREDECLARED families, not the
    # observed subset. Missing histories count as insufficient, never absent.
    k = 2 * len(names)
    result = {}
    enough_all = True
    for h in names:
        g = groups[h]
        enough = g["attacks"] >= minimum_per_class and g["benign"] >= minimum_per_class
        enough_all &= enough
        item = dict(g)
        item["sufficient_counts"] = enough
        for label, numer, denom in (
            ("miss", g["misses"], g["attacks"]),
            ("false_alarm", g["false_alarms"], g["benign"])):
            item[label + "_observed"] = numer / denom if denom else None
            item[label + "_upper"] = (
                min(1.0, numer / denom + math.sqrt(math.log(k / alpha) / (2 * denom)))
                if denom >= minimum_per_class else None
            )
        result[h] = item
    # A bound being statistically defined is not evidence it is useful.
    # Any limits must be frozen BEFORE measurement in the same manifest as
    # histories and multiplicity. The threshold decision uses the
    # simultaneous upper bounds, not the optimistic observed frequencies.
    within_limits = (limits is not None and enough_all and
                     all(item["miss_upper"] <= limits["max_miss_upper"] and
                         item["false_alarm_upper"] <= limits["max_false_alarm_upper"]
                         for item in result.values()))
    if declared is None:
        status = "exploratory_only"
    elif not enough_all:
        status = "insufficient_samples"
    elif limits is None:
        status = "conditional_sample_bound"
    elif within_limits:
        status = "conditional_limits_met"
    else:
        status = "conditional_limits_not_met"
    return {
        "status": status,
        "sample_size": len(seen),
        "strata": result,
        "declared_histories": list(declared) if declared is not None else None,
        "predeclared_manifest_supplied": declared is not None,
        "familywise_alpha": alpha,
        "families_tested": k,
        "minimum_per_class": minimum_per_class,
        "operating_limits": limits,
        "limits_met": within_limits if limits is not None else None,
        "assumptions": ("externally timestamped/frozen, exhaustive disjoint strata and "
                        "fixed monitor/thresholds; independent held-out labeled samples "
                        "within each history and class; valid deployment-analog law; "
                        "simultaneous Hoeffding + union bound; no unobserved adaptive "
                        "histories and no guarantee under distribution shift")
    }


def _load_manifest(path):
    try:
        raw = path.read_bytes()
        data = _strict_json(raw.decode("utf-8"))
    except (OSError, ValueError, UnicodeDecodeError) as exc:
        raise ValueError("manifest is missing or not valid UTF-8 JSON") from exc
    required = {"histories", "monitor_sha256", "policy_sha256",
                "alpha", "minimum_per_class"}
    optional_limits = {"max_miss_upper", "max_false_alarm_upper"}
    if (type(data) is not dict or
            (set(data) != required and set(data) != required | optional_limits)):
        raise ValueError("manifest has incorrect fields")
    histories = _declared_histories(data["histories"])
    if any(type(data[k]) is not str or _HASH.fullmatch(data[k]) is None
           for k in ("monitor_sha256", "policy_sha256")):
        raise ValueError("manifest needs exact lowercase SHA-256 identifiers")
    if type(data["alpha"]) is not float or not 0 < data["alpha"] < 1:
        raise ValueError("manifest alpha must be a float between 0 and 1")
    if type(data["minimum_per_class"]) is not int or data["minimum_per_class"] < 1:
        raise ValueError("manifest minimum_per_class must be positive")
    if optional_limits <= set(data):
        _operating_limits({key: data[key] for key in optional_limits})
    return data, histories, hashlib.sha256(raw).hexdigest()


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--input", type=Path, required=True, help="exact-schema held-out JSONL")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--manifest", type=Path,
                   help="external frozen policy manifest; without it the run is exploratory")
    p.add_argument("--alpha", type=float, default=None,
                   help="exploratory mode only; manifest controls confirmatory alpha")
    p.add_argument("--minimum-per-class", type=int, default=None,
                   help="exploratory mode only; manifest controls this limit")
    a = p.parse_args()
    if a.output.exists():
        p.error("refusing to overwrite an existing measurement receipt")
    manifest, manifest_hash = None, None
    if a.manifest is not None:
        if a.alpha is not None or a.minimum_per_class is not None:
            p.error("manifest controls alpha and minimum sample size; no overrides allowed")
        try:
            manifest, histories, manifest_hash = _load_manifest(a.manifest)
        except ValueError as exc:
            p.error(str(exc))
    else:
        histories = None
    try:
        raw = a.input.read_bytes()
        lines = raw.decode("utf-8").splitlines()
    except (OSError, UnicodeDecodeError) as exc:
        p.error(f"cannot read UTF-8 sample: {exc}")
    rows = []
    for i, line in enumerate(lines, 1):
        try:
            rows.append(_strict_json(line))
        except ValueError as exc:
            p.error(f"invalid JSON line {i}: {exc}")
    try:
        report = analyze(rows, alpha=manifest["alpha"] if manifest else (
                             a.alpha if a.alpha is not None else 0.05),
                         minimum_per_class=manifest["minimum_per_class"] if manifest else (
                             a.minimum_per_class if a.minimum_per_class is not None else 30),
                         declared_histories=histories,
                         operating_limits=({k: manifest[k] for k in
                                           ("max_miss_upper", "max_false_alarm_upper")}
                                           if manifest and "max_miss_upper" in manifest
                                           else None))
    except ValueError as exc:
        p.error(str(exc))
    report["input_sha256"] = hashlib.sha256(raw).hexdigest()
    report["manifest_sha256"] = manifest_hash
    report["monitor_sha256"] = manifest["monitor_sha256"] if manifest else None
    report["policy_sha256"] = manifest["policy_sha256"] if manifest else None
    # Exclusive creation is essential: exists()+write_text() is a TOCTOU
    # overwrite and a dangling symlink can redirect into frozen evidence.
    # Preserve failed/sparse receipts for inspection, without ever replacing
    # an existing path. Directory ownership/isolation is an external premise.
    try:
        fd = os.open(a.output, os.O_WRONLY | os.O_CREAT | os.O_EXCL |
                     os.O_NOFOLLOW | os.O_CLOEXEC, 0o600)
        with os.fdopen(fd, "w", encoding="utf-8") as out:
            out.write(json.dumps(report, sort_keys=True, indent=2) + "\n")
            out.flush()
            os.fsync(out.fileno())
    except OSError as exc:
        p.error(f"cannot create new receipt exclusively: {exc}")
    print(report["status"] + ": " + str(report["sample_size"]) + " samples")
    if report["status"] not in ("conditional_sample_bound",
                                "conditional_limits_met"):
        raise SystemExit(2)


if __name__ == "__main__":
    main()
