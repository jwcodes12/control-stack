#!/usr/bin/env python3
"""Run off-the-shelf baselines (Conftest/OPA, Trivy, Hadolint, KICS) over the sealed held-out corpora and score them against
the sealed ground truth (gate G3). Needs the tools installed: conftest, trivy, hadolint on PATH and Docker with the
checkmarx/kics image. Not run in CI. Output: JSON plus the per-tool raw artifacts under --output.

A baseline "rejects" a case if it reports at least one finding (KICS: also reported at HIGH or above). A negative is a case whose
ground truth is not SAFE_IN_SUPPORTED_MODEL. Caught = negative and rejected; over-rejected = safe and rejected. Baselines read
declared Compose fields only, so this is a comparison of scope, not a claim that those tools are poor.
"""
import argparse
import os
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from deployment.rules_baseline import assess  # noqa: E402

CORPORA = {"tier6": ROOT / "deployment/heldout/tier6", "tier10": ROOT / "deployment/heldout/tier10"}
SAFE = "SAFE_IN_SUPPORTED_MODEL"


def key(k):
    import re
    return k if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.-]*", k) and k.lower() not in ("true", "false", "null", "yes", "no", "on", "off") else json.dumps(k)


def to_yaml(value, indent=0):
    """Minimal block-style YAML emitter for JSON values (KICS does not detect Compose in flow-style JSON text)."""
    pad = "  " * indent
    if isinstance(value, dict):
        if not value:
            return "{}"
        lines = []
        for k, v in value.items():
            if isinstance(v, (dict, list)) and v:
                lines.append(f"{pad}{key(k)}:\n{to_yaml(v, indent + 1)}")
            else:
                lines.append(f"{pad}{key(k)}: {to_yaml(v, indent + 1)}")
        return "\n".join(lines)
    if isinstance(value, list):
        if not value:
            return "[]"
        lines = []
        for item in value:
            if isinstance(item, (dict, list)) and item:
                body = to_yaml(item, indent + 1).split("\n")
                lines.append(f"{pad}- {body[0].lstrip()}" + ("\n" + "\n".join(body[1:]) if len(body) > 1 else ""))
            else:
                lines.append(f"{pad}- {to_yaml(item, indent + 1)}")
        return "\n".join(lines)
    return json.dumps(value)


def run(argv, **kw):
    return subprocess.run(argv, text=True, capture_output=True, **kw)


def manifest(corpus):
    m = json.loads((corpus / "manifest.json").read_text())
    return m["cases"] if isinstance(m, dict) else m


def conftest_findings(compose_path):
    p = run(["conftest", "test", "--policy", str(ROOT / "deployment/baselines"), "--output", "json", str(compose_path)])
    data = json.loads(p.stdout)
    return [f["msg"] for f in data[0].get("failures", [])]


def kics_findings(cases_by_dir, workdir):
    """One KICS run over a directory with one subdirectory per case; returns {case_dir: [(severity, query)]}."""
    out = workdir / "kics-out"
    out.mkdir()
    p = run(["docker", "run", "--rm", "--user", f"{os.getuid()}:{os.getgid()}", "-v", f"{workdir/'cases'}:/path:ro", "-v", f"{out}:/out", "checkmarx/kics:latest", "scan",
             "-p", "/path", "-q", "/app/bin/assets/queries", "--no-progress", "--disable-secrets", "-o", "/out",
             "--report-formats", "json"])
    result = json.loads((out / "results.json").read_text())
    found = {}
    for q in result["queries"]:
        for f in q["files"]:
            case_dir = Path(f["file_name"]).parent.name  # KICS reports "../../path/<case>/docker-compose.yml"
            found.setdefault(case_dir, []).append((q["severity"], q["query_name"]))
    return found, result.get("files_scanned"), p.returncode


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True)
    a = ap.parse_args()
    out = Path(a.output).resolve()
    out.mkdir(parents=True, exist_ok=False)
    tools = {}
    for name, flag in (("conftest", "--version"), ("trivy", "--version"), ("hadolint", "--version")):
        path = shutil.which(name)
        tools[name] = {"path": path, "sha256": hashlib.sha256(Path(path).read_bytes()).hexdigest() if path else None,
                       "version": run([name, flag]).stdout.strip().splitlines()[0] if path else None}
    img = run(["docker", "image", "inspect", "checkmarx/kics:latest", "--format", "{{.Id}}"]).stdout.strip()
    kv = run(["docker", "run", "--rm", "checkmarx/kics:latest", "version"]).stdout.strip()
    tools["kics"] = {"image_id": img, "version": kv}
    report = {"tools": tools, "corpora": {}}
    for cname, corpus in CORPORA.items():
        cases = manifest(corpus)
        with tempfile.TemporaryDirectory() as tmp:
            work = Path(tmp)
            (work / "cases").mkdir()
            for c in cases:
                d = work / "cases" / c["id"]
                d.mkdir()
                (d / "docker-compose.yml").write_text(to_yaml(json.loads((corpus / c["compose"]).read_text())) + "\n")
            kics, scanned, kics_exit = kics_findings(cases, work)
            unknown = set(kics) - {c["id"] for c in cases}
            if unknown:
                raise SystemExit(f"KICS findings for unknown case directories {sorted(unknown)}: mapping is wrong")
            if scanned != len(cases):
                raise SystemExit(f"KICS scanned {scanned} files for {len(cases)} cases in {cname}: the baseline is not valid")
            trivy = run(["trivy", "config", "--skip-check-update", "--format", "json", str(work / "cases")])
            trivy_json = json.loads(trivy.stdout) if trivy.stdout.strip().startswith("{") else {}
            trivy_results = trivy_json.get("Results") or []
            hadolint_dockerfiles = [c["id"] for c in cases if (corpus / c["compose"]).with_name(c["id"] + ".Dockerfile").exists()]
            rows = []
            for c in cases:
                compose = json.loads((corpus / c["compose"]).read_text())
                cf = conftest_findings(corpus / c["compose"])
                py = assess(compose)
                kf = kics.get(c["id"], [])
                rows.append({
                    "id": c["id"], "ground_truth": c["ground_truth"],
                    "python_rules": py["verdict"], "python_findings": py["findings"],
                    "conftest_owasp": "REJECT" if cf else "ALLOW", "conftest_findings": cf,
                    "kics_any": "REJECT" if kf else "ALLOW", "kics_high": "REJECT" if any(s in ("HIGH", "CRITICAL") for s, _ in kf) else "ALLOW",
                    "kics_findings": sorted(set(f"{s}:{q}" for s, q in kf)),
                })
            summary = {}
            negatives = [r for r in rows if r["ground_truth"] != SAFE]
            safe = [r for r in rows if r["ground_truth"] == SAFE]
            for key in ("python_rules", "conftest_owasp", "kics_any", "kics_high"):
                summary[key] = {"negatives": len(negatives), "caught": sum(r[key] == "REJECT" for r in negatives),
                                "safe": len(safe), "over_rejected": sum(r[key] == "REJECT" for r in safe)}
            report["corpora"][cname] = {
                "cases": len(rows), "summary": summary,
                "trivy": {"exit": trivy.returncode, "result_targets": len(trivy_results), "applicable": bool(trivy_results),
                          "note": "no Compose scanner: 'Detected config files num=0; Supported files for scanner(s) not found'" if not trivy_results else ""},
                "hadolint": {"dockerfiles_in_corpus": len(hadolint_dockerfiles), "applicable": bool(hadolint_dockerfiles),
                             "note": "no case has a Dockerfile; Hadolint reads Dockerfiles only"},
                "kics_files_scanned": scanned, "kics_exit": kics_exit, "rows": rows}
    (out / "results.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({c: v["summary"] for c, v in report["corpora"].items()}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
