"""Offline project import build; all generated files stay beside this script."""
from pathlib import Path
import os, re, subprocess, hashlib, json
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[3]
CACHE = OUT / "imports"
MODULES = ["ControlStack.Core.AntiRollback", "ControlStack.Scenarios.SC27Chain", "ControlStack.Scenarios.SC27ExtensionOnly", "ControlStack.Scenarios.SC27Refinement"]
def prepare(cache=None, record=True):
    cache = Path(cache) if cache is not None else CACHE
    env = dict(os.environ)
    env["LEAN_PATH"] = str(cache) + (":" + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    done = set()
    hashes = {}
    def build(module):
        if module in done: return
        source = ROOT / (module.replace(".", "/") + ".lean")
        content = source.read_text()
        # During typing this reads import directives only; no declarations are displayed.
        for dep in re.findall(r"^import\s+([A-Za-z0-9_.]+)", content, re.M):
            if dep.startswith("ControlStack."): build(dep)
        dest = cache / (module.replace(".", "/") + ".olean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        proc = subprocess.run(["lake", "env", "lean", "-o", str(dest), str(source)], cwd=ROOT, env=env, capture_output=True, text=True)
        if record:
            (OUT / "compile-logs" / (module + ".txt")).write_text(proc.stdout + proc.stderr)
        if proc.returncode: raise RuntimeError(module + " build failed: " + proc.stdout + proc.stderr)
        hashes[module] = {"source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(), "olean_sha256": hashlib.sha256(dest.read_bytes()).hexdigest()}
        done.add(module)
    for module in MODULES: build(module)
    if record:
        (cache / "HASHES.json").write_text(json.dumps(hashes, indent=2) + "\n")
    return env
if __name__ == "__main__":
    prepare()
    print("Offline imports ready")
