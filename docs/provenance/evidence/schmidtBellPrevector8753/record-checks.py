"""Record source-bound checks for the Schmidt and Bell prevector contribution."""
from pathlib import Path
import gzip
import hashlib
import json
import subprocess
import time

root = Path.cwd()
evidence = Path(__file__).resolve().parent
source = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
assert source == "67e75fc624d73eb36ba92737cc47e21e5f4e1b8a"
files = ["QICLean/Representation/SchmidtBellPrevector.lean",
    "blueprint/src/fragment/schmidt_bell_prevector.tex", "docs/tactic_patterns.md"]
production = {path: hashlib.sha256((root / path).read_bytes()).hexdigest() for path in files}
for path in files:
    assert subprocess.check_output(["git", "show", f"{source}:{path}"]) == (root / path).read_bytes()
manifest = json.loads((root / "lake-manifest.json").read_text())
mathlib = next(package["rev"] for package in manifest["packages"] if package["name"] == "mathlib")
actual = subprocess.check_output(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"], text=True).strip()
assert actual == mathlib
assert (root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean").is_file()
(evidence / "source-freeze.json").write_text(json.dumps(dict(source_revision=source,
    base_revision="d6dbfb2b497184c1cd8f4819b3d1429eca21aba8", production_sha256=production,
    mathlib_revision=mathlib, actual_mathlib_revision=actual, Mathlib_olean_exists=True), indent=2)+"\n")
checks = {}
def run(name, argv):
    for path, digest in production.items():
        assert hashlib.sha256((root / path).read_bytes()).hexdigest() == digest
    log = evidence / f"{name}.log"
    start = time.monotonic()
    with log.open("wb") as output:
        result = subprocess.run(argv, stdout=output, stderr=subprocess.STDOUT)
    raw = log.read_bytes()
    if len(raw) > 100000:
        log = log.with_suffix(".log.gz")
        log.write_bytes(gzip.compress(raw, mtime=0))
        (evidence / f"{name}.log").unlink()
    item = dict(source_revision=source, production_sha256=production, argv=argv,
        cwd=str(root), exit_code=result.returncode, elapsed_seconds=time.monotonic()-start,
        log=str(log.relative_to(root)), sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
        uncompressed_sha256=hashlib.sha256(raw).hexdigest(), uncompressed_bytes=len(raw),
        compressed=log.suffix == ".gz", deterministic_gzip_mtime=0 if log.suffix == ".gz" else None)
    checks[name] = item
    (evidence / f"{name}-exit.json").write_text(json.dumps(item, indent=2)+"\n")
    (evidence / "checks.json").write_text(json.dumps(checks, indent=2)+"\n")
    print(f"{name}: exit {result.returncode}, {item['elapsed_seconds']:.2f}s", flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
flags = ["-DwarningAsError=true", "-Dlinter.mathlibStandardSet=true",
    "-DrelaxedAutoImplicit=false", "-DmaxSynthPendingDepth=3"]
run("strict-source", ["lake", "env", "lean", *flags, files[0]])
run("target", ["lake", "build", "QICLean.Representation.SchmidtBellPrevector"])
run("axioms", ["lake", "env", "lean", *flags, str((evidence / "Axioms.lean").relative_to(root))])
run("prose", ["python3", "/Users/siruilu/Local/agentFormalization/TNLean/scripts/check_reader_facing_prose.py",
    "--root", ".", "--diff-base", "d6dbfb2b497184c1cd8f4819b3d1429eca21aba8"])
run("tactic-patterns", ["python3", "/Users/siruilu/Local/agentFormalization/TNLean/scripts/tactic_pattern_scan.py",
    "--root", "QICLean/Representation", "--top", "2", "--show-locations", "2"])
parents = json.loads((evidence / "parents-before-merge.json").read_text())
for records in parents.values():
    for path, digest in records.items():
        assert hashlib.sha256((root / path).read_bytes()).hexdigest() == digest, path
(evidence / "parent-preservation.json").write_text(json.dumps(dict(source_revision=source,
    compared_parent_bindings=sum(len(records) for records in parents.values()),
    distinct_paths=len(set().union(*(set(records) for records in parents.values()))),
    parents={parent: len(records) for parent, records in parents.items()}, passed=True), indent=2)+"\n")
print("Both parents' immutable mathematical and evidence bindings passed", flush=True)
