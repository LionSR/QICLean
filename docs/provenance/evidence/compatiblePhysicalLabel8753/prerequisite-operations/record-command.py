"""Record one command against the compatible physical-label prerequisite."""
from pathlib import Path
import gzip
import hashlib
import json
import subprocess
import sys
import time

root = Path.cwd()
evidence = Path(__file__).resolve().parent
freeze = json.loads((evidence / "source-freeze.json").read_text())
name, argv = sys.argv[1], sys.argv[2:]
assert argv
command_cwd = root
if argv[0] == '--cwd':
    command_cwd = (root / argv[1]).resolve()
    argv = argv[2:]
    assert argv
for path, digest in freeze["production_sha256"].items():
    assert hashlib.sha256((root / path).read_bytes()).hexdigest() == digest, path
assert subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip() == freeze["source_revision"]
manifest = json.loads((root / "lake-manifest.json").read_text())
mathlib = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
actual = subprocess.check_output(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"], text=True).strip()
if argv[:2] == ["lake", "build"]:
    assert mathlib == actual
    assert (root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean").is_file()
log = evidence / f"{name}.log"
start = time.monotonic()
with log.open("wb") as out:
    result = subprocess.run(argv, cwd=command_cwd, stdout=out, stderr=subprocess.STDOUT)
raw = log.read_bytes()
if len(raw) > 100000 or name in {"full-build", "pdf", "bbl", "web", "blueprint-sync"}:
    packed = gzip.compress(raw, mtime=0)
    log.unlink()
    log = log.with_suffix(".log.gz")
    log.write_bytes(packed)
record = dict(source_revision=freeze["source_revision"],
    mathematical_revision=freeze["mathematical_revision"],
    production_sha256=freeze["production_sha256"], argv=argv, cwd=str(command_cwd),
    exit_code=result.returncode, elapsed_seconds=time.monotonic()-start, log=str(log.relative_to(root)) if log.is_relative_to(root) else str(log),
    sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
    uncompressed_sha256=hashlib.sha256(raw).hexdigest(), uncompressed_bytes=len(raw),
    compressed=log.suffix == ".gz", deterministic_gzip_mtime=0 if log.suffix == ".gz" else None,
    mathlib_revision=mathlib, actual_mathlib_revision=actual,
    Mathlib_olean_exists=(root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean").is_file())
(evidence / f"{name}-exit.json").write_text(json.dumps(record, indent=2)+"\n")
print(json.dumps(record), flush=True)
for path, digest in freeze["production_sha256"].items():
    assert hashlib.sha256((root / path).read_bytes()).hexdigest() == digest, path
raise SystemExit(result.returncode)
