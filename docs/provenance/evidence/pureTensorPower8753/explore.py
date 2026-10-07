"""Capture exploratory diagnostics separately from the eventual frozen checks."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

root = Path.cwd()
evidence = root / "docs/provenance/evidence/pureTensorPower8753"
source = root / "QICLean/Entropy/PureTensorPower.lean"
name = sys.argv[1]
args = sys.argv[2:]
sha = hashlib.sha256(source.read_bytes()).hexdigest()
start = time.monotonic()
with (evidence / (name + ".log")).open("wb") as out:
    result = subprocess.run(args, stdout=out, stderr=subprocess.STDOUT)
assert hashlib.sha256(source.read_bytes()).hexdigest() == sha
raw = (evidence / (name + ".log")).read_bytes()
(evidence / (name + "-exit.json")).write_text(json.dumps({
    "status": "exploratory, excluded from final provenance",
    "source_sha256": sha, "argv": args, "exit_code": result.returncode,
    "elapsed_seconds": time.monotonic() - start,
    "raw_log_sha256": hashlib.sha256(raw).hexdigest()
}, indent=2) + "\n")
print(raw.decode(errors="replace")[-6000:])
sys.exit(result.returncode)
