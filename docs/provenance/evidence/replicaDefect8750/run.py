"""Record a command's complete output, exit status and immutable source identity."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

evidence = Path(__file__).resolve().parent
root = evidence.parents[3]
label, *command = sys.argv[1:]
if command and command[0] == "--":
    command = command[1:]
if not command:
    raise SystemExit("A command is required.")
freeze = json.loads((evidence / "source-freeze.json").read_text())
for record in freeze["files"] + [freeze["preserved_cutoff"]]:
    if hashlib.sha256((root / record["path"]).read_bytes()).hexdigest() != record["sha256"]:
        raise SystemExit(f"Frozen source changed: {record['path']}")
started = datetime.now(timezone.utc).isoformat()
clock = time.monotonic()
log = evidence / f"{label}.log"
with log.open("wb") as output:
    result = subprocess.run(command, cwd=root, stdout=output, stderr=subprocess.STDOUT)
record = {
    "source_revision": freeze["source_revision"],
    "command": command,
    "cwd": str(root),
    "started_utc": started,
    "elapsed_seconds": round(time.monotonic() - clock, 3),
    "exit_code": result.returncode,
    "log": str(log.relative_to(root)),
    "sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
}
(evidence / f"{label}-exit.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record))
raise SystemExit(result.returncode)
