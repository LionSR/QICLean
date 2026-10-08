"""Check every tracked parent byte, allowing only the recorded ledger append."""
from pathlib import Path
import hashlib
import json
import subprocess
root = Path.cwd()
parent = "f675fee80416c966989bc8bc124a3d54b1348492"
records = subprocess.check_output(["git", "ls-tree", "-rz", "--full-tree", parent]).split(b"\0")
count = 0
for record in records:
    if not record:
        continue
    info, name = record.split(b"\t", 1)
    kind, oid = info.split()[1:]
    if kind != b"blob":
        continue
    path = name.decode()
    data = (root / path).read_bytes()
    if path == "docs/tactic_patterns.md":
        original = subprocess.check_output(["git", "show", f"{parent}:{path}"])
        assert data.startswith(original), path
        continue
    actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    assert actual == oid.decode(), path
    count += 1
print(json.dumps({"parent_revision": parent, "exact_unchanged_parent_files": count, "sole_parent_edit": "docs/tactic_patterns.md: append only", "parent_mathematical_sources_and_bound_evidence": "unchanged"}))
