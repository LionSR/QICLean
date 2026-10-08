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
    if path == "QICLean/Representation.lean":
        data = data.replace(b"import QICLean.Representation.CompatiblePhysicalLabel\n", b"")
    if path == "blueprint/src/chapter/ch13_schur_labels.tex":
        data = data.replace(b"\\input{fragment/compatible_physical_label}\n", b"")
    if path == "docs/tactic_patterns.md":
        original = subprocess.check_output(["git", "show", f"{parent}:{path}"])
        assert data.startswith(original), path
        continue
    actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    assert actual == oid.decode(), path
    count += 1
print(json.dumps({"parent_revision": parent, "exact_unchanged_parent_files": count, "permitted_parent_edits": "exact import/input; ledger append only", "parent_mathematical_sources_and_bound_evidence": "unchanged"}))

leaf = root / "docs/provenance/evidence/compatiblePhysicalLabel8753"
m = json.loads((leaf / "manifest.json").read_text())
for path, item in m["artifacts"].items():
    assert hashlib.sha256((root / path).read_bytes()).hexdigest() == item["sha256"], path
    assert (root / path).read_bytes() == subprocess.check_output(["git", "show", "925b12b6:"+path]), path
for path in ["docs/provenance/evidence/compatiblePhysicalLabel8753/manifest.json", "docs/provenance/openai-math.d/compatiblePhysicalLabel8753.json"]:
    assert (root / path).read_bytes() == subprocess.check_output(["git", "show", "925b12b6:"+path]), path
for branch, revision in {"feat/area-law-pair-merge-moment": "ef7442f03ea09bb7997295304ba4ddc289b540b0e", "feat/area-law-pair-merge-deficit": "038138a077800f1b4b2f82378e423bddd8de9582"}.items():
    actual = subprocess.check_output(["git", "rev-parse", branch], text=True).strip()
    if branch.endswith("pair-merge-moment"):
        assert actual.startswith("ef7442f0"), actual
    else:
        assert actual == revision, actual
print("Frozen mathematical source, leaf artifacts and both published branches preserved.")
