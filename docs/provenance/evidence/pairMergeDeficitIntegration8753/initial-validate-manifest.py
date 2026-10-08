"""Validate immutable source, inherited bytes, actual exits and reader evidence."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess

root = Path.cwd()
folder = Path(__file__).resolve().parent
sha = lambda data: hashlib.sha256(data).hexdigest()
freeze = json.loads((folder / "source-freeze.json").read_text())
for name, digest in freeze["production_sha256"].items():
    assert sha((root / name).read_bytes()) == digest, name
    assert sha(subprocess.check_output(["git", "show", freeze["source_revision"]+":"+name])) == digest, name
exposition=json.loads((folder / "exposition-change.json").read_text())
assert sha((root/exposition["fragment_path"]).read_bytes())==exposition["revised_fragment_sha256"]
assert sha(subprocess.check_output(["git","show",freeze["mathematical_revision"]+":"+exposition["fragment_path"]]))==exposition["original_fragment_sha256"]
for name,digest in exposition["unchanged_production_sha256"].items():
 assert sha((root/name).read_bytes())==digest,name
 assert sha(subprocess.check_output(["git","show",freeze["mathematical_revision"]+":"+name]))==digest,name
leaf = root / "docs/provenance/evidence/pairMergeDeficit8753"
for name, digest in json.loads((leaf / "manifest.json").read_text())["artifacts_sha256"].items():
    assert sha((root / name).read_bytes()) == digest, name
    assert sha(subprocess.check_output(["git", "show", freeze["leaf_evidence_revision"]+":"+name])) == digest, name
parent = json.loads((leaf / "parent-before.json").read_text())
changed = sorted(name for name,digest in parent["files_sha256"].items() if sha((root/name).read_bytes()) != digest)
assert changed == ["QICLean/Representation.lean", "blueprint/src/chapter/ch13_schur_labels.tex", "docs/tactic_patterns.md"], changed
get = lambda name: subprocess.check_output(["git", "show", parent["revision"]+":"+name])
assert (root / changed[0]).read_bytes().replace(b"import QICLean.Representation.PairMergeMoment\n", b"") == get(changed[0])
assert (root / changed[1]).read_bytes().replace(b"\\input{fragment/pair_merge_deficit}\n", b"") == get(changed[1])
assert (root / changed[2]).read_bytes().startswith(get(changed[2]))
for path in folder.glob("*-exit.json"):
    if path.name == "validation-exit.json": continue
    record = json.loads(path.read_text())
    assert record["source_revision"] == freeze["source_revision"] and record["exit_code"] == 0, path
    raw = (root / record["log"]).read_bytes()
    assert sha(raw) == record["sha256"], path
    if record["compressed"]:
        assert raw[4:8] == b"\0"*4, path
        raw = gzip.decompress(raw)
    assert sha(raw) == record["uncompressed_sha256"] and len(raw) == record["uncompressed_bytes"], path
full = gzip.decompress((folder / "full-build.log.gz").read_bytes()).decode()
assert "Build completed successfully (9793 jobs)." in full
assert not re.search(r"Built Mathlib(?:\.|\s)", full)
pdf = json.loads((folder / "pdf-inspection.json").read_text())
assert pdf["visual_review"] == "passed" and pdf["inspected_physical_pages"]
assert sha(gzip.decompress((root / pdf["archived_pdf_gzip"]).read_bytes())) == pdf["pdf_sha256"]
assert sha((root / pdf["archived_pdf_gzip"]).read_bytes()) == pdf["archived_pdf_gzip_sha256"]
text = (folder / "complete-book-text.txt.gz").read_bytes()
assert text[4:8] == b"\0"*4 and sha(text) == pdf["compressed_text_sha256"]
assert sha(gzip.decompress(text)) == pdf["text_sha256"]
native = json.loads((folder / "native-targets.json").read_text())
assert native["contains_all_six_owned"] and len(native["owned_declarations"]) == 6
assert native["contains_all_active_fragment_targets"]
assert sha((folder / "NativeDeclarations.txt").read_bytes()) == native["native_list_sha256"]
assert native["native_declarations"]==3640 and native["fragment_declarations"]==13
assert json.loads((folder / "web-inspection.json").read_text())["visual_review"]=="passed"
mobile = json.loads((folder / "mobile-equations.json").read_text())
assert mobile["result"] == "passed" and len(mobile["equations"]) == 3
assert all(e["clientWidth"] > 0 for e in mobile["equations"])
assert all(e["scrollLeft"] > 0 for e in mobile["equations"] if e["scrollWidth"] > e["clientWidth"]+1)
web = json.loads((folder / "whole-web.log").read_text())
assert web["pages"] > 0 and web["typeset"] > 0
print("Passed: fixed source, exact parent/leaf bytes, all actual exits and dual log hashes, complete book and native inventory, desktop/mobile open proofs and all three displays, whole-web regression.")
