"""Collect actual integration results after mathematical and visual checks pass."""
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess

root = Path.cwd()
evidence = root / "docs/provenance/evidence/pureTensorPowerIntegration8753"
leaf = root / "docs/provenance/evidence/pureTensorPower8753"
freeze = json.loads((evidence / "source-freeze.json").read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(name, value):
    (evidence / name).write_text(json.dumps(value, indent=2) + "\n")


for path, expected in freeze["production_sha256"].items():
    data = (root / path).read_bytes()
    assert sha(data) == expected
    assert subprocess.check_output([
        "git", "show", freeze["source_revision"] + ":" + path]) == data
parent = json.loads((leaf / "parent-evidence-preservation.json").read_text())
for path, expected in parent["sha256"].items():
    assert sha((root / path).read_bytes()) == expected
assert len(parent["sha256"]) == 196

commands = {}
for path in sorted(evidence.glob("*-exit.json")):
    value = json.loads(path.read_text())
    assert value["source_revision"] == freeze["source_revision"]
    assert value["exit_code"] == 0
    data = (root / value["log"]).read_bytes()
    assert sha(data) == value["sha256"]
    if value["compressed"]:
        assert data[4:8] == b"\0" * 4
        data = gzip.decompress(data)
    assert sha(data) == value["uncompressed_sha256"]
    assert len(data) == value["uncompressed_bytes"]
    commands[path.name.removesuffix("-exit.json")] = value

for path in sorted((evidence / "excluded").glob("*-exit.json")):
    value = json.loads(path.read_text())
    assert value["source_revision"] == freeze["source_revision"]
    assert value["exit_code"] == 1
    data = (root / value["log"]).read_bytes()
    assert sha(data) == value["sha256"]
    if value["compressed"]:
        assert data[4:8] == b"\0" * 4
        data = gzip.decompress(data)
    assert sha(data) == value["uncompressed_sha256"]
    assert len(data) == value["uncompressed_bytes"]

build_record = commands["full-build"]
build = (root / build_record["log"]).read_bytes()
if build_record["compressed"]:
    build = gzip.decompress(build)
build = build.decode()
assert "Build completed successfully (9695 jobs)." in build
assert not re.search(r"Built Mathlib\.", build)
assert (evidence / "axioms.log").read_bytes() == (leaf / "axioms.log").read_bytes()

decls = (root / "blueprint/lean_decls").read_bytes()
(evidence / "lean_decls").write_bytes(decls)
ledger = json.loads((root / "docs/provenance/openai-math.d/pureTensorPower8753.json").read_text())
names = [entry["downstream"]["declaration"] for entry in ledger["entries"]]
assert len(names) == 2
assert all(name in decls.decode().split() for name in names)

pdf = root / "blueprint/print/print.pdf"
pages = int(re.search(r"Pages:\s+(\d+)", (evidence / "pdfinfo.log").read_text()).group(1))
inspection = json.loads((evidence / "render-inspection.json").read_text())
assert inspection["source_revision"] == freeze["source_revision"]
assert inspection["pdf_sha256"] == sha(pdf.read_bytes())
assert inspection["pdf_pages"] == pages
assert inspection["visual_result"] == "passed"
raw_print = (root / "blueprint/print/print.log").read_bytes()
assert b"Output written on" in raw_print
assert str(pages).encode() + b" pages" in raw_print
assert not re.search(rb"undefined|multiply defined", raw_print, re.IGNORECASE)
new_print = raw_print.split(b"(./fragment/pure_tensor_power.tex", 1)[1]
new_print = new_print.split(b"(./chapter/ch12_entropy_corollaries.tex", 1)[0]
assert new_print.count(b"Overfull") == 1
assert b"1.2038pt too wide" in new_print
assert b"paragraph at lines 1--1" in new_print
assert "1.2038pt" in inspection["new_fragment_heading_warning"]
with (evidence / "final-print.log.gz").open("wb") as out:
    with gzip.GzipFile(filename="", mode="wb", fileobj=out, mtime=0) as zipped:
        zipped.write(raw_print)

html = (root / "blueprint/web/ch-entropy.html").read_text()
start = html.index('<h1 id="sec:pure_tensor_power">')
end = html.index("<h1 ", start + 5)
excerpt = html[start:end]
labels = ["sec:pure_tensor_power", "thm:pure_tensor_power_marginal",
          "thm:pure_tensor_power_projection_mass"]
assert all(f'id="{label}"' in excerpt for label in labels)
assert all(f'../docs/find/#doc/{name}' in excerpt for name in names)
anchors = set(re.findall(r'id="([^"]+)"', html))
references = re.findall(r'href="ch-entropy.html#([^"]+)"', excerpt)
assert all(reference in anchors for reference in references)
citation = re.search(r'<a href="([^"#]+)#OpenAI2026AreaLaw"[^>]*>Ope26b</a>', excerpt)
assert citation
bibliography = root / "blueprint/web" / citation.group(1)
assert 'id="OpenAI2026AreaLaw"' in bibliography.read_text()
(evidence / "web-section.html").write_text(excerpt)
write("web-inspection.json", {
    "source_revision": freeze["source_revision"],
    "entropy_html_sha256": sha(html.encode()), "excerpt_sha256": sha(excerpt.encode()),
    "labels": labels, "exact_declarations": names,
    "all_local_references_resolve": True,
    "bibliography_sha256": sha(bibliography.read_bytes()),
    "bibliography_preceded_web_generation": True,
    "reader_check": "Actual browser typesetting and page overflow checks at 360 and 1440 pixels; new section screenshot visually inspected."
})
checker = root / ".lake/packages/checkdecls/.lake/build/bin/checkdecls"
write("verification.json", {
    **freeze, "commands": commands, "full_library_jobs": 9695,
    "fresh_owned_stock_kernel_reports": 2, "new_owned_shards": 1,
    "allowed_kernel_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "leaf_and_final_reports_byte_identical": True,
    "preserved_parent_evidence_files": 196,
    "parent_audit_scope": "Unchanged parent evidence preserved; no fresh parent declaration audit claimed.",
    "native_declaration_count": len(decls.decode().split()),
    "exact_new_declarations_in_retained_native_list": names,
    "native_checker_revision": subprocess.check_output([
        "git", "-C", str(checker.parents[3]), "rev-parse", "HEAD"]).decode().strip(),
    "native_checker_sha256": sha(checker.read_bytes()),
    "paper_gap_registered_slugs": 59, "Mathlib_source_compilation_in_full_log": False,
    "excluded_attempts": "The incomplete leaf audit capture and earlier overlapping dependency attempt remain explicitly excluded in the leaf evidence. The first integration validator invocation omitted its required repository argument. The initial full library build exited 1 after file-table exhaustion during output-hash removal in an unchanged dependency. Both attempts are retained under excluded/."
})
compressed = {}
for path in sorted(evidence.glob("*.gz")):
    data = path.read_bytes()
    assert data[4:8] == b"\0" * 4
    raw = gzip.decompress(data)
    compressed[path.name] = {"gzip_sha256": sha(data), "uncompressed_sha256": sha(raw),
        "uncompressed_bytes": len(raw), "gzip_mtime": 0}
write("compressed-logs.json", compressed)
write("evidence-sha256.json", {str(path.relative_to(evidence)): sha(path.read_bytes())
    for path in sorted(evidence.rglob("*")) if path.is_file() and path.name != "evidence-sha256.json"})
print("Verified complete integration, two owned reports, exact names, parent records and rendered artifacts.")
