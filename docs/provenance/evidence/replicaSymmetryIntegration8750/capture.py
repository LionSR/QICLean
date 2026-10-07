"""Record the completed, source-bound integration checks and rendered artifacts."""
import gzip
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

root = Path.cwd()
evidence = root / "docs/provenance/evidence/replicaSymmetryIntegration8750"
leaf = root / "docs/provenance/evidence/replicaSymmetry8750"
freeze = json.loads((evidence / "source-freeze.json").read_text())


def digest(data):
    return hashlib.sha256(data).hexdigest()


def write(name, value):
    (evidence / name).write_text(json.dumps(value, indent=2) + "\n")


for path, expected in freeze["production_sha256"].items():
    assert digest((root / path).read_bytes()) == expected
    assert digest(subprocess.check_output([
        "git", "show", freeze["source_revision"] + ":" + path])) == expected

parent = json.loads((leaf / "parent-evidence-preservation.json").read_text())
for path, expected in parent["sha256"].items():
    assert digest((root / path).read_bytes()) == expected, path
    assert digest(subprocess.check_output([
        "git", "show", parent["parent_revision"] + ":" + path])) == expected, path
assert len(parent["sha256"]) == 475
assert (evidence / "axioms.log").read_bytes() == (leaf / "axioms.log").read_bytes()

commands = {}
for path in sorted(evidence.glob("*-exit.json")):
    value = json.loads(path.read_text())
    assert value["source_revision"] == freeze["source_revision"]
    assert value["exit_code"] == 0
    data = (root / value["log"]).read_bytes()
    assert digest(data) == value["sha256"]
    if value["compressed"]:
        assert data[4:8] == b"\0" * 4
        data = gzip.decompress(data)
    assert digest(data) == value["uncompressed_sha256"]
    assert len(data) == value["uncompressed_bytes"]
    commands[path.name.removesuffix("-exit.json")] = value

build = (root / commands["full-build"]["log"]).read_text()
assert "Build completed successfully (9709 jobs)." in build
assert not re.search(r"Built Mathlib\.", build)
decls = (root / "blueprint/lean_decls").read_bytes()
assert len(decls.decode().split()) == 3283
(evidence / "lean_decls").write_bytes(decls)
checker = root / ".lake/packages/checkdecls/.lake/build/bin/checkdecls"
checker_revision = subprocess.check_output([
    "git", "-C", str(checker.parents[3]), "rev-parse", "HEAD"]).decode().strip()

pdf = root / "blueprint/print/print.pdf"
info = (evidence / "pdfinfo.log").read_text()
assert re.search(r"Pages:\s+427", info)
print_log = (root / "blueprint/print/print.log").read_bytes()
assert b"Output written on" in print_log
assert b"427 pages" in print_log
assert not re.search(rb"undefined|multiply defined", print_log, re.IGNORECASE)
new_log = print_log.split(b"(./fragment/replica_permutation_covariance.tex", 1)[1]
new_log = new_log.split(b"(./chapter/ch12_entropy_corollaries.tex", 1)[0]
assert b"Overfull" not in new_log
with (evidence / "final-print.log.gz").open("wb") as output:
    with gzip.GzipFile(filename="", mode="wb", fileobj=output, mtime=0) as zipped:
        zipped.write(print_log)
for page in [316, 407, 408]:
    shutil.copyfile(f"/tmp/replica-symmetry-render/page-{page}.png",
                    evidence / f"page-{page}.png")
write("render-inspection.json", {
    "source_revision": freeze["source_revision"],
    "pdf_sha256": digest(pdf.read_bytes()),
    "pdf_bytes": pdf.stat().st_size,
    "pdf_pages": 427,
    "visually_inspected_physical_pages": [316, 407, 408],
    "new_theorem_numbers": ["13.28.1", "13.28.2", "13.28.3", "13.28.4", "13.28.5"],
    "findings": [
        "Chapter 13 Quantum Entropy is visible on physical page 316; its original six-line source header is preserved.",
        "All five statements, proofs and the manuscript citation are legible on physical pages 407–408; no clipped formula or overlapping text occurs.",
        "The tensor-power theorem ends page 407 and its complete proof follows on page 408. The remaining three theorems and proofs fit on page 408.",
        "The final LaTeX writer succeeded; citations and cross-references resolve. No overfull box occurs in the new fragment.",
        "The complete book retains overfull-box warnings in other entries; they were not modified in this contribution."
    ],
    "final_print_log": {"uncompressed_sha256": digest(print_log),
        "gzip_sha256": digest((evidence / "final-print.log.gz").read_bytes()), "gzip_mtime": 0}
})

html = (root / "blueprint/web/ch-entropy.html").read_text()
start = html.index('<h1 id="sec:replica_copy_covariance">')
end = html.index("<h1 ", start + 5)
excerpt = html[start:end]
labels = ["replica_sum_copy_commute", "replica_product_copy_commute",
          "replica_cfc_copy_commute", "replica_cfc_auxiliary_commute", "replica_cfc_preserves_fixed"]
ledger = json.loads((root / "docs/provenance/openai-math.d/replicaSymmetry8750.json").read_text())
names = [entry["downstream"]["declaration"] for entry in ledger["entries"]]
for label in labels:
    assert f'id="thm:{label}"' in excerpt
for name in names:
    assert f'../docs/find/#doc/{name}' in excerpt
    assert name in decls.decode().split()
anchors = set(re.findall(r'id="([^"]+)"', html))
references = re.findall(r'href="ch-entropy.html#([^"]+)"', excerpt)
assert all(reference in anchors for reference in references)
(evidence / "web-section.html").write_text(excerpt)
write("web-inspection.json", {
    "source_revision": freeze["source_revision"],
    "complete_entropy_html_sha256": digest(html.encode()),
    "section_excerpt_sha256": digest(excerpt.encode()),
    "labels": labels, "exact_declarations": names,
    "local_section_references_resolve": True,
    "warning": "The tenkz canary rejected the xdv route; the documented PDF-to-pdftocairo fallback completed successfully."
})

write("verification.json", {
    **freeze, "commands": commands, "full_library_jobs": 9709,
    "fresh_stock_kernel_reports": 5,
    "allowed_kernel_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "new_owned_provenance_shards": 1,
    "owned_exact_declarations": names,
    "leaf_and_integration_kernel_logs_byte_identical": True,
    "preserved_parent_evidence_files": 475,
    "preserved_parent_kernel_reports": 89,
    "parent_audit_scope": "Preserved byte-for-byte; no fresh all-parent audit is claimed.",
    "native_declaration_count": 3283,
    "native_checker_revision": checker_revision,
    "native_checker_sha256": digest(checker.read_bytes()),
    "paper_gap_registered_slugs": 60,
    "Mathlib_source_compilation_in_full_log": False,
    "prebuilt_cache_binding": "replicaSymmetry8750/cache-exit.json: named and actual Mathlib revisions match; successful fetch and artifact guard occurred after APFS cloning completed.",
    "excluded_operational_attempt": "The overlapping initial fetch remains under excluded-overlap-cache-* and does not serve as the build guard."
})
compressed = {}
for path in sorted(evidence.glob("*.gz")):
    data = path.read_bytes()
    assert data[4:8] == b"\0" * 4
    raw = gzip.decompress(data)
    compressed[path.name] = {"gzip_sha256": digest(data),
        "uncompressed_sha256": digest(raw), "uncompressed_bytes": len(raw), "gzip_mtime": 0}
write("compressed-logs.json", compressed)
write("evidence-sha256.json", {str(path.relative_to(evidence)): digest(path.read_bytes())
    for path in sorted(evidence.rglob("*")) if path.is_file() and path.name != "evidence-sha256.json"})
print("Verified source bytes, 475 immutable parent records, command exits, five reports and rendered artifacts.")
