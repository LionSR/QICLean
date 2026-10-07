"""Validate the eight owned provenance records against the frozen TNLean policy."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

import jsonschema

POLICY = "806099b4dddcce591b3a62ee1921926a6af5ad55"
root = Path.cwd()
evidence = Path(__file__).resolve().parent
tnlean = Path(sys.argv[1]).resolve()
with tempfile.TemporaryDirectory() as directory:
    validator = Path(directory) / "validator.py"
    validator.write_bytes(subprocess.check_output(["git", "-C", str(tnlean), "show",
        f"{POLICY}:scripts/check_openai_provenance.py"]))
    assert hashlib.sha256(validator.read_bytes()).hexdigest() == "8183e29f5a339bba37e28e9473aa7a6a42791282ed6877071dfd4096eda7cb65"
    schema = json.loads(subprocess.check_output(["git", "-C", str(tnlean), "show",
        f"{POLICY}:docs/provenance/openai-math.schema.json"]))
    spec = importlib.util.spec_from_file_location("frozen_validator", validator)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    names = json.loads((evidence / "owned-shards.json").read_text())
    ledgers = [module.read_json(root / "docs/provenance/openai-math.d" / name) for name in names]
    total = module.validate(ledgers, schema, {"LionSR/QICLean": root}, scan=False)
    entries = [entry for ledger in ledgers for entry in ledger["entries"]]
    raw = (evidence / "axioms.log").read_text()
    for entry in entries:
        module.check_axiom_output(raw, entry["downstream"]["declaration"])
    assert total == 57, total
    expected_names = {entry["downstream"]["declaration"] for entry in entries}
    files = {entry["downstream"]["path"] for entry in entries}
    public_names = set()
    for file in files:
        source = (root / file).read_text()
        public_names.update(module.declarations(source))
        code, blocks = module.lean_parts(source)
        assert not re.search(r"\b(?:sorry|admit|native_decide|unsafeCast|axiom)\b", code), file
        ids = [identifier for block in blocks for identifier in module.ID_RE.findall(block)]
        file_entries = [entry for entry in entries if entry["downstream"]["path"] == file]
        assert sorted(ids) == sorted(entry["id"] for entry in file_entries)
        for entry in file_entries:
            module.notice_block(source, entry)
    assert expected_names <= public_names, expected_names - public_names
    leaf_path = "QICLean/Analysis/ShiftedDensityCommutation.lean"
    leaf_names = {entry["downstream"]["declaration"] for entry in entries if entry["downstream"]["path"] == leaf_path}
    assert set(module.declarations((root / leaf_path).read_text())) == leaf_names
    previous = json.loads((root / "docs/provenance/evidence/area-law-analytic-integration/latest-checks.json").read_text())
    for file, digest in previous["files"].items():
        assert hashlib.sha256((root / file).read_bytes()).hexdigest() == digest
    print("Owned production token scan passed.")
    print("Prior 54-declaration production files preserved byte for byte.")
    print("All 57 recorded declarations and their original notices verified; the new leaf public set is complete.")
    print(f"Validated entries: {total}")
    print(f"Validated exact-name combined kernel reports: {len(entries)}")
