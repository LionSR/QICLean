"""Validate the actual actual two-deficit component moment provenance record against the frozen TNLean policy."""
import importlib.util
import json
from pathlib import Path
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
    schema = json.loads(subprocess.check_output(["git", "-C", str(tnlean), "show",
        f"{POLICY}:docs/provenance/openai-math.schema.json"]))
    spec = importlib.util.spec_from_file_location("frozen_validator", validator)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    names = json.loads((evidence / "owned-shards.json").read_text())
    ledgers = [module.read_json(root / "docs/provenance/openai-math.d" / name) for name in names]
    total = module.validate(ledgers, schema, {"LionSR/QICLean": root}, scan=False)
    entries = [entry for ledger in ledgers for entry in ledger["entries"]]
    raw = (evidence / "bound-axioms.log").read_text()
    for entry in entries:
        module.check_axiom_output(raw, entry["downstream"]["declaration"])
    print(f"Validated entries: {total}")
    print(f"Validated exact-name combined kernel reports: {len(entries)}")
