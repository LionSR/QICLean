"""Validate the two original records against the frozen TNLean policy."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

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
    ledger = module.read_json(root / "docs/provenance/openai-math.d/typicalStateFromTail8753.json")
    total = module.validate([ledger], schema, {"LionSR/QICLean": root}, scan=False)
    raw = (evidence / "axioms.log").read_text()
    for entry in ledger["entries"]:
        module.check_axiom_output(raw, entry["downstream"]["declaration"])
    print(f"Validated entries and exact-name kernel reports: {total}")
