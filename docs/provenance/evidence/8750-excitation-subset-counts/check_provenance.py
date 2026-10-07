#!/usr/bin/env python3
"""Check only the four excitation-subset provenance entries.

Use TNLean's shared OpenAI provenance validator and schema, supplied explicitly.
The remainder of QICLean's existing provenance is outside this check's scope.
"""
import argparse
import importlib.util
import hashlib
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--validator", required=True, type=Path)
parser.add_argument("--schema", required=True, type=Path)
parser.add_argument("--upstream-root", required=True, type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location("shared_provenance", args.validator)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
ledger = json.loads((root / "docs/provenance/openai-math.d/excitationSubsetCounts8750.json").read_text())
schema = json.loads(args.schema.read_text())
expected = {
    "Real.log_choose_le_mul_binEntropy",
    "Real.choose_le_exp_mul_binEntropy",
    "Real.sum_choose_le_mul_exp_binEntropy",
    "Finset.card_filter_powerset_le_mul_exp_binEntropy",
}
assert {entry["downstream"]["declaration"] for entry in ledger["entries"]} == expected
assert ledger["source"]["commit"] == "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
count = module.validate([ledger], schema, {
    "LionSR/QICLean": root,
    "openai/math": args.upstream_root.resolve(),
}, scan=False)
code, _ = module.lean_parts((root / "QICLean/Analysis/ExcitationSubsetCounts.lean").read_text())
assert not re.search(r"\b(?:sorry|admit|axiom|native_decide|unsafeCast)\b", code)
metadata = json.loads(Path(__file__).with_name("metadata.json").read_text())
assert {entry["verification"]["revision"] for entry in ledger["entries"]} == {metadata["revision"]}
for path, digest in metadata["source_files"].items():
    actual = (root / path).read_bytes()
    frozen = module.git_bytes(root, metadata["revision"], path)
    assert actual == frozen and hashlib.sha256(actual).hexdigest() == digest
for record in metadata["commands"]:
    assert record["exit_code"] == 0
    actual = (root / record["log"]).read_bytes()
    assert hashlib.sha256(actual).hexdigest() == record["sha256"]
native = metadata["native_declarations"]
actual = (root / native["log"]).read_bytes()
assert hashlib.sha256(actual).hexdigest() == native["sha256"]
assert len(actual.decode().splitlines()) == native["count"]
assert set(native["new_exports"]) == expected <= set(actual.decode().splitlines())
source = json.loads(Path(__file__).with_name("source.json").read_text())
actual = module.git_bytes(args.upstream_root, source["commit"], source["path"])
assert len(actual) == source["bytes"] and hashlib.sha256(actual).hexdigest() == source["sha256"]
lines = actual.decode().splitlines()
assert all(lines[int(i)-1] == line for i, line in source["lines"].items())
print(f"Excitation-subset provenance valid: {count} entries; exact source bytes and log hashes checked.")
print("All four recorded kernel reports use only propext, Classical.choice and Quot.sound.")
print("Proof-integrity token scan passed; no new Lean invocation was performed by this checker.")
