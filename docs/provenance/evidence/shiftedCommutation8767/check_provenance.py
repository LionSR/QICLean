"""Check the owned shifted-power commutation shard with the frozen TNLean provenance policy."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("--root", type=Path, required=True)
p.add_argument("--validator", type=Path, required=True)
p.add_argument("--schema", type=Path, required=True)
a = p.parse_args()
expected = {
    "validator": "8183e29f5a339bba37e28e9473aa7a6a42791282ed6877071dfd4096eda7cb65",
    "schema": "a691d8e95b668c968365f2c7e33f614d49635aade8fdd4c2f27cd64f0cd6b459",
}
for key in expected:
    assert hashlib.sha256(getattr(a, key).read_bytes()).hexdigest() == expected[key]
spec = importlib.util.spec_from_file_location("frozen_policy", a.validator)
policy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(policy)
ledger = policy.read_json(a.root / "docs/provenance/openai-math.d/shiftedCommutation8767.json")
schema = policy.read_json(a.schema)
count = policy.validate([ledger], schema, {"LionSR/QICLean": a.root}, scan=False)
# Only this module is owned by this shard; unrelated inherited rows are excluded.
source = (a.root / "QICLean/Analysis/ShiftedDensityCommutation.lean").read_text()
public = policy.declarations(source)
expected_names = {entry["downstream"]["declaration"] for entry in ledger["entries"]}
assert set(public) == expected_names, (set(public), expected_names)
_, blocks = policy.lean_parts(source)
ids = [identifier for block in blocks for identifier in policy.ID_RE.findall(block)]
assert sorted(ids) == sorted(entry["id"] for entry in ledger["entries"])
for entry in ledger["entries"]:
    policy.notice_block(source, entry)
print(f"Owned shard valid: {count} public declarations, immutable source and log hashes, standard kernel axioms, complete original notices.")
print("Policy: TNLean@c738e87489bc1b4ae1d58a6bdefb2c1cbd654114. Repository-wide inherited shards not re-audited.")
