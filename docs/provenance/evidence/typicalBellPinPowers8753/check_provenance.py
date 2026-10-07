"""Check the five owned finite-copy Bell declarations against the frozen TNLean provenance policy."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import re

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("--root", type=Path, required=True)
p.add_argument("--validator", type=Path, required=True)
p.add_argument("--schema", type=Path, required=True)
a = p.parse_args()
expected = {
    "validator": "8183e29f5a339bba37e28e9473aa7a6a42791282ed6877071dfd4096eda7cb65",
    "schema": "a691d8e95b668c968365f2c7e33f614d49635aade8fdd4c2f27cd64f0cd6b459",
}
for key, digest in expected.items():
    assert hashlib.sha256(getattr(a, key).read_bytes()).hexdigest() == digest
spec = importlib.util.spec_from_file_location("frozen_policy", a.validator)
policy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(policy)
ledger = policy.read_json(a.root / "docs/provenance/openai-math.d/typicalBellPinPowers8753.json")
schema = policy.read_json(a.schema)
count = policy.validate([ledger], schema, {"LionSR/QICLean": a.root}, scan=False)
source = (a.root / "QICLean/Entropy/TypicalBellPinPowers.lean").read_text()
code, blocks = policy.lean_parts(source)
lines = code.splitlines()
# The frozen conservative index includes private commands; they have no public provenance rows.
public = {name for name, line in policy.declarations(source).items()
          if not re.match(r"\s*private\b", lines[line - 1])}
expected_names = {entry["downstream"]["declaration"] for entry in ledger["entries"]}
assert public == expected_names, (public, expected_names)
assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafeCast)\b", code)
ids = [identifier for block in blocks for identifier in policy.ID_RE.findall(block)]
assert sorted(ids) == sorted(entry["id"] for entry in ledger["entries"])
for entry in ledger["entries"]:
    policy.notice_block(source, entry)
print(f"Owned shard valid: {count} public declarations, no new public definitions.")
print("Frozen entire source bytes, exact names, original notices, logs and standard kernel axioms validated.")
print("Comment-aware source audit: no sorry, admit, axiom, native_decide or unsafeCast.")
print("Policy: TNLean@806099b4dddcce591b3a62ee1921926a6af5ad55. Inherited shards not re-audited.")
