"""Audit this packet with the separately pinned TNLean provenance parser."""

import importlib.util
import json
from pathlib import Path
import re
import sys

policy_path = Path(sys.argv[1])
spec = importlib.util.spec_from_file_location("policy", policy_path)
policy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(policy)
root = Path.cwd()
entries = [
    entry
    for shard in [root / "docs/provenance/openai-math.d" / ("8769-" + name + ".json")
                  for name in ["contraction-chain", "subnormalized-pure", "product-transport", "source-only-density"]]
    for entry in json.loads(shard.read_text())["entries"]
]
registered = {entry["downstream"]["declaration"] for entry in entries}
files = sorted({entry["downstream"]["path"] for entry in entries})
public = set()
for file in files:
    code, _ = policy.lean_parts((root / file).read_text())
    assert not re.search(r"\b(sorry|admit|unsafeCast|native_decide|axiom)\b", code), file
    declarations = policy.declarations((root / file).read_text())
    for name, line in declarations.items():
        if not re.search(r"\bprivate\b", code.splitlines()[line - 1]):
            public.add(name)
    print("PASS no proof placeholders/custom axioms:", file)
assert public == registered, (sorted(public - registered), sorted(registered - public))
output = (root / "docs/provenance/evidence/8769-source-reduction/axioms.log").read_text()
for name in sorted(registered):
    policy.check_axiom_output(output, name)
print("PASS complete public-source mapping:", len(public), "declarations in", len(files), "modules.")
print("PASS compiled kernel reports: only propext, Classical.choice, Quot.sound or no axioms.")
print("PASS adapted/original classifications:",
      sum(entry["reuse_kind"] == "adapted" for entry in entries), "adapted;",
      sum(entry["reuse_kind"] == "original" for entry in entries), "original.")
