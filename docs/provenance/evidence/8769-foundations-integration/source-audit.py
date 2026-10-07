"""Re-audit the 139 declarations in the foundations packet after main integration."""
import importlib.util
import json
from pathlib import Path
import re
import sys
spec = importlib.util.spec_from_file_location("policy", Path(sys.argv[1]))
policy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(policy)
root = Path.cwd()
shards = ["8769-gaussian.json", "8769-sampling.json", "8769-second-moment.json", "8769-weighted.json"]
entries = [e for name in shards for e in json.loads((root / "docs/provenance/openai-math.d" / name).read_text())["entries"]]
registered = {e["downstream"]["declaration"] for e in entries}
files = sorted({e["downstream"]["path"] for e in entries})
public = set()
for file in files:
    text = (root / file).read_text()
    code, blocks = policy.lean_parts(text)
    assert not re.search(r"\b(sorry|admit|unsafeCast|native_decide|axiom)\b", code), file
    notices = {ident for block in blocks for ident in policy.ID_RE.findall(block)}
    owned = [e for e in entries if e["downstream"]["path"] == file]
    assert notices == {e["id"] for e in owned}, file
    for e in owned:
        policy.notice_block(text, e)
    for name, line in policy.declarations(text).items():
        if not re.search(r"\bprivate\b", code.splitlines()[line - 1]):
            public.add(name)
    print("PASS owned source and notice coverage:", file)
assert public == registered
output = (root / "docs/provenance/evidence/8769-foundations-integration/axioms.log").read_text()
for name in sorted(registered):
    policy.check_axiom_output(output, name)
print("PASS scoped public coverage and compiled kernel reports:", len(public), "declarations in", len(files), "modules")
print("PASS classifications:", sum(e["reuse_kind"] == "adapted" for e in entries), "adapted;", sum(e["reuse_kind"] == "original" for e in entries), "original")
print("Scope: foundations packet only; unrelated issue 8742 notice gaps are tracked separately.")
