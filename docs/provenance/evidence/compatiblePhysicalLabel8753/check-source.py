"""Check the immutable comparator source and the absence of proof placeholders."""
from pathlib import Path
import hashlib
import json
import re
source = Path("/Users/siruilu/Local/agentFormalization/TNLean/Scratch/openai-area-law-sources/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/07-comparators.tex")
expected = "5c8d8dd55a283a7ffe9573067c631ea70d93b01c207a297aee02352c25d2573b"
actual = hashlib.sha256(source.read_bytes()).hexdigest()
assert actual == expected
lean = Path("QICLean/Representation/CompatiblePhysicalLabel.lean").read_text()
assert not re.search(r"\b(?:sorry|admit|native_decide|unsafeCast)\b", lean)
assert not re.search(r"^\s*(?:unsafe\s+)?axiom\s", lean, re.M)
public = re.findall(r"^(?:noncomputable def|theorem) (\w+)", lean, re.M)
assert len(public) == 5
print(json.dumps({"manuscript_commit": "adc7f1241b42e322a6451854ab7e4b4c146bf78a", "comparator_sha256": actual, "supporting_lines": [501, 522], "public_declarations": public, "proof_placeholders": []}))
