"""Check the owned source for proof-integrity hazards and public export count."""
from pathlib import Path
import re
s=Path('QICLean/Analysis/ReplicaJointDensity.lean').read_text()
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafeCast|unsafeCoerce)\b',s)
assert len(re.findall(r'^noncomputable def |^theorem ',s,re.M))==2
print('No proof-integrity hazards; exactly two public exports.')
