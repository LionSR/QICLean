from pathlib import Path
import re
s=Path('QICLean/Analysis/ReplicaGoodPhysicalSupport.lean').read_text()
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafeCast|unsafeCoerce)\b',s)
assert len(re.findall(r'^theorem ',s,re.M))==1
print('No proof-integrity hazards; exactly one public theorem and no new definitions.')
