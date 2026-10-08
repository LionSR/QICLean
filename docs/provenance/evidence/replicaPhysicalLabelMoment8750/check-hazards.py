from pathlib import Path
import re
s=Path('QICLean/Analysis/ReplicaPhysicalLabelMoment.lean').read_text()
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafeCast)\b',s)
assert re.findall(r'^theorem (\w+)',s,re.M)==['trace_exp_labelEntropy_replicaExcitationComponent_eq']
print('No proof-integrity hazard; exactly one public theorem.')
