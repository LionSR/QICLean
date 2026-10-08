from pathlib import Path
import re
s=Path('QICLean/Analysis/ReplicaTwoMergeMoment.lean').read_text()
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafeCast)\b',s)
assert re.findall(r'^theorem (\w+)',s,re.M)==['replicaGoodPairMarginal_exp_sum_mergeDeficit_le']
print('No proof-integrity hazard; exactly one public theorem.')
