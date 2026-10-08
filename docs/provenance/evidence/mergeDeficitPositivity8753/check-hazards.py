"""Check the four new declarations and exclude proof-integrity hazards."""
from pathlib import Path
import json,re
r=Path.cwd();e=Path(__file__).resolve().parent;f=json.loads((e/'source-freeze.json').read_text())
for p in f['production_sha256']:
 if p.endswith('.lean'): assert not re.search(r'\b(sorry|admit|native_decide|unsafeCast|axiom)\b',(r/p).read_text()),p
for name in ['posSemidef_mergeDeficit','posSemidef_pairMergeDeficit','PosSemidef.spectralProjectionGE_zero','spectralProjectionGE_zero_mul_of_intertwine']:
 assert sum(len(re.findall(r'\btheorem\s+'+re.escape(name)+r'\b',(r/p).read_text())) for p in f['production_sha256'] if p.endswith('.lean'))==1,name
print('No proof-integrity hazards; exactly four owned declarations.')
