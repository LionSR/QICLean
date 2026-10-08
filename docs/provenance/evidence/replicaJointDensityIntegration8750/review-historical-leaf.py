"""Verify the immutable mathematical leaf and the authorized exposition child."""
from pathlib import Path
import hashlib,json,subprocess
r=Path.cwd();p=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
leaf=r/'docs/provenance/evidence/replicaJointDensity8750';m=json.loads((leaf/'verification.json').read_text());freeze=json.loads((leaf/'source-freeze.json').read_text());e=json.loads((p/'exposition-freeze.json').read_text())
for n,h in m['file_hashes'].items():
 if n==e['path']:assert sha(subprocess.check_output(['git','show',freeze['source_revision']+':'+n]))==h,n
 else:assert sha((r/n).read_bytes())==h,n
for n,h in freeze['production_sha256'].items():
 old=subprocess.check_output(['git','show',freeze['source_revision']+':'+n]);assert sha(old)==h,n
 if n!=e['path']:assert (r/n).read_bytes()==old,n
assert sha((r/e['path']).read_bytes())==e['sha256']
assert (r/e['path']).read_bytes()==subprocess.check_output(['git','show',e['revision']+':'+e['path']])
print('All',len(m['file_hashes']),'historical leaf hashes verified; unchanged mathematical source and three frozen files; one authorized typesetting-only fragment child.')
