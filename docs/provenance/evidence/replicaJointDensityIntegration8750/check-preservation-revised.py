"""Verify exact mathematical inclusion with its authorized exposition child."""
from pathlib import Path
import hashlib,io,json,subprocess,tarfile
r=Path.cwd();p=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
m=json.loads((p/'parent-preservation.json').read_text());e=json.loads((p/'exposition-freeze.json').read_text())
with tarfile.open(fileobj=io.BytesIO(subprocess.check_output(['git','archive',m['parent_revision']]))) as t:
 for n,h in m['sha256'].items():
  old=t.extractfile(n).read();now=(r/n).read_bytes();assert sha(old)==h,n
  if n==e['path']:assert sha(now)==e['sha256'] and now==subprocess.check_output(['git','show',e['revision']+':'+n]),n;continue
  if n=='QICLean/Analysis.lean':addition=b'import QICLean.Analysis.ReplicaJointDensity\n'
  elif n=='blueprint/src/chapter/ch12_entropy.tex':addition=b'\\input{fragment/replica_joint_density}\n'
  else:assert now==old,n;continue
  assert now.count(addition)==1 and now.replace(addition,b'')==old,n
print(len(m['sha256']),'parent files unchanged except the exact two inclusion lines and authorized typesetting-only fragment child.')
