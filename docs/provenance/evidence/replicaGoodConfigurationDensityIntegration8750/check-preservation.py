"""Check all leaf-parent files and the two exact inclusion additions."""
from pathlib import Path
import json,hashlib,subprocess,io,tarfile
r=Path.cwd();p=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
f=json.loads((p/'source-freeze.json').read_text())
for n,h in {**f['production_sha256'],**f['inclusion_sha256']}.items():assert sha((r/n).read_bytes())==h,n
m=json.loads((p/'parent-preservation.json').read_text())
with tarfile.open(fileobj=io.BytesIO(subprocess.check_output(['git','archive',m['parent_revision']]))) as t:
 for n,h in m['sha256'].items():
  original=t.extractfile(n).read();assert sha(original)==h,n
  if n in m['allowed_inclusion_lines']:
   line=m['allowed_inclusion_lines'][n].encode();current=(r/n).read_bytes()
   assert current.count(line)==1 and current.replace(line,b'')==original,n
  else:assert sha((r/n).read_bytes())==h,n
print('All',len(m['sha256']),'leaf-parent files preserved with only the two exact inclusion lines.')
