"""Check literal parent files and the four current frozen files."""
from pathlib import Path
import hashlib,io,json,subprocess,tarfile
r=Path.cwd();p=Path(__file__).resolve().parent
f=json.loads((p/'source-freeze.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
for n,h in f['production_sha256'].items():assert sha((r/n).read_bytes())==h and (r/n).read_bytes()==subprocess.check_output(['git','show',f['source_revision']+':'+n]),n
parent=json.loads((p/'parent-preservation.json').read_text())
with tarfile.open(fileobj=io.BytesIO(subprocess.check_output(['git','archive',parent['parent_revision']]))) as t:
 for n,h in parent['sha256'].items():
  original=t.extractfile(n).read();assert sha(original)==h,n
  if n==parent['cumulative_ledger_exception']:assert (r/n).read_bytes().startswith(original) and sha((r/n).read_bytes())==parent['new_ledger_sha256'],n
  else:assert sha((r/n).read_bytes())==h,n
print('Four frozen files and',len(parent['sha256']),'parent files preserved; only the recorded cumulative ledger append differs.')
