"""Check exact proof bytes and the immutable integration source tree."""
from pathlib import Path
import hashlib,json,subprocess
r=Path.cwd();p=Path(__file__).resolve().parent
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
j=json.loads((p/'parent-compatibility.json').read_text())
for key in ['incoming_changed_production_sha256','main_existing_production_sha256','identical_toolchain_configuration_and_dependencies_sha256']:
 for n,h in j[key].items():assert sha(r/n)==h,n
f=json.loads((p/'source-freeze.json').read_text())
for n,h in f['sha256'].items():
 assert sha(r/n)==h,n
 assert (r/n).read_bytes()==subprocess.check_output(['git','show',f"{f['source_revision']}:{n}"])
print('Exact incoming',len(j['incoming_changed_production_sha256']),'and current-main',len(j['main_existing_production_sha256']),'production files preserved; all',len(f['sha256']),'frozen integration files preserved.')
