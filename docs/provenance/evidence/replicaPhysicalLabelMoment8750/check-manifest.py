"""Verify the source-bound original physical-moment evidence and exact parent tree."""
from pathlib import Path
import argparse,json,hashlib,subprocess
p=argparse.ArgumentParser();p.add_argument('--git',action='store_true');p.add_argument('--index',action='store_true');args=p.parse_args()
e=Path(__file__).resolve().parent;root=e.parents[3];sha=lambda data:hashlib.sha256(data).hexdigest()
rows=json.loads((e/'evidence-sha256.json').read_text())['files']
for r in rows:
 data=(root/r['path']).read_bytes();assert sha(data)==r['sha256'],r['path']
 if args.git:assert subprocess.check_output(['git','show','HEAD:'+r['path']],cwd=root)==data,r['path']
 if args.index:assert subprocess.check_output(['git','show',':'+r['path']],cwd=root)==data,r['path']
f=json.loads((e/'source-freeze.json').read_text())
for r in f['files']:
 data=(root/r['path']).read_bytes();assert sha(data)==r['sha256'],r['path']
 assert subprocess.check_output(['git','show',f['source_revision']+':'+r['path']],cwd=root)==data,r['path']
for p in e.glob('bound-*-exit.json'):
 r=json.loads(p.read_text());assert r['source_revision']==f['source_revision'] and r['exit_code']==0,p.name
 assert sha((root/r['log']).read_bytes())==r['sha256'],p.name
for p in e.glob('audit-wrapper-*-exit.json'):
 r=json.loads(p.read_text());assert r['exit_code']==1 and 'module doc-string' in (root/r['log']).read_text()
 assert sha((root/r['log']).read_bytes())==r['sha256']
for name in json.loads((e/'owned-shards.json').read_text()):
 entries=json.loads((root/'docs/provenance/openai-math.d'/name).read_text())['entries'];assert len(entries)==1
 for entry in entries:
  assert entry['verification']['revision']==f['source_revision']
  for c in entry['verification']['commands']:assert c['exit_code']==0 and sha((root/c['log']).read_bytes())==c['sha256']
assert (e/'bound-axioms.log').read_text()=="'Matrix.trace_exp_labelEntropy_replicaExcitationComponent_eq' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
subprocess.run(['python3',str(e/'check-preservation.py')],cwd=root,check=True)
print('Verified',len(rows),'portable bindings, exact source freeze, sole standard-only report and original provenance binding.')
