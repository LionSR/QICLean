"""Verify the immutable marginal leaf and portable evidence bindings."""
from pathlib import Path
import argparse,hashlib,json,subprocess
p=argparse.ArgumentParser();p.add_argument('--index',action='store_true');p.add_argument('--git',action='store_true');args=p.parse_args()
e=Path(__file__).resolve().parent;root=e.parents[3]
sha=lambda data:hashlib.sha256(data).hexdigest()
rows=json.loads((e/'evidence-sha256.json').read_text())['files']
for row in rows:
 data=(root/row['path']).read_bytes();assert sha(data)==row['sha256'],row['path']
 if args.index:assert subprocess.check_output(['git','show',':'+row['path']],cwd=root)==data
 if args.git:assert subprocess.check_output(['git','show','HEAD:'+row['path']],cwd=root)==data
freeze=json.loads((e/'source-freeze.json').read_text())
for row in freeze['files']:
 data=(root/row['path']).read_bytes();assert sha(data)==row['sha256'],row['path']
 assert data==subprocess.check_output(['git','show',freeze['source_revision']+':'+row['path']],cwd=root)
for p in e.glob('*-exit.json'):
 r=json.loads(p.read_text());assert r['exit_code']==0 or p.name in {'draft-strict-exit.json','axioms-exit.json','statements-exit.json','tactic-patterns-exit.json','provenance-exit.json'};assert sha((root/r['log']).read_bytes())==r['sha256']
for shard in json.loads((e/'owned-shards.json').read_text()):
 for entry in json.loads((root/'docs/provenance/openai-math.d'/shard).read_text())['entries']:
  assert entry['verification']['revision']==freeze['source_revision']
  for command in entry['verification']['commands']:
   assert sha((root/command['log']).read_bytes())==command['sha256']
assert subprocess.check_output(['git','rev-parse',freeze['preserved_published_branch']['branch']],cwd=root,text=True).strip()==freeze['preserved_published_branch']['revision']
for row in json.loads((e/'preexisting-output-preservation.json').read_text())['files']:
 assert sha((root/row['path']).read_bytes())==row['sha256']
for name in ['inherited-byte-preservation.json','production-preservation.json']:
 for row in json.loads((e/name).read_text())['records']:
  assert sha((root/row['path']).read_bytes())==row['sha256'],row['path']
correction=json.loads((e/'source-citation-correction.json').read_text())
before=subprocess.check_output(['git','show',correction['from_revision']+':'+correction['path']],cwd=root)
after=(root/correction['path']).read_bytes()
assert before.replace(b'comparator rough estimate',b'comparator:component-inverse')==after
print('Verified',len(rows),'portable files, entire frozen source and the original provenance/kernel binding.')
