"""Verify the portable records, immutable proof bytes and original command hashes."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess
p=argparse.ArgumentParser();p.add_argument('--index',action='store_true');p.add_argument('--git',action='store_true');args=p.parse_args()
e=Path(__file__).resolve().parent;root=e.parents[3]
sha=lambda data:hashlib.sha256(data).hexdigest()
inventory=json.loads((e/'evidence-sha256.json').read_text())
for row in inventory['files']:
 path=root/row['path'];data=path.read_bytes();assert sha(data)==row['sha256'],row['path']
 if args.index:assert subprocess.check_output(['git','show',':'+row['path']],cwd=root)==data,row['path']
 if args.git:assert subprocess.check_output(['git','show','HEAD:'+row['path']],cwd=root)==data,row['path']
freeze=json.loads((e/'source-freeze.json').read_text())
for row in freeze['files']:
 data=(root/row['path']).read_bytes();assert sha(data)==row['sha256'],row['path']
 assert data==subprocess.check_output(['git','show',freeze['source_revision']+':'+row['path']],cwd=root),row['path']
compressed={row['raw_path']:row for row in json.loads((e/'compressed-logs.json').read_text())['files']}
for path in e.glob('*-exit.json'):
 record=json.loads(path.read_text());assert record['exit_code']==0,path.name;log=root/record['log']
 data=log.read_bytes() if log.exists() else gzip.decompress((root/compressed[record['log']]['archive_path']).read_bytes())
 assert sha(data)==record['sha256'],path.name
for row in compressed.values():
 archive=(root/row['archive_path']).read_bytes();assert sha(archive)==row['archive_sha256'];raw=gzip.decompress(archive);assert sha(raw)==row['raw_sha256'];assert gzip.compress(raw,mtime=0)==archive
for path in json.loads((e/'owned-shards.json').read_text()):
 ledger=json.loads((root/'docs/provenance/openai-math.d'/path).read_text())
 for entry in ledger['entries']:
  for command in entry['verification']['commands']:
   assert sha((root/command['log']).read_bytes())==command['sha256'],command['log']
for name,key in [('inherited-byte-preservation.json','sha256'),('production-preservation.json','sha256'),('blueprint-source-preservation.json','current_sha256')]:
 for row in json.loads((e/name).read_text())['records']:
  assert sha((root/row['path']).read_bytes())==row[key],row['path']
for row in json.loads((e/'preexisting-output-preservation.json').read_text())['files']:
 assert sha((root/row['path']).read_bytes())==row['sha256'],row['path']
old=freeze['preserved_published_branch'];assert subprocess.check_output(['git','rev-parse',old['branch']],cwd=root,text=True).strip()==old['revision']
correction=json.loads((e/'fragment-citation-correction.json').read_text())
before=subprocess.check_output(['git','show',correction['initial_source_revision']+':'+correction['path']],cwd=root)
after=(root/correction['path']).read_bytes()
assert before.replace(b'{Ope26b}',b'{OpenAI2026AreaLaw}')==after
for row in json.loads((e/'individual-source-preservation.json').read_text())['files']:
 assert sha((root/row['path']).read_bytes())==row['sha256']
print('Verified',len(inventory['files']),'portable files, exact frozen source bytes, all original command hashes, the original one-entry provenance shard and deterministic PDF-log compression.')
