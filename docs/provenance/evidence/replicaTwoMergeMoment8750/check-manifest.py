from pathlib import Path
import argparse,json,hashlib,subprocess,gzip
p=argparse.ArgumentParser();p.add_argument('--git',action='store_true');p.add_argument('--index',action='store_true');a=p.parse_args()
e=Path(__file__).resolve().parent;root=e.parents[3]
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=json.loads((e/'evidence-sha256.json').read_text())['files']
for row in rows:
 data=(root/row['path']).read_bytes();assert sha(data)==row['sha256'],row['path']
 if a.git:assert subprocess.check_output(['git','show','HEAD:'+row['path']],cwd=root)==data,row['path']
 if a.index:assert subprocess.check_output(['git','show',':'+row['path']],cwd=root)==data,row['path']
f=json.loads((e/'source-freeze.json').read_text())
for row in f['files']:
 data=(root/row['path']).read_bytes();assert sha(data)==row['sha256'],row['path']
 assert subprocess.check_output(['git','show',f['source_revision']+':'+row['path']],cwd=root)==data,row['path']
for record in e.glob('bound-*-exit.json'):
 r=json.loads(record.read_text());assert r['exit_code']==0,record.name
 assert r['source_revision']==f['source_revision'];assert sha((root/r['log']).read_bytes())==r['sha256']
for name in json.loads((e/'owned-shards.json').read_text()):
 for entry in json.loads((root/'docs/provenance/openai-math.d'/name).read_text())['entries']:
  assert entry['verification']['revision']==f['source_revision']
  for c in entry['verification']['commands']:
   assert c['exit_code']==0 and sha((root/c['log']).read_bytes())==c['sha256']
raw=(e/'bound-axioms.log').read_text()
assert raw=="'Matrix.replicaGoodPairMarginal_exp_sum_mergeDeficit_le' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
for name in ['replica-two-merge-production-prefreeze-exit.json','replica-two-merge-production-prefreeze-retry-exit.json']:
 r=json.loads((e/name).read_text());assert r['exit_code']==1
 assert sha((e/'replica-two-merge-docstring-placement.lean.txt').read_bytes())==r['unfrozen_source_sha256']
 assert 'unexpected token' in (e/Path(r['log']).name).read_text()
for row in json.loads((e/'compressed-inventories.json').read_text())['files']:
 data=(root/row['compressed_path']).read_bytes();assert sha(data)==row['compressed_sha256']
 assert sha(gzip.decompress(data))==row['uncompressed_sha256']
branch=f['preserved_published_branch'];assert subprocess.check_output(['git','rev-parse',branch['branch']],cwd=root,text=True).strip()==branch['revision']
subprocess.run(['python3',str(e/'check-preservation.py')],cwd=root,check=True)
print('Verified',len(rows),'portable bindings, exact source freeze and sole original kernel/provenance binding.')
