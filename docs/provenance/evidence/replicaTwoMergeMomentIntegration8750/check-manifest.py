"""Check exact proof bytes, recorded commands, inherited evidence and portable files."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess
p=argparse.ArgumentParser();p.add_argument('--index',action='store_true');p.add_argument('--git',action='store_true');args=p.parse_args()
e=Path(__file__).resolve().parent;root=e.parents[3]
sha=lambda data:hashlib.sha256(data).hexdigest()
inventory=json.loads((e/'evidence-sha256.json').read_text())
for row in inventory['files']:
 data=(root/row['path']).read_bytes();assert sha(data)==row['sha256'],row['path']
 if args.index:assert subprocess.check_output(['git','show',':'+row['path']],cwd=root)==data,row['path']
 if args.git:assert subprocess.check_output(['git','show','HEAD:'+row['path']],cwd=root)==data,row['path']
freeze=json.loads((e/'source-freeze.json').read_text())
for row in freeze['files']:
 data=(root/row['path']).read_bytes();assert sha(data)==row['sha256'],row['path']
 assert data==subprocess.check_output(['git','show',freeze['source_revision']+':'+row['path']],cwd=root),row['path']
compressed={row['raw_path']:row for row in json.loads((e/'compressed-logs.json').read_text())['files']}
for path in e.glob('*-exit.json'):
 record=json.loads(path.read_text())
 if path.name=='provenance-helper-invocation-exit.json':
  assert record['exit_code']==1 and 'IndexError' in (root/record['log']).read_text()
 elif path.name=='manifest-index-preliminary-exit.json':
  assert record['exit_code']==1 and 'not in the index' in (root/record['log']).read_text()
 else:assert record['exit_code']==0,path.name
 assert record['source_revision']==freeze['source_revision'],path.name
 log=root/record['log']
 data=log.read_bytes() if log.exists() else gzip.decompress((root/compressed[record['log']]['archive_path']).read_bytes())
 assert sha(data)==record['sha256'],path.name
for row in compressed.values():
 archive=(root/row['archive_path']).read_bytes();assert sha(archive)==row['archive_sha256']
 raw=gzip.decompress(archive);assert sha(raw)==row['raw_sha256'];assert gzip.compress(raw,mtime=0)==archive
raw=(e/'axioms-final.log').read_text()
assert raw=="'Matrix.replicaGoodPairMarginal_exp_sum_mergeDeficit_le' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
for path in json.loads((e/'owned-shards.json').read_text()):
 ledger=json.loads((root/'docs/provenance/openai-math.d'/path).read_text())
 assert len(ledger['entries'])==1
 for entry in ledger['entries']:
  for command in entry['verification']['commands']:
   assert command['exit_code']==0 and sha((root/command['log']).read_bytes())==command['sha256'],command['log']
for row in json.loads((e/'individual-source-preservation.json').read_text())['records']:
 assert sha((root/row['path']).read_bytes())==row['sha256'],row['path']
old=freeze['preserved_published_branch'];assert subprocess.check_output(['git','rev-parse',old['branch']],cwd=root,text=True).strip()==old['revision']
subprocess.run(['python3',str(e/'check-inherited.py')],cwd=root,check=True)
for row in json.loads((e/'generated-output-hashes.json').read_text())['files']:
 assert sha((root/row['path']).read_bytes())==row['sha256'],row['path']
visual=json.loads((e/'pdf-visual-inspection.json').read_text());assert visual['all_pages_inspected'] and visual['physical_pages']
assert json.loads((e/'web-visual-inspection.json').read_text())['all_images_inspected']
print('Verified',len(inventory['files']),'portable bindings, exact source and inherited bytes, sole original provenance/kernel binding and complete PDF/web inspections.')
