"""Check frozen source, eleven refreshed reports, original provenance and complete book artifacts."""
from pathlib import Path
import argparse,gzip,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--index',action='store_true');p.add_argument('--git',action='store_true');args=p.parse_args();e=Path(__file__).resolve().parent;root=e.parents[3];sha=lambda d:hashlib.sha256(d).hexdigest()
inv=json.loads((e/'evidence-sha256.json').read_text())
for row in inv['files']:
 data=(root/row['path']).read_bytes();assert sha(data)==row['sha256'],row['path']
 if args.index:assert data==subprocess.check_output(['git','show',':'+row['path']],cwd=root),row['path']
 if args.git:assert data==subprocess.check_output(['git','show','HEAD:'+row['path']],cwd=root),row['path']
f=json.loads((e/'source-freeze.json').read_text());compressed={r['raw_path']:r for r in json.loads((e/'compressed-logs.json').read_text())['files']}
for path in e.glob('*-exit.json'):
 rec=json.loads(path.read_text());assert rec['exit_code']==0,path.name;assert rec['source_revision']==f['source_revision'];log=root/rec['log'];data=log.read_bytes() if log.exists() else gzip.decompress((root/compressed[rec['log']]['archive_path']).read_bytes());assert sha(data)==rec['sha256'],path.name
for row in compressed.values():
 archive=(root/row['archive_path']).read_bytes();assert sha(archive)==row['archive_sha256'];raw=gzip.decompress(archive);assert sha(raw)==row['raw_sha256'];assert gzip.compress(raw,mtime=0)==archive
raw=(e/'axioms-final.log').read_bytes();assert raw==(root/'docs/provenance/evidence/weightedTraceHolder8753/bound-axioms.log').read_bytes()
names=json.loads((root/'docs/provenance/evidence/weightedTraceHolder8753/public-declarations.json').read_text());reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",raw.decode(),re.S);assert [n for n,_ in reports]==names['new']+names['refreshed']
for n,axioms in reports:assert [s.strip() for s in axioms.split(',')]==['propext','Classical.choice','Quot.sound'],n
subprocess.run(['python3',str(e/'check-preservation.py')],cwd=root,check=True)
for row in json.loads((e/'generated-output-hashes.json').read_text())['files']:assert sha((root/row['path']).read_bytes())==row['sha256'],row['path']
pdf=json.loads((e/'pdf-visual-inspection.json').read_text());web=json.loads((e/'web-visual-inspection.json').read_text());assert pdf['all_pages_inspected'] and pdf['physical_pages']==[459,460];assert web['all_images_inspected']
for row in pdf['images']+web['images']:assert sha((root/row['path']).read_bytes())==row['sha256']
print('Verified',len(inv['files']),'portable bindings, exact original leaf/source, five owned IDs and eleven standard-only refreshed kernel reports, plus complete PDF/web inspections.')
