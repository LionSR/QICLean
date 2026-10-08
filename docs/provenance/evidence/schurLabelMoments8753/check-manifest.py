"""Verify canonical source, historical records and exact three-name checks."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--index',action='store_true');p.add_argument('--git',action='store_true');a=p.parse_args();e=Path(__file__).resolve().parent;root=e.parents[3];sha=lambda d:hashlib.sha256(d).hexdigest()
files=json.loads((e/'evidence-sha256.json').read_text())['files']
for row in files:
 d=(root/row['path']).read_bytes();assert sha(d)==row['sha256'],row['path']
 if a.index:assert d==subprocess.check_output(['git','show',':'+row['path']],cwd=root),row['path']
 if a.git:assert d==subprocess.check_output(['git','show','HEAD:'+row['path']],cwd=root),row['path']
f=json.loads((e/'source-freeze.json').read_text())
for row in f['files']:
 d=(root/row['path']).read_bytes();assert sha(d)==row['sha256'];assert d==subprocess.check_output(['git','show',f['source_revision']+':'+row['path']],cwd=root)
for path in e.glob('*-exit.json'):
 rec=json.loads(path.read_text());assert sha((root/rec['log']).read_bytes())==rec['sha256'];assert rec['source_revision']==f['source_revision'];assert rec['exit_code']==0,path.name
reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(e/'bound-axioms.log').read_text(),re.S);names=json.loads((e/'public-declarations.json').read_text())['new'];assert [n for n,_ in reports]==names
for n,axs in reports:assert [x.strip() for x in axs.split(',')]==['propext','Classical.choice','Quot.sound'],n
ledger=json.loads((root/'docs/provenance/openai-math.d/schurLabelMoments8753.json').read_text());assert len(ledger['entries'])==3
for i,entry in enumerate(ledger['entries'],1):
 assert entry['id']==f'8753-qic-schur-label-moments-{i:02}';assert entry['verification']['revision']==f['source_revision'];assert entry['downstream']['declaration']==names[i-1]
 for cmd in entry['verification']['commands']:assert cmd['exit_code']==0 and sha((root/cmd['log']).read_bytes())==cmd['sha256']
subprocess.run(['python3',str(e/'compare-source.py')],cwd=root,check=True)
print('Verified',len(files),'portable bindings, frozen four-file source, original 22 historical records, three original IDs and three fresh standard-only reports.')
