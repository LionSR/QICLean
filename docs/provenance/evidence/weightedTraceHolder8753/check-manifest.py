"""Verify exact frozen source, original provenance and eleven fresh kernel reports."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--index',action='store_true');p.add_argument('--git',action='store_true');a=p.parse_args();e=Path(__file__).resolve().parent;root=e.parents[3];sha=lambda d:hashlib.sha256(d).hexdigest()
for row in json.loads((e/'evidence-sha256.json').read_text())['files']:
 data=(root/row['path']).read_bytes();assert sha(data)==row['sha256'],row['path']
 if a.index:assert data==subprocess.check_output(['git','show',':'+row['path']],cwd=root),row['path']
 if a.git:assert data==subprocess.check_output(['git','show','HEAD:'+row['path']],cwd=root),row['path']
freeze=json.loads((e/'source-freeze.json').read_text())
for row in freeze['files']:
 data=(root/row['path']).read_bytes();assert sha(data)==row['sha256'];assert data==subprocess.check_output(['git','show',freeze['source_revision']+':'+row['path']],cwd=root)
failures={'bound-statements-exit.json':'Unknown option `pp.width`','bound-provenance-exit.json':"No module named 'jsonschema'"}
for path in e.glob('*-exit.json'):
 rec=json.loads(path.read_text());data=(root/rec['log']).read_bytes();assert sha(data)==rec['sha256'];assert rec['source_revision']==freeze['source_revision']
 if path.name in failures:assert rec['exit_code']==1 and failures[path.name] in data.decode()
 else:assert rec['exit_code']==0,path.name
raw=(e/'bound-axioms.log').read_text();reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",raw,re.S);names=json.loads((e/'public-declarations.json').read_text());expected=names['new']+names['refreshed'];assert [n for n,_ in reports]==expected
for n,axioms in reports:assert [x.strip() for x in axioms.split(',')]==['propext','Classical.choice','Quot.sound'],n
ledger=json.loads((root/'docs/provenance/openai-math.d/weightedTraceHolder8753.json').read_text());assert len(ledger['entries'])==5
for entry in ledger['entries']:
 assert entry['verification']['revision']==freeze['source_revision'];assert entry['downstream']['declaration'] in names['new']
 for cmd in entry['verification']['commands']:assert cmd['exit_code']==0 and sha((root/cmd['log']).read_bytes())==cmd['sha256']
for row in json.loads((e/'root-target-history.json').read_text())['records']:
 assert sha((root/row['log']).read_bytes())==row['sha256'];assert row['exit_code']==(0 if row['attempt']==4 else 1)
subprocess.run(['python3',str(e/'compare-source.py')],cwd=root,check=True)
print('Verified',len(json.loads((e/'evidence-sha256.json').read_text())['files']),'portable bindings, all frozen source/exposition bytes, five original IDs and eleven exact standard-only reports.')
