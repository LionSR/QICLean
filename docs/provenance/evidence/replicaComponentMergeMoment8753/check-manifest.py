"""Independently check the component-moment source and retained evidence."""
from pathlib import Path
import argparse,hashlib,json,subprocess,re
p=argparse.ArgumentParser();p.add_argument('--git',action='store_true');a=p.parse_args()
r=Path.cwd();e=Path(__file__).resolve().parent;m=json.loads((e/'manifest.json').read_text());f=json.loads((e/'source-freeze.json').read_text())
for name,digest in m['files'].items():
 b=(r/name).read_bytes();assert hashlib.sha256(b).hexdigest()==digest,name
 if a.git:
  tracked=subprocess.check_output(['git','show','HEAD:'+name]);assert b==tracked,name
for name,digest in f['production_sha256'].items():
 b=subprocess.check_output(['git','show',f['source_revision']+':'+name]);assert hashlib.sha256(b).hexdigest()==digest,name
v=json.loads((e/'verification.json').read_text())
for c in v['successful_checks']:
 assert c['exit_code']==0
 assert hashlib.sha256((r/c['log']).read_bytes()).hexdigest()==c['sha256']
t=(e/'axioms-corrected.log').read_text();matches=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",t)
assert len(matches)==1 and matches[0][0]=='Matrix.replicaGoodRegionalAuxiliaryMarginal_exp_mergeDeficit_le'
assert set(x.strip() for x in matches[0][1].split(','))=={'propext','Classical.choice','Quot.sound'}
assert len(v['retained_failed_preparations'])==2
print(f"Verified {len(m['files'])} source/evidence bindings and the exact imported standard kernel report.")
