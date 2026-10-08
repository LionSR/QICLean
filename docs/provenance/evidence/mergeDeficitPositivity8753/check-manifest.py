"""Verify frozen merge-positivity sources and retained command evidence."""
from pathlib import Path
import argparse,gzip,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--git',action='store_true');args=p.parse_args()
r=Path.cwd();e=Path(__file__).resolve().parent;m=json.loads((e/'manifest.json').read_text());f=json.loads((e/'source-freeze.json').read_text());v=json.loads((e/'verification.json').read_text())
for name,digest in m['files'].items():
 b=(r/name).read_bytes();assert hashlib.sha256(b).hexdigest()==digest,name
 if args.git:assert subprocess.check_output(['git','show','HEAD:'+name])==b,name
for name,digest in f['production_sha256'].items():
 assert hashlib.sha256(subprocess.check_output(['git','show',f['source_revision']+':'+name])).hexdigest()==digest,name
for c in v['successful_checks']+v['retained_metadata_failures']:
 b=(r/c['log']).read_bytes();assert hashlib.sha256(b).hexdigest()==c['sha256'];assert gzip.decompress((r/(c['log']+'.gz')).read_bytes())==b
assert all(c['exit_code']==0 for c in v['successful_checks']);assert len(v['retained_metadata_failures'])==1 and v['retained_metadata_failures'][0]['exit_code']==1
for log,count in [('axioms.log',4),('parent-axioms.log',8)]:
 reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",(e/log).read_text());assert len(reports)==count
 for _,xs in reports:assert set(x.strip() for x in xs.split(','))=={'propext','Classical.choice','Quot.sound'}
print(f"Verified {len(m['files'])} portable bindings, four new and eight unchanged standard kernel reports.")
