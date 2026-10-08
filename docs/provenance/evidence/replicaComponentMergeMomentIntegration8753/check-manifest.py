"""Check the retained sources, successful commands, and exact kernel report."""
from pathlib import Path
import argparse,gzip,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--git',action='store_true');args=p.parse_args()
r=Path.cwd();e=Path(__file__).resolve().parent
m=json.loads((e/'manifest.json').read_text());f=json.loads((e/'source-freeze.json').read_text());v=json.loads((e/'verification.json').read_text())
for name,digest in m['files'].items():
 b=(r/name).read_bytes();assert hashlib.sha256(b).hexdigest()==digest,name
 if args.git: assert subprocess.check_output(['git','show','HEAD:'+name])==b,name
for name,digest in f['production_sha256'].items():
 b=subprocess.check_output(['git','show',f['mathematical_source_revision']+':'+name]);assert hashlib.sha256(b).hexdigest()==digest,name
for c in v['successful_checks']:
 assert c['exit_code']==0
 b=(r/c['log']).read_bytes();assert hashlib.sha256(b).hexdigest()==c['sha256']
 assert gzip.decompress((r/(c['log']+'.gz')).read_bytes())==b
reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",(e/'axioms-final.log').read_text())
assert len(reports)==1 and reports[0][0]=='Matrix.replicaGoodRegionalAuxiliaryMarginal_exp_mergeDeficit_le'
assert set(x.strip() for x in reports[0][1].split(','))=={'propext','Classical.choice','Quot.sound'}
assert v['full_library_revision']==f['full_library_revision'] and v['book_revision']==f['book_revision']
assert json.loads((e/'render/pages.json').read_text())['pdf_pages']==469
assert len(v['successful_checks'])==15
print(f"Verified {len(m['files'])} source/evidence bindings, fifteen successful checks, and the exact standard kernel report.")
