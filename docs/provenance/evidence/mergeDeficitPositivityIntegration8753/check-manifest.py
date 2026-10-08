"""Verify the exact source, complete command records, and four kernel reports."""
from pathlib import Path
import argparse,gzip,hashlib,json,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--git',action='store_true');args=p.parse_args()
r=Path.cwd();e=Path(__file__).resolve().parent
m=json.loads((e/'manifest.json').read_text());f=json.loads((e/'source-freeze.json').read_text());v=json.loads((e/'verification.json').read_text())
for name,digest in m['files'].items():
 b=(r/name).read_bytes();assert hashlib.sha256(b).hexdigest()==digest,name
 if args.git:assert subprocess.check_output(['git','show','HEAD:'+name])==b,name
for group,revision in [('production_sha256',f['mathematical_source_revision']),('integration_sha256',f['source_revision'])]:
 for name,digest in f[group].items():assert hashlib.sha256(subprocess.check_output(['git','show',revision+':'+name])).hexdigest()==digest,name
assert len(v['successful_checks'])==16 and all(c['exit_code']==0 for c in v['successful_checks'])
assert len(v['retained_metadata_failures'])==4 and sorted(c['exit_code'] for c in v['retained_metadata_failures'])==[1,1,1,2]
for c in v['successful_checks']+v['retained_metadata_failures']:
 assert c['source_revision']==f['source_revision'];b=(r/c['log']).read_bytes();assert hashlib.sha256(b).hexdigest()==c['sha256'];assert gzip.decompress((r/(c['log']+'.gz')).read_bytes())==b
names=['PermutationRepresentation.posSemidef_mergeDeficit','TensorPower.posSemidef_pairMergeDeficit','Matrix.PosSemidef.spectralProjectionGE_zero','Matrix.spectralProjectionGE_zero_mul_of_intertwine']
reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",(e/'axioms.log').read_text());assert [x[0] for x in reports]==names
for _,xs in reports:assert set(x.strip() for x in xs.split(','))=={'propext','Classical.choice','Quot.sound'}
assert not re.search(r'\bBuilt Mathlib(?:\.[\w.]+)?\b',(e/'full-build.log').read_text()),'Unexpected Mathlib source build'
assert 'Build completed successfully (9823 jobs).' in (e/'full-build.log').read_text()
assert json.loads((e/'render/pages.json').read_text())['pdf_pages']==471
native=(e/'NativeDeclarations.txt').read_text().splitlines();assert len(native)==len(set(native))==3763
for n in names:assert native.count(n)==1,n
subprocess.run(['python3',str(e/'check-preservation-corrected.py')],check=True)
subprocess.run(['python3',str(r/'docs/provenance/evidence/mergeDeficitPositivity8753/check-manifest.py')]+(['--git'] if args.git else []),check=True)
print(f"Verified {len(m['files'])} portable source/evidence bindings,16 successful commands,4 retained metadata failures and4 exact standard kernel reports.")
