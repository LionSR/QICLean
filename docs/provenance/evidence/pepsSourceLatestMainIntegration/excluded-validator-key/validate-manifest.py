"""Validate the exact source and the append-only latest-main evidence record."""
from pathlib import Path
import gzip,hashlib,json,re,subprocess
r=Path.cwd();p=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda name:json.loads((p/name).read_text())
m=read('manifest.json')
actual={str(x.relative_to(r)) for x in p.rglob('*') if x.is_file() and x.name!='manifest.json' and '__pycache__' not in x.parts}
assert actual==set(m['sha256']), 'inventory paths differ'
for name,digest in m['sha256'].items():assert sha((r/name).read_bytes())==digest,name
v=read('verification.json');assert len(v['successful_commands'])==19
assert not v['excluded_attempts']
for c in v['successful_commands']:
 assert c['exit_code']==0 and c['source_revision']==v['source_revision']
 assert sha((r/c['log']).read_bytes())==c['sha256'],c['log']
for name,c in read('compression.json').items():
 raw=(r/name).read_bytes();z=(r/c['gzip']).read_bytes()
 assert sha(raw)==c['sha256'] and sha(z)==c['gzip_sha256']
 assert gzip.decompress(z)==raw and z[4:8]==b'\0'*4
for name,digest in v['generated_outputs_sha256'].items():
 if name.startswith(str(p.relative_to(r))):assert sha((r/name).read_bytes())==digest,name
assert 'Build completed successfully (9791 jobs).' in (p/'full-build.log').read_text()
audit=(p/'source-contraction-kernels.log').read_text()
reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",audit)
assert len(reports)==8 and all(re.sub(r'\s+','',a)=='propext,Classical.choice,Quot.sound' for _,a in reports)
assert len({n for n,_ in reports})==8
native=(p/'NativeDeclarations.txt').read_text().splitlines();assert len(native)==3627
nt=read('native-targets.json');assert nt['result']=='passed' and nt['total_source_targets']==240
assert sha((p/'NativeDeclarations.txt').read_bytes())==nt['native_list_sha256']
for names in nt['source_chapters'].values():assert set(names)<=set(native)
comparison=read('render-comparison.json');assert len(comparison['byte_identical_previously_inspected_images'])==29 and not comparison['different_images']
old=r/'docs/provenance/evidence/pepsSourceMainIntegration'
for name in comparison['byte_identical_previously_inspected_images']:
 x=r/name;assert x.read_bytes()==(old/'render'/x.name).read_bytes(),name
for page in [436,437]:assert (p/'render'/f'page-{page}.png').is_file()
assert json.loads((p/'whole-web.log').read_text())=={'pages':50,'typeset':38820}
assert '9 complete entries' in (p/'focused-web.log').read_text()
subprocess.run(['python3',str(p/'check-preservation.py')],check=True,cwd=r)
print(f"Validated {len(m['sha256'])} evidence hashes, 19 successful commands, 1455 source files, 8 focused kernel reports, 240 native targets and 29 unchanged source images.")
