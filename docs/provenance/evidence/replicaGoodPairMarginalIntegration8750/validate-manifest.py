"""Check the source-bound complete-library and reader evidence for the common density."""
from pathlib import Path
import gzip,hashlib,json,re,subprocess
r=Path.cwd();p=Path(__file__).resolve().parent
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
m=json.loads((p/'verification.json').read_text());f=json.loads((p/'source-freeze.json').read_text())
tracked=set(subprocess.check_output(['git','ls-files'],text=True).splitlines())
for n,h in m['file_hashes'].items():assert n in tracked and sha(r/n)==h,n
for c in m['commands']:
 assert c['exit_code']==0 and c['source_revision']==f['inclusion_revision'],c
 assert sha(r/c['log'])==c['sha256'] and c['log'] in tracked,c['log']
 data=(r/c['log']).read_bytes();gz=(r/(c['log']+'.gz')).read_bytes()
 assert gzip.decompress(gz)==data and int.from_bytes(gz[4:8],'little')==0,c['log']
for n,h in f['production_sha256'].items():
 assert sha(r/n)==h and (r/n).read_bytes()==subprocess.check_output(['git','show',f['source_revision']+':'+n]),n
for n,h in f['inclusion_sha256'].items():assert sha(r/n)==h,n
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(p/'axioms.log').read_text(),re.S)
assert len(reports)==4 and {n for n,_ in reports}==set(m['owned_declarations'])
for _,a in reports:assert {s.strip() for s in a.split(',')}<={'propext','Classical.choice','Quot.sound'}
subprocess.run(['python3',str(p/'check-preservation.py')],check=True)
subprocess.run(['python3','docs/provenance/evidence/replicaGoodPairMarginal8750/validate-manifest.py','--allow-inclusion'],check=True)
n=json.loads((p/'native-targets.json').read_text())
assert set(n['owned_declarations'])==set(m['owned_declarations']) and n['contains_all_active_fragment_targets']
assert n['native_list_sha256']==sha(p/'NativeDeclarations.txt')
v=json.loads((p/'visual-inspection.json').read_text());assert v['result']=='passed' and v['mathematical_source_revision']==f['source_revision'] and v['book_revision']==f['inclusion_revision']
print(len(m['commands']),'actual successful integration commands;',len(m['file_hashes']),'portable tracked hashes; four exact standard-kernel reports.')
print('All inherited files preserved except the two exact inclusion lines; no inherited mathematical audit is repeated.')
