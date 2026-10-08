"""Validate the frozen physical-support source, owned evidence and released parent."""
from pathlib import Path
import gzip,hashlib,io,json,re,subprocess,tarfile,sys
r=Path.cwd();p=Path(__file__).resolve().parent
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
tracked=set(subprocess.check_output(['git','ls-files'],text=True).splitlines())
m=json.loads((p/'verification.json').read_text());f=json.loads((p/'source-freeze.json').read_text())
for n,h in f['production_sha256'].items():
 assert sha(r/n)==h and (r/n).read_bytes()==subprocess.check_output(['git','show',f['source_revision']+':'+n]),n
required={'guard-notice','target-notice','strict-notice','axioms-notice','provenance-notice','preservation-notice','statements-notice'}
assert required<={Path(c['log']).stem for c in m['checks']}, 'Missing successful current whole-file verification commands'
for c in m['checks']:
 assert c['exit_code']==0 and c['source_revision']==f['source_revision']
 assert c['log'] in tracked and sha(r/c['log'])==c['sha256'],c['log']
 gz=(r/(c['log']+'.gz')).read_bytes()
 assert gzip.decompress(gz)==(r/c['log']).read_bytes() and int.from_bytes(gz[4:8],'little')==0
for n,h in m['file_hashes'].items():assert n in tracked and sha(r/n)==h,n
for c in m.get('excluded_checks',[]):
 assert c['exit_code']==1
 name=Path(c['log']).stem
 assert (name in {'axioms','statements','provenance'} and c['source_revision']==f['mathematical_introduction']) or (name=='manifest-notice-check' and c['source_revision']==f['source_revision']),name
 assert c['log'] in tracked and sha(r/c['log'])==c['sha256']
 gz=(r/(c['log']+'.gz')).read_bytes();assert gzip.decompress(gz)==(r/c['log']).read_bytes() and int.from_bytes(gz[4:8],'little')==0

parent=json.loads((p/'parent-preservation.json').read_text())
with tarfile.open(fileobj=io.BytesIO(subprocess.check_output(['git','archive',parent['parent_revision']]))) as t:
 for n,h in parent['sha256'].items():
  original=t.extractfile(n).read();assert hashlib.sha256(original).hexdigest()==h,n
  if n==parent['cumulative_ledger_exception']:
   assert (r/n).read_bytes().startswith(original) and sha(r/n)==parent['new_ledger_sha256'],n
  elif '--allow-inclusion' in sys.argv and n in ['QICLean/Analysis.lean','blueprint/src/chapter/ch12_entropy.tex'] and sha(r/n)!=h:
   addition=(b'import QICLean.Analysis.ReplicaGoodPhysicalSupport\n' if n=='QICLean/Analysis.lean' else b'\\input{fragment/replica_good_physical_support}\n')
   current=(r/n).read_bytes();assert current.count(addition)==1 and current.replace(addition,b'')==original,n
  else:assert sha(r/n)==h,n
for c in m.get('historical_checks',[]):
 assert c['exit_code']==0 and c['source_revision']==f['mathematical_introduction']
 assert c['log'] in tracked and sha(r/c['log'])==c['sha256']
 gz=(r/(c['log']+'.gz')).read_bytes();assert gzip.decompress(gz)==(r/c['log']).read_bytes() and int.from_bytes(gz[4:8],'little')==0
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(p/'axioms-notice.log').read_text(),re.S)
assert len(reports)==1 and {n for n,_ in reports}==set(m['declarations'])
for _,a in reports:assert {s.strip() for s in a.split(',')}<={'propext','Classical.choice','Quot.sound'}
print(len(m['checks']),'source-bound successful commands;',len(m['file_hashes']),'tracked hashes; one exact standard-kernel report.')
print('All four frozen files and',len(parent['sha256']),'released-parent files preserved, allowing only the recorded cumulative ledger append and, when requested, the two exact inclusion lines.')
print('Actual physical support is derived without a supplied symmetry/support certificate.')
