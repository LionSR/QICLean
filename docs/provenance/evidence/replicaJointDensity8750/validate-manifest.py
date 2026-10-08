"""Validate the source-bound leaf evidence and exact released joint-density parent."""
from pathlib import Path
import gzip,hashlib,io,json,re,subprocess,tarfile,sys
r=Path.cwd();p=Path(__file__).resolve().parent
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();tracked=set(subprocess.check_output(['git','ls-files'],text=True).splitlines())
m=json.loads((p/'verification.json').read_text());freeze=json.loads((p/'source-freeze.json').read_text())
for n,h in freeze['production_sha256'].items():
 assert sha(r/n)==h and (r/n).read_bytes()==subprocess.check_output(['git','show',freeze['source_revision']+':'+n]),n
for c in m['checks']+m['preparatory_checks']:
 assert c['exit_code']==0
 if c in m['checks']:assert c['source_revision']==freeze['source_revision']
 else:assert c['stage']=='pre-freeze preparation' and c['source_revision']==subprocess.check_output(['git','rev-parse','076b8c48'],text=True).strip()
 assert sha(r/c['log'])==c['sha256'] and c['log'] in tracked
 gz=(r/(c['log']+'.gz')).read_bytes();assert gzip.decompress(gz)==(r/c['log']).read_bytes() and int.from_bytes(gz[4:8],'little')==0
for n,h in m['file_hashes'].items():assert n in tracked and sha(r/n)==h,n
parent=json.loads((p/'parent-preservation.json').read_text());archive=tarfile.open(fileobj=io.BytesIO(subprocess.check_output(['git','archive',parent['parent_revision']])))
for n,h in parent['sha256'].items():
 original=archive.extractfile(n).read();assert hashlib.sha256(original).hexdigest()==h,n
 if n==parent['cumulative_ledger_exception']:assert (r/n).read_bytes().startswith(original) and sha(r/n)==parent['new_ledger_sha256'],n
 elif '--allow-inclusion' in sys.argv and n in ['QICLean/Analysis.lean','blueprint/src/chapter/ch12_entropy.tex'] and sha(r/n)!=h:
  addition=(b'import QICLean.Analysis.ReplicaJointDensity\n' if n=='QICLean/Analysis.lean' else b'\\input{fragment/replica_joint_density}\n')
  current=(r/n).read_bytes();assert current.count(addition)==1 and current.replace(addition,b'')==original,n
 else:assert sha(r/n)==h,n
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(p/'axioms.log').read_text(),re.S)
assert len(reports)==2 and {n for n,_ in reports}==set(m['declarations'])
for _,a in reports:assert {s.strip() for s in a.split(',')}<={'propext','Classical.choice','Quot.sound'}
print(len(m['checks']),'source-bound successful commands;',len(m['file_hashes']),'tracked hashes; two exact standard-kernel reports.')
print('Four frozen source/exposition files and all',len(parent['sha256']),'released parent files preserved, with the frozen cumulative ledger append and, only when requested, the two exact later inclusion lines.')
