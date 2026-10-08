"""Check the recorded individual-module evidence without rebuilding."""
from pathlib import Path
import gzip,hashlib,json,subprocess
root=Path.cwd();p=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
for e in json.loads((p/'evidence-sha256.json').read_text())['files']:
 assert sha((root/e['path']).read_bytes())==e['sha256'],e['path']
f=json.loads((p/'source-freeze.json').read_text())
for name,digest in f['production_sha256'].items():
 b=(root/name).read_bytes();assert sha(b)==digest,name
 assert subprocess.check_output(['git','show',f['source_revision']+':'+name])==b,name
parent=json.loads((p/'parent-evidence.json').read_text())
for e in parent['files']:assert sha((root/e['path']).read_bytes())==e['sha256'],e['path']
checks=json.loads((p/'verification.json').read_text())['checks']
for e in checks:
 b=(root/e['log']).read_bytes();assert e['exit_code']==0 and sha(b)==e['sha256']
 gz=(root/(e['log']+'.gz')).read_bytes();assert gzip.decompress(gz)==b and int.from_bytes(gz[4:8],'little')==0
raw=' '.join((p/'axioms.log').read_text().split());assert 'sorryAx' not in raw
names=['PermutationRepresentation.commute_partialTraceLeft_vecMulVec_of_fixed_kronecker_permOp','Matrix.commute_partialTraceLeft_replicaExcitationComponent']
for name in names:assert "'"+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in raw,name
print(len(checks),'successful commands,',len(parent['files']),'inherited evidence files, four frozen files and two exact stock reports verified')
