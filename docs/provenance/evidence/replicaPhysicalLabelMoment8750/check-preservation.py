from pathlib import Path
import subprocess,json,hashlib
root=Path.cwd();e=Path(__file__).resolve().parent
base='a820e67e2f30782485361fa71c8c0763981f8edb'
allowed={'QICLean/Analysis/ReplicaPhysicalLabelMoment.lean','blueprint/src/fragment/replica_physical_label_moment.tex','docs/area-law-replica-physical-label-moment.md'}
lines=subprocess.check_output(['git','diff','--name-status',base],text=True).splitlines()
for line in lines:
 status,path=line.split('\t')
 if path=='QICLean/Analysis.lean':
  before=subprocess.check_output(['git','show',base+':'+path]);after=(root/path).read_bytes();added=b'import QICLean.Analysis.ReplicaPhysicalLabelMoment\n';assert after.replace(added,b'')==before and after.count(added)==1
 elif path=='blueprint/src/chapter/ch13_schur_labels.tex':
  before=subprocess.check_output(['git','show',base+':'+path]);after=(root/path).read_bytes();assert after==before.rstrip()+b'\n\n\\input{fragment/replica_physical_label_moment}\n'
 else:assert status=='A' and (path in allowed or path.startswith('docs/provenance/evidence/replicaPhysicalLabelMoment') or path=='docs/provenance/openai-math.d/replicaPhysicalLabelMoment8750.json'),line
assert subprocess.check_output(['git','rev-parse','feat/area-law-two-deficit-moment'],text=True).strip()==base
inventory=json.loads((root/'docs/provenance/evidence/replicaTwoMergeMomentIntegration8750/evidence-sha256.json').read_text())['files']
for row in inventory:
 data=(root/row['path']).read_bytes();assert hashlib.sha256(data).hexdigest()==row['sha256'],row['path']
 assert data==subprocess.check_output(['git','show',base+':'+row['path']]),row['path']
print('Entire checked parent Git tree and',len(inventory),'portable records preserved; any aggregate changes are exact one-import/one-input additions. No inherited semantic audit or old generated-output comparison.')
