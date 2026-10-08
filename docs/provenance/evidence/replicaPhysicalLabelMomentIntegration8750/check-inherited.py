from pathlib import Path
import json,hashlib,subprocess
root=Path.cwd();e=Path(__file__).resolve().parent
for row in json.loads((e/'individual-source-preservation.json').read_text())['records']:
 assert hashlib.sha256((root/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
subprocess.run(['python3','docs/provenance/evidence/replicaPhysicalLabelMoment8750/check-manifest.py','--git'],check=True)
base='a2b266d6';path='QICLean/Analysis.lean';before=subprocess.check_output(['git','show',base+':'+path]);after=(root/path).read_bytes();added=b'import QICLean.Analysis.ReplicaPhysicalLabelMoment\n';assert after.replace(added,b'')==before and after.count(added)==1
path='blueprint/src/chapter/ch13_schur_labels.tex';before=subprocess.check_output(['git','show',base+':'+path]);after=(root/path).read_bytes();assert after==before.rstrip()+b'\n\n\\input{fragment/replica_physical_label_moment}\n'
print('Original physical-moment leaf and complete checked parent tree preserved; exact unique import/input verified.')

for row in json.loads((root/'docs/provenance/evidence/replicaTwoMergeMomentIntegration8750/generated-output-hashes.json').read_text())['files']:
 if row['path'].startswith('output/pdf/'):
  assert hashlib.sha256((root/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
for row in json.loads((root/'docs/provenance/evidence/replicaTwoMergeMoment8750/preexisting-output-preservation.json').read_text())['files']:
 assert hashlib.sha256((root/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
print('Previously saved PDF artifacts also remain exact; transient generated book outputs may be regenerated.')
