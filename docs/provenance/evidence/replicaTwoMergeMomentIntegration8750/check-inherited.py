from pathlib import Path
import json,hashlib,subprocess
root=Path.cwd();e=Path(__file__).resolve().parent
for row in json.loads((e/'individual-source-preservation.json').read_text())['records']:
 assert hashlib.sha256((root/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
subprocess.run(['python3','docs/provenance/evidence/replicaTwoMergeMoment8750/check-manifest.py','--git'],check=True)
base='1966e51e';path='QICLean/Analysis.lean';before=subprocess.check_output(['git','show',base+':'+path]);after=(root/path).read_bytes();added=b'import QICLean.Analysis.ReplicaTwoMergeMoment\n';assert after.replace(added,b'')==before and after.count(added)==1
path='blueprint/src/chapter/ch13_schur_labels.tex';before=subprocess.check_output(['git','show',base+':'+path]);after=(root/path).read_bytes();assert after==before.rstrip()+b'\n\n\\input{fragment/replica_two_merge_moment}\n'
print('Original leaf and inherited parents preserved; exact one-import/one-input addition verified.')
