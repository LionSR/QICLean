"""Check the frozen source, original leaf and the two exact inclusion changes."""
from pathlib import Path
import hashlib,json,subprocess
r=Path.cwd();e=Path(__file__).resolve().parent;sha=lambda d:hashlib.sha256(d).hexdigest()
f=json.loads((e/'source-freeze.json').read_text());leaf=f['leaf_evidence_revision']
for row in json.loads((e/'individual-source-preservation.json').read_text())['files']:
 data=(r/row['path']).read_bytes();assert sha(data)==row['sha256'];assert data==subprocess.check_output(['git','show',leaf+':'+row['path']])
for row in f['files']:
 data=(r/row['path']).read_bytes();assert sha(data)==row['sha256'];assert data==subprocess.check_output(['git','show',f['source_revision']+':'+row['path']])
p='QICLean/Representation.lean';before=subprocess.check_output(['git','show',leaf+':'+p]);after=(r/p).read_bytes();added=b'import QICLean.Representation.SchurLabelMoments\n';assert after.count(added)==1 and after.replace(added,b'')==before
p='blueprint/src/chapter/ch13_schur_labels.tex';before=subprocess.check_output(['git','show',leaf+':'+p]);assert (r/p).read_bytes()==before.rstrip()+b'\n\n\\input{fragment/schur_label_moments}\n'
subprocess.run(['python3','docs/provenance/evidence/schurLabelMoments8753/check-manifest.py','--git'],check=True)
print('Frozen four mathematical/exposition files and two inclusion files and original leaf exact; unique import and input checked against authoritative leaf. No wider inherited semantic audit is claimed.')
