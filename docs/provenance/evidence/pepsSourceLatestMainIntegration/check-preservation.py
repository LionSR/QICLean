"""Check the proof-preserving extension by the accepted Schur-label contribution."""
from pathlib import Path
import hashlib,json,subprocess
r=Path.cwd();p=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
f=json.loads((p/'source-freeze.json').read_text())
for name,digest in f['sha256'].items():
 b=(r/name).read_bytes();assert sha(b)==digest,name
 assert b==subprocess.check_output(['git','show',f['source_revision']+':'+name]),name
parents=json.loads((p/'parent-preservation.json').read_text())
old=r/'docs/provenance/evidence/pepsSourceMainIntegration'
oldf=json.loads((old/'source-freeze.json').read_text())['sha256']
exceptions=parents['old_source_inventory_preserved_except_exact_accepted_main_files']
for name,digest in oldf.items():
 if name in exceptions:
  assert (r/name).read_bytes()==subprocess.check_output(['git','show',parents['accepted_main']+':'+name]),name
 else:assert sha((r/name).read_bytes())==digest,name
compat=json.loads((old/'parent-compatibility.json').read_text())
for name,digest in compat['incoming_changed_production_sha256'].items():assert sha((r/name).read_bytes())==digest,name
newfiles=['ColumnAntisymmetrizer','IrrepLabelCount','PartitionCount','SchurWeylLabels','SchurWeylLift']
for name in newfiles:
 path='QICLean/Representation/'+name+'.lean'
 assert (r/path).read_bytes()==subprocess.check_output(['git','show',parents['accepted_main']+':'+path]),path
print(len(f['sha256']),'whole frozen files preserved;',len(oldf),'previous source files preserved except two exact accepted-main files;',len(newfiles),'accepted proof files and all25 PEPS files exact.')
