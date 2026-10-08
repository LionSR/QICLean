"""Collect exact command records and deterministic raw-log compression."""
from pathlib import Path
import gzip,hashlib,json
r=Path.cwd();p=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
commands=[json.loads(q.read_text()) for q in sorted(p.glob('*-exit.json'))]
compressed=[]
for c in commands:
 q=r/c['log'];data=q.read_bytes();target=Path(str(q)+'.gz');target.write_bytes(gzip.compress(data,mtime=0))
 compressed.append({'raw':str(q.relative_to(r)),'raw_sha256':sha(data),'gzip':str(target.relative_to(r)),'gzip_sha256':sha(target.read_bytes()),'mtime':0})
(p/'compression.json').write_text(json.dumps(compressed,indent=2)+'\n')
f=json.loads((p/'source-freeze.json').read_text());files={str(q.relative_to(r)):sha(q.read_bytes()) for q in sorted(p.rglob('*')) if q.is_file() and q.name!='verification.json'}
files.update(f['production_sha256']);files.update(f['inclusion_sha256'])
for n in ['docs/provenance/openai-math.d/replicaGoodPhysicalSupport8750.json','docs/provenance/evidence/replicaGoodPhysicalSupport8750/verification.json']:files[n]=sha((r/n).read_bytes())
m={'mathematical_source_revision':f['source_revision'],'leaf_evidence_revision':json.loads((p/'parent-preservation.json').read_text())['parent_revision'],'inclusion_revision':f['inclusion_revision'],'owned_declarations':['Matrix.symProj_mul_replicaExcitationComponent_goodAuxiliary_density'],'commands':commands,'file_hashes':files,'inventory_exclusions':['verification.json: self inventory'],'scope':'One actual physical symmetric-support theorem; inherited mathematical proofs and audits are preserved, not freshly reviewed.'}
(p/'verification.json').write_text(json.dumps(m,indent=2)+'\n');print(len(commands),'commands;',len(files),'portable file hashes')
