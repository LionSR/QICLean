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
f=json.loads((p/'source-freeze.json').read_text());files={str(q.relative_to(r)):sha(q.read_bytes()) for q in sorted(p.rglob('*')) if q.is_file() and q.name!='verification.json' and not q.name.startswith('manifest-check')}
files.update(f['production_sha256']);files.update(f['inclusion_sha256'])
for n in ['docs/provenance/openai-math.d/replicaGoodPairMarginal8750.json','docs/provenance/evidence/replicaGoodPairMarginal8750/verification.json']:files[n]=sha((r/n).read_bytes())
m={'mathematical_source_revision':f['source_revision'],'leaf_evidence_revision':json.loads((p/'parent-preservation.json').read_text())['parent_revision'],'inclusion_revision':f['inclusion_revision'],'owned_declarations':['Matrix.replicaGoodPairMarginal','Matrix.partialTraceRight_replicaGoodPairMarginal','Matrix.partialTraceLeft_replicaGoodPairMarginal','Matrix.trace_replicaGoodPairMarginal'],'commands':commands,'file_hashes':files,'inventory_exclusions':['verification.json: self inventory','manifest-check* command records: final validation output; validated through commands after collection'],'scope':'Four actual common-density coordinate and mass declarations; inherited mathematical proofs and audits are preserved, not freshly reviewed.'}
(p/'verification.json').write_text(json.dumps(m,indent=2)+'\n');print(len(commands),'commands;',len(files),'portable file hashes')
