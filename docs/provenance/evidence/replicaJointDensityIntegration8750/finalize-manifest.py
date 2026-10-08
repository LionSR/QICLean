"""Collect literal evidence and artifact hashes after the complete checks."""
from pathlib import Path
import gzip,hashlib,json
p=Path(__file__).resolve().parent;r=Path.cwd();sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
records=[json.loads(q.read_text()) for q in sorted(p.glob('*-exit.json'))]
assert all(c['exit_code']==0 for c in records), 'Classify and preserve failed attempts explicitly before finalization.'
compression=[]
for q in sorted(p.glob('*.log')):
 gz=Path(str(q)+'.gz');gz.write_bytes(gzip.compress(q.read_bytes(),mtime=0))
 compression.append({'path':str(q.relative_to(r)),'sha256':sha(q),'gzip_path':str(gz.relative_to(r)),'gzip_sha256':sha(gz),'mtime':0})
(p/'compression.json').write_text(json.dumps(compression,indent=2)+'\n')
n=json.loads((p/'native-targets.json').read_text());pdf=json.loads((p/'pdf-page-selection.json').read_text())
files={str(q.relative_to(r)):sha(q) for q in sorted(p.rglob('*')) if q.is_file() and q.name!='verification.json' and '__pycache__' not in q.parts}
f=json.loads((p/'source-freeze.json').read_text());files.update(f['production_sha256'])
shard=r/'docs/provenance/openai-math.d/replicaJointDensity8750.json';files[str(shard.relative_to(r))]=sha(shard)
m={'mathematical_source_revision':f['source_revision'],'leaf_evidence_revision':'f94ea7d410bb5fe7af8b9da1a8fcb5dd80f41a9b','inclusion_revision':'69b31fc6bbb94576c69def6d42d3153b39afcf04','owned_declarations':n['owned_declarations'],'commands':records,'excluded_attempts':[],'complete_pdf_pages':pdf['pages'],'file_hashes':files}
(p/'verification.json').write_text(json.dumps(m,indent=2)+'\n')
print(len(records),'successful actual commands;',len(files),'file hashes;',len(compression),'deterministic raw/gzip log pairs.')
