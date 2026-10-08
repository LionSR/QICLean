"""Collect final evidence while retaining the initial visual failure unchanged."""
from pathlib import Path
import gzip,hashlib,json
p=Path(__file__).resolve().parent;r=Path.cwd();sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
initial_names={'blueprint-sync','pdf','bbl','web','native','native-targets','focused-web','whole-web','render'}
commands=[];initial=[];failed=[]
for q in sorted(p.glob('*-exit.json')):
 c=json.loads(q.read_text())
 if c['exit_code']!=0:
  assert q.name=='manifest-initial-exit.json' and c['exit_code']==1
  failed.append({'record':c,'reason':'The final metadata validator shadowed its native-report variable in a later filename loop; all assertions passed before its reporting line failed. The helper snapshot and first tool output are preserved.','claimed_as_successful_verification':False});continue
 (initial if q.name.removesuffix('-exit.json') in initial_names else commands).append(c)
compression=[]
for q in sorted(p.glob('*.log')):
 gz=Path(str(q)+'.gz');gz.write_bytes(gzip.compress(q.read_bytes(),mtime=0))
 compression.append({'path':str(q.relative_to(r)),'sha256':sha(q),'gzip_path':str(gz.relative_to(r)),'gzip_sha256':sha(gz),'mtime':0})
(p/'compression-revised.json').write_text(json.dumps(compression,indent=2)+'\n')
n=json.loads((p/'native-targets-revised.json').read_text());pdf=json.loads((p/'pdf-page-selection-revised.json').read_text());f=json.loads((p/'source-freeze.json').read_text());e=json.loads((p/'exposition-freeze.json').read_text())
files={str(q.relative_to(r)):sha(q) for q in sorted(p.rglob('*')) if q.is_file() and q.name!='verification.json' and '__pycache__' not in q.parts}
for name in f['production_sha256']:files[name]=sha(r/name)
shard=r/'docs/provenance/openai-math.d/replicaJointDensity8750.json';files[str(shard.relative_to(r))]=sha(shard)
m={'mathematical_source_revision':f['source_revision'],'leaf_evidence_revision':'f94ea7d410bb5fe7af8b9da1a8fcb5dd80f41a9b','inclusion_revision':'69b31fc6bbb94576c69def6d42d3153b39afcf04','exposition_revision':e['revision'],'owned_declarations':n['owned_declarations'],'commands':commands,'initial_visual_attempt':{'commands':initial,'reason':'Technical checks passed, but visual inspection found the long inline definition formula clipped on mobile. Original book artifacts and records are preserved.','claimed_as_complete_final_verification':False},'failed_command_attempts':failed,'complete_pdf_pages':pdf['pages'],'file_hashes':files}
(p/'verification.json').write_text(json.dumps(m,indent=2)+'\n')
print(len(commands),'final successful commands;',len(initial),'preserved initial book records;',len(files),'file hashes;',len(compression),'deterministic log pairs.')
