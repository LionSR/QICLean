"""Bind the frozen contribution and the complete verification records."""
from pathlib import Path
import hashlib,json,shutil
r=Path.cwd();e=Path(__file__).resolve().parent
shutil.copyfile(r/'blueprint/lean_decls',e/'NativeDeclarations.txt')
f=json.loads((e/'source-freeze.json').read_text());files=set(f['production_sha256'])|set(f['integration_sha256'])|{'docs/provenance/openai-math.d/mergeDeficitPositivity8753.json'}
files.update(str(p.relative_to(r)) for p in e.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='manifest.json')
leaf=json.loads((r/'docs/provenance/evidence/mergeDeficitPositivity8753/manifest.json').read_text());files.update(leaf['files']);files.add('docs/provenance/evidence/mergeDeficitPositivity8753/manifest.json')
report={'mathematical_source_revision':f['mathematical_source_revision'],'full_library_and_book_revision':f['source_revision'],'files':{n:hashlib.sha256((r/n).read_bytes()).hexdigest() for n in sorted(files)}}
(e/'manifest.json').write_text(json.dumps(report,indent=2)+'\n');print('Bound',len(files),'source/evidence files.')
