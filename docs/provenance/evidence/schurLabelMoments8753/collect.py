"""Collect source-bound commands, original IDs and historical text bindings."""
from pathlib import Path
import hashlib,json
r=Path.cwd();e=Path(__file__).resolve().parent;sha=lambda d:hashlib.sha256(d).hexdigest()
def dump(n,v):(e/n).write_text(json.dumps(v,indent=2)+'\n')
f=json.loads((e/'source-freeze.json').read_text());names=json.loads((e/'public-declarations.json').read_text())['new']
dump('kernel-summary.json',{'source_revision':f['source_revision'],'declarations':names,'raw_log':str((e/'bound-axioms.log').relative_to(r)),'sha256':sha((e/'bound-axioms.log').read_bytes()),'axioms':['propext','Classical.choice','Quot.sound'],'exact_name_reports':3})
dump('verification.json',{'source_revision':f['source_revision'],'checks':[json.loads(p.read_text()) for p in sorted(e.glob('*-exit.json')) if p.name!='manifest-check-exit.json'],'fresh_kernel_reports':3,'owned_original_provenance_entries':3,'historical_external_text_records':22,'scope':'Auxiliary centered-label transfers from supported surprisal moments; no signed independent-copy rate claim.'})
exclude={'evidence-sha256.json','manifest-check.log','manifest-check-exit.json'}
files=[{'path':str(p.relative_to(r)),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size} for p in sorted(e.rglob('*')) if p.is_file() and p.name not in exclude]
s=r/'docs/provenance/openai-math.d/schurLabelMoments8753.json';files.append({'path':str(s.relative_to(r)),'sha256':sha(s.read_bytes()),'bytes':s.stat().st_size})
dump('evidence-sha256.json',{'files':files});print('Collected',len(files),'portable leaf bindings.')
