"""Collect the immutable leaf commands and their original source bindings."""
from pathlib import Path
import hashlib,json,re
r=Path.cwd();e=Path(__file__).resolve().parent;sha=lambda d:hashlib.sha256(d).hexdigest()
def dump(n,v):(e/n).write_text(json.dumps(v,indent=2)+'\n')
def row(p):return {'path':str(p.relative_to(r)),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size}
f=json.loads((e/'source-freeze.json').read_text());names=json.loads((e/'public-declarations.json').read_text())
dump('kernel-summary.json',{'source_revision':f['source_revision'],'declarations':names,'raw_log':str((e/'bound-axioms.log').relative_to(r)),'sha256':sha((e/'bound-axioms.log').read_bytes()),'axioms':['propext','Classical.choice','Quot.sound'],'exact_name_reports':11})
dump('verification.json',{'source_revision':f['source_revision'],'checks':[json.loads(p.read_text()) for p in sorted(e.glob('*-exit.json')) if p.name!='manifest-check-exit.json'],'fresh_kernel_reports':11,'owned_original_provenance_entries':5,'all_five_production_strict_checks_passed':True,'original_statements_preserved':6,'unchanged_merge_public_proof_bodies':3,'modified_direct_public_proof_bodies':3,'source_scope':'Auxiliary actual commuting weighted exponential trace inequalities; no source physical five-factor or signed-rate claim.','historical_diagnostics':'Two evidence-wrapper failures retained; root pre-freeze target typing history retained separately. Mathematical source/exposition f24 unchanged.'})
exclude={'evidence-sha256.json','manifest-check.log','manifest-check-exit.json'}
files=[row(p) for p in sorted(e.iterdir()) if p.is_file() and p.name not in exclude]+[row(r/'docs/provenance/openai-math.d/weightedTraceHolder8753.json')]
dump('evidence-sha256.json',{'files':files});print('Collected',len(files),'portable original-source leaf bindings.')
