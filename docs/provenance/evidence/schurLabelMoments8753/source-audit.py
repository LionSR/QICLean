"""Check frozen original-source notices and exclude forbidden proof shortcuts."""
from pathlib import Path
import re,json
r=Path.cwd();e=Path(__file__).resolve().parent;freeze=json.loads((e/'source-freeze.json').read_text());facts=[]
for row in freeze['files']:
 if not row['path'].endswith('.lean'):continue
 text=(r/row['path']).read_text();code=re.sub(r'/-[\s\S]*?-/', '',text);code=re.sub(r'--[^\n]*','',code)
 found=re.findall(r'\b(?:sorry|admit|native_decide|unsafeCast|unsafeCoerce|lcProof|ofReduceBool|ofReduceNat|axiom)\b',code);assert not found,(row['path'],found)
 facts.append({'path':row['path'],'forbidden_code_tokens':found})
paths=['QICLean/Representation/SchurLabelMoments.lean'];combined='\n'.join((r/p).read_text() for p in paths)
for i,n in enumerate(json.loads((e/'public-declarations.json').read_text())['new'],1):
 assert combined.count('Provenance-ID: 8753-qic-schur-label-moments-'+str(i).zfill(2))==1
 assert combined.count('Declaration: '+n+'\n')==1
(e/'source-audit.json').write_text(json.dumps({'production_files':facts,'new_original_notices':3,'owned_declarations':3,'manuscript_commit':'adc7f1241b42e322a6451854ab7e4b4c146bf78a','faithfulness':'Centered Schur-label transfer from supported surprisal moments; independent-copy surprisal rate estimates remain downstream.'},indent=2)+'\n');print('Three original public notices and all frozen Lean proof-token checks passed.')
