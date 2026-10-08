"""Bind three original declarations to the frozen source and actual verification records."""
from pathlib import Path
import json,hashlib
root=Path.cwd();e=Path(__file__).resolve().parent
freeze=json.loads((e/'source-freeze.json').read_text());entries=[]
names=json.loads((e/'public-declarations.json').read_text())['new']
def command(name,kind):
 r=json.loads((e/(name+'-exit.json')).read_text());assert r['exit_code']==0
 assert hashlib.sha256((root/r['log']).read_bytes()).hexdigest()==r['sha256']
 return {'kind':kind,'command':' '.join(r['command']),'exit_code':0,'log':r['log'],'sha256':r['sha256']}
for i,n in enumerate(names,1):
 path='QICLean/Representation/SchurLabelMoments.lean';strict='bound-strict'
 entries.append({'id':f'8753-qic-schur-label-moments-{i:02}','status':'ported','reuse_kind':'original','upstream':None,'downstream':{'repository':'LionSR/QICLean','path':path,'declaration':n,'name_status':'declared'},'paper_sources':[{'version':'September 24, 2026','path':'preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/07-comparators.tex','labels':['comparator:signed-label-moments']}],'license':'Apache-2.0','notices':[],'changes':['Original auxiliary centered Schur-label comparison with supported surprisal moments. No upstream Lean proof text reused; signed independent-copy surprisal rate estimates remain downstream.'],'no_upstream_proof_text_reused':True,'verification':{'result':'passed','repository':'LionSR/QICLean','revision':freeze['source_revision'],'commands':[command('bound-target','build'),command(strict,'build'),command('bound-axioms','axioms')]}})
(root/'docs/provenance/openai-math.d/schurLabelMoments8753.json').write_text(json.dumps({'schema_version':1,'source':{'repository':'openai/math','commit':'adc7f1241b42e322a6451854ab7e4b4c146bf78a'},'entries':entries},indent=2)+'\n')
print('Created three original source-bound provenance entries; historical original shards unchanged.')
