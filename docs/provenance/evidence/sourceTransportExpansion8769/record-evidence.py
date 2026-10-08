#!/usr/bin/env python3
"""Record the verified orthonormal-coordinate norm identity and its intended consumers."""
from pathlib import Path
import gzip,hashlib,json,re,shlex,shutil,subprocess
root=Path('/Users/siruilu/Local/agentFormalization/QICLean/worktrees/source-transport-expansion');b=Path('/private/tmp/qic-source-transport-expansion');out=root/'docs/provenance/evidence/sourceTransportExpansion8769';out.mkdir(parents=True,exist_ok=True)
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip();read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
builds=read(b/'build-commands.json');audit=read(b/'audit-command.json');deps=read(b/'imported-dependencies.json')
for r in builds:
 data=subprocess.check_output(['git','show',rev+':'+r['source_path']],cwd=root);assert hashlib.sha256(data).hexdigest()==r['source_sha256']==sha(root/r['source_path']);assert r['returncode']==0 and not (b/(r['module']+'.log')).read_bytes();assert sha(Path(r['artifact']))==r['artifact_sha256'];r['source_revision']=rev
for r in deps:assert sha(Path(r['artifact']))==r['sha256']
audit['source_revision']=rev;audit['all_imported_artifact_hashes_unchanged_at_pin']=True
save(b/'build-commands.json',builds);save(b/'audit-command.json',audit)
lines=['Direct Lean compilation with package options and warnings as errors.',f'Source revision: {rev}','No local Lake build or cache mutation was performed.','']
for r in builds:lines += [f'Source: {r["source_path"]}',f'Source SHA256: {r["source_sha256"]}',f'Working directory: {r["cwd"]}',f'Command: {shlex.join(r["command"])}',f'Exit code: {r["returncode"]}',f'Elapsed seconds: {r["seconds"]}','Diagnostics: none.','']
(out/'direct-build.log').write_text('\n'.join(lines));(out/'axioms.log').write_text(f'Source revision: {rev}\nCommand: {shlex.join(audit["command"])}\n\n'+(b/'axioms.log').read_text())
for p in ['build-commands.json','audit-command.json','axiom-dependencies.json','Axioms.lean','env.json','preparation.json','format-command.json','source-original.lean']:shutil.copy2(b/p,out/p)
for p in ['imported-dependencies.json','imported-modules.json']:(out/(p+'.gz')).write_bytes(gzip.compress((b/p).read_bytes(),mtime=0))
for p in b.glob('QICLean*.log'):shutil.copy2(p,out/p.name)
(out/'declaration-check').mkdir(exist_ok=True)
for p in (b/'declaration-check').iterdir():
 if p.name=='lean_declarations.txt':(out/'declaration-check'/(p.name+'.gz')).write_bytes(gzip.compress(p.read_bytes(),mtime=0))
 else:shutil.copy2(p,out/'declaration-check'/p.name)
(out/'verification-scripts').mkdir(exist_ok=True)
for name in ['prepare-source-transport-expansion.py','check-source-transport-expansion.py','audit-source-transport-expansion.py','format-source-transport-expansion.py','check-source-transport-blueprint-declarations.py']:
 shutil.copy2(Path('/tmp')/name,out/'verification-scripts'/name)
shutil.copy2(Path(__file__),out/'record-evidence.py')
(out/'consumers').mkdir(exist_ok=True)
consumer=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-gaussian/TNLean/PEPS/Approximation/PreparedSourceTransport.lean');shutil.copy2(consumer,out/'consumers/PreparedSourceTransport.lean')
save(out/'consumer-references.json',{'status':'Unpublished TNLean consumer, checked directly against this leaf; dependency pin awaits publication.','references':[{'path':'consumers/PreparedSourceTransport.lean','sha256':sha(consumer)}],'declaration':'TNLean.PEPS.PairEffect.Word.sourceContraction_preparedDensityCoefficient_selected_frames'})
# The checker is the canonical TNLean policy, preserved here for scoped QIC use.
canonical=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-corrections');(out/'canonical').mkdir(exist_ok=True)
shutil.copy2(canonical/'scripts/check_openai_provenance.py',out/'canonical/check_openai_provenance.py');shutil.copy2(canonical/'docs/provenance/openai-math.schema.json',out/'canonical/openai-math.schema.json')
commands=[]
for kind,cmd,log in [('build',builds[0]['command'],'direct-build.log'),('axioms',audit['command'],'axioms.log')]:commands.append({'kind':kind,'command':shlex.join(cmd),'exit_code':0,'log':str((out/log).relative_to(root)),'sha256':sha(out/log)})
entry={'id':'p09-qic-source-transport-expansion','status':'ported','reuse_kind':'original','upstream':None,'downstream':{'repository':'LionSR/QICLean','path':'QICLean/Probability/ComplexGaussian/SourceTransportExpansion.lean','declaration':'QICLean.ComplexGaussian.sourceTransport_eq_sum_rankOne','name_status':'declared'},'paper_sources':[{'version':'September 24, 2026','path':'preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex','labels':['eq:compression-random-source']}],'license':'Apache-2.0','notices':[],'changes':['Independently formalized by expanding finite matrix products; no upstream Lean proof text reused.','An algebraic supporting identity for transported Gaussian sources, not the complete polynomial-PEPS theorem. Endpoint maps are arbitrary; only the two summed Schmidt index types are finite.'],'verification':{'result':'passed','repository':'LionSR/QICLean','revision':rev,'commands':commands},'no_upstream_proof_text_reused':True}
save(root/'docs/provenance/openai-math.d/8769-source-transport-expansion.json',{'schema_version':1,'source':{'repository':'openai/math','commit':'adc7f1241b42e322a6451854ab7e4b4c146bf78a'},'entries':[entry]})
save(out/'source-revision.json',{'source_revision':rev,'base_revision':'95411dd3d2f08ec2f65c7613ab0b81c330d28f5c','source_sha256':sha(root/'QICLean/Probability/ComplexGaussian/SourceTransportExpansion.lean'),'parent_branch_634_unchanged':True})
print('RECORDED_SOURCE_EVIDENCE',rev,len(deps))
