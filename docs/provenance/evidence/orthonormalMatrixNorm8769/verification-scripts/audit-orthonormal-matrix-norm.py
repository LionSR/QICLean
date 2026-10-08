from pathlib import Path
import hashlib,json,os,re,subprocess,time
b=Path('/private/tmp/qic-orthonormal-matrix-norm');cfg=json.loads((b/'env.json').read_text());src=b/'Axioms.lean';src.write_text('''import QICLean.Analysis.OrthonormalMatrixNorm

set_option linter.hashCommand false
#print axioms ContinuousLinearMap.norm_toMatrix_orthonormal

run_cmd do
  let e ← Lean.getEnv
  let names := e.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)
  IO.FS.writeFile "imported-modules.json" (Lean.Json.compress (Lean.Json.arr names))
''');env=os.environ.copy();env['LEAN_PATH']=cfg['LEAN_PATH'];cmd=[cfg['lean'],*cfg['options'],'-DwarningAsError=true','Axioms.lean'];t=time.monotonic();r=subprocess.run(cmd,cwd=b,env=env,capture_output=True,text=True);log=r.stdout+r.stderr;(b/'axioms.log').write_text(log);assert r.returncode==0,log
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=re.search(r"'ContinuousLinearMap.norm_toMatrix_orthonormal' depends on axioms: \[(.*?)\]",log,re.S);assert m;axs=[x.strip() for x in m[1].split(',')];assert set(axs)<={'propext','Classical.choice','Quot.sound'}
roots=[Path(p) for p in cfg['LEAN_PATH'].split(':')];deps=[]
for mod in json.loads((b/'imported-modules.json').read_text()):
 rel=mod.replace('.','/')+'.olean';p=next(root/rel for root in roots if (root/rel).is_file());deps.append({'module':mod,'artifact':str(p),'resolved_artifact':str(p.resolve()),'sha256':sha(p),'bytes':p.stat().st_size})
(b/'imported-dependencies.json').write_text(json.dumps(deps,indent=2)+'\n');(b/'axiom-dependencies.json').write_text(json.dumps({'ContinuousLinearMap.norm_toMatrix_orthonormal':axs},indent=2)+'\n');(b/'audit-command.json').write_text(json.dumps({'command':cmd,'cwd':str(b),'LEAN_PATH':cfg['LEAN_PATH'],'returncode':r.returncode,'seconds':round(time.monotonic()-t,3),'source_sha256':sha(src),'log_sha256':sha(b/'axioms.log'),'imported_artifacts':len(deps),'imported_dependencies_sha256':sha(b/'imported-dependencies.json')},indent=2)+'\n');print('AUDIT_PASS',len(deps))
