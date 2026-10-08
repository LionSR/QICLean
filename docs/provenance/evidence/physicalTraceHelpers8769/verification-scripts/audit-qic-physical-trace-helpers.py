from pathlib import Path
import hashlib,json,os,re,subprocess,time
b=Path('/private/tmp/qic-physical-trace-helpers');cfg=json.loads((b/'env.json').read_text());rows=json.loads((b/'declarations.json').read_text());names=[x['declaration'] for x in rows];src=b/'Axioms.lean';s='import QICLean\n\nset_option linter.hashCommand false\n'
for name in names:
 ns,leaf=name.rsplit('.',1);s+=f'\nnamespace {ns}\n#print axioms {leaf}\nend {ns}\n'
s+='\nrun_cmd do\n  let e ← Lean.getEnv\n  let ns := e.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)\n  IO.FS.writeFile "imported-modules.json" (Lean.Json.compress (Lean.Json.arr ns))\n';src.write_text(s);env=os.environ.copy();env['LEAN_PATH']=cfg['LEAN_PATH'];cmd=[cfg['lean'],*cfg['options'],'-DwarningAsError=true','Axioms.lean'];t=time.monotonic();r=subprocess.run(cmd,cwd=b,env=env,capture_output=True,text=True);log=r.stdout+r.stderr;(b/'axioms.log').write_text(log);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();record={'command':cmd,'cwd':str(b),'LEAN_PATH':cfg['LEAN_PATH'],'returncode':r.returncode,'seconds':round(time.monotonic()-t,3),'source_sha256':sha(src),'log_sha256':sha(b/'axioms.log')};(b/'audit-command.json').write_text(json.dumps(record,indent=2)+'\n');assert r.returncode==0,log
found={}
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",log,re.S):
 n,a=m.groups();found[n]=[] if a is None else [v.strip() for v in a.split(',')]
assert set(found)==set(names);assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in found.values());(b/'axiom-dependencies.json').write_text(json.dumps(found,indent=2)+'\n')
roots=[Path(p) for p in cfg['LEAN_PATH'].split(':')];deps=[]
for mod in json.loads((b/'imported-modules.json').read_text()):
 rel=mod.replace('.','/')+'.olean';p=next(root/rel for root in roots if (root/rel).is_file());deps.append({'module':mod,'artifact':str(p),'resolved_artifact':str(p.resolve()),'sha256':sha(p),'bytes':p.stat().st_size})
(b/'imported-dependencies.json').write_text(json.dumps(deps,indent=2)+'\n');record.update({'audited_declarations':len(names),'imported_artifacts':len(deps),'imported_dependencies_sha256':sha(b/'imported-dependencies.json')});(b/'audit-command.json').write_text(json.dumps(record,indent=2)+'\n');print('TEN_STANDARD_AXIOMS_ONLY',len(deps))
