from pathlib import Path
import hashlib,json,os,subprocess,time
b=Path('/private/tmp/qic-physical-trace-helpers');cfg=json.loads((b/'env.json').read_text());root=Path(cfg['source_root']);env=os.environ.copy();env['LEAN_PATH']=cfg['LEAN_PATH'];prior={x['module']:x for x in json.loads((b/'build-commands.json').read_text())} if (b/'build-commands.json').exists() else {};rows=[];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mods=['QICLean.Channel.PartialTraceBasisInvariance','QICLean.Channel.PartialTraceBlocks','QICLean.Probability.MatrixTraceNormIntegrability','QICLean.Channel','QICLean.Probability','QICLean']
for mod in mods:
 rel=Path(mod.replace('.','/')+'.lean');src=root/rel;dst=Path(cfg['output_root'])/rel.with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 if mod in prior:
  x=prior[mod]
  if x['returncode']==0 and sha(src)==x['source_sha256'] and dst.is_file() and sha(dst)==x['artifact_sha256']:
   rows.append(x);print('REUSE EXACT',mod,flush=True);continue
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  p=dst.with_suffix(suffix)
  if p.is_symlink():p.unlink()
 snap=b/'checked-sources'/rel;snap.parent.mkdir(parents=True,exist_ok=True);snap.write_bytes(src.read_bytes());cmd=[cfg['lean'],*cfg['options'],'-DwarningAsError=true','-o',str(dst),str(rel)];t=time.monotonic();r=subprocess.run(cmd,cwd=root,env=env,capture_output=True,text=True);log=b/(mod+'.log');log.write_text(r.stdout+r.stderr);rows.append({'module':mod,'source_path':str(rel),'source_sha256':sha(src),'command':cmd,'cwd':str(root),'LEAN_PATH':cfg['LEAN_PATH'],'returncode':r.returncode,'seconds':round(time.monotonic()-t,3),'log_sha256':sha(log),'artifact':str(dst),'artifact_sha256':sha(dst) if dst.exists() else None});(b/'build-commands.json').write_text(json.dumps(rows,indent=2)+'\n');print(mod,r.returncode,rows[-1]['seconds'],flush=True);assert r.returncode==0 and not log.read_bytes(),r.stdout+r.stderr
print('STRICT_SIX_PASS')
