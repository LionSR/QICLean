from pathlib import Path
import hashlib,json,os,subprocess,time
b=Path('/private/tmp/qic-orthonormal-matrix-norm');cfg=json.loads((b/'env.json').read_text());root=Path(cfg['source_root']);env=os.environ.copy();env['LEAN_PATH']=cfg['LEAN_PATH'];rows=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for mod in ['QICLean.Analysis.OrthonormalMatrixNorm','QICLean.Analysis','QICLean']:
 rel=mod.replace('.','/');src=root/(rel+'.lean');dst=Path(cfg['output_root'])/(rel+'.olean');dst.parent.mkdir(parents=True,exist_ok=True);assert not dst.is_symlink()
 cmd=[cfg['lean'],*cfg['options'],'-DwarningAsError=true','-o',str(dst),rel+'.lean'];t=time.monotonic();r=subprocess.run(cmd,cwd=root,env=env,capture_output=True,text=True);log=b/(mod+'.log');log.write_text(r.stdout+r.stderr)
 rows.append({'module':mod,'source_path':rel+'.lean','source_sha256':sha(src),'command':cmd,'cwd':str(root),'LEAN_PATH':cfg['LEAN_PATH'],'returncode':r.returncode,'seconds':round(time.monotonic()-t,3),'log_sha256':sha(log),'artifact':str(dst),'artifact_sha256':sha(dst) if dst.exists() else None});(b/'build-commands.json').write_text(json.dumps(rows,indent=2)+'\n');print(mod,r.returncode,rows[-1]['seconds'],flush=True);assert r.returncode==0,r.stdout+r.stderr
