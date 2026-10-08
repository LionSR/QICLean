from pathlib import Path
import hashlib,json,os,shutil,subprocess,time
b=Path('/private/tmp/qic-orthonormal-matrix-norm');out=Path((b/'blueprint-dir').read_text().strip());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rows=json.loads((out/'commands.json').read_text());shutil.copy2(out/'browser.log',out/'initial-browser.log');rows[-1]['name']='initial-browser';rows[-1]['log']='initial-browser.log'
def run(name,cmd,cwd,env=None):
 t=time.monotonic();r=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True);p=out/(name+'.log');p.write_text(r.stdout+r.stderr);rows.append({'name':name,'command':cmd,'cwd':str(cwd),'returncode':r.returncode,'seconds':round(time.monotonic()-t,3),'log_sha256':sha(p)});(out/'commands.json').write_text(json.dumps(rows,indent=2)+'\n');print(name,r.returncode,flush=True);assert r.returncode==0,(r.stdout+r.stderr)[-5000:]
env=os.environ.copy();env['PYTHONPATH']='/Users/siruilu/.local/share/uv/tools/texra-blueprint/lib/python3.14/site-packages'
run('browser',['/tmp/qic-regional-blueprint-env/bin/python',str(out/'scripts/test_blueprint_web_render.py'),'--web-root',str(out/'blueprint/web')],out,env)
run('render',['pdftoppm','-f','3','-singlefile','-scale-to','1400','-png',str(out/'blueprint/src/focused.pdf'),str(out/'theorem-page')],out)
# leanblueprint web rewrites lean_decls for its focused document; restore the full list.
run('restore-full-declarations',['python3',str(out/'scripts/blueprint_lean_sync.py'),'--root',str(out),'--report',str(out/'sync-final.json'),'--ci','--update-lean-decls'],out)
shutil.copy2(out/'blueprint/lean_decls',out/'full-lean-decls.txt');print('BLUEPRINT_COMPLETE',out,flush=True)
