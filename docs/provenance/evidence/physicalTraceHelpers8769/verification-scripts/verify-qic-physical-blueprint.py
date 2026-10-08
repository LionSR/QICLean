from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
root=Path('/Users/siruilu/Local/agentFormalization/QICLean/worktrees/physical-trace-helpers');records=Path('/private/tmp/qic-physical-trace-helpers');out=Path(tempfile.mkdtemp(prefix='qic-physical-trace-blueprint-'));(records/'blueprint-dir').write_text(str(out)+'\n')
for d in ['QICLean','scripts','blueprint']:shutil.copytree(root/d,out/d,ignore=shutil.ignore_patterns('web','print','*.pdf','*.log','*.aux','__pycache__'))
for f in ['QICLean.lean','lakefile.toml','lake-manifest.json','lean-toolchain','tenkz.toml','texra-blueprint.toml']:shutil.copy2(root/f,out/f)
old=Path(Path('/tmp/tnlean-source-corrections/blueprint-dir').read_text().strip());shutil.copytree(old/'.deps/tenkz',out/'.deps/tenkz')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rows=[]
def run(name,cmd,cwd,env=None):
 t=time.monotonic();r=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True);p=out/(name+'.log');p.write_text(r.stdout+r.stderr);rows.append({'name':name,'command':cmd,'cwd':str(cwd),'returncode':r.returncode,'seconds':round(time.monotonic()-t,3),'log_sha256':sha(p)});(out/'commands.json').write_text(json.dumps(rows,indent=2)+'\n');print(name,r.returncode,flush=True);assert r.returncode==0,(r.stdout+r.stderr)[-5000:]
run('sync',['python3',str(root/'scripts/blueprint_lean_sync.py'),'--root',str(out),'--report',str(out/'sync.json'),'--ci','--update-lean-decls'],root)
(out/'source-hashes.json').write_text(json.dumps({str(p.relative_to(out)):sha(p) for p in [*out.rglob('*.lean'),*(out/'blueprint/src').rglob('*.tex')]},indent=2)+'\n')
(out/'blueprint/src/content-focused.tex').write_text('\\input{chapter/ch13_physical_trace_coordinates}\n')
(out/'blueprint/src/focused.tex').write_text('\\def\\blueprinttitle{Partial traces in orthonormal coordinates}\n\\def\\blueprintcontent{content-focused}\n\\input{print}\n')
p=out/'blueprint/src/web.tex';p.write_text(p.read_text().replace('\\input{content}','\\input{content-focused}'))
env=os.environ.copy();env['PATH']='/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin:'+env['PATH'];env['TEXINPUTS']=str(out/'.deps/tenkz/tex')+'//:'
run('pdf',['latexmk','-lualatex','-interaction=nonstopmode','-halt-on-error','focused.tex'],out/'blueprint/src',env)
# Reuse the focused bibliography for the corresponding web document.
shutil.copy2(out/'blueprint/src/focused.bbl',out/'blueprint/src/web.bbl')
run('init-disposable-project',['git','init','-q'],out)
run('web',['/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin/leanblueprint','web'],out/'blueprint',env)
env['PYTHONPATH']='/Users/siruilu/.local/share/uv/tools/texra-blueprint/lib/python3.14/site-packages'
run('browser',['/tmp/qic-regional-blueprint-env/bin/python',str(out/'scripts/test_blueprint_web_render.py'),'--web-root',str(out/'blueprint/web')],out,env)
run('restore-full-declarations',['python3',str(out/'scripts/blueprint_lean_sync.py'),'--root',str(out),'--report',str(out/'sync-final.json'),'--ci','--update-lean-decls'],out)
shutil.copy2(out/'blueprint/lean_decls',out/'full-lean-decls.txt')
run('render',['pdftoppm','-f','3','-singlefile','-scale-to','1400','-png',str(out/'blueprint/src/focused.pdf'),str(out/'theorem-page')],out)
print('BLUEPRINT_COMPLETE',out,flush=True)
