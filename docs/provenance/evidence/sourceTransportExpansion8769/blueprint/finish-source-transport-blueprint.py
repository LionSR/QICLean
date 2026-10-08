from pathlib import Path
import hashlib,json,os,shutil,subprocess,time
b=Path('/private/tmp/qic-source-transport-expansion');out=Path((b/'blueprint-dir').read_text().strip());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rows=json.loads((out/'commands.json').read_text())
for name in ['pdf','web','browser','render']:
 p=out/(name+'.log');shutil.copy2(p,out/('initial-'+name+'.log'))
 for r in rows:
  if r['name']==name:r['name']='initial-'+name
shutil.copy2(out/'blueprint/src/focused.log',out/'initial-tex.log')
src=out/'blueprint/src';a=(src/'chapter/ch13_source_error.tex').read_text();sample=a[a.index(r'\begin{definition}[Sampled Schmidt-source operators]'):a.index(r'\begin{theorem}[Unbiasedness and actual correction-entry covariance]')]
a=(src/'chapter/ch13_source_reduction.tex').read_text();ambient=a[a.index(r'\begin{definition}[Transport through four endpoint maps]'):a.index(r'\begin{theorem}[Unbiased ambient product sources]')]
(src/'transport-excerpt.tex').write_text(sample+ambient)
def run(name,cmd,cwd,env=None):
 t=time.monotonic();r=subprocess.run(cmd,cwd=cwd,env=env,capture_output=True,text=True);p=out/(name+'.log');p.write_text(r.stdout+r.stderr);rows.append({'name':name,'command':cmd,'cwd':str(cwd),'returncode':r.returncode,'seconds':round(time.monotonic()-t,3),'log_sha256':sha(p)});(out/'commands.json').write_text(json.dumps(rows,indent=2)+'\n');print(name,r.returncode,flush=True);assert r.returncode==0,(r.stdout+r.stderr)[-5000:]
env=os.environ.copy();env['PATH']='/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin:'+env['PATH'];env['TEXINPUTS']=str(out/'.deps/tenkz/tex')+'//:'
run('pdf',['latexmk','-lualatex','-interaction=nonstopmode','-halt-on-error','focused.tex'],src,env)
shutil.copy2(src/'focused.bbl',src/'web.bbl')
run('web',['/Users/siruilu/.local/share/uv/tools/texra-blueprint/bin/leanblueprint','web'],out/'blueprint',env)
env['PYTHONPATH']='/Users/siruilu/.local/share/uv/tools/texra-blueprint/lib/python3.14/site-packages'
run('browser',['/tmp/qic-regional-blueprint-env/bin/python',str(out/'scripts/test_blueprint_web_render.py'),'--web-root',str(out/'blueprint/web')],out,env)
run('restore-full-declarations',['python3',str(out/'scripts/blueprint_lean_sync.py'),'--root',str(out),'--report',str(out/'sync-final.json'),'--ci','--update-lean-decls'],out)
shutil.copy2(out/'blueprint/lean_decls',out/'full-lean-decls.txt')
run('pdf-text',['pdftotext','-layout',str(src/'focused.pdf'),str(out/'focused.txt')],out)
print(out)
