from pathlib import Path
import gzip,hashlib,json,shutil,subprocess
root=Path('/Users/siruilu/Local/agentFormalization/QICLean/worktrees/orthonormal-matrix-norm');b=Path('/private/tmp/qic-orthonormal-matrix-norm');bp=Path((b/'blueprint-dir').read_text().strip());out=root/'docs/provenance/evidence/orthonormalMatrixNorm8769';rev='361713b3a0fc203724a720d34b980d4e12320035';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=json.loads((bp/'source-hashes.json').read_text());proc=subprocess.Popen(['git','-C',str(root),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
for p,h in paths.items():
 proc.stdin.write((rev+':'+p+'\n').encode());proc.stdin.flush();header=proc.stdout.readline().split();assert len(header)==3,(p,header);data=proc.stdout.read(int(header[2]));assert proc.stdout.read(1)==b'\n';assert hashlib.sha256(data).hexdigest()==h,p
proc.stdin.close();assert proc.wait()==0
(bp/'source-pin.json').write_text(json.dumps({'source_revision':rev,'checked_files':len(paths),'all_source_hashes_match':True,'visual_review':{'pdf_page':3,'result':'pass','notes':'The complete theorem and proof are readable; no overflow or undefined references.'}},indent=2)+'\n')
for sub in ['declaration-check','blueprint']:(out/sub).mkdir(exist_ok=True)
for p in (b/'declaration-check').iterdir():
 if p.name=='lean_declarations.txt':(out/'declaration-check'/(p.name+'.gz')).write_bytes(gzip.compress(p.read_bytes(),mtime=0))
 else:shutil.copy2(p,out/'declaration-check'/p.name)
for p in ['commands.json','initial-commands.json','source-pin.json','theorem-page.png']:shutil.copy2(bp/p,out/'blueprint'/p)
for p in ['source-hashes.json','sync.json','sync-final.json','full-lean-decls.txt']:(out/'blueprint'/(p+'.gz')).write_bytes(gzip.compress((bp/p).read_bytes(),mtime=0))
for p in bp.glob('*.log'):(out/'blueprint'/(p.name+'.gz')).write_bytes(gzip.compress(p.read_bytes(),mtime=0))
(out/'blueprint/final-tex.log.gz').write_bytes(gzip.compress((bp/'blueprint/src/focused.log').read_bytes(),mtime=0));shutil.copy2(bp/'blueprint/src/focused.pdf',out/'blueprint/focused.pdf')
(out/'blueprint/render-inputs').mkdir(exist_ok=True)
for name in ['focused.tex','content-focused.tex','web.tex']:shutil.copy2(bp/'blueprint/src'/name,out/'blueprint/render-inputs'/name)
for p in ['verify-orthonormal-matrix-blueprint.py','finish-orthonormal-matrix-blueprint.py','complete-orthonormal-blueprint.py']:shutil.copy2(Path('/tmp')/p,out/'blueprint'/p)
shutil.copy2(Path(__file__),out/'blueprint/package-blueprint.py')
print('BLUEPRINT_PACKAGED',len(paths))
