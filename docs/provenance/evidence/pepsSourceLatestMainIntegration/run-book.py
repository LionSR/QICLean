from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent
for name,argv in [('blueprint-sync',['python3','scripts/blueprint_lean_sync.py','--root','.','--update-lean-decls']),('pdf',['python3','-c','import os,subprocess,sys;os.chdir("blueprint");sys.exit(subprocess.call(["leanblueprint","pdf"]))']),('bbl',['texra-blueprint','bbl']),('web',['texra-blueprint','web']),('native',['lake','exe','checkdecls','blueprint/lean_decls']),('whole-web',['/Users/siruilu/miniforge3/bin/python3','scripts/test_blueprint_web_render.py','--web-root','blueprint/web'])]:
 result=subprocess.run([sys.executable,str(p/'capture.py'),name,*argv])
 if result.returncode:raise SystemExit(result.returncode)
