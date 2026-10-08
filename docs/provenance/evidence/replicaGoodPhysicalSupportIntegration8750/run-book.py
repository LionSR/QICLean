from pathlib import Path
import subprocess,sys,shutil
p=Path(__file__).resolve().parent
checks=[('tenkz',['python3','scripts/fetch_tenkz.py']),('blueprint-sync',['python3','scripts/blueprint_lean_sync.py','--root','.','--update-lean-decls']),('pdf',['python3','-c','import os,subprocess,sys;os.chdir("blueprint");sys.exit(subprocess.call(["leanblueprint","pdf"]))']),('bbl',['texra-blueprint','bbl']),('web',['texra-blueprint','web']),('native',['lake','exe','checkdecls','blueprint/lean_decls'])]
for name,argv in checks:
 result=subprocess.run([sys.executable,str(p/'capture.py'),name,*argv])
 if result.returncode:raise SystemExit(result.returncode)
shutil.copyfile('blueprint/lean_decls',p/'NativeDeclarations.txt');shutil.copyfile('blueprint/print/print.pdf',p/'physical-support-blueprint.pdf')
for name,argv in [('native-targets',['python3',str(p/'check-native-targets.py')]),('render',['/Users/siruilu/miniforge3/bin/python3',str(p/'render-pdf.py')]),('focused-web',['/Users/siruilu/miniforge3/bin/python3',str(p/'inspect-web.py')]),('whole-web',['/Users/siruilu/miniforge3/bin/python3','scripts/test_blueprint_web_render.py','--web-root','blueprint/web'])]:
 result=subprocess.run([sys.executable,str(p/'capture.py'),name,*argv])
 if result.returncode:raise SystemExit(result.returncode)
