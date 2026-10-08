from pathlib import Path
import subprocess,sys,shutil
p=Path(__file__).resolve().parent
checks=[('blueprint-sync-revised',['python3','scripts/blueprint_lean_sync.py','--root','.','--update-lean-decls']),('pdf-revised',['python3','-c','import os,subprocess,sys;os.chdir("blueprint");sys.exit(subprocess.call(["leanblueprint","pdf"]))']),('bbl-revised',['texra-blueprint','bbl']),('web-revised',['texra-blueprint','web']),('native-revised',['lake','exe','checkdecls','blueprint/lean_decls'])]
for name,argv in checks:
 result=subprocess.run([sys.executable,str(p/'capture.py'),name,*argv])
 if result.returncode:raise SystemExit(result.returncode)
shutil.copyfile('blueprint/lean_decls',p/'NativeDeclarations-revised.txt');shutil.copyfile('blueprint/print/print.pdf',p/'joint-density-revised-blueprint.pdf')
for name,argv in [('native-targets-revised',['python3',str(p/'check-native-targets-revised.py')]),('focused-web-revised',['/Users/siruilu/miniforge3/bin/python3',str(p/'inspect-web-revised.py')]),('whole-web-revised',['/Users/siruilu/miniforge3/bin/python3','scripts/test_blueprint_web_render.py','--web-root','blueprint/web'])]:
 result=subprocess.run([sys.executable,str(p/'capture.py'),name,*argv])
 if result.returncode:raise SystemExit(result.returncode)
