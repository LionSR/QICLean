from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent
for name,argv in [('cache',['lake','exe','cache','get']),('guard',['python3',str(p/'mathlib-guard.py')]),('imports',['python3','scripts/generate_import_aggregators.py','--check']),('build',['lake','build'])]:
 q=subprocess.run([sys.executable,str(p/'capture.py'),name,*argv])
 if q.returncode:raise SystemExit(q.returncode)
