from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent
for name,argv in [('guard',['python3',str(p/'mathlib-guard.py')]),('build',['lake','build'])]:
 q=subprocess.run([sys.executable,str(p/'capture.py'),name,*argv])
 if q.returncode:raise SystemExit(q.returncode)
