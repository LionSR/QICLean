from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent
for folder in ['8769-foundations-integration','8769-source-error','8769-source-reduction','8769-source-bridges']:
 q=subprocess.run([sys.executable,str(p/'capture.py'),'provenance-recheck-'+folder,'/Users/siruilu/miniforge3/bin/python3','docs/provenance/evidence/'+folder+'/source-audit.py',str(p/'provenance-policy.py')])
 if q.returncode:raise SystemExit(q.returncode)
