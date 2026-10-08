from pathlib import Path
import subprocess,sys,json
p=Path(__file__).resolve().parent
for item in json.loads((p/'ci-source-regressions.json').read_text())['tests']:
 result=subprocess.run([sys.executable,str(p/'capture.py'),item['name'],*item['argv']])
 if result.returncode:raise SystemExit(result.returncode)
