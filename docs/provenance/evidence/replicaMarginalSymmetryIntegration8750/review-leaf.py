from pathlib import Path
import hashlib,json,subprocess,sys
r=Path.cwd();p=Path(__file__).resolve().parent;leaf=r/'docs/provenance/evidence/replicaMarginalSymmetry8750'
subprocess.run(['python3',str(leaf/'validate-manifest.py')],check=True)
tracked=set(subprocess.check_output(['git','ls-files'],text=True).splitlines())
j=json.loads((leaf/'evidence-sha256.json').read_text());assert all(e['path'] in tracked for e in j['files'])
subprocess.run(['/Users/siruilu/miniforge3/bin/python3',str(leaf/'validate-owned.py'),'/Users/siruilu/Local/agentFormalization/TNLean'],check=True)
print('All',len(j['files']),'owned leaf files are tracked, including original helper failure records; mathematical and signature review passes.')
