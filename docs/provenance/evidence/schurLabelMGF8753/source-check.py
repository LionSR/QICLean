from pathlib import Path
import hashlib,json,re,subprocess
r=Path.cwd();p=Path(__file__).resolve().parent
f=json.loads((p/'source-freeze.json').read_text())
for row in f['files']:
 b=(r/row['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==row['sha256'];assert b==subprocess.check_output(['git','show',f['source_revision']+':'+row['path']])
a=(r/'QICLean/Representation/SchurLabelMomentBounds.lean').read_bytes();assert hashlib.sha256(a).hexdigest()=='9845b65181ba4dc234344bc280f08147c4d799d8198abc4be48a7bf9f256e4b0'
assert a==(p/'historical/SchurLabelMomentBounds.lean').read_bytes()
assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafeCast)\b',a.decode())
for row in json.loads((p/'historical-bindings.json').read_text()):assert hashlib.sha256((r/row['path']).read_bytes()).hexdigest()==row['sha256']
reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(p/'bound-axioms.log').read_text(),re.S)
assert [n for n,_ in reports]==json.loads((p/'declarations.json').read_text())
for n,ax in reports:assert [s.strip() for s in ax.split(',')]==['propext','Classical.choice','Quot.sound'],n
print('Exact original mathematical bytes, three source files, historical bindings, two exact standard-only kernel reports and proof integrity verified.')
