"""Verify immutable mathematical sources, parent evidence and the exact inclusion."""
from pathlib import Path
import hashlib,json,subprocess
root=Path.cwd()
folder=Path(__file__).resolve().parent
leaf=root/'docs/provenance/evidence/schmidtBellPrevector8753'
parents=json.loads((leaf/'parents-before-merge.json').read_text())
comparisons=0
paths=set()
for revision, bindings in parents.items():
    for path,digest in bindings.items():
        assert hashlib.sha256((root/path).read_bytes()).hexdigest()==digest,path
        comparisons+=1
        paths.add(path)
x=json.loads((leaf/'evidence-sha256.json').read_text())
for path,digest in x['artifacts_sha256'].items():
    assert hashlib.sha256((root/path).read_bytes()).hexdigest()==digest,path
permitted=['QICLean/Representation.lean','blueprint/src/chapter/ch12_entropy.tex']
changed=subprocess.check_output(['git','diff','--name-only','e9f2d8914a7a93ca022daf566b375fad2b97d797','HEAD'],text=True).splitlines()
assert sorted(changed)==sorted(permitted),changed
assert not subprocess.check_output(['git','diff','--name-only'],text=True).strip()
report=dict(parent_comparisons=comparisons,distinct_parent_paths=len(paths),leaf_artifacts=len(x['artifacts_sha256']),unchanged_parent_bytes=True,unchanged_leaf_bytes=True,only_inclusion_paths=changed,result='passed')
(folder/'preservation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
