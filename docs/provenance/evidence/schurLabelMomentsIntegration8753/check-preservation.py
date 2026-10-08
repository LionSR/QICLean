"""Compare the exact frozen files by one batch Git-object read."""
from pathlib import Path
import hashlib,json,subprocess
r=Path.cwd();e=Path(__file__).resolve().parent;sha=lambda d:hashlib.sha256(d).hexdigest()
f=json.loads((e/'source-freeze.json').read_text());leaf=f['leaf_evidence_revision'];parent='d21af4657ca03bf6a71aa738d72efd71f5eb7521'
leaf_paths=subprocess.check_output(['git','ls-tree','-r','--name-only',leaf,'docs/provenance/evidence/schurLabelMoments8753','docs/provenance/openai-math.d/schurLabelMoments8753.json'],text=True).splitlines()
parent_paths=subprocess.check_output(['git','ls-tree','-r','--name-only',parent,'QICLean','docs/provenance/evidence/weightedTraceHolder8753','docs/provenance/evidence/weightedTraceHolderIntegration8753','docs/provenance/openai-math.d'],text=True).splitlines()
refs=[leaf+':'+p for p in leaf_paths]+[parent+':'+p for p in parent_paths]+[f['source_revision']+':'+x['path'] for x in f['files']]+[leaf+':QICLean/Representation.lean',leaf+':blueprint/src/chapter/ch13_schur_labels.tex'];refs=list(dict.fromkeys(refs))
raw=subprocess.check_output(['git','cat-file','--batch'],input=('\n'.join(refs)+'\n').encode());objects={};offset=0
for ref in refs:
 end=raw.index(b'\n',offset);header=raw[offset:end].split();assert header[1]==b'blob',ref;size=int(header[2]);start=end+1;objects[ref]=raw[start:start+size];offset=start+size+1;assert raw[offset-1:offset]==b'\n'
assert offset==len(raw)
for path in leaf_paths:assert (r/path).read_bytes()==objects[leaf+':'+path],path
for row in json.loads((e/'individual-source-preservation.json').read_text())['files']:assert sha((r/row['path']).read_bytes())==row['sha256'],row['path']
for row in f['files']:
 d=(r/row['path']).read_bytes();assert sha(d)==row['sha256'];assert d==objects[f['source_revision']+':'+row['path']],row['path']
for path in parent_paths:
 d=(r/path).read_bytes();before=objects[parent+':'+path]
 if path=='QICLean/Representation.lean':
  added=b'import QICLean.Representation.SchurLabelMoments\n';assert d.count(added)==1 and d.replace(added,b'')==before,path
 else:assert d==before,path
p='QICLean/Representation.lean';added=b'import QICLean.Representation.SchurLabelMoments\n';assert (r/p).read_bytes().replace(added,b'')==objects[leaf+':'+p]
p='blueprint/src/chapter/ch13_schur_labels.tex';assert (r/p).read_bytes()==objects[leaf+':'+p].rstrip()+b'\n\n\input{fragment/schur_label_moments}\n'
leaf_e=r/'docs/provenance/evidence/schurLabelMoments8753'
for row in json.loads((leaf_e/'evidence-sha256.json').read_text())['files']:assert sha((r/row['path']).read_bytes())==row['sha256'],row['path']
history=json.loads((leaf_e/'historical-bindings.json').read_text())['files'];assert len(history)==22
for row in history:assert sha((r/row['archived_path']).read_bytes())==row['sha256'],row['archived_path']
assert (r/'QICLean/Representation/SchurLabelMoments.lean').read_bytes()==(leaf_e/'historical/SchurLabelMoments.lean').read_bytes()
print('Batch-verified',len(leaf_paths),'original leaf files,',len(parent_paths),'Holder-parent files and all frozen source/exposition bytes; exact generated import/chapter exceptions only. No inherited semantic audit repeated.')
