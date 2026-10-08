"""Check frozen source, historical text and exact Holder-parent preservation."""
from pathlib import Path
import hashlib,json,subprocess
r=Path.cwd();e=Path(__file__).resolve().parent;sha=lambda d:hashlib.sha256(d).hexdigest()
freeze=json.loads((e/'source-freeze.json').read_text())
for item in freeze['files']:
 d=(r/item['path']).read_bytes();assert sha(d)==item['sha256'];assert d==subprocess.check_output(['git','show',freeze['source_revision']+':'+item['path']],cwd=r)
history=json.loads((e/'historical-bindings.json').read_text())['files'];assert len(history)==22
for item in history:assert sha((r/item['archived_path']).read_bytes())==item['sha256'],item['archived_path']
assert (r/'QICLean/Representation/SchurLabelMoments.lean').read_bytes()==(e/'historical/SchurLabelMoments.lean').read_bytes()
parent='d21af4657ca03bf6a71aa738d72efd71f5eb7521'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',parent,'QICLean','docs/provenance/evidence/weightedTraceHolder8753','docs/provenance/evidence/weightedTraceHolderIntegration8753','docs/provenance/openai-math.d'],cwd=r,text=True).splitlines()
for path in paths:
 current=(r/path).read_bytes();before=subprocess.check_output(['git','show',parent+':'+path],cwd=r)
 if path=='QICLean/Representation.lean':
  added=b'import QICLean.Representation.SchurLabelMoments\n'
  assert current==before or (current.count(added)==1 and current.replace(added,b'')==before),path
 else:assert current==before,path
out={'frozen_revision':freeze['source_revision'],'external_whole_lean_sha256':sha((r/'QICLean/Representation/SchurLabelMoments.lean').read_bytes()),'historical_text_records':22,'holder_parent_revision':parent,'mechanically_preserved_parent_files':len(paths),'shared_source_exception':{'path':'QICLean/Representation.lean','authoritative_parent':parent,'only_permitted_addition':'import QICLean.Representation.SchurLabelMoments'},'ledger_authority':freeze['source_revision'],'scope':'Byte preservation only; no unchanged parent semantic audit repeated.'}
(e/'source-comparison.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
