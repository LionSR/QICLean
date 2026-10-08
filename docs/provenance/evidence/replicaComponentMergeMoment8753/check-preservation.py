"""Verify immutable prerequisites and the four-file source extension."""
from pathlib import Path
import json,subprocess
r=Path.cwd();e=Path(__file__).resolve().parent;f=json.loads((e/'source-freeze.json').read_text())
def tree(rev):
 records=subprocess.check_output(['git','ls-tree','-r','-z',rev]).split(b'\0')
 return {p.decode():meta.decode().split()[2] for x in records if x for meta,p in [x.split(b'\t',1)]}
parent=tree(f['prerequisite_revision']);source=tree(f['source_revision'])
changed=[p for p,h in parent.items() if source.get(p)!=h]
assert changed==['docs/tactic_patterns.md'],changed
old=subprocess.check_output(['git','show',f['prerequisite_revision']+':docs/tactic_patterns.md'])
new=subprocess.check_output(['git','show',f['source_revision']+':docs/tactic_patterns.md'])
assert new.startswith(old)
added=sorted(set(source)-set(parent));assert len(added)==3,added
report={'parent_revision':f['prerequisite_revision'],'source_revision':f['source_revision'],'unchanged_parent_files':len(parent)-1,'append_only':['docs/tactic_patterns.md'],'added_files':added,'no_parent_proof_or_provenance_changed':True}
(e/'source-preservation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
