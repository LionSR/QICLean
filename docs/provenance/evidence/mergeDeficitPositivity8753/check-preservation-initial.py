from pathlib import Path
import json,subprocess
r=Path.cwd();e=r/'docs/provenance/evidence/mergeDeficitPositivity8753';f=json.loads((e/'source-freeze.json').read_text());parent=f['prerequisite_revision'];source=f['source_revision']
def tree(rev):
 return {x.split(b'\t',1)[1].decode():x.split(b'\t',1)[0].split()[-1].decode() for x in subprocess.check_output(['git','ls-tree','-rz',rev]).split(b'\0') if x}
p=tree(parent);s=tree(source);changed={n:[h,s.get(n)] for n,h in p.items() if s.get(n)!=h};assert set(changed)=={'QICLean/Representation/MergeExponential.lean','QICLean/Representation/PairMergeDeficit.lean','docs/tactic_patterns.md'}
for name,extra in [('QICLean/Representation/MergeExponential.lean','import QICLean.Representation.MergeDimensions\n'),('QICLean/Representation/PairMergeDeficit.lean','import QICLean.Representation.MergeExponential\n')]:
 old=subprocess.check_output(['git','show',parent+':'+name],text=True);new=(r/name).read_text();start=new.index('/-\nProvenance-ID: 8753-qic-merge-deficit-positivity-');prefix=new[:start].replace(extra,'');end='end PermutationRepresentation\n' if 'MergeExponential' in name else 'end TensorPower\n';assert prefix.rstrip()+'\n\n'+end==old,name
old=subprocess.check_output(['git','show',parent+':docs/tactic_patterns.md']);assert (r/'docs/tactic_patterns.md').read_bytes().startswith(old)
report={'prerequisite_revision':parent,'source_revision':source,'unchanged_parent_files':len(p)-3,'new_files':sorted(set(s)-set(p)),'existing_module_changes':'One required import and an appended new theorem per module; all original declarations and proof bodies are exact.','all_parent_provenance_preserved':True,'ledger_append_only':True}
(e/'preservation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
