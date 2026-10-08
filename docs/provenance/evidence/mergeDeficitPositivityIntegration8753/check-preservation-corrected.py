from pathlib import Path
import json,subprocess,hashlib
r=Path.cwd();e=r/'docs/provenance/evidence/mergeDeficitPositivityIntegration8753';f=json.loads((e/'source-freeze.json').read_text())
def tree(rev):
 return {x.split(b'\t',1)[1].decode():x.split(b'\t',1)[0].split()[-1].decode() for x in subprocess.check_output(['git','ls-tree','-rz',rev]).split(b'\0') if x}
p=tree(f['leaf_evidence_revision']);s=tree(f['source_revision']);changed={n:[h,s.get(n)] for n,h in p.items() if s.get(n)!=h};assert set(changed)==set(f['integration_sha256']),changed
for n in p:
 if n not in changed:b=(r/n).read_bytes();assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==p[n],n
for n,line in [('QICLean/Analysis.lean','import QICLean.Analysis.SpectralProjectionIntertwiner\n'),('blueprint/src/chapter/ch13_schur_labels.tex','\\input{fragment/merge_deficit_positivity}\n')]:
 old=subprocess.check_output(['git','show',f['leaf_evidence_revision']+':'+n]);new=(r/n).read_bytes();assert new.count(line.encode())==1,(n,line);assert new.replace(line.encode(),b'')==old,n
report={'leaf_evidence_revision':f['leaf_evidence_revision'],'inclusion_revision':f['source_revision'],'parent_files_checked':len(p),'unchanged_parent_files':len(p)-2,'exact_two_added_lines':list(changed),'all_leaf_evidence_preserved':True,'all_predecessor_source_and_evidence_preserved':True}
(e/'preservation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
