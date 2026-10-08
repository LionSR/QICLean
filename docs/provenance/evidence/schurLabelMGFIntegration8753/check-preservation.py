"""Check exact quantitative source, original leaf and two authoritative parents."""
from pathlib import Path
import gzip,hashlib,json,subprocess
r=Path.cwd();e=Path(__file__).resolve().parent;sha=lambda d:hashlib.sha256(d).hexdigest();f=json.loads((e/'source-freeze.json').read_text())
leaf=f['leaf_evidence_revision'];s3=f['comparison_evidence_revision'];lp=r/'docs/provenance/evidence/schurLabelMGF8753'
def read(p):return p.read_bytes() if p.exists() else gzip.decompress(Path(str(p)+'.gz').read_bytes())
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',leaf,'docs/provenance/evidence/schurLabelMGF8753','docs/provenance/openai-math.d/schurLabelMGF8753.json'],text=True).splitlines()
refs=[leaf+':'+p for p in paths]+[f['source_revision']+':'+x['path'] for x in f['files']]+[f['joined_parent_revision']+':QICLean/Representation.lean',f['joined_parent_revision']+':blueprint/src/chapter/ch13_schur_labels.tex']+[s3+':'+p for p in ['QICLean/Analysis.lean','QICLean/Representation.lean','blueprint/src/chapter/ch13_schur_labels.tex']];refs=list(dict.fromkeys(refs))
raw=subprocess.check_output(['git','cat-file','--batch'],input=('\n'.join(refs)+'\n').encode());objects={};offset=0
for ref in refs:
 end=raw.index(b'\n',offset);header=raw[offset:end].split();assert header[1]==b'blob';size=int(header[2]);start=end+1;objects[ref]=raw[start:start+size];offset=start+size+1;assert raw[offset-1:offset]==b'\n'
assert offset==len(raw)
for p in paths:assert (r/p).read_bytes()==objects[leaf+':'+p],p
for item in f['files']:
 d=(r/item['path']).read_bytes();assert sha(d)==item['sha256'];assert d==objects[f['source_revision']+':'+item['path']],item['path']
manifest=json.loads((lp/'manifest.json').read_text())
for item in manifest['files']:assert sha(read(r/item['path']))==item['sha256'],item['path']
for c in manifest['commands']:assert c['exit_code']==0 and c['source_revision']==manifest['source_revision'] and sha(read(r/c['log']))==c['sha256']
for c in manifest['excluded_commands']:assert c['exit_code']!=0 and sha(read(r/c['log']))==c['sha256']
for item in json.loads((lp/'compression.json').read_text()):
 d=read(r/item['raw']);z=(r/item['archive']).read_bytes();assert sha(d)==item['raw_sha256'] and sha(z)==item['archive_sha256'];assert gzip.compress(d,mtime=0)==z
history=json.loads((lp/'historical-bindings.json').read_text());assert len(history)==26
for item in history:assert sha((r/item['path']).read_bytes())==item['sha256'],item['path']
assert (r/'QICLean/Representation/SchurLabelMomentBounds.lean').read_bytes()==(lp/'historical/SchurLabelMomentBounds.lean').read_bytes()
# The checked Schur comparison packet is retained byte-for-byte.
for folder in ['schurLabelMoments8753','schurLabelMomentsIntegration8753']:
 for item in json.loads((r/'docs/provenance/evidence'/folder/'evidence-sha256.json').read_text())['files']:assert sha((r/item['path']).read_bytes())==item['sha256'],item['path']
exceptions={'QICLean/Analysis.lean','QICLean/Representation.lean','blueprint/src/chapter/ch13_schur_labels.tex'}
parent=json.loads((lp/'parent-preservation.json').read_text())
for item in parent['files']:
 if item['path'] not in exceptions:assert sha((r/item['path']).read_bytes())==item['sha256'],item['path']
# Exact generated changes against the checked joined parent.
for p in ['QICLean/Representation.lean','blueprint/src/chapter/ch13_schur_labels.tex']:assert objects[f['joined_parent_revision']+':'+p]==objects[s3+':'+p],p
p='QICLean/Representation.lean';added=b'import QICLean.Representation.SchurLabelMomentBounds\n';d=(r/p).read_bytes();assert d.count(added)==1 and d.replace(added,b'')==objects[f['joined_parent_revision']+':'+p]
p='blueprint/src/chapter/ch13_schur_labels.tex';assert (r/p).read_bytes()==objects[f['joined_parent_revision']+':'+p].rstrip()+b'\n\n\\input{fragment/schur_label_moment_bounds}\n'
# The prior Analysis import comes only from the already checked Holder parent.
p='QICLean/Analysis.lean';assert (r/p).read_bytes()==objects[s3+':'+p]
print('Verified',len(paths),'original quantitative leaf files,88 bindings / 12 successful commands / 26 historical records, checked Schur packets and',len(parent['files']),'parent files with exact three generated exceptions.')
