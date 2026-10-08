"""Check committed source bindings, actual outputs, preservation and reader evidence."""
from pathlib import Path
import gzip,hashlib,json,subprocess
root=Path.cwd()
p=Path(__file__).resolve().parent
sha=lambda data:hashlib.sha256(data).hexdigest()
f=json.loads((p/'source-freeze.json').read_text())
for name,digest in f['production_sha256'].items():
    assert sha((root/name).read_bytes())==digest,name
    assert sha(subprocess.check_output(['git','show',f['source_revision']+':'+name]))==digest,name
for name,digest in json.loads((p/'evidence-sha256.json').read_text())['artifacts_sha256'].items():
    assert sha((root/name).read_bytes())==digest,name
records=[]
for path in sorted(p.glob('*-exit.json')):
    if path.name.startswith('initial-folded-'): continue
    r=json.loads(path.read_text());records.append(r)
    assert r['exit_code']==0,path
    assert r['source_revision']==f['source_revision'],path
    raw=(root/r['log']).read_bytes();assert sha(raw)==r['sha256'],path
    if r['compressed']:
        assert raw[4:8]==b'\x00'*4,path
        raw=gzip.decompress(raw)
    assert sha(raw)==r['uncompressed_sha256'],path
    assert len(raw)==r['uncompressed_bytes'],path
c=json.loads((p/'pdf-text-compression.json').read_text())
g=(root/c['path']).read_bytes();assert sha(g)==c['sha256']
assert g[4:8]==b'\x00'*4 and sha(gzip.decompress(g))==c['uncompressed_sha256']
n=json.loads((p/'native-targets.json').read_text())
assert n['native_declarations']==3315 and n['fragment_declarations']==61
assert len(n['active_fragments'])==15 and n['contains_all_two_owned']
assert sha((p/'NativeDeclarations.txt').read_bytes())==n['native_list_sha256']
a=json.loads((p/'pdf-inspection.json').read_text())
assert sha((p/a['pdf']).read_bytes())==a['pdf_sha256'] and a['visually_inspected']
assert a['pages']==436 and a['inspected_physical_pages']==[415,416]
m=json.loads((p/'mobile-equations.json').read_text())
assert len(m['equations'])==7 and all(e['clientWidth']>0 for e in m['equations'])
assert all(e['scrollLeft']>0 for e in m['equations'] if e['scrollWidth']>e['clientWidth']+1)
w=json.loads((p/'whole-web.log').read_text())
assert w=={'pages':38,'typeset':37769}
parents=json.loads((root/'docs/provenance/evidence/schmidtBellPrevector8753/parents-before-merge.json').read_text())
for revision,bindings in parents.items():
    for name,digest in bindings.items(): assert sha((root/name).read_bytes())==digest,name
leaf=json.loads((root/'docs/provenance/evidence/schmidtBellPrevector8753/evidence-sha256.json').read_text())
for name,digest in leaf['artifacts_sha256'].items(): assert sha((root/name).read_bytes())==digest,name
print('Passed: immutable source and leaf/parent bytes, all actual final exits and dual output hashes, complete native inventory, PDF and all seven open-proof mobile displays, whole-web regression.')
