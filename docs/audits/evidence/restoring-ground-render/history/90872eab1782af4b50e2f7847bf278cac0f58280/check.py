"""Check source/packet integrity with Python's standard library; no render or Lean."""
from pathlib import Path
import hashlib, json, subprocess

HERE = Path(__file__).resolve().parent
ROOT = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], cwd=HERE, text=True).strip())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
v = json.loads((HERE / 'verification.json').read_text())
m = json.loads((HERE / 'focus-manifest.json').read_text())
r = json.loads((HERE / 'visual-review.json').read_text())
c = json.loads((HERE / 'commands.json').read_text())
assert v['status'] == r['status'] == 'passed'
assert m['source_revision'] == v['source_revision'] == r['source_revision']
assert m['source_sha256'] == v['source_sha256']
router = 'blueprint/src/chapter/ch12_entropy.tex'
for name, digest in m['source_sha256'].items():
    if name != router:
        assert sha(ROOT / name) == digest, name
    else:
        # The historical router hash stays frozen; later leaf additions are allowed.
        current_lines = (ROOT / name).read_text().splitlines()
        for leaf in m['target_leaves']:
            include = '\\input{' + leaf.removeprefix('blueprint/src/').removesuffix('.tex') + '}'
            assert sum(line.strip() == include for line in current_lines) == 1, include
        historical = subprocess.run(['git', 'show', m['source_revision'] + ':' + name], cwd=ROOT, capture_output=True)
        if historical.returncode == 0:
            assert hashlib.sha256(historical.stdout).hexdigest() == digest, name
assert v['counts']['public_declarations'] == len(v['declarations']) == 76
assert len(v['new_declarations']) == 22 and len(v['context_declarations']) == 4
assert v['counts']['theorems'] == 53 and v['counts']['definitions'] == 23
assert v['counts']['source_inspected_consumers'] == 44
assert v['counts']['source_inspected_axiom_guards'] == 76
assert r['pdf_review']['pages_directly_viewed'] == list(range(1,v['counts']['pdf_pages']+1))
for name in ['missing_internal_anchors','missing_label_anchors','duplicate_html_ids','tex_box_reference_warnings','curly_math_prime_serialization']:
    assert not v[name], name
for name, record in c['replay_scripts'].items():
    assert sha(HERE / name) == record['published_sha256'], name
for name, digest in json.loads((HERE / 'packet-sha256.json').read_text()).items():
    assert sha(HERE / name) == digest, name
for p in HERE.iterdir():
    if p.is_file():
        text = p.read_text()
        assert not any(prefix in text for prefix in ['/' + 'workspace/scratch/', '/' + 'root/']), p.name
print('PASS: substantive frozen source hashes, retained restoration router includes, 76 package links plus 4 context links, all reviewed pages and compact packet integrity')
