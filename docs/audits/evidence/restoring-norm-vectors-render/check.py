"""Check source/packet integrity with Python's standard library; no render or Lean."""
from pathlib import Path
import argparse, hashlib, json, subprocess

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
parser = argparse.ArgumentParser(description='Verify the historical 54-declaration render against an explicit source commit.')
parser.add_argument('--source-revision', default='2bddde9e49330bab20260b002b7f0ba7de51918e')
args = parser.parse_args()
selected = subprocess.check_output(['git', 'rev-parse', args.source_revision], cwd=ROOT, text=True).strip()
for name, digest in m['source_sha256'].items():
    historical = subprocess.check_output(['git', 'show', selected + ':' + name], cwd=ROOT)
    assert hashlib.sha256(historical).hexdigest() == digest, name
assert v['counts']['public_declarations'] == len(v['declarations']) == 54
assert len(v['new_declarations']) == 25 and len(v['context_declarations']) == 4
assert v['counts']['theorems'] == 34 and v['counts']['definitions'] == 20
assert v['counts']['source_inspected_consumers'] == 30
assert v['counts']['source_inspected_axiom_guards'] == 54
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
print('PASS: historical source ' + selected + ', 54 package links plus 4 context links, all reviewed pages and compact packet integrity')
