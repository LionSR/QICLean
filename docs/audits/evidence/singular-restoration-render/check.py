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
parser = argparse.ArgumentParser(description='Check the historical 29-declaration render against a selected public ancestor.')
parser.add_argument('--source-revision', default='2bddde9e49330bab20260b002b7f0ba7de51918e')
selected = subprocess.check_output(['git', 'rev-parse', parser.parse_args().source_revision], cwd=ROOT, text=True).strip()
router = 'blueprint/src/chapter/ch12_entropy.tex'
for name, digest in m['source_sha256'].items():
    historical = subprocess.check_output(['git', 'show', selected + ':' + name], cwd=ROOT)
    if name != router:
        assert hashlib.sha256(historical).hexdigest() == digest, name
    else:
        # The public ancestor has extra leaves; the frozen router record stays unchanged.
        lines = historical.decode().splitlines()
        for leaf in m['target_leaves']:
            include = '\\input{' + leaf.removeprefix('blueprint/src/').removesuffix('.tex') + '}'
            assert sum(line.strip() == include for line in lines) == 1, include
for name, digest in m['fixture_source_sha256'].items():
    assert hashlib.sha256(subprocess.check_output(['git', 'show', selected + ':' + name], cwd=ROOT)).hexdigest() == digest, name
assert v['counts']['public_declarations'] == len(v['declarations']) == 29
assert v['counts']['theorems'] == 17 and v['counts']['definitions'] == 12
assert v['counts']['source_inspected_consumers'] == 15
assert v['counts']['source_inspected_axiom_guards'] == 29
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
print('PASS: historical core source ' + selected + ', exact fixture/substantive hashes, retained core includes and compact packet integrity')
