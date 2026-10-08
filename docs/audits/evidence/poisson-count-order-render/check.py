"""Verify the source-bound text packet using the standard library; no Lean or render."""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--source-revision', help='Check this historical revision instead of current files.')
args = parser.parse_args()
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def read_json(name):
    return json.loads((HERE / name).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


m = read_json('focus-manifest.json')
v = read_json('verification.json')
r = read_json('visual-review.json')
c = read_json('commands.json')
assert v['status'] == r['status'] == 'passed'
assert m['source_revision'] == v['source_revision'] == r['source_revision'] == c['source_revision']
assert m['source_sha256'] == v['source_sha256']
assert c['public_source']['revision'] == m['source_revision']
assert c['public_source']['url'].endswith('/commit/' + m['source_revision'])
for name, digest in (m['source_sha256'] | m['fixture_source_sha256']).items():
    data = subprocess.check_output(['git', 'show', args.source_revision + ':' + name], cwd=ROOT) if args.source_revision else (ROOT / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == digest, name
expected = {
    'production_modules': 5, 'production_lines': 456,
    'explicitly_named_public_declarations': 33, 'context_public_declarations': 20,
    'all_linked_public_constants': 53, 'blueprint_entries': 15, 'proofs': 12,
    'checked_markers': 27, 'equation_labels': 11, 'all_labels': 31,
    'pdf_pages': 7, 'html_pages': 6, 'pdf_declaration_links': 53,
    'html_chapter_declaration_links': 53, 'html_all_declaration_links': 159,
    'explicit_dependency_edges': 30, 'diagrams': 0,
}
for name, count in expected.items():
    assert v['counts'][name] == count, name
assert len(v['target_declarations']) == len(set(v['target_declarations'])) == 33
assert Counter(v['declarations']) == Counter(v['target_declarations'] + v['context_declarations'])
assert len(v['artifact_sha256']) == 17
assert r['pdf_review']['pages_directly_viewed'] == list(range(1, 8))
assert r['web_review']['static_pages_checked'] == v['html_files']
assert not r['web_review']['live_browser_runtime_pass_claimed']
for name in ['unlinked_public_constants', 'missing_internal_anchors', 'missing_label_anchors',
             'duplicate_html_ids', 'tex_box_reference_warnings', 'curly_math_prime_serialization']:
    assert not v[name], name
for graph in v['dependency_graphs'].values():
    assert graph['nodes'] == 15 and graph['edges'] == 18
    assert graph['reachability_matches_explicit_uses']
    assert graph['rendered_edge_styles_match_dependency_placement']
for name, record in c['replay_scripts'].items():
    assert sha(HERE / name) == record['published_sha256'], name
for name, digest in read_json('packet-sha256.json').items():
    assert sha(HERE / name) == digest, name
for path in HERE.iterdir():
    if path.is_file():
        text = path.read_text()
        assert not any(prefix in text for prefix in ['/' + 'workspace/scratch/', '/' + 'root/']), path.name
print('PASS: 5 target modules, 33 target and 20 prerequisite public links, 31 labels, 7 reviewed PDF pages, 6 static HTML pages, 17 artifact hashes, public source binding, and text-packet integrity')
