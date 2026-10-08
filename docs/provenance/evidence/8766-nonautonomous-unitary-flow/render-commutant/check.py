"""Verify committed source hashes and focused-render record consistency."""
from pathlib import Path
import hashlib, json, subprocess
p = Path(__file__).resolve().parent
root = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], cwd=p, text=True).strip())
v = json.loads((p / 'verification.json').read_text())
assert v['status'] == 'passed'
for name, digest in v['source_sha256'].items():
    assert hashlib.sha256((root / name).read_bytes()).hexdigest() == digest, name
assert v['counts']['public_declarations'] == 19
assert v['counts']['pdf_pages'] == 9
assert len(v['declarations']) == 19
for key in ['missing_internal_anchors', 'duplicate_html_ids', 'tex_box_reference_warnings', 'curly_math_prime_serialization']:
    assert not v[key], key
c = json.loads((p / 'commands.json').read_text())
for name, info in c['replay_scripts'].items():
    assert hashlib.sha256((p / name).read_bytes()).hexdigest() == info['published_sha256'], name
print('PASS: source hashes, 19 declaration links, 9-page render and replay scripts')
