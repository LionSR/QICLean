"""Validate source continuity, complete checks and mathematical reader evidence."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess
import sys

root = Path.cwd()
folder = Path(__file__).resolve().parent
sha = lambda data: hashlib.sha256(data).hexdigest()
freeze = json.loads((folder / 'source-freeze.json').read_text())
for path, digest in freeze['production_sha256'].items():
    assert sha((root / path).read_bytes()) == digest, path
    assert sha(subprocess.check_output(['git', 'show', freeze['source_revision']+':'+path])) == digest
leaf = root / 'docs/provenance/evidence/compatiblePhysicalLabel8753'
leaf_manifest = json.loads((leaf / 'manifest.json').read_text())
for path, item in leaf_manifest['artifacts'].items():
    assert sha((root / path).read_bytes()) == item['sha256'], path
    assert (root / path).read_bytes() == subprocess.check_output(['git', 'show', '925b12b6:'+path])
assert (folder / 'axioms.log').read_bytes() == (leaf / 'axioms.log').read_bytes()
for p in sorted(folder.glob('*-exit.json')):
    if p.name == 'validation-exit.json':
        continue
    record = json.loads(p.read_text())
    assert record['source_revision'] == freeze['source_revision'] and record['exit_code'] == 0, p
    raw = (root / record['log']).read_bytes()
    assert sha(raw) == record['sha256'], p
    if record['compressed']:
        assert raw[4:8] == b'\0'*4, p
        raw = gzip.decompress(raw)
    assert sha(raw) == record['uncompressed_sha256'] and len(raw) == record['uncompressed_bytes'], p
full = gzip.decompress((folder / 'full-build.log.gz').read_bytes())
assert b'Build completed successfully (9824 jobs).' in full
assert not re.search(rb'Built Mathlib(?:\.|\s)', full)
subprocess.run(['python3', str(folder / 'check-preservation.py')], check=True)
pdf = json.loads((folder / 'pdf-inspection.json').read_text())
assert pdf['visual_review'] == 'passed' and pdf['inspected_physical_pages']
archive = root / pdf['archived_pdf_gzip']
assert sha(archive.read_bytes()) == pdf['archived_pdf_gzip_sha256']
assert sha(gzip.decompress(archive.read_bytes())) == pdf['pdf_sha256']
assert sha(gzip.decompress((folder / 'complete-book-text.txt.gz').read_bytes())) == pdf['text_sha256']
native = json.loads((folder / 'native-targets.json').read_text())
assert native['contains_all_five_owned'] and len(native['owned_declarations']) == 5
assert native['contains_all_active_fragment_targets']
assert sha((folder / 'NativeDeclarations.txt').read_bytes()) == native['native_list_sha256']
assert all(len(values) == 1 for values in native['rendered_doc_links'].values())
web = json.loads((folder / 'web-inspection.json').read_text())
assert web['visual_review'] == 'passed'
mobile = json.loads((folder / 'mobile-equations.json').read_text())
assert mobile['result'] == 'passed' and len(mobile['equations']) == 3
assert all(item['clientWidth'] > 0 for item in mobile['equations'])
assert all(item['scrollLeft'] > 0 for item in mobile['equations']
           if item['scrollWidth'] > item['clientWidth']+1)
whole = json.loads((folder / 'whole-web.log').read_text())
assert whole['pages'] > 0 and whole['typeset'] > 0
if '--git' in sys.argv:
    manifest = json.loads((folder / 'manifest.json').read_text())
    for path, item in manifest['artifacts'].items():
        assert sha((root / path).read_bytes()) == item['sha256'], path
        assert sha(subprocess.check_output(['git', 'show', 'HEAD:'+path])) == item['sha256'], path
print('Passed: frozen source and parent/leaf bytes, actual exits and dual hashes, full9824, five exact stock reports, complete book, all native fragment targets and five owned links, desktop/mobile full proofs and all three displays, whole-web regression.')
