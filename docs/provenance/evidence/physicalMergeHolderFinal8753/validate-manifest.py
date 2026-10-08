"""Validate the frozen actual five-factor inequality and its own evidence."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess
import sys

root = Path.cwd()
folder = Path(__file__).resolve().parent
sha = lambda b: hashlib.sha256(b).hexdigest()
freeze = json.loads((folder / 'source-freeze.json').read_text())
for path, digest in freeze['production_sha256'].items():
    assert sha((root / path).read_bytes()) == digest, path
    assert sha(subprocess.check_output(['git', 'show', freeze['source_revision']+':'+path])) == digest, path
for p in sorted(folder.glob('*-exit.json')):
    if p.name == 'validation-exit.json':
        continue
    item = json.loads(p.read_text())
    assert item['source_revision'] == freeze['source_revision'] and item['exit_code'] == 0, p
    raw = (root / item['log']).read_bytes()
    assert sha(raw) == item['sha256'], p
    if item['compressed']:
        assert raw[4:8] == b'\0'*4
        raw = gzip.decompress(raw)
    assert sha(raw) == item['uncompressed_sha256'] and len(raw) == item['uncompressed_bytes'], p
assert b'Build completed successfully (3499 jobs).' in (folder / 'target.log').read_bytes()
assert not re.search(rb'Built Mathlib(?:\.|\s)', (folder / 'target.log').read_bytes())
assert not (folder / 'strict-source.log').read_bytes()
raw = (folder / 'axioms.log').read_text()
name = 'TensorPower.re_trace_mul_exp_mergeDeficits_sub_physicalMergeDeficit_le'
reports = re.findall(r"'"+re.escape(name)+r"' depends on axioms:\s*\[([^]]*)\]", raw)
assert len(reports) == 1
assert {x.strip() for x in reports[0].split(',')} == {'propext', 'Classical.choice', 'Quot.sound'}
assert (folder / 'axioms.log').read_bytes() == (root / 'docs/provenance/evidence/physicalMergeHolder8753/axioms.log').read_bytes()
assert subprocess.check_output(['git', 'rev-parse', 'feat/area-law-compatible-physical-label'], text=True).strip() == '1a61097225a153adeb32270edb0778363e2ddfb1'
assert sha((root / 'QICLean/Representation/CompatiblePhysicalLabel.lean').read_bytes()) == 'c2162ffd1e5fb9be94dab14e10bc1d6c71a984860f7d85df10fae564a226ec8d'
subprocess.run(['python3', str(folder / 'check-source.py')], check=True)
if '--git' in sys.argv:
    manifest = json.loads((folder / 'manifest.json').read_text())
    for path, item in manifest['artifacts'].items():
        assert sha((root / path).read_bytes()) == item['sha256'], path
        assert sha(subprocess.check_output(['git', 'show', 'HEAD:'+path])) == item['sha256'], path
print('Passed: immutable whole-file source, notice-only continuity, actual final exits/hashes, target3499, strict source, one exact stock report, owned provenance1 and held compatible branch/source. Complete-library and book checks remain pending.')
