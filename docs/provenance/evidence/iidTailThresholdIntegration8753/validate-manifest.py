"""Validate source preservation, actual exits, and the recorded evidence hashes."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess

root = Path.cwd()
folder = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((folder / 'verification.json').read_text())
for command in manifest['commands']:
    assert command['exit_code'] == 0, command
    path = root / command['log']
    assert sha(path) == command['sha256'], path
    subprocess.run(['git', 'ls-files', '--error-unmatch', str(path.relative_to(root))],
                   check=True, stdout=subprocess.DEVNULL)
for name, digest in manifest['file_hashes'].items():
    assert sha(root / name) == digest, name
preservation = json.loads((folder / 'source-preservation.json').read_text())
for field in ['parent_production_files_preserved', 'owned_frozen_files_preserved', 'inherited_iid_evidence_and_exposition_preserved']:
    for name, digest in preservation[field].items():
        assert sha(root / name) == digest, name
for entry in json.loads((folder / 'compression.json').read_text()):
    raw, compressed = root / entry['path'], root / entry['gzip_path']
    assert sha(raw) == entry['sha256']
    assert sha(compressed) == entry['gzip_sha256']
    assert gzip.decompress(compressed.read_bytes()) == raw.read_bytes()
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",
                     (folder / 'axioms.log').read_text(), re.S)
assert len(reports) == 5
names = {e['downstream']['declaration'] for shard in ['iidSurprisal8753', 'iidTailThreshold8753'] for e in json.loads((root / f'docs/provenance/openai-math.d/{shard}.json').read_text())['entries']}
assert {name for name, _ in reports} == names
for _, axioms in reports:
    assert {a.strip() for a in axioms.split(',')} <= {'propext', 'Classical.choice', 'Quot.sound'}
print(f"Verified {len(manifest['commands'])} successful command records, "
      f"{len(manifest['file_hashes'])} file hashes and all tracked raw logs.")
print(f"All {len(preservation['parent_production_files_preserved'])} inherited Lean files "
      'and three frozen owned files retain their bytes.')
print('Five exact kernel reports contain only the standard axioms; raw/gzip hashes agree.')
