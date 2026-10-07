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
assert len(manifest['excluded_attempts']) == 1
for attempt in manifest['excluded_attempts']:
    assert not attempt['claimed_as_successful_verification']
    assert attempt['record']['exit_code'] == 1
    for name, digest in [(attempt['record']['log'], attempt['record']['sha256']),
                         (attempt['snapshot'], attempt['snapshot_sha256'])]:
        path = root / name
        assert sha(path) == digest, name
        subprocess.run(['git', 'ls-files', '--error-unmatch', name],
                       check=True, stdout=subprocess.DEVNULL)
preservation = json.loads((folder / 'source-preservation.json').read_text())
for field in ['parent_production_files_preserved', 'owned_frozen_files_preserved', 'inherited_evidence_and_exposition_preserved']:
    for name, digest in preservation[field].items():
        assert sha(root / name) == digest, name
for entry in json.loads((folder / 'compression.json').read_text()):
    raw, compressed = root / entry['path'], root / entry['gzip_path']
    assert sha(raw) == entry['sha256']
    assert sha(compressed) == entry['gzip_sha256']
    assert gzip.decompress(compressed.read_bytes()) == raw.read_bytes()
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",
                     (folder / 'axioms.log').read_text(), re.S)
assert len(reports) == 11
names = {e['downstream']['declaration'] for shard in ['highLabelWindow8753', 'pureTensorPower8753', 'iidSurprisal8753', 'iidTailThreshold8753'] for e in json.loads((root / f'docs/provenance/openai-math.d/{shard}.json').read_text())['entries']}
assert {name for name, _ in reports} == names
for _, axioms in reports:
    assert {a.strip() for a in axioms.split(',')} <= {'propext', 'Classical.choice', 'Quot.sound'}
print(f"Verified {len(manifest['commands'])} successful command records, "
      f"{len(manifest['file_hashes'])} file hashes and all tracked raw logs.")
print(f"All {len(preservation['parent_production_files_preserved'])} inherited Lean files "
      'and three frozen owned files retain their bytes.')
print('Eleven exact kernel reports contain only the standard axioms; raw/gzip hashes agree.')

leaf_folder = root / 'docs/provenance/evidence/highLabelWindow8753'
leaf = json.loads((leaf_folder / 'verification.json').read_text())
assert len(leaf['commands']) == 11 and len(leaf['excluded_attempts']) == 2
for item in leaf['commands'] + [v['record'] for v in leaf['excluded_attempts']]:
    path = root / item['log']
    assert sha(path) == item['sha256']
    subprocess.run(['git', 'ls-files', '--error-unmatch', str(path.relative_to(root))],
                   check=True, stdout=subprocess.DEVNULL)
for item in leaf['commands']:
    assert item['exit_code'] == 0
for item in leaf['excluded_attempts']:
    assert not item['claimed_as_successful_verification']
    assert sha(root / item['wrapper_snapshot']) == item['wrapper_sha256']
assert [v['record']['exit_code'] for v in leaf['excluded_attempts']] == [12, 0]
for field, digest in leaf['source_files'].items():
    assert sha(root / field) == digest
native = json.loads((folder / 'native-targets.json').read_text())
assert native['contains_all_active_fragment_targets'] and native['contains_all_eleven_owned']
assert not native['missing'] and len(native['owned_declarations']) == 11
assert sha(root / native['native_list']) == native['native_list_sha256']
print('The 11 final leaf commands and both honest excluded attempts are bound to tracked logs/snapshots.')
print(f"All {native['fragment_declarations']} active-fragment declarations occur in the literal native list.")
