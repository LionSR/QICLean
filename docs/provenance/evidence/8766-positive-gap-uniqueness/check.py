#!/usr/bin/env python3
"""Check retained positive-gap evidence without Lean, network, or external writes."""
import hashlib
import json
from pathlib import Path
import re

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[3]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def load(path):
    return json.loads(path.read_text(), object_pairs_hook=unique)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


index = load(PACKET / 'verification.json')
ledger = load(ROOT / 'docs/provenance/openai-math.d/positivegap8766.json')
for path in PACKET.rglob('*.json'):
    load(path)
for row in index['normalization']['original_to_normalized']:
    path = PACKET / row['retained']
    require(digest(path) == row['normalized_sha256'], f"Changed retained input: {path}")
    require(path.stat().st_size == row['normalized_bytes'], f"Changed input size: {path}")
for row in index['source_files']:
    path = ROOT / row['path']
    require(digest(path) == row['sha256'], f"Changed checked source: {path}")
    data = path.read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    require(blob == row['public_git_blob'], f"Public checkpoint blob differs: {path}")

source = (ROOT / index['source_files'][0]['path']).read_text()
test = (ROOT / index['source_files'][1]['path']).read_text()
driver = (ROOT / index['source_files'][2]['path']).read_text()
pairs = re.findall(r'^Provenance-ID: (\S+)\nDownstream declaration: (\S+)$', source, re.M)
names = [name for _, name in pairs]
require(len(pairs) == len(ledger['entries']) == 3, 'Expected three declarations and ledger rows')
require(len(set(names)) == 3, 'Duplicate declaration')
require(names == ['Matrix.' + name for name in re.findall(r'^theorem (\S+)', source, re.M)],
        'Public declaration coverage differs')
require(names == re.findall(r'^#guard_msgs[^\n]*\n#print axioms (\S+)$', test, re.M),
        'Guarded axiom coverage differs')
require(names == re.findall(r'^#print axioms (\S+)$', driver, re.M), 'Raw coverage differs')
require(len(re.findall(r'^example\b', test, re.M)) == index['test_examples'] == 8,
        'Consumer count differs')
require('doubled_gap_partialSwap hgap hΩ heigen hΔ.le' in test,
        'Missing doubled partial-swap consumer')
require(not re.search(r'\b(sorry|admit|native_decide|unsafeCast|unsafeCoerce)\b', source),
        'Proof integrity blocker in production')

for chosen in index['selected_successful_runs']:
    row = load(PACKET / chosen['record'])[chosen['row']]
    require(row['exit_code'] == 0, 'Selected run failed')
    require((ROOT / row['log']).is_file(), 'Selected output is missing')
    if row['sha256']:
        require(digest(ROOT / row['file']) == row['sha256'], 'Checked source hash differs')
failed = []
for record in sorted((PACKET / 'runs').glob('*.json')):
    for ordinal, row in enumerate(load(record)):
        require((ROOT / row['log']).is_file(), 'Historical output is missing')
        if row['exit_code']:
            failed.append((f'runs/{record.name}', ordinal, row['head']))
require(failed == [(r['record'], r['row'], r['head'])
                  for r in index['historical_failed_runs']], 'Historical failures differ')
require(len(failed) == 4, 'Expected four preserved failures')

for entry, pair in zip(ledger['entries'], pairs):
    require((entry['id'], entry['downstream']['declaration']) == pair, 'Ledger identity differs')
    require(entry['reuse_kind'] == 'original' and entry['upstream'] is None and
            entry['no_upstream_proof_text_reused'], 'OpenAI provenance category differs')
    require(entry['verification']['revision'] == index['public_checkpoint_revision'],
            'Public verification revision differs')
    for command in entry['verification']['commands']:
        require(command['exit_code'] == 0, 'Ledger command failed')
        require(digest(ROOT / command['log']) == command['sha256'], 'Ledger log hash differs')

raw = load(PACKET / 'runs/positive-gap-raw-5bbc.json')[1]
output = (ROOT / raw['log']).read_text()
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
require([name for name, _ in reports] == names, 'Raw named reports differ')
require(all([a.strip() for a in axioms.split(',')] ==
            ['propext', 'Classical.choice', 'Quot.sound'] for _, axioms in reports),
        'Unexpected axiom')
require(output.count('[linter.hashCommand]') == 3, 'Raw informational diagnostics differ')
reuse = load(PACKET / 'reuse-and-overlap.json')
require(reuse['adapted_proof']['downstream'] == names[0], 'Missing local proof attribution')
require(digest(ROOT / reuse['adapted_proof']['path']) == reuse['adapted_proof']['sha256'],
        'Local reused proof source differs')
for path in PACKET.rglob('*'):
    if path.is_file():
        require(not re.search(r'/(?:workspace/scratch|home/agent|root)/', path.read_text()),
                f"Private executor path retained: {path}")
print(json.dumps({'status': 'passed', 'public_declarations': 3, 'consumer_examples': 8,
                  'guarded_reports': 3, 'raw_reports': 3, 'historical_failures': 4,
                  'public_checkpoint': index['public_checkpoint_revision'],
                  'scope': 'Retained evidence and file identities; no Lean or CI execution.'},
                 indent=2))
