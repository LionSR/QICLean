#!/usr/bin/env python3
"""Validate retained Gaussian matrix evidence without Lean, network, or remote writes."""
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
ledger = load(ROOT / 'docs/provenance/openai-math.d/gaussian-matrix8766.json')
for path in PACKET.rglob('*.json'):
    load(path)
for row in index['normalization']['original_to_normalized']:
    path = PACKET / row['retained']
    require(digest(path) == row['normalized_sha256'], f"Changed retained input: {path}")
    require(path.stat().st_size == row['normalized_bytes'], f"Changed retained size: {path}")
for row in index['source_files']:
    path = ROOT / row['path']
    data = path.read_bytes()
    require(digest(path) == row['sha256'], f"Changed checked source: {path}")
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    require(blob == row['git_blob'], f"Checked Git blob differs: {path}")

source = (ROOT / index['source_files'][0]['path']).read_text()
test = (ROOT / index['source_files'][1]['path']).read_text()
raw = (ROOT / index['source_files'][2]['path']).read_text()
guarded = (ROOT / index['source_files'][3]['path']).read_text()
pairs = re.findall(r'^Provenance-ID: (\S+)\nDownstream declaration: (\S+)$', source, re.M)
names = [name for _, name in pairs]
public = re.findall(r'^(?:@\[simp\] )?(?:noncomputable def|theorem) (\w+)', source, re.M)
require(names == ['GaussianFilter.' + name for name in public], 'Public coverage differs')
require(len(names) == len(set(names)) == len(ledger['entries']) == 21, 'Expected 21 rows')
require(names == re.findall(r'^#print axioms (\S+)$', raw, re.M), 'Raw coverage differs')
require(names == re.findall(r'^#guard_msgs[^\n]*\n#print axioms (\S+)$', guarded, re.M),
        'Guarded coverage differs')
require(len(re.findall(r'^example\b', test, re.M)) == index['test_examples'] == 6,
        'Consumer count differs')
for witness in ['¬ (gaussianIntertwiner', 'Complex.exp (-(t : ℂ) * I)',
                'gaussianIntertwiner 0', 'gaussianIntertwinerTruncated h (-1)',
                'Matrix (Fin 0) (Fin 0) ℂ']:
    require(witness in test, f"Missing regression witness: {witness}")
require(not re.search(r'\b(sorry|admit|native_decide|unsafeCast|unsafeCoerce)\b', source),
        'Proof integrity blocker in production')
require('LionSR/TNLean issue #8766' in source and 'GLM23' not in source,
        'Manuscript or tracker attribution differs')

selected = []
for chosen in index['selected_successful_runs']:
    row = load(PACKET / chosen['record'])[chosen['row']]
    require(row['exit_code'] == 0, 'Selected run failed')
    require((ROOT / row['log']).is_file(), 'Selected log missing')
    if row['sha256'] and chosen['kind'] != 'strict-production-before-attribution-correction':
        require(digest(ROOT / row['file']) == row['sha256'], 'Checked file hash differs')
    selected.append((chosen['kind'], row))
final = [row for kind, row in selected if kind == 'strict-production-final']
require(len(final) == 1 and final[0]['head'] == index['verified_source_revision'],
        'Missing exact final source check')
require(any(kind == 'native-target-final' and row['head'] == index['verified_source_revision']
            for kind, row in selected), 'Missing exact final native target')
failed = []
for record in sorted((PACKET / 'runs').glob('*.json')):
    for ordinal, row in enumerate(load(record)):
        require((ROOT / row['log']).is_file(), 'Historical output missing')
        if row['exit_code']:
            failed.append((f'runs/{record.name}', ordinal, row['head']))
require(failed == [(r['record'], r['row'], r['head'])
                  for r in index['historical_failed_runs']], 'Historical failures differ')
require(len(failed) == 2, 'Expected two preserved historical source/fixture failures')
incident = load(PACKET / index['runner_incident'])
require(incident['command_receipt'] is None and incident['exit_code'] is None and
        incident['seconds'] is None, 'Unrecorded runner metadata was invented')
require('no such file or directory' in (ROOT / incident['log']).read_text(),
        'Missing runner diagnostic')

rawrow = next(row for kind, row in selected if kind == 'strict-raw-axioms')
output = (ROOT / rawrow['log']).read_text()
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
require([name for name, _ in reports] == names, 'Raw named reports differ')
expected = ['propext', 'Classical.choice', 'Quot.sound']
for name, axioms in reports:
    require([a.strip() for a in axioms.split(',')] == expected == index['axioms'][name],
            'Unexpected axiom')
require(output.count('[linter.hashCommand]') == 21, 'Raw informational diagnostics differ')
for entry, pair in zip(ledger['entries'], pairs):
    require((entry['id'], entry['downstream']['declaration']) == pair, 'Ledger identity differs')
    require(entry['reuse_kind'] == 'original' and entry['upstream'] is None and
            entry['no_upstream_proof_text_reused'], 'OpenAI proof-text category differs')
    require(entry['verification']['revision'] == index['verified_source_revision'],
            'Verification revision differs')
    for command in entry['verification']['commands']:
        require(command['exit_code'] == 0, 'Ledger command failed')
        require(digest(ROOT / command['log']) == command['sha256'], 'Ledger log differs')
        require(any(' '.join(row['command']) == command['command'] and
                    row['log'] == command['log'] for _, row in selected),
                'Ledger command has no actual selected receipt')
reuse = load(PACKET / 'reuse.json')
require(digest(ROOT / reuse['path']) == reuse['sha256'], 'Adapted local QIC source differs')
require(len(reuse['adaptations']) == 7, 'Local adaptation coverage differs')
require(not reuse['openai_lean_proof_text_reused'], 'OpenAI reuse claim differs')
for row in reuse['adaptations']:
    require(row['downstream'] in names, 'Unknown adaptation target')
for path in PACKET.rglob('*'):
    if path.is_file():
        require(not re.search(r'/(?:workspace/scratch|home/agent|root)/', path.read_text()),
                f"Private executor path retained: {path}")
print(json.dumps({'status': 'passed', 'public_declarations': 21, 'consumer_examples': 6,
                  'guarded_reports': 21, 'raw_reports': 21, 'historical_failures': 2,
                  'separate_runner_incidents': 1,
                  'verified_source_revision': index['verified_source_revision'],
                  'scope': 'Retained evidence and file identities; no Lean or CI execution.'},
                 indent=2))
