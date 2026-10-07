#!/usr/bin/env python3
"""Check retained Gaussian spectral evidence without Lean or network access."""
import hashlib
import json
from pathlib import Path
import re
import shlex

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
ledger = load(ROOT / 'docs/provenance/openai-math.d/gaussian-spectral8766.json')
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
    require(blob == row['git_blob'], f"Verified source blob differs: {path}")
    require(len(data.splitlines()) == row['lines'], f"Verified line count differs: {path}")
    require(row['source_revision'] == index['verified_source_revision'], 'Revision differs')

source, test, driver = [(ROOT / row['path']).read_text() for row in index['source_files']]
pairs = re.findall(r'^Provenance-ID: (\S+)\nDownstream declaration: (\S+)$', source, re.M)
names = [name for _, name in pairs]
require(len(pairs) == len(ledger['entries']) == index['public_declarations'] == 2,
        'Expected two public declarations and ledger rows')
require(len(set(names)) == 2, 'Duplicate declaration')
require(names == ['GaussianFilter.' + n for n in re.findall(r'^theorem (\S+)', source, re.M)],
        'Public declaration coverage differs')
require(names == re.findall(r'^#guard_msgs[^\n]*\n#print axioms (\S+)$', test, re.M),
        'Guarded axiom coverage differs')
require(names == re.findall(r'^#print axioms (\S+)$', driver, re.M), 'Raw coverage differs')
require(len(re.findall(r'^example\b', test, re.M)) == index['test_examples'] == 3,
        'Consumer count differs')
require('b.sum_sq_norm_inner_right' in source, 'Missing Parseval norm argument')
require('hgap.eq_inner_smul_of_gap' in source, 'Missing ground-uniqueness reuse')
require('gaussianVector_coeff' in test and 'Real.exp (-4) * 2' in test,
        'Missing exact synthesis or concrete norm-scaling consumer')
require(not re.search(r'\b(sorry|admit|native_decide|unsafeCast|unsafeCoerce)\b|^axiom\s',
                      source + test, re.M), 'Proof integrity blocker')
require(not re.search(r'set_option\s+(?:maxHeartbeats|maxRecDepth|linter\.)', source + test),
        'Unapproved budget or linter option')

selected = []
for chosen in index['selected_successful_runs']:
    row = load(PACKET / chosen['record'])[chosen['row']]
    selected.append(row)
    require(row['exit_code'] == 0, 'Selected run failed')
    require(row['head'] == index['verified_source_revision'], 'Selected run revision differs')
    require((ROOT / row['log']).is_file(), 'Selected output is missing')
    if row['sha256']:
        require(digest(ROOT / row['file']) == row['sha256'], 'Checked source hash differs')
require(len(selected) == 4, 'Expected native, strict source, strict test, and raw commands')
require('3128 jobs' in (ROOT / selected[0]['log']).read_text(), 'Native target result differs')
failed = []
for record in sorted((PACKET / 'runs').glob('*.json')):
    for ordinal, row in enumerate(load(record)):
        require((ROOT / row['log']).is_file(), 'Historical output is missing')
        if row['exit_code']:
            failed.append((f'runs/{record.name}', ordinal, row['head'], row['exit_code']))
require(failed == [(r['record'], r['row'], r['head'], r['exit_code'])
                  for r in index['historical_failed_runs']], 'Historical failures differ')
require(len(failed) == 2, 'Expected two retained failed invocations')

for entry, pair in zip(ledger['entries'], pairs):
    require((entry['id'], entry['downstream']['declaration']) == pair, 'Ledger identity differs')
    require(entry['reuse_kind'] == 'original' and entry['upstream'] is None and
            entry['no_upstream_proof_text_reused'], 'OpenAI provenance category differs')
    require(entry['verification']['revision'] == index['verified_source_revision'],
            'Ledger revision differs')
    require(len(entry['verification']['commands']) == len(selected), 'Missing ledger commands')
    for command, run in zip(entry['verification']['commands'], selected):
        require(command['exit_code'] == run['exit_code'] == 0, 'Ledger command failed')
        require(shlex.split(command['command']) == run['command'], 'Ledger command differs')
        require(command['log'] == run['log'], 'Ledger output differs')
        require(digest(ROOT / command['log']) == command['sha256'], 'Ledger log hash differs')

output = (ROOT / selected[3]['log']).read_text()
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
require([name for name, _ in reports] == names, 'Raw named reports differ')
for name, axioms in reports:
    require([a.strip() for a in axioms.split(',')] == index['axioms'][name] ==
            ['propext', 'Classical.choice', 'Quot.sound'], 'Unexpected axiom')
require(output.count('[linter.hashCommand]') == 2, 'Raw informational diagnostics differ')
reuse = load(PACKET / 'reuse.json')
require(not reuse['openai_lean_proof_text_reused'], 'OpenAI proof attribution differs')
require(len(reuse['local_adaptations']) == 3, 'Missing local QIC adaptations')
for row in reuse['local_adaptations']:
    require(digest(ROOT / row['path']) == row['sha256'], 'Adapted local source differs')
    data = (ROOT / row['path']).read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    require(blob == row['git_blob'], 'Adapted local blob differs')
for path in PACKET.rglob('*'):
    if path.is_file():
        require(not re.search(r'/(?:workspace/scratch|home/agent|root)/', path.read_text()),
                f"Private executor path retained: {path}")
print(json.dumps({'status': 'passed', 'public_declarations': 2, 'consumer_examples': 3,
                  'guarded_reports': 2, 'raw_reports': 2, 'historical_failures': 2,
                  'verified_source_revision': index['verified_source_revision'],
                  'scope': 'Retained evidence and source identities; no Lean or CI execution.'},
                 indent=2))
