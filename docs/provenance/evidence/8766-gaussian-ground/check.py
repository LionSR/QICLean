#!/usr/bin/env python3
"""Check the retained Gaussian ground-estimate evidence without Lean or network access."""
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
        require(key not in result, f'Duplicate JSON key: {key}')
        result[key] = value
    return result


def load(path):
    return json.loads(path.read_text(), object_pairs_hook=unique)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


index = load(PACKET / 'verification.json')
ledger = load(ROOT / 'docs/provenance/openai-math.d/gaussian-ground8766.json')
for path in PACKET.rglob('*.json'):
    load(path)
for row in index['normalization']['original_to_normalized']:
    path = PACKET / row['retained']
    require(digest(path) == row['normalized_sha256'], f'Changed retained input: {path}')
    require(path.stat().st_size == row['normalized_bytes'], f'Changed input size: {path}')
for row in index['source_files']:
    data = (ROOT / row['path']).read_bytes()
    require(hashlib.sha256(data).hexdigest() == row['sha256'], 'Checked source hash differs')
    require(git_blob(data) == row['git_blob'], 'Checked Git blob differs')
    require(len(data.splitlines()) == row['lines'], 'Checked line count differs')
require([r['source_revision'] for r in index['source_files']] ==
        [index['production_check_revision']] * 2 + [index['raw_driver_revision']],
        'Source and driver revisions differ')
checkpoint = index['public_checkpoint']
require(checkpoint['revision'] == index['verified_source_revision'], 'Public revision differs')
require(checkpoint['tree'] == checkpoint['locally_verified_tree'], 'Public/local tree differs')
require(checkpoint['equivalent_local_revision'] == index['raw_driver_revision'],
        'Equivalent local revision differs')
binding = load(PACKET / checkpoint['evidence'])
require(binding['public_revision'] == checkpoint['revision'], 'Binding revision differs')
require(binding['public_tree'] == binding['equivalent_local_tree'] == checkpoint['tree'],
        'Binding tree differs')
require(len(binding['source_identities']) == 3, 'Missing source binding')
for bound, checked in zip(binding['source_identities'], index['source_files']):
    require(bound['path'] == checked['path'] and
            bound['actual_checked_revision'] == checked['source_revision'],
            'Bound checked revision differs')
    require(bound['public_git_blob'] == bound['checked_git_blob'] == checked['git_blob'],
            'Public and checked blobs differ')
    require(bound['checked_sha256'] == checked['sha256'], 'Bound source hash differs')
require(len(binding['commands']) == 8 and all(r['exit_code'] == 0
        for r in binding['commands']), 'Git binding evidence incomplete')
source, test, driver = [(ROOT / row['path']).read_text() for row in index['source_files']]
pairs = re.findall(r'^Provenance-ID: (\S+)\nDownstream declaration: (\S+)$', source, re.M)
names = [name for _, name in pairs]
require(len(pairs) == len(set(names)) == len(ledger['entries']) ==
        index['public_declarations'] == 5, 'Expected five public declarations')
require(names == ['GaussianFilter.' + name for name in
                  re.findall(r'^theorem (\S+)', source, re.M)], 'Public coverage differs')
require(names == re.findall(r'^#guard_msgs[^\n]*\n#print axioms (\S+)$', test, re.M),
        'Guard coverage differs')
require(names == re.findall(r'^#print axioms (\S+)$', driver, re.M), 'Raw coverage differs')
require(len(re.findall(r'^example\b', test, re.M)) == index['test_examples'] == 5,
        'Expected five consumers')
for witness in ['inner_gaussianIntertwiner h', 'norm_sub_ground_le_of_coefficients',
                'SpectralFilter.mulVec_eigenvectorBasis_complex', 'l2_opNorm_mulVec',
                'star z', 'norm_gaussianIntertwiner_sub_truncated_le', 'norm_add_le']:
    require(witness in source, f'Missing actual integral argument: {witness}')
for witness in ['W.IsHermitian', 'gaussianIntertwiner 2',
                'gaussianIntertwiner_two_sided_ground_estimate 0',
                'gaussianIntertwinerTruncated 2 3', '(-I) • Φ', 'I • Ψ',
                'gaussianIntertwiner_two_sided_of_real_overlap']:
    require(witness in test, f'Missing consumer: {witness}')
require(not re.search(r'\b(sorry|admit|native_decide|unsafeCast|unsafeCoerce)\b|^axiom\s',
                      source + test + driver, re.M), 'Proof integrity blocker')
require(not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth|linter\.)', source + test),
        'Unapproved budget or linter option')

selected = []
for chosen in index['selected_successful_runs']:
    row = load(PACKET / chosen['record'])[chosen['row']]
    selected.append(row)
    require(row['exit_code'] == 0, 'Selected run failed')
    require(row['head'] == chosen['revision'], 'Run revision relabeled')
    require((ROOT / row['log']).is_file(), 'Missing run log')
    if row['sha256']:
        require(digest(ROOT / row['file']) == row['sha256'], 'Run source hash differs')
require(len(selected) == 5, 'Expected both native builds, strict source, consumers and raw')
require([r['head'] for r in selected] == [index['production_check_revision']] * 3 +
        [index['raw_driver_revision']] * 2, 'Actual run revisions differ')
require([s['kind'] for s in index['selected_successful_runs']] ==
        ['native-target', 'strict-production', 'strict-consumers-and-guards',
         'native-target-recheck', 'strict-raw-axioms'], 'Run purpose differs')
for i in [0, 3]:
    require('3269 jobs' in (ROOT / selected[i]['log']).read_text(), 'Native result differs')
failed = []
for record in sorted((PACKET / 'runs').glob('*.json')):
    for ordinal, row in enumerate(load(record)):
        require((ROOT / row['log']).is_file(), 'Historical log missing')
        if row['exit_code']:
            failed.append((f'runs/{record.name}', ordinal, row['head'], row['exit_code']))
require(failed == [(r['record'], r['row'], r['head'], r['exit_code'])
                  for r in index['historical_failed_runs']], 'Historical failure differs')
require(len(failed) == 1 and failed[0][2].startswith('000af37'), 'Expected retained 000a failure')

for entry, pair in zip(ledger['entries'], pairs):
    require((entry['id'], entry['downstream']['declaration']) == pair, 'Ledger identity differs')
    require(entry['reuse_kind'] == 'original' and entry['upstream'] is None and
            entry['no_upstream_proof_text_reused'], 'OpenAI proof attribution differs')
    require(entry['verification']['revision'] == index['verified_source_revision'],
            'Ledger source revision differs')
    require(len(entry['verification']['commands']) == len(selected), 'Ledger command missing')
    for command, run in zip(entry['verification']['commands'], selected):
        require(command['exit_code'] == run['exit_code'] == 0, 'Ledger command failed')
        require(shlex.split(command['command']) == run['command'], 'Ledger command differs')
        require(command['log'] == run['log'], 'Ledger log differs')
        require(digest(ROOT / command['log']) == command['sha256'], 'Ledger log hash differs')
output = (ROOT / selected[-1]['log']).read_text()
reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
require([name for name, _ in reports] == names, 'Raw reports differ')
for name, axioms in reports:
    require([a.strip() for a in axioms.split(',')] == index['axioms'][name] ==
            ['propext', 'Classical.choice', 'Quot.sound'], 'Unexpected axiom')
require(index['raw_status'] == 'passed' and index['raw_axiom_reports'] ==
        index['guarded_axiom_reports'] == 5, 'Raw or guarded audit incomplete')
require(output.count('[linter.hashCommand]') == 5, 'Raw diagnostics differ')
reuse = load(PACKET / 'reuse.json')
require(not reuse['openai_lean_proof_text_reused'], 'OpenAI reuse changed')
require(len(reuse['local_adaptations']) == 2, 'Missing local fixture adaptations')
for row in reuse['local_adaptations']:
    data = (ROOT / row['path']).read_bytes()
    require(hashlib.sha256(data).hexdigest() == row['sha256'], 'Local fixture hash differs')
    require(git_blob(data) == row['git_blob'], 'Local fixture blob differs')
for path in PACKET.rglob('*'):
    if path.is_file():
        require(not re.search(r'/(?:workspace/scratch|home/agent|root)/', path.read_text()),
                f'Private executor path retained: {path}')
print(json.dumps({'status': 'passed', 'public_declarations': 5, 'consumer_examples': 5,
                  'guarded_reports': 5, 'raw_reports': 5, 'historical_failures': 1,
                  'verified_source_revision': index['verified_source_revision'],
                  'raw_driver_revision': index['raw_driver_revision'],
                  'scope': 'Source identities and retained evidence; no Lean or CI execution.'},
                 indent=2))
