#!/usr/bin/env python3
"""Recheck this local evidence packet without Lean, network, or external writes."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[3]
PREFIX = PACKET.relative_to(ROOT).as_posix()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def load(path):
    return json.loads(path.read_text(), object_pairs_hook=unique)


def report(text):
    matches = re.findall(
        r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
        text, re.S)
    require(len(matches) == len({name for name, _ in matches}), "duplicate axiom report")
    return {name: [a.strip() for a in axioms.split(',') if a.strip()]
            for name, axioms in matches}


index = load(PACKET / 'verification.json')
ledger = load(ROOT / 'docs/provenance/openai-math.d/physical-buffer8766.json')
for path in PACKET.rglob('*.json'):
    load(path)
for row in index['normalization']['original_to_normalized']:
    path = PACKET / row['retained']
    require(digest(path) == row['normalized_sha256'], f"changed retained input: {path}")
    require(path.stat().st_size == row['normalized_bytes'], f"changed input length: {path}")
for row in index['source_files']:
    path = ROOT / row['path']
    require(digest(path) == row['sha256'], f"changed checked source: {path}")
    if '/drivers/' not in row['path']:
        committed = subprocess.check_output(
            ['git', '-C', str(ROOT), 'show', index['source_revision'] + ':' + row['path']])
        require(committed == path.read_bytes(), f"source revision mismatch: {path}")

runs = {row['id']: row for row in index['successful_runs']}
require(len(runs) == 9, 'expected nine selected successful runs')
for row in runs.values():
    recorded = load(PACKET / row['record'])[row['row']]
    require(recorded['exit_code'] == row['exit_code'] == 0, 'nonzero selected run')
    require(recorded['sha256'] == row['sha256'], 'run source digest mismatch')
    require(recorded['seconds'] == row['seconds'], 'run duration mismatch')
    require(' '.join(recorded['command']) == row['command'], 'run command mismatch')
    require(digest(PACKET / row['log']) == row['log_sha256'], 'run output digest mismatch')

notices, guards, raw, consumers = {}, {}, {}, 0
for module in index['modules']:
    source = (ROOT / module['source']).read_text()
    pairs = re.findall(r'^Provenance-ID: (\S+)\nDownstream declaration: (\S+)$', source, re.M)
    require(len(pairs) == module['declarations'], 'notice count mismatch')
    require('No upstream Lean declaration or proof text is reused.' in source,
            'missing original-proof notice')
    require(not set(notices).intersection(k for k, _ in pairs), 'duplicate provenance ID')
    notices.update({key: (module['source'], name) for key, name in pairs})
    test = (ROOT / module['test']).read_text()
    guarded = re.findall(r'^#guard_msgs[^\n]*\n#print axioms (\S+)$', test, re.M)
    printed = re.findall(r'^#print axioms (\S+)$', (ROOT / module['raw_driver']).read_text(), re.M)
    require(guarded == printed == [name for _, name in pairs], 'coverage mismatch')
    require(len(guarded) == module['guarded_axiom_reports'], 'guard count mismatch')
    examples = len(re.findall(r'^example\b', test, re.M))
    require(examples == module['consumer_examples'], 'consumer count mismatch')
    consumers += examples
    guards.update(report(test))
    driver_run = next(row for row in runs.values()
                      if row.get('replay_command', '').endswith(module['raw_driver']))
    output = (PACKET / driver_run['log']).read_text()
    require(output.count('[linter.hashCommand]') == module['raw_hash_command_diagnostics'],
            'raw informational diagnostic count mismatch')
    raw.update(report(output))
require(len(notices) == len(ledger['entries']) == len(raw) == len(guards) == 42,
        'expected 42 unique declarations, entries, raw reports and guards')
require(consumers == index['counts']['consumer_examples'] == 17, 'consumer total mismatch')
require(raw == guards == index['axioms_by_declaration'], 'exact axiom reports disagree')
require(Counter(tuple(a) for a in raw.values()) == Counter({
    ('propext', 'Classical.choice', 'Quot.sound'): 36, ('Quot.sound',): 2, (): 4}),
    'unexpected axiom summary')
require({e['id'] for e in ledger['entries']} == set(notices), 'ledger ID coverage mismatch')
for entry in ledger['entries']:
    down = entry['downstream']
    require(notices[entry['id']] == (down['path'], down['declaration']), 'notice/name mismatch')
    require(entry['reuse_kind'] == 'original' and entry['upstream'] is None and
            entry['no_upstream_proof_text_reused'] is True, 'wrong reuse classification')
    require(entry['verification']['revision'] == index['source_revision'], 'wrong revision')
    require({c['kind'] for c in entry['verification']['commands']} == {'build', 'axioms'},
            'missing required evidence kinds')
    for command in entry['verification']['commands']:
        require(command['exit_code'] == 0 and digest(ROOT / command['log']) == command['sha256'],
                'ledger command evidence mismatch')
        if command['kind'] == 'axioms':
            require(down['declaration'] in report((ROOT / command['log']).read_text()),
                    'ledger axiom report missing declaration')
for dep in index['reused_dependencies']:
    require(digest(ROOT / dep['path']) == dep['sha256'], 'dependency hash mismatch')
    base = subprocess.check_output(
        ['git', '-C', str(ROOT), 'show', index['base_revision'] + ':' + dep['path']])
    require(base == (ROOT / dep['path']).read_bytes(), 'reused dependency was changed')
manifest = load(PACKET / 'render/focus-manifest.json')
for group in ['lean_source_sha256', 'documentation_sha256']:
    for path, expected in manifest[group].items():
        require(digest(ROOT / path) == expected, f"render/source mismatch: {path}")
for path in [*PACKET.rglob('*'), ROOT / 'docs/provenance/openai-math.d/physical-buffer8766.json']:
    if path.is_file() and path.name != 'check.py':
        text = path.read_text()
        require(not re.search(r'/(?:workspace|home|root|tmp)/|_workspace_scratch_', text),
                f"private executor path retained: {path}")
print(json.dumps({'status': 'passed', 'declarations': 42, 'consumer_examples': consumers,
                  'guarded_axiom_reports': len(guards), 'raw_axiom_reports': len(raw),
                  'retained_inputs': len(index['normalization']['original_to_normalized']),
                  'lean_build_performed': False}, indent=2))
