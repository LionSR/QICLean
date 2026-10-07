#!/usr/bin/env python3
"""Check public source identity and retained historical evidence; never run Lean."""
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
PUBLIC_REVISION = '16b81356549158a8393aaea5085defd4c5022e71'
SOURCE_TREE = '41d46a48626973c9056f36ca6163fe3b5e23665d'
LOCAL_REVISION = '90bcaa0d425ad9f7916ce322edfcb229ecec8b9d'
PACKETS = {'kernel': ('gaussiankernel8766.json', 15),
           'matrix': ('gaussian-matrix8766.json', 21),
           'spectral': ('gaussian-spectral8766.json', 2)}


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


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args])


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def object_id(kind, data):
    return hashlib.sha1(kind.encode() + b' ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def relative(path):
    return path.relative_to(ROOT).as_posix()


def identity(path):
    data = path.read_bytes()
    return {'path': relative(path), 'sha256': sha256(data),
            'git_blob': object_id('blob', data), 'bytes': len(data)}


def verify_file(item, public_path=None):
    path = ROOT / item['path']
    require(identity(path) == {key: item[key] for key in
                              ('path', 'sha256', 'git_blob', 'bytes')},
            f'Changed bound file: {item["path"]}')
    if public_path is not None:
        require(path.read_bytes() == git('show', f'{PUBLIC_REVISION}:{public_path}'),
                f'Public checkpoint bytes differ: {public_path}')


def validate_packet(packet, index, current_ledger):
    """Validate the public binding, then return the intact historical ledger.

    Existing packet checkers run all their original assertions on that ledger.
    The current ledger must equal it except for the explicit binding revision
    and explanation. Historical verification indexes and run records stay intact.
    Only the public Git commit must exist locally; local-only commits are not used.
    """
    manifest = load(HERE / 'manifest.json')
    require(manifest['format_version'] == 1, 'Unknown binding format')
    public = manifest['public_checkpoint']
    require(public['repository'] == 'LionSR/QICLean' and
            public['remote'] == 'https://github.com/LionSR/QICLean.git' and
            public['branch'] == 'codex/gaussian-two-generator-filter-8766' and
            public['revision'] == PUBLIC_REVISION and public['tree'] == SOURCE_TREE,
            'Public checkpoint identity differs')
    require(git('rev-parse', PUBLIC_REVISION + '^{tree}').decode().strip() == SOURCE_TREE,
            'Public source tree differs')
    trees = manifest['source_tree_equivalence']
    require(trees['local_source_revision'] == LOCAL_REVISION and trees['equal'] is True and
            trees['local_source_tree'] == trees['public_source_tree'] == SOURCE_TREE,
            'Source-tree equivalence differs')
    verify_file(trees['local_commit_object'])
    commit = (ROOT / trees['local_commit_object']['path']).read_bytes()
    require(object_id('commit', commit) == LOCAL_REVISION and
            commit.splitlines()[0] == b'tree ' + SOURCE_TREE.encode(),
            'Archived local commit does not establish the identical source tree')
    require(set(manifest['packets']) == set(PACKETS), 'Expected three public bindings')
    name = packet.name.removeprefix('8766-gaussian-')
    filename, count = PACKETS[name]
    binding = manifest['packets'][name]
    require(binding['packet'] == relative(packet) and
            binding['current_ledger'] == f'docs/provenance/openai-math.d/{filename}' and
            binding['declarations'] == count, 'Packet identity differs')
    require(binding['historical_verified_source_revision'] == index['verified_source_revision'],
            'Historical verification revision differs')
    verify_file(binding['original_ledger'], binding['current_ledger'])
    verify_file(binding['original_checker'], relative(packet / 'check.py'))
    original = load(ROOT / binding['original_ledger']['path'])
    require(len(original['entries']) == count, 'Historical ledger coverage differs')
    expected = copy.deepcopy(original)
    for entry in expected['entries']:
        require(entry['verification']['revision'] == index['verified_source_revision'],
                'Archived ledger lost its historical revision')
        entry['verification']['revision'] = PUBLIC_REVISION
        replacement = binding['replaced_change_index']
        require(replacement == (3 if name in ('kernel', 'matrix') else None),
                'Unexpected ledger edit scope')
        if replacement is None:
            entry['changes'].append(binding['binding_note'])
        else:
            require(entry['changes'][replacement].startswith('The verification revision'),
                    'Unexpected historical revision explanation')
            entry['changes'][replacement] = binding['binding_note']
    require(current_ledger == expected,
            'Current ledger differs beyond the public revision and binding explanation')

    require(len(binding['source_files']) == len(index['source_files']),
            'Bound source coverage differs')
    for actual, historical in zip(binding['source_files'], index['source_files']):
        require(actual['path'] == historical['path'] and
                actual['sha256'] == historical['sha256'] and
                actual['git_blob'] == historical['git_blob'] and
                actual['historical_source_revision'] == historical['source_revision'] and
                actual['public_source_revision'] == PUBLIC_REVISION,
                'Historical/public source identity differs')
        verify_file(actual, actual['path'])
    for source in binding['adapted_source_files']:
        verify_file(source, source['path'])

    retained = binding['retained_packet_files']
    actual_paths = sorted(relative(p) for p in packet.rglob('*')
                          if p.is_file() and p.name != 'check.py')
    public_paths = sorted(p for p in git('ls-tree', '-r', '--name-only', PUBLIC_REVISION,
                                         '--', relative(packet)).decode().splitlines()
                          if p != relative(packet / 'check.py'))
    require([item['path'] for item in retained] == actual_paths == public_paths,
            'Retained packet coverage differs from the public checkpoint')
    for item in retained:
        verify_file(item, item['path'])

    selected = []
    for chosen in index['selected_successful_runs']:
        record = packet / chosen['record']
        row = load(record)[chosen['row']]
        selected.append({'record': relative(record), 'row': chosen['row'],
                         'kind': chosen['kind'], 'actual_run_revision': row['head'],
                         'command': row['command'], 'exit_code': row['exit_code'],
                         'file': row['file'], 'checked_file_sha256': row['sha256'],
                         'log': identity(ROOT / row['log'])})
    require(binding['selected_historical_runs'] == selected,
            'Historical run revision, command, source, or exact log hash differs')
    return original


if __name__ == '__main__':
    require(len(sys.argv) <= 2, 'Usage: check_binding.py [provenance-schema.json]')
    manifest = load(HERE / 'manifest.json')
    schema = None
    if len(sys.argv) == 2:
        import jsonschema
        schema_path = Path(sys.argv[1])
        require(sha256(schema_path.read_bytes()) == manifest['schema']['sha256'],
                'Pinned provenance schema differs')
        schema = load(schema_path)
    for name, (filename, _) in PACKETS.items():
        packet = ROOT / f'docs/provenance/evidence/8766-gaussian-{name}'
        ledger = load(ROOT / f'docs/provenance/openai-math.d/{filename}')
        original = validate_packet(packet, load(packet / 'verification.json'), ledger)
        if schema is not None:
            jsonschema.validate(ledger, schema)
            jsonschema.validate(original, schema)
    print(json.dumps({'status': 'passed', 'public_source_revision': PUBLIC_REVISION,
                      'source_tree': SOURCE_TREE, 'source_tree_equivalent': True,
                      'ledger_entries': 38, 'source_files': 10,
                      'retained_packet_files': 62, 'selected_historical_runs': 15,
                      'schema_validated': schema is not None,
                      'scope': 'Public Git objects, exact retained evidence, and ledger binding; '
                               'no Lean, Lake, CI, network, or remote-write execution.'}, indent=2))
