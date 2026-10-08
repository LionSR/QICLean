#!/usr/bin/env python3
"""Validate recorded source-transport expansion checks without running Lean."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    args = parser.parse_args()
    root, evidence = args.root.resolve(), Path(__file__).resolve().parent
    manifest = read(evidence / 'manifest.json')['sha256']
    for path, expected in manifest.items():
        assert sha(evidence / path) == expected, path
    pin = read(evidence / 'source-revision.json')
    builds = read(evidence / 'build-commands.json')
    assert len(builds) == 4
    for row in builds:
        source = subprocess.check_output(
            ['git', '-C', str(root), 'show', pin['source_revision'] + ':' + row['source_path']])
        assert hashlib.sha256(source).hexdigest() == row['source_sha256']
        assert sha(root / row['source_path']) == row['source_sha256']
        assert row['returncode'] == 0 and '-DwarningAsError=true' in row['command']
        assert not (evidence / (row['module'] + '.log')).read_bytes()
    audit = read(evidence / 'audit-command.json')
    assert audit['returncode'] == 0 and audit['all_imported_artifact_hashes_unchanged_at_pin']
    assert set(read(evidence / 'axiom-dependencies.json')[
        'QICLean.ComplexGaussian.sourceTransport_eq_sum_rankOne']) <= {
            'propext', 'Classical.choice', 'Quot.sound'}
    dependencies = gzip.decompress((evidence / 'imported-dependencies.json.gz').read_bytes())
    assert hashlib.sha256(dependencies).hexdigest() == audit['imported_dependencies_sha256']
    assert len(json.loads(dependencies)) == audit['imported_artifacts'] == 5300
    assert read(evidence / 'declaration-check/command.json')['checked_count'] == 3629
    assert read(evidence / 'provenance-command.json')['returncode'] == 0
    assert read(evidence / 'blueprint/source-pin.json')['all_source_hashes_match']
    assert read(evidence / 'format-command.json')['idempotent']
    consumers = read(evidence / 'consumer-references.json')
    for row in consumers['references']:
        assert sha(evidence / row['path']) == row['sha256']
    print(f'Evidence valid: {len(manifest)} files, four strict module checks, '
          'one standard-axiom theorem, 5,300 imported artifacts, 3,629 blueprint names.')
    print('Recorded checks only; no Lean compilation performed.')


if __name__ == '__main__':
    main()
