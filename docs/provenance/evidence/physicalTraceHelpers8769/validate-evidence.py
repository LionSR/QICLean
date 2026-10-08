#!/usr/bin/env python3
"""Validate recorded physical-trace checks without compiling Lean."""
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
    assert len(builds) == 6
    for row in builds:
        data = subprocess.check_output(
            ['git', '-C', str(root), 'show', pin['source_revision'] + ':' + row['source_path']])
        assert hashlib.sha256(data).hexdigest() == row['source_sha256']
        assert sha(root / row['source_path']) == row['source_sha256']
        assert row['source_revision'] == pin['source_revision']
        assert row['returncode'] == 0 and '-DwarningAsError=true' in row['command']
        assert not (evidence / (row['module'] + '.log')).read_bytes()
        snapshot = evidence / 'checked-sources' / (row['source_path'] + '.gz')
        assert gzip.decompress(snapshot.read_bytes()) == data
    audit = read(evidence / 'audit-command.json')
    assert audit['returncode'] == 0 and audit['all_imported_artifact_hashes_unchanged_at_pin']
    assert audit['source_revision'] == pin['source_revision']
    axioms = read(evidence / 'axiom-dependencies.json')
    declarations = read(evidence / 'declarations.json')
    assert set(axioms) == {x['declaration'] for x in declarations}
    assert len(axioms) == 10
    for dependencies in axioms.values():
        assert set(dependencies) <= {'propext', 'Classical.choice', 'Quot.sound'}
    dependencies = gzip.decompress((evidence / 'imported-dependencies.json.gz').read_bytes())
    assert hashlib.sha256(dependencies).hexdigest() == audit['imported_dependencies_sha256']
    assert len(json.loads(dependencies)) == audit['imported_artifacts'] == 11629
    native = read(evidence / 'declaration-check/command.json')
    assert native['returncode'] == 0 and native['checked_count'] == 3639
    assert native['source_revision'] == pin['source_revision']
    assert read(evidence / 'provenance-command.json')['returncode'] == 0
    blueprint = evidence / 'blueprint'
    bp_pin = read(blueprint / 'source-pin.json')
    assert bp_pin['all_source_hashes_match'] and bp_pin['source_revision'] == pin['source_revision']
    assert bp_pin['visual_review']['pdf_pages'] == [3, 4, 5]
    assert read(evidence / 'format-command.json')['idempotent']
    tags = read(blueprint / 'tag-coverage.json')
    assert set(tags) == set(axioms) and set(tags.values()) == {1}
    graph = read(blueprint / 'dependency-graph.json')
    assert not graph['cycles'] and not graph['duplicate_labels']
    assert all(x['returncode'] == 0 for x in read(blueprint / 'commands.json'))
    canonical = evidence / 'canonical'
    for name, expected in read(canonical / 'source-hashes.json')['sha256'].items():
        assert sha(canonical / name) == expected
    print(f'Evidence valid: {len(manifest)} files; six strict module checks; '
          'ten standard-axiom declarations; 11,629 imported artifacts; 3,639 blueprint names.')
    print('Recorded checks only; no Lean compilation performed.')


if __name__ == '__main__':
    main()
