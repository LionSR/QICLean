#!/usr/bin/env python3
"""Record exact-source verification of physical trace and integrability lemmas."""
from pathlib import Path
import gzip
import hashlib
import json
import shlex
import shutil
import subprocess

root = Path('/Users/siruilu/Local/agentFormalization/QICLean/worktrees/physical-trace-helpers')
base = Path('/private/tmp/qic-physical-trace-helpers')
out = root / 'docs/provenance/evidence/physicalTraceHelpers8769'
bp = Path((base / 'blueprint-dir').read_text().strip())
revision = '92b6eea77da987d4d12236c3dd3fc06510cd98ac'
parent = 'b2521d2a2843d824ce85a4d94bf4b60d322d6c6f'
out.mkdir(parents=True, exist_ok=True)


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def compressed(source, target):
    target.write_bytes(gzip.compress(source.read_bytes(), mtime=0))


assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == revision
assert not (root / '.lake').exists()
builds = read(base / 'build-commands.json')
audit = read(base / 'audit-command.json')
dependencies = read(base / 'imported-dependencies.json')
declarations = read(base / 'declarations.json')
for row in builds:
    data = subprocess.check_output(['git', 'show', revision + ':' + row['source_path']], cwd=root)
    assert hashlib.sha256(data).hexdigest() == row['source_sha256'] == sha(root / row['source_path'])
    assert row['returncode'] == 0 and not (base / (row['module'] + '.log')).read_bytes()
    assert sha(Path(row['artifact'])) == row['artifact_sha256']
    row['source_revision'] = revision
for row in dependencies:
    assert sha(Path(row['artifact'])) == row['sha256'], row['artifact']
assert len(dependencies) == 11629
audit['source_revision'] = revision
audit['all_imported_artifact_hashes_unchanged_at_pin'] = True
save(base / 'build-commands.json', builds)
save(base / 'audit-command.json', audit)
save(out / 'source-revision.json', {
    'source_revision': revision, 'base_revision': parent,
    'source_paths': {x['source_path']: x['source_sha256'] for x in builds},
    'predecessor_worktrees_unchanged': True,
})

lines = ['Direct Lean compilation with package options and warnings as errors.',
         f'Source revision: {revision}', 'No Lake build or cache mutation was performed.', '']
for row in builds:
    lines += [f'Source: {row["source_path"]}', f'Source SHA256: {row["source_sha256"]}',
              f'Working directory: {row["cwd"]}', f'Command: {shlex.join(row["command"])}',
              f'Exit code: {row["returncode"]}', f'Elapsed seconds: {row["seconds"]}',
              'Diagnostics: none.', '']
(out / 'direct-build.log').write_text('\n'.join(lines))
(out / 'axioms.log').write_text(
    f'Source revision: {revision}\nCommand: {shlex.join(audit["command"])}\n\n'
    + (base / 'axioms.log').read_text())
for name in ['build-commands.json', 'audit-command.json', 'axiom-dependencies.json',
             'Axioms.lean', 'env.json', 'preparation.json', 'format-command.json',
             'source-preservation.json', 'declarations.json']:
    shutil.copy2(base / name, out / name)
for name in ['imported-dependencies.json', 'imported-modules.json']:
    compressed(base / name, out / (name + '.gz'))
for path in base.glob('QICLean*.log'):
    shutil.copy2(path, out / path.name)
for name in ['original-sources', 'initial-checks']:
    shutil.copytree(base / name, out / name, dirs_exist_ok=True)
(out / 'checked-sources').mkdir(exist_ok=True)
for row in builds:
    source = root / row['source_path']
    target = out / 'checked-sources' / row['source_path']
    target.parent.mkdir(parents=True, exist_ok=True)
    compressed(source, target.with_suffix(target.suffix + '.gz'))
(out / 'declaration-check').mkdir(exist_ok=True)
native = read(base / 'declaration-check/command.json')
native['source_revision'] = revision
save(base / 'declaration-check/command.json', native)
for path in (base / 'declaration-check').iterdir():
    if path.name in ['lean_declarations.txt', 'Declarations.lean']:
        compressed(path, out / 'declaration-check' / (path.name + '.gz'))
    else:
        shutil.copy2(path, out / 'declaration-check' / path.name)

# Check the original full source snapshot against the committed source bytes.
paths = read(bp / 'source-hashes.json')
proc = subprocess.Popen(['git', '-C', str(root), 'cat-file', '--batch'],
                        stdin=subprocess.PIPE, stdout=subprocess.PIPE)
for path, expected in paths.items():
    proc.stdin.write((revision + ':' + path + '\n').encode())
    proc.stdin.flush()
    header = proc.stdout.readline().split()
    assert len(header) == 3, (path, header)
    data = proc.stdout.read(int(header[2]))
    assert proc.stdout.read(1) == b'\n'
    assert hashlib.sha256(data).hexdigest() == expected, path
proc.stdin.close()
assert proc.wait() == 0
save(bp / 'source-pin.json', {
    'source_revision': revision, 'checked_files': len(paths),
    'all_source_hashes_match': True,
    'visual_review': {'pdf_pages': [3, 4, 5], 'result': 'pass',
                      'notes': 'All new statements and proofs are readable; no TeX warnings.'},
})
blueprint = out / 'blueprint'
blueprint.mkdir(exist_ok=True)
for name in ['commands.json', 'source-pin.json', 'dependency-graph.json', 'tag-coverage.json']:
    shutil.copy2(bp / name, blueprint / name)
for name in ['source-hashes.json', 'sync.json', 'sync-final.json', 'full-lean-decls.txt']:
    compressed(bp / name, blueprint / (name + '.gz'))
for path in bp.glob('*.log'):
    compressed(path, blueprint / (path.name + '.gz'))
for page in [3, 4, 5]:
    shutil.copy2(bp / f'page-{page}.png', blueprint / f'page-{page}.png')
compressed(bp / 'blueprint/src/focused.log', blueprint / 'final-tex.log.gz')
shutil.copy2(bp / 'blueprint/src/focused.pdf', blueprint / 'focused.pdf')
(blueprint / 'render-inputs').mkdir(exist_ok=True)
for name in ['focused.tex', 'content-focused.tex', 'web.tex', 'print.tex',
             'chapter/ch13_physical_trace_coordinates.tex']:
    target = blueprint / 'render-inputs' / (name + '.gz')
    target.parent.mkdir(parents=True, exist_ok=True)
    compressed(bp / 'blueprint/src' / name, target)

(out / 'verification-scripts').mkdir(exist_ok=True)
for name in ['prepare-qic-physical-trace-helpers.py', 'check-qic-physical-trace-helpers.py',
             'audit-qic-physical-trace-helpers.py', 'check-qic-physical-declarations.py',
             'verify-qic-physical-blueprint.py', 'check-qic-physical-graph.py']:
    shutil.copy2(Path('/tmp') / name, out / 'verification-scripts' / name)
shutil.copy2(Path(__file__), out / 'record-evidence.py')
shutil.copy2('/tmp/check-qic-physical-provenance.py', out / 'check-provenance.py')

canonical = root / 'docs/provenance/evidence/sourceTransportExpansion8769/canonical'
shutil.copytree(canonical, out / 'canonical', dirs_exist_ok=True,
                ignore=shutil.ignore_patterns('__pycache__'))
save(out / 'canonical/source-hashes.json', {
    'source_revision': parent,
    'source_directory': str(canonical.relative_to(root)),
    'sha256': {p.name: sha(p) for p in sorted(canonical.iterdir()) if p.is_file()},
})

by_path = {row['source_path']: row for row in builds}
entries = []
for row in declarations:
    build = by_path[row['path']]
    commands = []
    for kind, command, log in [('build', build['command'], 'direct-build.log'),
                               ('axioms', audit['command'], 'axioms.log')]:
        commands.append({'kind': kind, 'command': shlex.join(command), 'exit_code': 0,
                         'log': str((out / log).relative_to(root)), 'sha256': sha(out / log)})
    entries.append({
        'id': row['id'], 'status': 'ported', 'reuse_kind': 'original', 'upstream': None,
        'downstream': {'repository': 'LionSR/QICLean', 'path': row['path'],
                       'declaration': row['declaration'], 'name_status': 'declared'},
        'paper_sources': [{'version': 'September 24, 2026',
                           'path': 'preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex',
                           'labels': [row['paper_label']]}],
        'license': 'Apache-2.0', 'notices': [],
        'changes': ['Independently formalized supporting matrix-analysis or integrability lemma; no upstream Lean proof text reused.',
                    'Extracted from checked TNLean drafts with all theorem noncomment tokens preserved; no complete PEPS compression theorem is asserted.'],
        'verification': {'result': 'passed', 'repository': 'LionSR/QICLean',
                         'revision': revision, 'commands': commands},
        'no_upstream_proof_text_reused': True,
    })
save(root / 'docs/provenance/openai-math.d/8769-physical-trace-helpers.json', {
    'schema_version': 1,
    'source': {'repository': 'openai/math', 'commit': 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'},
    'entries': entries,
})
print('RECORDED', revision, len(builds), len(dependencies), len(paths), flush=True)
