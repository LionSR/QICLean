"""Check the verified prerequisite join, the exact inclusion and immutable evidence."""
from pathlib import Path
import hashlib
import json
import subprocess

root = Path.cwd()
parent = '44817678b6bf19ea7b17a0722f43abccf5182f65'
count = 0
for record in subprocess.check_output(['git', 'ls-tree', '-rz', '--full-tree', parent]).split(b'\0'):
    if not record:
        continue
    info, name = record.split(b'\t', 1)
    _, kind, oid = info.split()
    if kind != b'blob':
        continue
    path = name.decode()
    data = (root / path).read_bytes()
    if path == 'QICLean/Representation.lean':
        line = b'import QICLean.Representation.PhysicalMergeHolder\n'
        assert data.count(line) == 1
        data = data.replace(line, b'')
    if path == 'blueprint/src/chapter/ch13_schur_labels.tex':
        line = b'\\input{fragment/physical_merge_holder}\n'
        assert data.count(line) == 1
        data = data.replace(line, b'')
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == oid.decode(), path
    count += 1
leaf = json.loads((root / 'docs/provenance/evidence/physicalMergeHolderFinal8753/manifest.json').read_text())
for path, item in leaf['artifacts'].items():
    data = (root / path).read_bytes()
    assert hashlib.sha256(data).hexdigest() == item['sha256'], path
    assert data == subprocess.check_output(['git', 'show', 'f932f7326e046299b0d0a59f43486dfa6f03b323:'+path])
for path, digest in leaf['production_sha256'].items():
    assert hashlib.sha256((root / path).read_bytes()).hexdigest() == digest, path
assert subprocess.check_output(['git', 'rev-parse', 'feat/area-law-compatible-physical-label'], text=True).strip() == '1a61097225a153adeb32270edb0778363e2ddfb1'
for path in ['QICLean/Representation/CompatiblePhysicalLabel.lean', 'blueprint/src/fragment/compatible_physical_label.tex']:
    assert (root / path).read_bytes() == subprocess.check_output(['git', 'show', '1a61097225a153adeb32270edb0778363e2ddfb1:'+path])
for path in ['QICLean/Analysis/OrthogonalResolution.lean', 'QICLean/Analysis/WeightedTraceHolder.lean', 'QICLean/Representation/GroupedLabelEntropy.lean', 'QICLean/Representation/MergeExponential.lean', 'QICLean/Representation/SchurSurprisal.lean', 'blueprint/src/fragment/weighted_trace_holder.tex']:
    assert (root / path).read_bytes() == subprocess.check_output(['git', 'show', 'f24f6b07ddf56b782f6e097e0fe6a95907fbeef2:'+path]), path
print(json.dumps(dict(verified_parent_join=parent, preserved_parent_files=count,
    exact_inclusion='one generated import and one unique chapter input',
    leaf_artifacts_preserved=len(leaf['artifacts']),
    compatible_and_holder_mathematical_sources='exact immutable prerequisite bytes',
    all_prerequisite_bound_evidence='unchanged')))
