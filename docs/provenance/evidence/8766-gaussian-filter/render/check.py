#!/usr/bin/env python3
"""Check committed Gaussian blueprint coverage and frozen evidence; no Lean needed."""
from pathlib import Path
import hashlib
import json
import re
import runpy

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[4]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((PACKET / 'focus-manifest.json').read_text())
    report = json.loads((PACKET / 'verification.json').read_text())
    visual = json.loads((PACKET / 'visual-review.json').read_text())
    hashes = json.loads((PACKET / 'packet-sha256.json').read_text())
    for relative, digest in hashes.items():
        assert sha(PACKET / relative) == digest, relative
    leaf = ROOT / manifest['leaf']['path']
    assert sha(leaf) == manifest['leaf']['sha256'] == report['leaf_sha256']
    for group in ('source_sha256', 'test_sha256'):
        for relative, digest in manifest[group].items():
            assert sha(ROOT / relative) == digest, relative
    tex = leaf.read_text()
    refs = [d.strip() for group in re.findall(r'\\lean\{([^}]+)\}', tex)
            for d in group.split(',')]
    api = runpy.run_path(str(ROOT / 'scripts/blueprint_lean_sync.py'))
    public = [d.fqn for relative in manifest['source_sha256']
              for d in api['collect_file_lean_decls'](ROOT / relative, ROOT / 'QICLean')
              if not d.is_private and d.kind in ('def', 'theorem', 'lemma')]
    assert len(refs) == len(set(refs)) == len(public) == 43
    assert set(refs) == set(public) == set(report['rendered_declarations'])
    assert report['missing_internal_anchors'] == []
    assert report['pdf_layout_or_reference_errors'] == []
    assert report['diagram_count'] == 0
    assert report['pdf_sha256'] == visual['final_pdf_sha256']
    assert visual['pages_inspected_at_reading_size'] == [3, 4, 5, 6, 7]
    commands = json.loads((PACKET / 'commands.json').read_text())
    assert all(code == 0 for code in commands['exit_codes'].values())
    for record in commands['normalization']:
        assert sha(PACKET / record['destination']) == record['normalized_sha256']
    for path in PACKET.iterdir():
        if path.is_file() and path.suffix != '.py':
            assert not re.search(r'/workspace/|/home/agent/|/root/|/tmp/', path.read_text()), path.name
    print('PASS: all 43 public references, frozen source/test bytes, final render evidence, and packet hashes')


if __name__ == '__main__':
    main()
