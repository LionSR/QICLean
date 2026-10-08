"""Verify committed source and compact render evidence; standard library only."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[4]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


def check():
    record = json.loads((PACKET / 'verification.json').read_text())
    assert record['status'] == 'passed'
    for path, digest in record['source_sha256'].items():
        assert sha(ROOT / path) == digest, path
    for path, digest in json.loads((PACKET / 'packet-sha256.json').read_text()).items():
        assert sha(PACKET / path) == digest, path
    commands = json.loads((PACKET / 'commands.json').read_text())
    assert all(x['exit_code'] == 0 for x in commands['commands'])
    for name, script in commands['replay_scripts'].items():
        assert sha(PACKET / name) == script['published_sha256'], name
    leaf = ROOT / 'blueprint/src/chapter/ch12_entropy_unitary_evolution.tex'
    source = leaf.read_text()
    original = subprocess.check_output([
        'git', 'show',
        '2794faaae0faf0482d4533ed8168554b531903cd:' + str(leaf.relative_to(ROOT))
    ], cwd=ROOT, text=True)
    assert source.replace(r'^{\prime}', "'") == original
    decls = [n.strip() for g in re.findall(r'\\lean\{([^}]+)\}', source, re.S)
             for n in g.split(',')]
    assert len(decls) == len(set(decls)) == 16
    assert set(decls) == set(record['declarations'])
    assert source.count(r'\leanok') == 27
    assert source.count(r'^{\prime}') == 50
    assert not record['curly_math_prime_serialization']
    assert not record['missing_internal_anchors']
    assert not record['duplicate_html_ids']
    assert record['counts']['all_labels'] == 35
    assert record['counts']['equation_labels'] == 19
    assert record['counts']['pdf_declaration_links'] == 16
    assert record['counts']['html_chapter_declaration_links'] == 16
    for graph in record['dependency_graphs'].values():
        assert graph == {'nodes': 14, 'edges': 16,
                         'reachability_matches_explicit_uses': True}
    for p in PACKET.iterdir():
        if p.suffix in ('.json', '.md', '.py'):
            text = p.read_text()
            assert not re.search(r'/workspace/scratch/[0-9a-f]{12}', text), p.name
    print('PASS: frozen source, 16 declaration links, 35 labels, prime repair, and packet hashes')


if __name__ == '__main__':
    check()
