"""Prepare exact frozen source for focused rendering; never run Lean/Lake."""
from pathlib import Path
import os
import hashlib, importlib.metadata, json, subprocess

BASE = Path(os.environ['WORKSPACE'])
ROOT = BASE / 'qiclean-interaction-picture-8745'
OUT = BASE / '8766-unitary-evolution-focused'
REV = '220aa2735fbc5f1629c2782edb6b43ae8951ceb3'
LEAF = 'blueprint/src/chapter/ch12_entropy_unitary_evolution.tex'

def frozen(name):
    return subprocess.check_output(['git', 'show', f'{REV}:{name}'], cwd=ROOT)

def sha(data):
    return hashlib.sha256(data).hexdigest()

paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', REV, 'blueprint/src'], cwd=ROOT, text=True).splitlines()
chosen = [p for p in paths if '/chapter/' not in p and '/appendix/' not in p and Path(p).name not in ('content.tex', 'content_ft_mps.tex', 'print_ft_mps.tex')]
chosen += [LEAF, 'texra-blueprint.toml', 'scripts/tenkz_paths.py']
for name in chosen:
    target = OUT / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(frozen(name))
(OUT / 'blueprint/src/content.tex').write_text('\\chapter{Quantum entropy}\n\\label{ch:unitary_evolution_focus}\n\\input{chapter/ch12_entropy_unitary_evolution}\n')
modules = [f'QICLean/Analysis/{m}.lean' for m in ['MatrixEvolution', 'UnitaryEvolution', 'ProjectedEvolution']]
tests = [f'QICLeanTest/{m}.lean' for m in ['MatrixEvolution', 'UnitaryEvolution', 'ProjectedEvolution']]
source_names = modules + tests + [LEAF, 'blueprint/src/chapter/ch12_entropy.tex']
paper = BASE / 'pinned-paper-sources/peps-02-information-adc7f124.tex'
manifest = {
    'source_revision': REV,
    'target_leaf': LEAF,
    'source_sha256': {p: sha(frozen(p)) for p in source_names},
    'fixture_source_sha256': {p: sha(frozen(p)) for p in chosen},
    'production_modules': modules,
    'test_modules': tests,
    'production_lines': sum(len(frozen(p).splitlines()) for p in modules),
    'fixture_only_changes': ['Replace content.tex with one Quantum entropy chapter wrapper and the byte-identical unitary-evolution leaf. Repository preambles, macros, packages, templates, full bibliography, and configuration are unchanged.'],
    'tools': {p: importlib.metadata.version(p) for p in ['texra-blueprint', 'plasTeX', 'leanblueprint']},
    'paper': {'revision': 'adc7f1241b42e322a6451854ab7e4b4c146bf78a', 'lines': [513, 536], 'retained_local_source': '${WORKSPACE}/pinned-paper-sources/peps-02-information-adc7f124.tex', 'sha256': sha(paper.read_bytes())},
    'scope': 'Focused PDF and static HTML; no Lean/Lake/checkdecls execution, full-book build, live browser, or remote publication.'
}
(OUT / 'focus-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'fixture': str(OUT), 'frozen_source': REV, 'production_lines': manifest['production_lines'], 'tools': manifest['tools'], 'copied_files': len(chosen)}, indent=2))
