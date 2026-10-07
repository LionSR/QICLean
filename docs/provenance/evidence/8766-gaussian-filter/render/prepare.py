#!/usr/bin/env python3
"""Prepare a single-leaf render without running Lean or changing the book router."""
from pathlib import Path
import argparse
import hashlib
import importlib.metadata
import json
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[5]
LEAF = Path('blueprint/src/chapter/ch12_entropy_gaussian_filter.tex')
MODULES = ('Kernel', 'MatrixIntegral', 'SpectralGap', 'GroundEstimate')
SOURCE_REVISION = '63a3390d92754752fcfbf055cb30e694bd31cfcb'
PAPER_REVISION = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--paper', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if out == ROOT or ROOT in out.parents:
        raise SystemExit('Use a render directory outside the checkout.')
    src = out / 'blueprint/src'
    src.mkdir(parents=True, exist_ok=True)
    copied = []
    for name in ('macros', 'print.tex', 'web.tex', 'plastex.cfg', 'extra_styles.css',
                 'blueprint.sty', 'texra_patches.sty', 'references.bib',
                 'tenkz_pic.sty', 'Packages', 'plastex_templates', 'latexmkrc'):
        source = ROOT / 'blueprint/src' / name
        target = src / name
        if source.is_dir():
            shutil.copytree(source, target, dirs_exist_ok=True)
            copied.extend(p for p in source.rglob('*') if p.is_file())
        else:
            shutil.copy2(source, target)
            copied.append(source)
    (out / 'scripts').mkdir(exist_ok=True)
    for relative in ('scripts/tenkz_paths.py', 'scripts/tenkz_blueprint_sweep.py',
                     'texra-blueprint.toml', 'tenkz.toml'):
        shutil.copy2(ROOT / relative, out / relative)
        copied.append(ROOT / relative)
    (src / 'chapter').mkdir(exist_ok=True)
    shutil.copy2(ROOT / LEAF, out / LEAF)
    (src / 'content.tex').write_text(
        '\\chapter{Gaussian filtering}\n'
        '\\label{ch:gaussian_focus}\n'
        '\\input{chapter/ch12_entropy_gaussian_filter}\n')
    # A title identifies the focused excerpt; mathematical content is unchanged.
    p = src / 'print.tex'
    p.write_text(p.read_text().replace(
        '\\providecommand{\\blueprinttitle}{Quantum Information and Channels:\\\\\n'
        '  \\large A formalization blueprint}',
        '\\providecommand{\\blueprinttitle}{Gaussian filtering:\\\\\n'
        '  \\large A focused mathematical blueprint}'))
    sources = {}
    tests = {}
    for module in MODULES:
        for relative, target in (
            (Path(f'QICLean/Analysis/GaussianFilter/{module}.lean'), sources),
            (Path(f'QICLeanTest/Gaussian{module}.lean'), tests),
        ):
            data = subprocess.check_output(
                ['git', 'show', f'{SOURCE_REVISION}:{relative}'], cwd=ROOT)
            if (ROOT / relative).read_bytes() != data:
                raise SystemExit(f'Current source differs from frozen revision: {relative}')
            target[str(relative)] = digest(data)
    manifest = {
        'source_revision': SOURCE_REVISION,
        'leaf': {'path': str(LEAF), 'sha256': digest((ROOT / LEAF).read_bytes())},
        'source_sha256': sources,
        'test_sha256': tests,
        'paper': {
            'revision': PAPER_REVISION,
            'filename': args.paper.name,
            'sha256': digest(args.paper.read_bytes()),
            'passage': 'lem:reset, Gaussian-filter passage, lines 426–452',
            'real_overlap': 'eq:info-reset-overlap, lines 402–414',
        },
        'tools': {name: importlib.metadata.version(name)
                  for name in ('texra-blueprint', 'plasTeX', 'leanblueprint')},
        'support_sha256': {str(p.relative_to(ROOT)): digest(p.read_bytes())
                           for p in sorted(copied)},
        'fixture_changes': ['Single-leaf router', 'Focused PDF title'],
        'scope': ['All four GaussianFilter modules and their 43 public declarations',
                  'No diagram: the cited passage is an algebraic integral argument'],
        'limits': ['No Lean/Lake/cache/checkdecls invocation by this renderer',
                   'No complete-book, root-import, or CI validation claim',
                   'Static HTML checks only; no browser/MathJax/responsive claim',
                   'No remote write; generated binaries and HTML remain untracked'],
    }
    (out / 'focus-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('Prepared single-leaf Gaussian-filter render and frozen source manifest.')


if __name__ == '__main__':
    main()
