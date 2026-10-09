#!/usr/bin/env python3
"""Prepare a new, exact six-leaf focused fixture; never run Lean or mutate source."""
import argparse
import hashlib
import importlib.metadata
import json
from pathlib import Path
import shutil
import subprocess

LEAVES = (
    'ch12_entropy_physical_buffer_overlap',
    'ch12_entropy_doubled_system_gap',
    'ch12_entropy_gaussian_filter',
    'ch12_entropy_gaussian_parameters',
    'ch12_entropy_gaussian_uniform_ground',
    'ch12_entropy_gaussian_physical_uniform',
)
LIMITS = [
    'Focused PDF and static HTML only; no full-book, browser, MathJax runtime, or responsive-layout claim.',
    'No Lean/Lake/checkdecls build or remote write; source parsing is not proof validation.',
    'Generated PDF, HTML, diagram SVG, and page images stay outside Git.',
    'Remote declaration-documentation URLs are checked for identity, not availability.',
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root, out = args.source_root.resolve(), args.output.resolve()
    assert out != root and root not in out.parents, 'Use an external fixture.'
    assert not out.exists(), 'Use a new directory; preserve earlier evidence.'
    src = out / 'blueprint/src'
    src.mkdir(parents=True)
    copied = []
    for name in ('macros', 'print.tex', 'web.tex', 'plastex.cfg', 'extra_styles.css',
                 'blueprint.sty', 'texra_patches.sty', 'references.bib', 'tenkz_pic.sty',
                 'Packages', 'plastex_templates', 'latexmkrc'):
        source, target = root / 'blueprint/src' / name, src / name
        if source.is_dir():
            shutil.copytree(source, target, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
            copied.extend(p.relative_to(root) for p in source.rglob('*')
                          if p.is_file() and p.suffix != '.pyc')
        else:
            shutil.copy2(source, target)
            copied.append(source.relative_to(root))
    (out / 'scripts').mkdir()
    for name in ('scripts/tenkz_paths.py', 'scripts/tenkz_blueprint_sweep.py',
                 'texra-blueprint.toml', 'tenkz.toml'):
        shutil.copy2(root / name, out / name)
        copied.append(Path(name))
    (src / 'chapter').mkdir()
    leaves = [Path('blueprint/src/chapter') / (name + '.tex') for name in LEAVES]
    for leaf in leaves:
        shutil.copy2(root / leaf, out / leaf)
    (src / 'content.tex').write_text(
        '\\chapter{Uniform Gaussian filtering on the physical buffer}\n'
        '\\label{ch:gaussian_uniform_physical_focus}\n' +
        ''.join(f'\\input{{chapter/{name}}}\n' for name in LEAVES))
    path = src / 'print.tex'
    path.write_text(path.read_text().replace(
        '\\providecommand{\\blueprinttitle}{Quantum Information and Channels:\\\\\n'
        '  \\large A formalization blueprint}',
        '\\providecommand{\\blueprinttitle}{Uniform physical-buffer Gaussian filtering:\\\\\n'
        '  \\large A focused mathematical blueprint}'))
    assert path.read_bytes() != (root / 'blueprint/src/print.tex').read_bytes()
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
    source_paths = sorted((root / 'QICLean/Analysis/GaussianFilter').glob('*.lean'))
    for leaf in leaves:
        assert subprocess.check_output(['git', 'show', f'{revision}:{leaf}'], cwd=root) == (root / leaf).read_bytes()
    manifest = {
        'source_revision': revision,
        'leaves_sha256': {str(p): sha(root / p) for p in leaves},
        'source_sha256': {str(p.relative_to(root)): sha(p) for p in source_paths},
        'support_source_sha256': {str(p): sha(root / p) for p in sorted(copied)},
        'support_fixture_sha256': {str(p): sha(out / p) for p in sorted(copied)},
        'router_sha256': sha(src / 'content.tex'),
        'tools': {n: importlib.metadata.version(n) for n in ('texra-blueprint', 'plasTeX', 'leanblueprint')},
        'fixture_changes': ['Focused content router and PDF title only; all six source leaves are unchanged.'],
        'limits': LIMITS,
    }
    (out / 'focus-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('Prepared six exact leaves from ' + revision)


if __name__ == '__main__':
    main()
