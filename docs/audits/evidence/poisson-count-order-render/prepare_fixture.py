"""Freeze five exact blueprint leaves and render context from a committed source."""
from pathlib import Path
import hashlib
import importlib.metadata
import json
import os
import subprocess

ROOT = Path(__file__).resolve().parents[4]
BASE = Path(os.environ.get('WORKSPACE', ROOT.parent))
OUT = Path(os.environ.get('RENDER_DIR', BASE / 'poisson-count-order-focused'))
REV = subprocess.check_output(['git', 'rev-parse', os.environ.get('SOURCE_REVISION', 'HEAD')], cwd=ROOT, text=True).strip()
LEAVES = ['blueprint/src/chapter/' + n + '.tex' for n in [
    'ch11_poisson_word_counts', 'ch11_poisson_independent_counts',
    'ch11_finite_uniform_conditioning', 'ch11_poisson_uniform_order']]
CONTEXT = ['blueprint/src/chapter/ch11_poisson_word.tex']
MODULES = ['QICLean/Algebra/WordMultiplicity.lean'] + [
    'QICLean/Probability/' + n + '.lean' for n in [
        'PoissonWordCounts', 'PoissonWordIndependentCounts',
        'FiniteUniformConditioning', 'PoissonWordUniformOrder']]
CONTEXT_MODULES = ['QICLean/Probability/PoissonWord.lean']


def frozen(name):
    return subprocess.check_output(['git', 'show', f'{REV}:{name}'], cwd=ROOT)


def sha(data):
    return hashlib.sha256(data).hexdigest()


paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', REV, 'blueprint/src'], cwd=ROOT, text=True).splitlines()
chosen = [p for p in paths if '/chapter/' not in p and '/appendix/' not in p
          and Path(p).name not in ('content.tex', 'content_ft_mps.tex', 'print_ft_mps.tex')]
chosen += CONTEXT + LEAVES + ['texra-blueprint.toml', 'scripts/tenkz_paths.py', 'scripts/test_blueprint_web_render.py']
for name in chosen:
    target = OUT / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(frozen(name))
wrapper = '\\chapter{Poisson counts and uniform word order}\n\\label{ch:poisson_count_order_focus}\n' + ''.join(
    '\\input{' + p.removeprefix('blueprint/src/').removesuffix('.tex') + '}\n' for p in CONTEXT + LEAVES)
(OUT / 'blueprint/src/content.tex').write_text(wrapper)
paper = BASE / 'pinned-paper-sources/arealaw-09-amplification-adc7f124.tex'
assert sha(paper.read_bytes()) == '17cb317a40f7348cce2fff888a5a3b8c6fb5e9b240d0bc9eca27452db482807f'
manifest = {
    'source_revision': REV, 'target_leaves': LEAVES, 'context_leaves': CONTEXT,
    'render_leaves': CONTEXT + LEAVES, 'production_modules': MODULES,
    'context_modules': CONTEXT_MODULES,
    'source_sha256': {p: sha(frozen(p)) for p in MODULES + CONTEXT_MODULES + CONTEXT + LEAVES + [
        'blueprint/src/content.tex', 'lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'texra-blueprint.toml']},
    'fixture_source_sha256': {p: sha(frozen(p)) for p in chosen},
    'fixture_wrapper_sha256': sha(wrapper.encode()),
    'production_lines': sum(len(frozen(p).splitlines()) for p in MODULES),
    'fixture_only_changes': ['Replace content.tex with a single chapter wrapper selecting four target leaves and the prerequisite word-law leaf. All five leaves and all copied repository rendering context are byte-identical to the stated committed source.'],
    'tools': {p: importlib.metadata.version(p) for p in ['texra-blueprint', 'plasTeX', 'leanblueprint']},
    'paper': {
        'section_title': 'Amplifying the collar estimate',
        'revision': 'adc7f1241b42e322a6451854ab7e4b4c146bf78a',
        'upstream_path': 'preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/09-amplification.tex',
        'estimate_lines': [237, 253], 'chronology_lines': [49, 54],
        'retained_local_source': '${WORKSPACE}/pinned-paper-sources/arealaw-09-amplification-adc7f124.tex',
        'sha256': sha(paper.read_bytes())},
    'scope': 'Focused PDF and static HTML render of the fixed-time count-and-order package. No Lean compilation, full-book build, remote documentation check, external write, clock process, or locality theorem.'}
assert manifest['tools']['texra-blueprint'] == '0.3.8'
(OUT / 'focus-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'source_revision': REV, 'production_lines': manifest['production_lines'], 'copied_files': len(chosen), 'tools': manifest['tools']}, indent=2))
