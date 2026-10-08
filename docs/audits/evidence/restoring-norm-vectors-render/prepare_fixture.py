"""Snapshot four restoration leaves and one exact partial-trace context definition using installed render tools only."""
from pathlib import Path
import hashlib, importlib.metadata, json, os, subprocess

BASE = Path(os.environ['WORKSPACE'])
ROOT = BASE / 'qiclean-singular-restoration-8757'
OUT = BASE / 'restoring-norm-vectors-focused'
REV = os.environ.get('SOURCE_REVISION', '947cfcb24904c7ba5c83e9723f9c0db994731935')
LEAVES = ['blueprint/src/chapter/ch12_support_inverse_sandwich.tex',
          'blueprint/src/chapter/ch12_entropy_restoring_operators.tex',
          'blueprint/src/chapter/ch12_entropy_restoring_norm.tex',
          'blueprint/src/chapter/ch12_entropy_restoring_vectors.tex']
MODULES = ['QICLean/Analysis/SupportInverseSandwich.lean',
           'QICLean/Entropy/RestoringMarginal.lean',
           'QICLean/Entropy/RestoringOperators.lean',
           'QICLean/Entropy/RestoringNorm.lean', 'QICLean/Entropy/RestoringVectors.lean']
TESTS = [f'QICLeanTest/{m}{suffix}.lean' for m in
         ['SupportInverseSandwich', 'RestoringMarginal', 'RestoringOperators', 'RestoringNorm', 'RestoringVectors']
         for suffix in ['', 'Axioms']]
DRIVERS = ['docs/audits/evidence/support-inverse-sandwich/SupportInverseSandwichAxiomsRaw.lean',
           'docs/audits/evidence/restoring-marginal/RestoringMarginalRawAxioms.lean',
           'docs/audits/evidence/restoring-marginal/RestoringOperatorsRawAxioms.lean',
           'docs/audits/evidence/restoring-marginal/RestoringNormRawAxioms.lean']
def frozen(name):
    return subprocess.check_output(['git', 'show', f'{REV}:{name}'], cwd=ROOT)
def sha(data):
    return hashlib.sha256(data).hexdigest()
paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', REV, 'blueprint/src'], cwd=ROOT, text=True).splitlines()
chosen = [p for p in paths if '/chapter/' not in p and '/appendix/' not in p and Path(p).name not in ('content.tex', 'content_ft_mps.tex', 'print_ft_mps.tex')]
chosen += LEAVES + ['texra-blueprint.toml', 'scripts/tenkz_paths.py', 'scripts/test_blueprint_web_render.py']
for name in chosen:
    target = OUT / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(frozen(name))
context_path = 'blueprint/src/chapter/ch03_channel_representations_choi_and_kraus.tex'
context_text = frozen(context_path).decode()
start = context_text.index('\\begin{definition}[Partial traces]')
end = context_text.index('\\end{definition}', start) + len('\\end{definition}')
context = context_text[start:end] + '\n'
(OUT / 'blueprint/src/partial-trace-context.tex').write_text(context)
wrapper = '\\chapter{Quantum entropy}\n\\label{ch:restoring_norm_vectors_focus}\n\\input{partial-trace-context}\n' + ''.join('\\input{' + p.removeprefix('blueprint/src/').removesuffix('.tex') + '}\n' for p in LEAVES)
(OUT / 'blueprint/src/content.tex').write_text(wrapper)
paper = BASE / 'pinned-paper-sources/arealaw-09-amplification-adc7f124.tex'
assert sha(paper.read_bytes()) == '17cb317a40f7348cce2fff888a5a3b8c6fb5e9b240d0bc9eca27452db482807f'
manifest = {
    'source_revision': REV, 'target_leaves': LEAVES,
    'new_leaves': LEAVES[2:],
    'context': {'source_path': context_path, 'first_line': context_text[:start].count('\n') + 1, 'last_line': context_text[:end].count('\n') + 1, 'fixture_path': 'blueprint/src/partial-trace-context.tex', 'sha256': sha(context.encode()), 'declarations': ['Matrix.traceLeft', 'Matrix.traceRight', 'Matrix.partialTraceRight', 'Matrix.partialTraceRight_apply']},
    'source_sha256': {p: sha(frozen(p)) for p in MODULES + TESTS + DRIVERS + LEAVES + [context_path, 'QICLean/Channel/PartialTrace.lean', 'blueprint/src/chapter/ch12_entropy.tex']},
    'fixture_source_sha256': {p: sha(frozen(p)) for p in chosen},
    'fixture_wrapper_sha256': sha(wrapper.encode()),
    'production_modules': MODULES, 'test_modules': TESTS, 'raw_axiom_drivers': DRIVERS,
    'production_lines': sum(len(frozen(p).splitlines()) for p in MODULES),
    'fixture_only_changes': ['Replace content.tex with one Quantum entropy chapter wrapper selecting four byte-identical frozen restoration leaves plus the exact partial-trace definition excerpt for cross-reference context. All selected repository preambles, macros, packages, templates, bibliography, and configuration are unchanged.'],
    'tools': {p: importlib.metadata.version(p) for p in ['texra-blueprint', 'plasTeX', 'leanblueprint']},
    'paper': {'revision': 'adc7f1241b42e322a6451854ab7e4b4c146bf78a', 'upstream_path': 'preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/09-amplification.tex', 'lines': [324, 446], 'retained_local_source': '${WORKSPACE}/pinned-paper-sources/arealaw-09-amplification-adc7f124.tex', 'sha256': sha(paper.read_bytes())},
    'scope': 'Focused PDF and static HTML; no Lean/Lake/checkdecls, full-book build, live browser, remote documentation access, or publication.'
}
assert manifest['tools']['texra-blueprint'] == '0.3.8'
assert manifest['production_lines'] == 1282
(OUT / 'focus-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'fixture': str(OUT), 'frozen_source': REV, 'production_lines': manifest['production_lines'], 'tools': manifest['tools'], 'copied_files': len(chosen)}, indent=2))
