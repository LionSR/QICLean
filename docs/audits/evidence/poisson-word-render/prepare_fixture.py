"""Freeze only four Poisson-word leaves and repository render context; no downloads."""
from pathlib import Path
import hashlib, importlib.metadata, json, os, subprocess
BASE = Path(os.environ['WORKSPACE'])
ROOT = BASE / 'qiclean-poisson-decay-8757'
OUT = BASE / os.environ.get('RENDER_NAME', 'poisson-word-focused')
REV = os.environ.get('SOURCE_REVISION', '8e0a72aa2ad07a02a5c5a13436b17607fdd5af61')
LEAVES = ['blueprint/src/chapter/' + n + '.tex' for n in ['ch11_poisson_word', 'ch13_contraction_word_decay', 'ch13_contraction_word_decay_spectator', 'ch13_poisson_contraction_decay']]
MODULES = ['QICLean/Probability/PoissonWord.lean'] + ['QICLean/Analysis/' + n + '.lean' for n in ['ContractionWordDecay', 'ContractionWordDecaySpectator', 'PoissonContractionDecay']]
TESTS = ['QICLeanTest/' + n + suffix + '.lean' for n in ['PoissonWord','ContractionWordDecay','ContractionWordDecaySpectator','PoissonContractionDecay'] for suffix in ['', 'Axioms']]
def frozen(name):
    return subprocess.check_output(['git','show',f'{REV}:{name}'],cwd=ROOT)
def sha(data): return hashlib.sha256(data).hexdigest()
paths = subprocess.check_output(['git','ls-tree','-r','--name-only',REV,'blueprint/src'],cwd=ROOT,text=True).splitlines()
chosen = [p for p in paths if '/chapter/' not in p and '/appendix/' not in p and Path(p).name not in ('content.tex','content_ft_mps.tex','print_ft_mps.tex')]
chosen += LEAVES + ['texra-blueprint.toml','scripts/tenkz_paths.py','scripts/test_blueprint_web_render.py']
for name in chosen:
    target=OUT/name; target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(frozen(name))
wrapper='\\chapter{Poissonized word decay}\n\\label{ch:poisson_word_focus}\n'+''.join('\\input{'+p.removeprefix('blueprint/src/').removesuffix('.tex')+'}\n' for p in LEAVES)
(OUT/'blueprint/src/content.tex').write_text(wrapper)
paper=BASE/'pinned-paper-sources/arealaw-09-amplification-adc7f124.tex'
assert sha(paper.read_bytes())=='17cb317a40f7348cce2fff888a5a3b8c6fb5e9b240d0bc9eca27452db482807f'
manifest={
 'source_revision':REV,'target_leaves':LEAVES,'production_modules':MODULES,'test_modules':TESTS,
 'source_sha256':{p:sha(frozen(p)) for p in MODULES+TESTS+LEAVES+['blueprint/src/content.tex','lean-toolchain','lake-manifest.json','lakefile.toml','texra-blueprint.toml']},
 'fixture_source_sha256':{p:sha(frozen(p)) for p in chosen},'fixture_wrapper_sha256':sha(wrapper.encode()),
 'production_lines':sum(len(frozen(p).splitlines()) for p in MODULES),
 'fixture_only_changes':['Replace content.tex with one chapter wrapper selecting four byte-identical frozen leaves. Repository preambles, commands, bibliography, templates, styles and render configuration are unchanged.'],
 'tools':{p:importlib.metadata.version(p) for p in ['texra-blueprint','plasTeX','leanblueprint']},
 'paper':{'section_title':'Amplifying the collar estimate','revision':'adc7f1241b42e322a6451854ab7e4b4c146bf78a','upstream_path':'preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/09-amplification.tex','estimate_lines':[237,253],'chronology_lines':[49,54],'retained_local_source':'${WORKSPACE}/pinned-paper-sources/arealaw-09-amplification-adc7f124.tex','sha256':sha(paper.read_bytes())},
 'scope':'Focused PDF/static HTML only. No Lean/Lake/checkdecls, full-book build, live browser, remote documentation check, external write or publication.'}
assert manifest['tools']['texra-blueprint']=='0.3.8'
(OUT/'focus-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'source_revision':REV,'production_lines':manifest['production_lines'],'copied_files':len(chosen),'tools':manifest['tools']},indent=2))
