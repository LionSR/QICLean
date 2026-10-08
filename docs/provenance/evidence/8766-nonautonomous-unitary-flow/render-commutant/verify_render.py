"""Check focused unitary-evolution artifacts without Lean or browser execution."""
from collections import Counter
from datetime import datetime, timezone
from html.parser import HTMLParser
from pathlib import Path
import os
from urllib.parse import unquote, urlsplit
import hashlib, json, re, runpy, subprocess
from pypdf import PdfReader

BASE = Path(os.environ['WORKSPACE'])
ROOT = BASE / 'qiclean-interaction-picture-8745'
OUT = BASE / '8766-unitary-commutant-focused'
manifest = json.loads((OUT / 'focus-manifest.json').read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rev = manifest['source_revision']
frozen = lambda p: subprocess.check_output(['git', 'show', f'{rev}:{p}'], cwd=ROOT)
leaf = manifest['target_leaf']
source = (OUT / leaf).read_text()
assert (OUT / leaf).read_bytes() == frozen(leaf)
for p, digest in manifest['source_sha256'].items():
    assert hashlib.sha256(frozen(p)).hexdigest() == digest, p
for p, digest in manifest['fixture_source_sha256'].items():
    assert sha(OUT / p) == digest, p
assert frozen('blueprint/src/chapter/ch12_entropy.tex').decode().rstrip().endswith('\\input{chapter/ch12_entropy_unitary_evolution}')
decls = [x.strip() for g in re.findall(r'\\lean\{([^}]+)\}', source, re.S) for x in g.split(',')]
public = []
for p in manifest['production_modules']:
    text = frozen(p).decode()
    names = re.findall(r'^(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?(?:theorem|def|lemma)\s+(\S+)', text, re.M)
    public.extend(n if n.startswith('Matrix.') else 'MatrixEvolution.' + n for n in names)
assert len(public) == len(decls) == 19 and Counter(public) == Counter(decls), (public, decls)
labels = re.findall(r'\\label\{([^}]+)\}', source)
assert len(labels) == len(set(labels))
refs = re.findall(r'\\ref\{([^}]+)\}', source)
assert set(refs) <= set(labels)
assert source.count('\\leanok') == 33
assert not re.search(r'\\begin\{(?:tikzpicture|tenkz)', source)

class Page(HTMLParser):
    def __init__(self, text):
        super().__init__(); self.ids=[]; self.links=[]; self.lean=[]; self.images=[]; self.text=[]; self.classes=Counter(); self.feed(text)
    def handle_starttag(self, tag, attrs):
        a=dict(attrs)
        if 'id' in a: self.ids.append(a['id'])
        if tag=='a' and 'name' in a and a.get('name')!=a.get('id'): self.ids.append(a['name'])
        self.classes.update(a.get('class','').split())
        if tag == 'a' and 'href' in a:
            self.links.append(a['href'])
            if 'lean_decl' in a.get('class','').split(): self.lean.append(a['href'])
        if tag == 'img': self.images.append(a.get('src',''))
    def handle_data(self, text): self.text.append(text)

web = OUT / 'blueprint/web'
pages = {p.name: Page(p.read_text()) for p in sorted(web.glob('*.html'))}
missing=[]
for name, page in pages.items():
    assert not [k for k,v in Counter(page.ids).items() if v>1], name
    for href in page.links:
        u=urlsplit(href)
        if u.scheme or u.netloc or u.path.startswith('../'): continue
        target=u.path or name
        if target.endswith('.html'):
            if target not in pages: missing.append([name,href,'file'])
            elif u.fragment and unquote(u.fragment) not in pages[target].ids: missing.append([name,href,'anchor'])
    for img in page.images: assert (web/img).is_file(), (name,img)
    visible=' '.join(page.text)
    assert '??' not in visible and not re.search(r'\\(?:lean|leanok|mathlibok|uses)\b', visible), name
assert not missing, missing
chapter = pages['ch-unitary_evolution_focus.html']
assert set(labels) <= set(chapter.ids), set(labels)-set(chapter.ids)
getname=lambda u: unquote(urlsplit(u).fragment).removeprefix('doc/')
assert Counter(map(getname, chapter.lean)) == Counter(decls)
for name in ['dep_graph_document.html','dep_graph_chapter_1.html']:
    assert Counter(map(getname, pages[name].lean)) == Counter(decls), name
assert chapter.classes['theorem_thmwrapper']==16
assert chapter.classes['definition_thmwrapper']==1
assert chapter.classes['proof_wrapper']==16
runpy.run_path(str(OUT/'scripts/test_blueprint_web_render.py'))['_assert_generated_source'](list(web.glob('*.html')))

# Rendered graph applies transitive reduction. Compare all dependency reachability,
# not a naive equality between explicit uses and the reduced graph edge set.
chunks = re.split(r'(?=\\begin\{(?:theorem|definition)\})', source)[1:]
entries=[]; explicit=set()
for chunk in chunks:
    label=re.search(r'\\label\{((?:thm|def):[^}]+)\}',chunk).group(1)
    entries.append(label)
    for group in re.findall(r'\\uses\{([^}]+)\}',chunk,re.S):
        for dep in group.split(','): explicit.add((dep.strip(),label))
assert set(x for pair in explicit for x in pair) <= set(entries)
assert ('thm:unitary_evolution_fixed_derivative', 'thm:unitary_evolution_conserved') in explicit
assert ('thm:unitary_evolution_preserved', 'thm:unitary_evolution_commutes') in explicit
assert ('thm:unitary_evolution_conserved', 'thm:unitary_evolution_commutes') in explicit
assert len(entries) == 17 and len(explicit) == 25
assert source.count(r'CG(t)-G(t)C') == 2
assert source.count(r'Neither Hermiticity of $C$ nor an initial-value condition is required.') == 1
assert 'The matrix $C$ need not be Hermitian or unitary.' in source
assert 'This includes negative times and a zero-dimensional matrix algebra.' in source
lean = frozen('QICLean/Analysis/UnitaryEvolution.lean').decode()
assert '(Complex.I • (C * G t - G t * C))' in lean
assert '[Nonempty n]' not in lean
assert 'IsHermitian C' not in lean and 'C.IsHermitian' not in lean
consumers = frozen('QICLeanTest/EvolutionCommutant.lean').decode()
assert len(re.findall(r'^example\b', consumers, re.M)) == 6
assert '(-2)' in consumers and '(Fin 0)' in consumers and '!![0, 1; 0, 0]' in consumers
def closure(edges):
    result=set(edges)
    while True:
        more={(a,d) for a,b in result for c,d in result if b==c}
        if more<=result: return result
        result |= more
graph_records={}
for filename in ['dep_graph_document.html','dep_graph_chapter_1.html']:
    text=(web/filename).read_text()
    dot=re.search(r'\.renderDot\(`(.*?)`\)',text,re.S).group(1)
    nodes=set(re.findall(r'"((?:thm|def):[^" ]+)"\s*\[',dot))
    edges=set(re.findall(r'"((?:thm|def):[^" ]+)"\s*->\s*"((?:thm|def):[^" ]+)"',dot))
    assert nodes==set(entries), nodes^set(entries)
    assert closure(edges)==closure(explicit), (edges, explicit)
    assert not any(a==b for a,b in closure(edges))
    assert dot.count('fillcolor="#1CAC78"')==16 and dot.count('fillcolor="#B0ECA3"')==1
    graph_records[filename]={'nodes':len(nodes),'edges':len(edges),'reachability_matches_explicit_uses':True}
    if filename=='dep_graph_chapter_1.html': (OUT/'dependency-graph.dot').write_text(dot+'\n')

pdf=PdfReader(OUT/'blueprint/src/print.pdf')
uris=[]; destlinks=[]
for page in pdf.pages:
    for ref in page.get('/Annots',[]):
        obj=ref.get_object(); action=obj.get('/A',{})
        if action.get('/URI'): uris.append(str(action['/URI']))
        if action.get('/S')=='/GoTo': destlinks.append(str(action['/D']))
        if obj.get('/Dest'): destlinks.append(str(obj['/Dest']))
pdfdecls=[getname(u) for u in uris if '/find/' in u and '#doc/' in u]
assert Counter(pdfdecls)==Counter(decls)
aux=(OUT/'blueprint/src/print.aux').read_text()
destmap={m[0]:m[1:] for m in re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}\{([^}]+)\}\{[^}]*\}\{([^}]+)\}',aux)}
assert set(labels)<=set(destmap)
for label in labels: assert destmap[label][2] in pdf.named_destinations, label
assert set(destlinks)<=set(pdf.named_destinations), set(destlinks)-set(pdf.named_destinations)
assert '??' not in '\n'.join(page.extract_text() for page in pdf.pages)
log=(OUT/'blueprint/src/print.log').read_text()
assert not re.search(r'^!|Overfull|Underfull|Missing character|undefined|LaTeX Warning',log,re.M)
assert '\\bibcite{OpenAI2026PolynomialPEPS}' in aux
assert 'OpenAI2026PolynomialPEPS' in (web/'sect0001.html').read_text()
curly=[]
for filename in pages:
    for match in re.finditer(r'<div class="displaymath"[^>]*>(.*?)</div>',(web/filename).read_text(),re.S):
        if '\u2019' in match.group(1): curly.append({'page':filename,'display':match.group(0)})
prime_source_count = source.count(r'^{\prime}')
prime_html_count = len(re.findall(r'\^\{\\prime\s*\}',(web/'ch-unitary_evolution_focus.html').read_text()))
assert prime_source_count==prime_html_count==52
assert not curly, curly
artifacts=[OUT/'blueprint/src/print.pdf',OUT/'blueprint/src/print.aux',*sorted(web.glob('*.html')),*sorted((OUT/'pdf-pages').glob('*.png'))]
result={
 'status':'passed' if not curly else 'structural checks passed; math-prime serialization requires repair',
 'recorded_at_utc':datetime.now(timezone.utc).isoformat(),
 'source_revision':rev,'source_sha256':manifest['source_sha256'],
 'counts':{'production_modules':3,'production_lines':manifest['production_lines'],'public_declarations':len(public),'blueprint_entries':len(entries),'proofs':16,'checked_markers':33,'equation_labels':sum(x.startswith('eq:') for x in labels),'all_labels':len(labels),'pdf_pages':len(pdf.pages),'html_pages':len(pages),'pdf_declaration_links':len(pdfdecls),'html_chapter_declaration_links':len(chapter.lean),'html_all_declaration_links':sum(len(p.lean) for p in pages.values()),'pdf_internal_link_annotations':len(destlinks),'explicit_dependency_edges':len(explicit),'diagrams':0},
 'declarations':decls,'labels':labels,'dependency_graphs':graph_records,'explicit_dependency_edges':sorted(explicit),
 'missing_internal_anchors':missing,'duplicate_html_ids':[],'tex_box_reference_warnings':[],
 'curly_math_prime_serialization':curly,
 'explicit_math_primes':{'source':prime_source_count,'html_chapter':prime_html_count},
 'commutant_checks':{'commutator_order':'C*G-G*C','arbitrary_fixed_matrix':True,'signed_time_and_empty_index':True,'six_consumer_examples_source_inspected':True,'new_proof_dependency_edges_verified':3},
 'artifact_sha256':{str(p.relative_to(OUT)):sha(p) for p in artifacts},
 'raw_log_sha256':{p:sha(OUT/p) for p in ['pdf-build.log','web-build.log','pdf-raster.log']},
 'limits':['Focused fixture only; no full-book build or live browser/MathJax runtime/responsive/click testing.','Declaration identifiers and generated local anchors verified; remote doc URL availability/publication not verified.','No Lean/Lake/checkdecls builds or CI performed by render worker.','No new tensor diagram; Tenkz picture validation is not applicable.']
}
(OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','source_revision','counts','dependency_graphs']},indent=2))
