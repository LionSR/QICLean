"""Verify the focused PDF, static HTML, declaration links and graph payloads."""
from collections import Counter
from datetime import datetime, timezone
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit
import hashlib, json, os, re, runpy, subprocess
from pypdf import PdfReader

BASE = Path(os.environ['WORKSPACE'])
ROOT = BASE / 'qiclean-singular-restoration-8757'
OUT = BASE / 'restoring-norm-vectors-focused'
manifest = json.loads((OUT / 'focus-manifest.json').read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
rev = manifest['source_revision']
frozen = lambda p: subprocess.check_output(['git', 'show', f'{rev}:{p}'], cwd=ROOT)
context = (OUT / manifest['context']['fixture_path']).read_text()
assert sha(OUT / manifest['context']['fixture_path']) == manifest['context']['sha256']
context_info = manifest['context']
context_full = frozen(context_info['source_path']).decode().splitlines(keepends=True)
assert context == ''.join(context_full[context_info['first_line']-1:context_info['last_line']])
source = '\n'.join((OUT / p).read_text() for p in manifest['target_leaves'])
for p, digest in manifest['source_sha256'].items():
    assert hashlib.sha256(frozen(p)).hexdigest() == digest, p
for p, digest in manifest['fixture_source_sha256'].items():
    assert sha(OUT / p) == digest and (OUT / p).read_bytes() == frozen(p), p
assert sha(OUT / 'blueprint/src/content.tex') == manifest['fixture_wrapper_sha256']
router = frozen('blueprint/src/chapter/ch12_entropy.tex').decode()
for p in manifest['target_leaves']:
    assert '\\input{' + p.removeprefix('blueprint/src/').removesuffix('.tex') + '}' in router

package_source = source
new_source = '\n'.join((OUT / p).read_text() for p in manifest['new_leaves'])
source = context + '\n' + source
decls = [x.strip() for group in re.findall(r'\\lean\{([^}]+)\}', source, re.S) for x in group.split(',')]
public = []; kinds = Counter()
for p in manifest['production_modules']:
    text = frozen(p).decode()
    namespace = re.search(r'^namespace (\S+)', text, re.M).group(1)
    for kind, name in re.findall(r'^(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?(theorem|def|lemma)\s+(\S+)', text, re.M):
        public.append(namespace + '.' + name); kinds[kind] += 1
package_decls = [x.strip() for group in re.findall(r'\\lean\{([^}]+)\}', package_source, re.S) for x in group.split(',')]
new_decls = [x.strip() for group in re.findall(r'\\lean\{([^}]+)\}', new_source, re.S) for x in group.split(',')]
assert len(public) == len(package_decls) == 54 and Counter(public) == Counter(package_decls)
assert len(new_decls) == 25 and len(decls) == 58
assert Counter(decls) == Counter(package_decls + manifest['context']['declarations'])
assert kinds == {'theorem': 34, 'def': 20}, kinds
guards = [x for p in manifest['test_modules'] if p.endswith('Axioms.lean') for x in re.findall(r'^#print axioms (\S+)', frozen(p).decode(), re.M)]
assert Counter(guards) == Counter(package_decls)
consumers = sum(len(re.findall(r'^example\b', frozen(p).decode(), re.M)) for p in manifest['test_modules'] if not p.endswith('Axioms.lean'))
assert consumers == 30
labels = re.findall(r'\\label\{([^}]+)\}', source)
assert len(labels) == len(set(labels))
refs = re.findall(r'\\ref\{([^}]+)\}', source)
assert set(refs) <= set(labels)
assert not re.search(r'\\begin\{(?:tikzpicture|tenkz)', source)

class Page(HTMLParser):
    def __init__(self, text):
        super().__init__(); self.ids=[]; self.links=[]; self.lean=[]; self.images=[]; self.text=[]; self.classes=Counter(); self.feed(text)
    def handle_starttag(self, tag, attrs):
        a=dict(attrs)
        if 'id' in a: self.ids.append(a['id'])
        if tag=='a' and 'name' in a and a.get('name')!=a.get('id'): self.ids.append(a['name'])
        self.classes.update(a.get('class','').split())
        if tag=='a' and 'href' in a:
            self.links.append(a['href'])
            if 'lean_decl' in a.get('class','').split(): self.lean.append(a['href'])
        if tag=='img': self.images.append(a.get('src',''))
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
# Missing static anchors are recorded as quality failures, not hidden.
chapter = pages['ch-restoring_norm_vectors_focus.html']
missing_labels = sorted(set(labels)-set(chapter.ids))
getname=lambda u: unquote(urlsplit(u).fragment).removeprefix('doc/')
assert Counter(map(getname, chapter.lean)) == Counter(decls)
assert Counter(chapter.lean) == Counter('../docs/find/#doc/' + d for d in decls)
assert chapter.classes['theorem_thmwrapper'] == 14
assert chapter.classes['lemma_thmwrapper'] == 2
assert chapter.classes['definition_thmwrapper'] == 4
assert chapter.classes['proof_wrapper'] == 16
for name in ['dep_graph_document.html','dep_graph_chapter_1.html']:
    assert Counter(map(getname, pages[name].lean)) == Counter(decls), name
runpy.run_path(str(OUT/'scripts/test_blueprint_web_render.py'))['_assert_generated_source'](list(web.glob('*.html')))

chunks = re.split(r'(?=\\begin\{(?:theorem|definition|lemma)\})', source)[1:]
entries=[]; explicit=set()
for chunk in chunks:
    label=re.search(r'\\label\{((?:thm|def|lem):[^}]+)\}',chunk).group(1)
    entries.append(label)
    for group in re.findall(r'\\uses\{([^}]+)\}',chunk,re.S):
        for dep in group.split(','): explicit.add((dep.strip(),label))
assert set(x for pair in explicit for x in pair) <= set(entries)
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
    nodes=set(re.findall(r'"((?:thm|def|lem):[^" ]+)"\s*\[',dot))
    edges=set(re.findall(r'"((?:thm|def|lem):[^" ]+)"\s*->\s*"((?:thm|def|lem):[^" ]+)"',dot))
    assert nodes==set(entries), nodes^set(entries)
    assert closure(edges)==closure(explicit), (edges, explicit)
    assert not any(a==b for a,b in closure(edges))
    assert len(nodes) == 20
    assert dot.count('fillcolor="#1CAC78"') == 16 and dot.count('fillcolor="#B0ECA3"') == 4
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
assert set(labels)<=set(destmap), set(labels)-set(destmap)
for label in labels: assert destmap[label][2] in pdf.named_destinations, label
assert set(destlinks)<=set(pdf.named_destinations), set(destlinks)-set(pdf.named_destinations)
assert '??' not in '\n'.join(page.extract_text() for page in pdf.pages)
log=(OUT/'blueprint/src/print.log').read_text()
warnings=re.findall(r'^.*(?:Overfull|Underfull|Missing character|undefined|LaTeX Warning|^!).*$',log,re.M)
# Preserve a complete failed-quality record before any source-owner repair.
assert '\\bibcite{OpenAI2026AreaLaw}' in aux
assert any('OpenAI2026AreaLaw' in (web/name).read_text() for name in pages)
curly=[]
for filename in pages:
    for match in re.finditer(r'<div class="displaymath"[^>]*>(.*?)</div>',(web/filename).read_text(),re.S):
        if '\u2019' in match.group(1): curly.append({'page':filename,'display':match.group(0)})
assert not curly, curly
artifacts=[OUT/'blueprint/src/print.pdf',OUT/'blueprint/src/print.aux',OUT/'dependency-graph.dot',*sorted(web.glob('*.html')),*sorted((OUT/'pdf-pages').glob('*.png'))]
result={
 'status':'passed' if not (warnings or missing or missing_labels) else 'quality findings require review', 'recorded_at_utc':datetime.now(timezone.utc).isoformat(),
 'source_revision':rev, 'source_sha256':manifest['source_sha256'],
 'counts':{'production_modules':5,'production_lines':manifest['production_lines'],'public_declarations':len(public),'new_public_declarations':len(new_decls),'context_declarations':4,'theorems':kinds['theorem'],'definitions':kinds['def'],'source_inspected_consumers':consumers,'source_inspected_axiom_guards':len(guards),'blueprint_entries':len(entries),'proofs':source.count('\\begin{proof}'),'checked_markers':source.count('\\leanok'),'equation_labels':sum(x.startswith('eq:') for x in labels),'all_labels':len(labels),'pdf_pages':len(pdf.pages),'html_pages':len(pages),'pdf_declaration_links':len(pdfdecls),'html_chapter_declaration_links':len(chapter.lean),'html_all_declaration_links':sum(len(p.lean) for p in pages.values()),'pdf_internal_link_annotations':len(destlinks),'explicit_dependency_edges':len(explicit),'diagrams':0},
 'declarations':package_decls,'new_declarations':new_decls,'context_declarations':manifest['context']['declarations'],'html_declaration_hrefs':chapter.lean,'pdf_declaration_uris':[u for u in uris if '/find/' in u and '#doc/' in u],'labels':labels,'html_files':list(pages),'html_chapter_classes':dict(chapter.classes),'dependency_graphs':graph_records,'explicit_dependency_edges':sorted(explicit),
 'missing_internal_anchors':missing,'missing_label_anchors':missing_labels,'duplicate_html_ids':[],'tex_box_reference_warnings':warnings,'curly_math_prime_serialization':curly,
 'artifact_sha256':{str(p.relative_to(OUT)):sha(p) for p in artifacts},
 'raw_log_sha256':{p:sha(OUT/p) for p in ['pdf-build.log','web-build.log','pdf-raster.log']},
 'limits':['Focused norm/vector fixture with restoration and partial-trace context only; no full-book build or live browser/MathJax runtime/responsive/click testing.','All declaration identifiers and generated local anchors verified; remote doc URL availability/publication not verified.','No Lean/Lake/checkdecls or CI performed by render worker; consumers and axiom guards source-inspected only.','No new tensor diagram; Tenkz picture validation is not applicable.','No existence of typical projections, localization theorem, purity-to-mutual-information identification, complete amplification theorem, or actual ground-component coefficient is established by this evidence.']
}
(OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','source_revision','counts','dependency_graphs']},indent=2))

if result['status'] != 'passed':
    raise SystemExit(1)
