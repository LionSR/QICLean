"""Check frozen source, all local PDF/HTML references, and dependency graph reachability."""
from collections import Counter
from datetime import datetime, timezone
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urlsplit
import hashlib, json, os, re, runpy, subprocess
from pypdf import PdfReader
BASE=Path(os.environ['WORKSPACE']); ROOT=BASE/'qiclean-poisson-decay-8757'
OUT=BASE/os.environ.get('RENDER_NAME','poisson-word-focused')
m=json.loads((OUT/'focus-manifest.json').read_text()); rev=m['source_revision']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frozen=lambda p:subprocess.check_output(['git','show',f'{rev}:{p}'],cwd=ROOT)
source='\n'.join((OUT/p).read_text() for p in m['target_leaves'])
for p,digest in m['source_sha256'].items(): assert hashlib.sha256(frozen(p)).hexdigest()==digest,p
for p,digest in m['fixture_source_sha256'].items(): assert sha(OUT/p)==digest and (OUT/p).read_bytes()==frozen(p),p
assert sha(OUT/'blueprint/src/content.tex')==m['fixture_wrapper_sha256']
router=frozen('blueprint/src/content.tex').decode()
for p in m['target_leaves']: assert router.count('\\input{'+p.removeprefix('blueprint/src/').removesuffix('.tex')+'}')==1,p
decls=[x.strip() for g in re.findall(r'\\lean\{([^}]+)\}',source,re.S) for x in g.split(',')]
public=[]; kinds=Counter()
for p in m['production_modules']:
    src=frozen(p).decode(); ns=re.search(r'^namespace (\S+)',src,re.M).group(1)
    for kind,name in re.findall(r'^(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?(theorem|def|lemma|abbrev|instance)\s+([a-zA-Z][a-zA-Z0-9_]*)',src,re.M):
        public.append(ns+'.'+name); kinds[kind]+=1
assert len(public)==50,(len(public),kinds)
generated=['PoissonWord.instMeasurableSpaceWord','PoissonWord.instMeasurableSingletonClassWord']
guards=[x for p in m['test_modules'] if p.endswith('Axioms.lean') for x in re.findall(r'^#print axioms (\S+)',frozen(p).decode(),re.M)]
assert Counter(guards)==Counter(public+generated)
assert not (Counter(decls)-Counter(public+generated))
unlinked=sorted(set(public+generated)-set(decls))
consumers=sum(len(re.findall(r'^example\b',frozen(p).decode(),re.M)) for p in m['test_modules'] if not p.endswith('Axioms.lean'))
labels=re.findall(r'\\label\{([^}]+)\}',source); refs=re.findall(r'\\ref\{([^}]+)\}',source)
assert len(labels)==len(set(labels)); assert set(refs)<=set(labels)
assert not re.search(r'\\begin\{(?:tikzpicture|tenkz)',source)
class Page(HTMLParser):
    def __init__(self,text):
        super().__init__(); self.ids=[]; self.links=[]; self.lean=[]; self.images=[]; self.text=[]; self.classes=Counter(); self.feed(text)
    def handle_starttag(self,tag,attrs):
        a=dict(attrs)
        if 'id' in a:self.ids.append(a['id'])
        if tag=='a' and 'name' in a and a.get('name')!=a.get('id'):self.ids.append(a['name'])
        self.classes.update(a.get('class','').split())
        if tag=='a' and 'href' in a:
            self.links.append(a['href'])
            if 'lean_decl' in a.get('class','').split():self.lean.append(a['href'])
        if tag=='img':self.images.append(a.get('src',''))
    def handle_data(self,text):self.text.append(text)
web=OUT/'blueprint/web';pages={p.name:Page(p.read_text()) for p in sorted(web.glob('*.html'))}
missing=[]; duplicates=[]
for name,page in pages.items():
    duplicates += [[name,k] for k,v in Counter(page.ids).items() if v>1]
    for href in page.links:
        u=urlsplit(href)
        if u.scheme or u.netloc or u.path.startswith('../'):continue
        target=u.path or name
        if target.endswith('.html'):
            if target not in pages:missing.append([name,href,'file'])
            elif u.fragment and unquote(u.fragment) not in pages[target].ids:missing.append([name,href,'anchor'])
    for img in page.images:assert (web/img).is_file(),(name,img)
    visible=' '.join(page.text)
    assert '??' not in visible and not re.search(r'\\(?:lean|leanok|mathlibok|uses)\b',visible),name
chapter=pages['ch-poisson_word_focus.html']; missing_labels=sorted(set(labels)-set(chapter.ids))
getname=lambda u:unquote(urlsplit(u).fragment).removeprefix('doc/')
assert Counter(map(getname,chapter.lean))==Counter(decls)
assert Counter(chapter.lean)==Counter('../docs/find/#doc/'+d for d in decls)
assert chapter.classes['definition_thmwrapper']==4
assert chapter.classes['lemma_thmwrapper']==2
assert chapter.classes['theorem_thmwrapper']==8
assert chapter.classes['proof_wrapper']==10
for name in ['dep_graph_document.html','dep_graph_chapter_1.html']: assert Counter(map(getname,pages[name].lean))==Counter(decls),name
runpy.run_path(str(OUT/'scripts/test_blueprint_web_render.py'))['_assert_generated_source'](list(web.glob('*.html')))
chunks=re.split(r'(?=\\begin\{(?:theorem|definition|lemma)\})',source)[1:]
entries=[];explicit=set(); placement=[]
for chunk in chunks:
    label=re.search(r'\\label\{((?:thm|def|lem):[^}]+)\}',chunk).group(1);entries.append(label)
    pieces=chunk.split('\\begin{proof}',1)
    for i,piece in enumerate(pieces):
        for group in re.findall(r'\\uses\{([^}]+)\}',piece,re.S):
            for dep in group.split(','):
                dep=dep.strip();explicit.add((dep,label));placement.append({'from':dep,'to':label,'placement':'statement' if i==0 else 'proof'})
assert set(x for pair in explicit for x in pair)<=set(entries)
def closure(edges):
    result=set(edges)
    while True:
        more={(a,d) for a,b in result for c,d in result if b==c}
        if more<=result:return result
        result|=more
graphs={}
for filename in ['dep_graph_document.html','dep_graph_chapter_1.html']:
    text=(web/filename).read_text();dot=re.search(r'\.renderDot\(`(.*?)`\)',text,re.S).group(1)
    nodes=set(re.findall(r'"((?:thm|def|lem):[^" ]+)"\s*\[',dot))
    edges=set(re.findall(r'"((?:thm|def|lem):[^" ]+)"\s*->\s*"((?:thm|def|lem):[^" ]+)"',dot))
    assert nodes==set(entries),nodes^set(entries)
    assert closure(edges)==closure(explicit);assert not any(a==b for a,b in closure(edges))
    assert dot.count('fillcolor="#1CAC78"')==10 and dot.count('fillcolor="#B0ECA3"')==4
    for a,b,attrs in re.findall(r'"((?:thm|def|lem):[^" ]+)"\s*->\s*"((?:thm|def|lem):[^" ]+)"\s*(\[[^]]*\])?;',dot):
        expected='statement' if 'dashed' in attrs else 'proof'
        assert {'from':a,'to':b,'placement':expected} in placement,(a,b,attrs)
    graphs[filename]={'nodes':len(nodes),'edges':len(edges),'reachability_matches_explicit_uses':True,'rendered_edge_styles_match_dependency_placement':True}
    if filename=='dep_graph_chapter_1.html':(OUT/'dependency-graph.dot').write_text(dot+'\n')
pdf=PdfReader(OUT/'blueprint/src/print.pdf');uris=[];destlinks=[]
for page in pdf.pages:
    for ref in page.get('/Annots',[]):
        obj=ref.get_object();action=obj.get('/A',{})
        if action.get('/URI'):uris.append(str(action['/URI']))
        if action.get('/S')=='/GoTo':destlinks.append(str(action['/D']))
        if obj.get('/Dest'):destlinks.append(str(obj['/Dest']))
pdfdecls=[getname(u) for u in uris if '/find/' in u and '#doc/' in u]; assert Counter(pdfdecls)==Counter(decls)
aux=(OUT/'blueprint/src/print.aux').read_text()
destmap={x[0]:x[1:] for x in re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}\{([^}]+)\}\{[^}]*\}\{([^}]+)\}',aux)}
assert set(labels)<=set(destmap)
for label in labels:assert destmap[label][2] in pdf.named_destinations,label
assert set(destlinks)<=set(pdf.named_destinations)
assert '??' not in '\n'.join(p.extract_text() for p in pdf.pages)
log=(OUT/'blueprint/src/print.log').read_text()
warnings=re.findall(r'^.*(?:Overfull|Underfull|Missing character|undefined|LaTeX Warning|^!).*$',log,re.M)
assert '\\bibcite{OpenAI2026AreaLaw}' in aux
assert any('OpenAI2026AreaLaw' in (web/name).read_text() for name in pages)
curly=[]
for filename in pages:
    for match in re.finditer(r'<div class="displaymath"[^>]*>(.*?)</div>',(web/filename).read_text(),re.S):
        if '\u2019' in match.group(1):curly.append({'page':filename,'display':match.group(0)})
artifacts=[OUT/'blueprint/src/print.pdf',OUT/'blueprint/src/print.aux',OUT/'dependency-graph.dot',*sorted(web.glob('*.html')),*sorted((OUT/'pdf-pages').glob('*.png'))]
artifacts += [OUT/'dependency-graph-white.png'] if (OUT/'dependency-graph-white.png').exists() else []
result={
 'status':'passed' if not(warnings or missing or missing_labels or duplicates or unlinked or curly) else 'quality findings require review',
 'recorded_at_utc':datetime.now(timezone.utc).isoformat(),'source_revision':rev,'source_sha256':m['source_sha256'],
 'counts':{'production_modules':len(m['production_modules']),'production_lines':m['production_lines'],'explicitly_named_public_declarations':len(public),'generated_public_instances':len(generated),'public_constants':len(public+generated),'declaration_kinds':dict(kinds),'source_inspected_consumers':consumers,'source_inspected_axiom_guards':len(guards),'blueprint_entries':len(entries),'proofs':source.count('\\begin{proof}'),'checked_markers':source.count('\\leanok'),'equation_labels':sum(x.startswith('eq:') for x in labels),'all_labels':len(labels),'pdf_pages':len(pdf.pages),'html_pages':len(pages),'pdf_declaration_links':len(pdfdecls),'html_chapter_declaration_links':len(chapter.lean),'html_all_declaration_links':sum(len(p.lean) for p in pages.values()),'pdf_internal_link_annotations':len(destlinks),'explicit_dependency_edges':len(explicit),'diagrams':0},
 'declarations':decls,'generated_instances':generated,'unlinked_public_constants':unlinked,'html_declaration_hrefs':chapter.lean,'pdf_declaration_uris':[u for u in uris if '/find/' in u and '#doc/' in u],
 'labels':labels,'html_files':list(pages),'html_chapter_classes':dict(chapter.classes),'dependency_graphs':graphs,'explicit_dependency_edges':sorted(explicit),'dependency_placement':placement,
 'missing_internal_anchors':missing,'missing_label_anchors':missing_labels,'duplicate_html_ids':duplicates,'tex_box_reference_warnings':warnings,'curly_math_prime_serialization':curly,
 'artifact_sha256':{str(p.relative_to(OUT)):sha(p) for p in artifacts},
 'raw_log_sha256':{p:sha(OUT/p) for p in ['pdf-build.log','web-build.log','pdf-raster.log'] if (OUT/p).exists()},
 'limits':['Focused four-leaf PDF/static HTML, not a full-book build or live-browser/MathJax runtime test.','Declaration URL identifiers and local anchors checked; remote Lean-document publication not tested.','No Lean/Lake/checkdecls or CI performed by this render worker; consumers and axiom guards source-inspected only.','No new tensor diagrams; Tenkz picture validation is inapplicable.','Concrete normalized word law is proved; independent rate-one clock identification, coupled-clock locality, and full amplification remain unproved.']}
(OUT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','source_revision','counts','dependency_graphs','unlinked_public_constants','missing_internal_anchors','missing_label_anchors','tex_box_reference_warnings']},indent=2))
if result['status']!='passed':raise SystemExit(1)
