"""Resolve all active fragment and four source-chapter declarations in the complete book."""
from pathlib import Path
from html.parser import HTMLParser
import re,json,hashlib
r=Path.cwd();p=Path(__file__).resolve().parent;src=r/'blueprint/src';seen=set();fragments=set()
def visit(q):
 q=q.resolve()
 if q in seen or not q.is_file():return
 seen.add(q)
 if q.parent.name=='fragment':fragments.add(q)
 t=re.sub(r'(?<!\\)%[^\n]*','',q.read_text())
 for n in re.findall(r'\\(?:input|include)\{([^}]+)\}',t):
  a=Path(n)
  if not a.suffix:a=a.with_suffix('.tex')
  for c in [src/a,q.parent/a]:
   if c.is_file():visit(c);break
visit(src/'content.tex')
chapters=[src/'chapter'/('ch13_'+n+'.tex') for n in ['random_sources','source_error','source_reduction','source_bridges']]
assert all(q.resolve() in seen for q in chapters)
def tags(q):return {n.strip() for group in re.findall(r'\\lean\{([^}]+)\}',re.sub(r'(?<!\\)%[^\n]*','',q.read_text())) for n in group.split(',') if n.strip()}
source={str(q.relative_to(r)):sorted(tags(q)) for q in chapters};frag={str(q.relative_to(r)):sorted(tags(q)) for q in sorted(fragments)}
source_names=set().union(*(set(v) for v in source.values()));frag_names=set().union(*(set(v) for v in frag.values()));expected=source_names|frag_names
native=(p/'NativeDeclarations.txt').read_bytes();assert native==(r/'blueprint/lean_decls').read_bytes();names=set(native.decode().splitlines());assert expected<=names,expected-names
class Links(HTMLParser):
 def __init__(self):super().__init__();self.links=[]
 def handle_starttag(self,t,attrs):
  a=dict(attrs)
  if t=='a' and 'lean_decl' in a.get('class','').split():self.links.append(a['href'])
links={n:[] for n in expected}
for q in sorted((r/'blueprint/web').glob('*.html')):
 if q.name.startswith('dep_graph'):continue
 h=Links();h.feed(q.read_text())
 for n in expected:links[n].extend({'document':str(q.relative_to(r)),'href':s} for s in h.links if s.endswith('#doc/'+n))
assert all(links.values()),[n for n,v in links.items() if not v]
audit=[line.split('axioms ')[1] for line in (p/'SourceContractionAxioms.lean').read_text().splitlines() if line.startswith('#print axioms ')]
assert set(audit)<=source_names
result={'result':'passed','native_list':str((p/'NativeDeclarations.txt').relative_to(r)),'native_list_sha256':hashlib.sha256(native).hexdigest(),'native_declarations':len(names),'source_chapters':source,'source_declarations':len(source_names),'active_fragments':frag,'fragment_declarations':len(frag_names),'source_contraction_exports':audit,'contains_all_source_targets':True,'contains_all_active_fragment_targets':True,'rendered_doc_links':links,'missing':[]}
(p/'native-targets.json').write_text(json.dumps(result,indent=2)+'\n')
print('Native',len(names),'; four source chapters:',len(source_names),'; active fragments:',len(frag_names),'; exact source-contraction exports:',len(audit))
