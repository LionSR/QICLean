from pathlib import Path
import collections,json,re
b=Path('/private/tmp/qic-physical-trace-helpers')
base=Path((b/'blueprint-dir').read_text().strip())
new=base/'blueprint/src/chapter/ch13_physical_trace_coordinates.tex'
names=[x['declaration'] for x in json.loads((b/'declarations.json').read_text())]
counts=collections.Counter(x.strip() for body in re.findall(r'\\lean\{([^}]+)\}',new.read_text()) for x in body.split(','))
assert set(counts)==set(names) and set(counts.values())=={1}
(base/'tag-coverage.json').write_text(json.dumps(counts,indent=2)+'\n')
nodes={};duplicates=[]
start=re.compile(r'\\begin\{(?:definition|theorem|lemma|proposition|corollary|remark|example)\}')
for p in sorted((base/'blueprint/src').rglob('*.tex')):
 if p.name in ['focused.tex','content-focused.tex']:continue
 s=re.sub(r'(?<!\\)%[^\n]*','',p.read_text());positions=list(start.finditer(s))
 for i,m in enumerate(positions):
  block=s[m.end():positions[i+1].start() if i+1<len(positions) else len(s)];label=re.search(r'\\label\{([^}]+)\}',block)
  if not label:continue
  key=label.group(1);deps={x.strip() for b in re.findall(r'\\uses\{([^}]+)\}',block) for x in b.split(',') if x.strip()}
  if key in nodes:duplicates.append(key)
  nodes[key]=deps
states={};cycles=[];stack=[]
def visit(n):
 if states.get(n)==2:return
 if states.get(n)==1:cycles.append(stack[stack.index(n):]+[n]);return
 states[n]=1;stack.append(n)
 for d in nodes[n]:
  if d in nodes:visit(d)
 stack.pop();states[n]=2
for n in nodes:visit(n)
assert not duplicates and not cycles
(base/'dependency-graph.json').write_text(json.dumps({'nodes':len(nodes),'edges':sum(len(x) for x in nodes.values()),'duplicate_labels':duplicates,'cycles':cycles},indent=2)+'\n')

print('GRAPH_PASS',len(nodes),sum(map(len,nodes.values())))
