"""Check every declaration in an active mathematical fragment against native names and rendered links."""
from html.parser import HTMLParser
from pathlib import Path
import hashlib
import json
import re

root = Path.cwd()
folder = Path(__file__).resolve().parent
src = root / 'blueprint/src'
seen, fragments = set(), set()

def visit(path):
    path = path.resolve()
    if path in seen or not path.is_file():
        return
    seen.add(path)
    if path.parent.name == 'fragment':
        fragments.add(path)
    text = re.sub(r'(?<!\\)%[^\n]*', '', path.read_text())
    for name in re.findall(r'\\(?:input|include)\{([^}]+)\}', text):
        relative = Path(name)
        if not relative.suffix:
            relative = relative.with_suffix('.tex')
        for candidate in [src / relative, path.parent / relative]:
            if candidate.is_file():
                visit(candidate)
                break

visit(src / 'content.tex')
expected = set()
fragment_names = {}
for fragment in sorted(fragments):
    names = {name.strip() for group in re.findall(r'\\lean\{([^}]+)\}', fragment.read_text())
             for name in group.split(',') if name.strip()}
    expected.update(names)
    fragment_names[str(fragment.relative_to(root))] = sorted(names)
owned = {entry['downstream']['declaration']
         for shard in ['replicaGoodConfigurationDensity8750']
         for entry in json.loads((root / f'docs/provenance/openai-math.d/{shard}.json').read_text())['entries']}
assert owned <= expected, owned - expected
native = (folder / 'NativeDeclarations.txt').read_bytes()
assert native == (root / 'blueprint/lean_decls').read_bytes()
names = set(native.decode().splitlines())
assert expected <= names, expected - names

class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links = []
    def handle_starttag(self, tag, attrs):
        values = dict(attrs)
        if tag == 'a' and 'lean_decl' in values.get('class', '').split():
            self.links.append(values['href'])

links = {name: [] for name in expected}
for document in sorted((root / 'blueprint/web').glob('*.html')):
    # Dependency graph pages repeat the same documentation links intentionally.
    if document.name.startswith('dep_graph'):
        continue
    parser = Links()
    parser.feed(document.read_text())
    for name in expected:
        links[name].extend({'document': str(document.relative_to(root)), 'href': href}
                           for href in parser.links if href.endswith('#doc/' + name))
assert all(len(values) == 1 for values in links.values()), {k:v for k,v in links.items() if len(v)!=1}
report = {'native_list': str((folder / 'NativeDeclarations.txt').relative_to(root)),
          'native_list_sha256': hashlib.sha256(native).hexdigest(),
          'native_declarations': len(names), 'active_fragments': fragment_names,
          'fragment_declarations': len(expected), 'owned_declarations': sorted(owned),
          'contains_all_active_fragment_targets': True, 'contains_the_owned': True,
          'missing': [], 'link_scope': 'content pages; dependency graph repeats excluded', 'rendered_doc_links': links, 'result': 'passed'}
(folder / 'native-targets.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
