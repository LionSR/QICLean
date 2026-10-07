"""Check all four concentration declarations in the actual native list and rendered links."""
from html.parser import HTMLParser
from pathlib import Path
import hashlib
import json

root = Path.cwd()
folder = Path(__file__).resolve().parent
expected = {e['downstream']['declaration'] for e in json.loads(
    (root / 'docs/provenance/openai-math.d/iidSurprisal8753.json').read_text())['entries']}
native = (folder / 'NativeDeclarations.txt').read_bytes()
assert native == (root / 'blueprint/lean_decls').read_bytes()
names = set(native.decode().splitlines())
assert expected <= names

class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links = []

    def handle_starttag(self, tag, attrs):
        values = dict(attrs)
        if tag == 'a' and 'lean_decl' in values.get('class', '').split():
            self.links.append(values['href'])

html = root / 'blueprint/web/ch-entropy.html'
parser = Links()
parser.feed(html.read_text())
links = {name: [href for href in parser.links if href.endswith('#doc/' + name)]
         for name in sorted(expected)}
assert all(len(values) == 1 for values in links.values()), links
report = {
    'native_list': 'docs/provenance/evidence/iidSurprisalIntegration8753/NativeDeclarations.txt',
    'native_list_sha256': hashlib.sha256(native).hexdigest(),
    'native_declarations': len(names),
    'expected_four_names': sorted(expected),
    'contains_all_four': True,
    'missing': [],
    'rendered_document': 'blueprint/web/ch-entropy.html',
    'rendered_document_sha256': hashlib.sha256(html.read_bytes()).hexdigest(),
    'rendered_doc_links': links,
    'result': 'passed',
}
(folder / 'native-targets.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
