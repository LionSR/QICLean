#!/usr/bin/env python3
"""Verify source coverage and a completed focused PDF/static-HTML render."""
from pathlib import Path
from html.parser import HTMLParser
from urllib.parse import unquote, urlsplit
import argparse
import hashlib
import json
import re
import runpy
import subprocess

ROOT = Path(__file__).resolve().parents[5]
LEAF = Path('blueprint/src/chapter/ch12_entropy_gaussian_filter.tex')
MODULES = ('Kernel', 'MatrixIntegral', 'SpectralGap', 'GroundEstimate')


class Links(HTMLParser):
    def __init__(self, source):
        super().__init__()
        self.ids, self.links = set(), []
        self.feed(source)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'id' in attrs:
            self.ids.add(attrs['id'])
        if tag == 'a' and 'name' in attrs:
            self.ids.add(attrs['name'])
        if tag == 'a' and 'href' in attrs:
            self.links.append(attrs['href'])


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--render', type=Path, required=True)
    args = parser.parse_args()
    render = args.render.resolve()
    tex = (ROOT / LEAF).read_text()
    assert (render / LEAF).read_text() == tex, 'Rendered leaf is stale'
    api = runpy.run_path(str(ROOT / 'scripts/blueprint_lean_sync.py'))
    declarations = []
    by_module = {}
    for module in MODULES:
        path = ROOT / f'QICLean/Analysis/GaussianFilter/{module}.lean'
        found = [d.fqn for d in api['collect_file_lean_decls'](path, ROOT / 'QICLean')
                 if not d.is_private and d.kind in ('def', 'theorem', 'lemma')]
        by_module[module] = found
        declarations.extend(found)
    references = [d.strip() for group in re.findall(r'\\lean\{([^}]+)\}', tex)
                  for d in group.split(',')]
    assert len(declarations) == len(set(declarations)) == 43
    assert len(references) == len(set(references)) == 43
    assert set(declarations) == set(references), 'Public declaration coverage differs'
    entries = re.findall(r'\\begin\{(definition|theorem)\}(.*?)\\end\{\1\}', tex, re.S)
    proofs = re.findall(r'\\begin\{proof\}(.*?)\\end\{proof\}', tex, re.S)
    assert all('\\leanok' in entry for _, entry in entries)
    assert all('\\leanok' in proof for proof in proofs)
    labels = re.findall(r'\\label\{([^}]+)\}', tex)
    assert len(labels) == len(set(labels)), 'Duplicate source labels'
    refs = re.findall(r'\\ref\{([^}]+)\}', tex)
    uses = [d.strip() for group in re.findall(r'\\uses\{([^}]+)\}', tex)
            for d in group.split(',')]
    assert set(refs + uses) <= set(labels), 'Unresolved source references'
    assert '\\begin{equation}' not in tex and '\\[' not in tex
    assert not re.search(r'GLM23|Lemma 2\.3', tex)
    web = render / 'blueprint/web'
    pages = {p.resolve(): Links(p.read_text()) for p in web.glob('*.html')}
    assert pages, 'No rendered HTML'
    missing = []
    internal_links = 0
    for path, page in pages.items():
        for href in page.links:
            target = urlsplit(href)
            if target.scheme or target.netloc or not target.fragment:
                continue
            dest = (path.parent / unquote(target.path)).resolve() if target.path else path
            if dest not in pages:
                # Declaration documentation is outside this focused excerpt.
                if dest.is_relative_to(web.resolve()):
                    missing.append([path.name, href, 'missing page'])
                continue
            internal_links += 1
            if unquote(target.fragment) not in pages[dest].ids:
                missing.append([path.name, href, 'missing anchor'])
    assert not missing, missing
    page_ids = set().union(*(page.ids for page in pages.values()))
    assert set(labels) <= page_ids, 'Source labels missing from HTML'
    all_html = '\n'.join(p.read_text() for p in pages)
    rendered_decls = sorted(set(unquote(s) for s in re.findall(
        r'#doc/(GaussianFilter\.[^\s"<>]+)', all_html)))
    assert set(rendered_decls) == set(declarations), 'Rendered declaration links differ'
    web_log = (render / 'web-build.log').read_text()
    assert not re.search(r'^ERROR:', web_log, re.M), 'plasTeX package error'
    source_checks = runpy.run_path(str(ROOT / 'scripts/test_blueprint_web_render.py'))
    source_checks['_assert_generated_source'](list(pages))
    assert not re.search(r'tenkz-missing|MISSING.SVG|/workspace/|/home/agent/|/tmp/', all_html)
    log = (render / 'blueprint/src/print.log').read_text()
    issues = [line for line in log.splitlines() if re.search(
        r'Overfull|Underfull|undefined|multiply defined|LaTeX Error|Emergency stop', line, re.I)]
    assert not issues, issues
    pdf = render / 'blueprint/src/print.pdf'
    pdf_info = subprocess.check_output(['pdfinfo', str(pdf)], text=True)
    import fitz
    document = fitz.open(pdf)
    pdf_uris = [link['uri'] for page in document for link in page.get_links()
                if 'uri' in link]
    assert all(any(uri.endswith('#doc/' + decl) for uri in pdf_uris)
               for decl in declarations), 'Missing PDF declaration links'
    pdf_pages = int(re.search(r'^Pages:\s+(\d+)', pdf_info, re.M).group(1))
    extracted = subprocess.check_output(['pdftotext', str(pdf), '-'], text=True)
    assert '??' not in extracted, 'Unresolved reference in PDF text'
    report = {
        'status': 'PASS: source coverage, focused PDF, and static HTML',
        'leaf_sha256': sha(ROOT / LEAF),
        'declarations': by_module,
        'public_declaration_count': len(declarations),
        'statement_count': len(entries), 'proof_count': len(proofs),
        'source_label_count': len(labels),
        'source_ref_count': len(refs), 'source_uses_count': len(uses),
        'html_page_count': len(pages),
        'internal_fragment_links_checked': internal_links,
        'missing_internal_anchors': missing,
        'rendered_declarations': rendered_decls,
        'pdf_page_count': pdf_pages,
        'pdf_layout_or_reference_errors': issues,
        'pdf_sha256': sha(pdf),
        'html_sha256': {p.name: sha(p) for p in sorted(pages)},
        'diagram_count': 0,
        'diagram_reason': 'The pinned Gaussian passage is an algebraic integral argument.',
        'limits': ['Static HTML only; no MathJax/browser/responsive verification',
                   'No Lean/Lake/checkdecls or complete-book build in this render check'],
    }
    (render / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k not in
                      ('declarations', 'rendered_declarations', 'html_sha256')}, indent=2))


if __name__ == '__main__':
    main()
