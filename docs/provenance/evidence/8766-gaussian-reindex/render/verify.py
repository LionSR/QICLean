#!/usr/bin/env python3
"""Verify exact-source identities, PDF links/destinations, and static HTML.

Adapted from retained Gaussian-uniform and physical-buffer render verifiers.
This reads Lean source declarations without invoking Lean, Lake, or checkdecls.
"""
import argparse
from collections import Counter
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import runpy
import subprocess
from urllib.parse import unquote, urlsplit
import xml.etree.ElementTree as ET


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class Page(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.ids, self.links, self.images = [], [], []
        self.display_ids = set()
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'displaymath' in attrs.get('class', '').split() and 'id' in attrs:
            self.display_ids.add(attrs['id'])
        if 'id' in attrs:
            self.ids.append(attrs['id'])
        if tag == 'a' and 'name' in attrs and attrs['name'] != attrs.get('id'):
            self.ids.append(attrs['name'])
        if tag == 'a' and 'href' in attrs:
            self.links.append(attrs['href'])
        if tag == 'img' and 'src' in attrs:
            self.images.append(attrs['src'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--render', type=Path, required=True)
    args = parser.parse_args()
    root, render = args.source_root.resolve(), args.render.resolve()
    manifest = json.loads((render / 'focus-manifest.json').read_text())
    for field, directory in [('leaves_sha256', root), ('leaves_sha256', render),
                             ('source_sha256', root), ('support_source_sha256', root),
                             ('support_fixture_sha256', render)]:
        for relative, digest in manifest[field].items():
            assert sha(directory / relative) == digest, (field, relative, 'changed')
    assert sha(render / 'blueprint/src/content.tex') == manifest['router_sha256']
    tex = '\n'.join((render / p).read_text() for p in manifest['leaves_sha256'])
    labels = re.findall(r'\\label\{([^}]+)\}', tex)
    refs = re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', tex)
    uses = [x.strip() for group in re.findall(r'\\uses\{([^}]+)\}', tex) for x in group.split(',')]
    declarations = [x.strip() for group in re.findall(r'\\lean\{([^}]+)\}', tex) for x in group.split(',')]
    assert len(labels) == len(set(labels)), 'Duplicate source labels'
    assert len(declarations) == len(set(declarations)), 'Duplicate declaration links'
    assert set(refs + uses) <= set(labels), set(refs + uses) - set(labels)
    entries = re.findall(r'\\begin\{(definition|theorem|lemma|corollary)\}(.*?)\\end\{\1\}', tex, re.S)
    proofs = re.findall(r'\\begin\{proof\}(.*?)\\end\{proof\}', tex, re.S)
    assert all('\\leanok' in body for _, body in entries)
    assert all('\\leanok' in body for body in proofs)
    equations = re.findall(r'\\begin\{(align|equation|gather)\}(.*?)\\end\{\1\}', tex, re.S)
    equation_labels = []
    for _, body in equations:
        found = re.findall(r'\\label\{([^}]+)\}', body)
        assert len(found) <= 1, ('Each anchored equation requires its own environment', found)
        equation_labels.extend(found)
    assert {r for r in refs if r.startswith('eq:')} <= set(equation_labels)
    api = runpy.run_path(str(root / 'scripts/blueprint_lean_sync.py'))
    all_source_declarations, gaussian = {}, {}
    for path in sorted((root / 'QICLean').rglob('*.lean')):
        found = [d.fqn for d in api['collect_file_lean_decls'](path, root / 'QICLean')
                 if not d.is_private and d.kind in ('def', 'theorem', 'lemma')]
        for declaration in found:
            all_source_declarations[declaration] = str(path.relative_to(root))
        if path.parent == root / 'QICLean/Analysis/GaussianFilter':
            gaussian[path.stem] = found
    assert set(declarations) <= set(all_source_declarations), set(declarations) - set(all_source_declarations)
    gaussian_declarations = {d for found in gaussian.values() for d in found}
    assert gaussian_declarations <= set(declarations), gaussian_declarations - set(declarations)
    assert declarations.count('GaussianFilter.exists_uniform_physicalBuffer_filter') == 1
    assert declarations.count('GaussianFilter.reindex_gaussianIntertwiner') == 1
    assert declarations.count('GaussianFilter.reindex_gaussianIntertwinerTruncated') == 1
    web = render / 'blueprint/web'
    pages = {p.resolve(): Page(p.read_text()) for p in sorted(web.glob('*.html'))}
    assert pages, 'No generated HTML'
    missing, duplicates, local_links = [], [], 0
    for path, page in pages.items():
        duplicates.extend([path.name, key] for key, count in Counter(page.ids).items() if count > 1)
        for href in page.links:
            target = urlsplit(href)
            if target.scheme or target.netloc:
                continue
            dest = (path.parent / unquote(target.path)).resolve() if target.path else path
            if not dest.is_relative_to(web):
                continue
            if target.fragment:
                local_links += 1
                if dest not in pages or unquote(target.fragment) not in pages[dest].ids:
                    missing.append([path.name, href])
            elif target.path and not dest.exists():
                missing.append([path.name, href])
        for src in page.images:
            url = urlsplit(src)
            if not url.scheme and not url.netloc:
                assert (path.parent / unquote(url.path)).is_file(), ('Missing image', src)
    assert not missing and not duplicates, (missing, duplicates)
    ids = set().union(*(set(p.ids) for p in pages.values()))
    assert set(labels) <= ids, set(labels) - ids
    display_ids = set().union(*(p.display_ids for p in pages.values()))
    assert set(equation_labels) <= display_ids, ('Equation labels missing their display block', set(equation_labels) - display_ids)
    html = '\n'.join(p.read_text() for p in pages)
    html_declarations = {unquote(href).split('#doc/', 1)[1]
                         for p in pages.values() for href in p.links if '#doc/' in unquote(href)}
    assert html_declarations == set(declarations), (html_declarations ^ set(declarations))
    assert not re.search(r'tenkz-missing|MISSING.SVG|/workspace/|/home/agent/|/tmp/', html)
    assert not re.search(r'^ERROR:', (render / 'web-build.log').read_text(), re.M)
    source_checks = runpy.run_path(str(root / 'scripts/test_blueprint_web_render.py'))
    source_checks['_assert_generated_source'](list(pages))
    svg_files = sorted({(path.parent / unquote(urlsplit(src).path)).resolve()
                        for path, page in pages.items() for src in page.images if urlsplit(src).path.endswith('.svg')})
    assert len(svg_files) == tex.count('\\begin{tenkz}') == 1
    for svg in svg_files:
        assert ET.parse(svg).getroot().tag.endswith('svg') and svg.stat().st_size > 1000
    log = (render / 'blueprint/src/print.log').read_text()
    problems = [line for line in log.splitlines() if re.search(
        r'Overfull|Underfull|undefined|multiply defined|LaTeX Error|Emergency stop', line, re.I)]
    assert not problems, problems
    from pypdf import PdfReader
    pdf = render / 'blueprint/src/print.pdf'
    reader = PdfReader(pdf)
    pdf_declarations = set()
    pdf_internal_link_count = 0
    for page in reader.pages:
        for annotation in page.get('/Annots', []):
            obj = annotation.get_object()
            action = obj.get('/A', {})
            uri = unquote(str(action.get('/URI', '')))
            if '#doc/' in uri:
                pdf_declarations.add(uri.split('#doc/', 1)[1])
            dest = obj.get('/Dest') or action.get('/D')
            if isinstance(dest, str):
                pdf_internal_link_count += 1
                assert dest in reader.named_destinations, ('Missing PDF destination', dest)
    assert pdf_declarations == set(declarations), (pdf_declarations ^ set(declarations))
    aux = (render / 'blueprint/src/print.aux').read_text()
    aux_labels = dict((name, (number, page, dest)) for name, number, page, dest in re.findall(
        r'\\newlabel\{([^}]+)\}\{\{([^}]+)\}\{([^}]+)\}\{[^\n]*?\}\{([^}]+)\}\{\}\}', aux))
    assert set(labels) <= set(aux_labels), ('Source labels missing from PDF aux', set(labels) - set(aux_labels))
    for label in labels:
        assert aux_labels[label][2] in reader.named_destinations, ('Missing label PDF destination', label)
    eq_destinations = [aux_labels[label][2] for label in equation_labels]
    assert len(eq_destinations) == len(set(eq_destinations)), 'Equation labels share a PDF destination'
    extracted = subprocess.check_output(['pdftotext', '-layout', str(pdf), '-'], text=True)
    assert '??' not in extracted, 'Unresolved PDF reference'
    (render / 'pdf-text.txt').write_text(extracted)
    report = {
        'status': 'PASS: exact source, declaration coverage, focused PDF, and static HTML',
        'source_revision': manifest['source_revision'],
        'leaves_sha256': manifest['leaves_sha256'],
        'gaussian_public_declarations': gaussian,
        'gaussian_public_declaration_count': len(gaussian_declarations),
        'all_declaration_count': len(declarations),
        'declaration_source_files': {d: all_source_declarations[d] for d in declarations},
        'statement_count': len(entries), 'proof_count': len(proofs),
        'source_label_count': len(labels), 'source_ref_count': len(refs), 'source_uses_count': len(uses),
        'equation_label_count': len(equation_labels),
        'one_label_per_equation_environment': True, 'distinct_pdf_equation_destinations': True,
        'equation_labels_attached_to_html_display_blocks': True,
        'html_page_count': len(pages), 'internal_html_fragment_links_checked': local_links,
        'missing_internal_anchors': missing, 'duplicate_html_ids': duplicates,
        'pdf_page_count': len(reader.pages), 'pdf_internal_links_checked': pdf_internal_link_count,
        'pdf_layout_or_reference_errors': problems,
        'pdf_sha256': sha(pdf),
        'html_sha256': {p.name: sha(p) for p in pages},
        'diagram_sha256': {str(p.relative_to(web)): sha(p) for p in svg_files},
        'final_leaf_pdf_labels': {k: aux_labels[k] for k in labels if 'gaussian_reindex' in k},
        'limits': manifest['limits'],
    }
    (render / 'verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k not in
                     ('gaussian_public_declarations', 'declaration_source_files', 'html_sha256', 'leaves_sha256')}, indent=2))


if __name__ == '__main__':
    main()
