"""Replay the narrow render from an explicit public revision and retain exact logs."""
from datetime import datetime, timezone
from pathlib import Path
import json
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BASE = Path(os.environ.get('WORKSPACE', ROOT.parent))
OUT = Path(os.environ['RENDER_DIR']).resolve()
assert os.environ.get('SOURCE_REVISION'), 'Set SOURCE_REVISION to the exact public commit.'
assert not (OUT / 'focus-manifest.json').exists(), 'Use a fresh RENDER_DIR to retain earlier evidence.'
OUT.mkdir(parents=True, exist_ok=True)
record = {'source_revision': os.environ['SOURCE_REVISION'], 'commands': []}


def norm(text):
    for path, name in [(OUT, '${RENDER_DIR}'), (ROOT, '${REPO}'), (BASE, '${WORKSPACE}')]:
        text = text.replace(str(path), name)
    return text


def run(args, cwd, log):
    start = datetime.now(timezone.utc).isoformat()
    with (OUT / log).open('wb') as stream:
        result = subprocess.run(args, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
    record['commands'].append({'argv': [norm(str(a)) for a in args], 'working_directory': norm(str(cwd)),
                               'log': log, 'started_at_utc': start, 'exit_code': result.returncode})
    (OUT / 'commands-executed.json').write_text(json.dumps(record, indent=2) + '\n')
    if result.returncode:
        print((OUT / log).read_text())
        raise SystemExit(result.returncode)


run([sys.executable, HERE / 'prepare_fixture.py'], ROOT, 'prepare-fixture.log')
run(['latexmk', '-xelatex', '-interaction=nonstopmode', '-halt-on-error', 'print.tex'], OUT / 'blueprint/src', 'pdf-build.log')
(OUT / 'blueprint/src/web.bbl').write_bytes((OUT / 'blueprint/src/print.bbl').read_bytes())
run(['plastex', '-c', 'plastex.cfg', 'web.tex'], OUT / 'blueprint/src', 'web-build.log')
(OUT / 'pdf-pages').mkdir()
run(['pdftoppm', '-scale-to', '1500', '-png', 'blueprint/src/print.pdf', 'pdf-pages/page'], OUT, 'pdf-raster.log')
run(['pdfinfo', 'blueprint/src/print.pdf'], OUT, 'pdf-info.txt')
run([sys.executable, HERE / 'verify_render.py'], ROOT, 'verify-render-first.log')
run(['dot', '-Gbgcolor=white', '-Tpng', 'dependency-graph.dot', '-o', 'dependency-graph-white.png'], OUT, 'graph-render.log')
run([sys.executable, HERE / 'verify_render.py'], ROOT, 'verify-render.log')
print('PASS: exact-source PDF, static HTML, all links, anchors, graph dependencies, and artifact hashes')
