from pathlib import Path
from pypdf import PdfReader
import json,subprocess
p=Path(__file__).resolve().parent;r=PdfReader(p/'physical-support-blueprint.pdf');pages=[]
for i,q in enumerate(r.pages):
 t=' '.join(q.extract_text().split())
 if ('Symmetric support of the good physical density' in t or 'Actual physical symmetric support' in t) and i>350:pages.append(i+1)
assert pages
pages=list(range(min(pages),max(pages)+1))
for n in pages:
 subprocess.run(['pdftoppm','-f',str(n),'-l',str(n),'-scale-to','1800','-singlefile','-png',str(p/'physical-support-blueprint.pdf'),str(p/'render'/f'page-{n}')],check=True)
result={'pages':len(r.pages),'physical_pages':pages,'printed_pages':[n-1 for n in pages]};(p/'pdf-page-selection.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
