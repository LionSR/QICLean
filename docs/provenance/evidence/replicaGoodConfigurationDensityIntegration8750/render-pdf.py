from pathlib import Path
from pypdf import PdfReader
import json,subprocess
p=Path(__file__).resolve().parent;r=PdfReader(p/'good-configuration-blueprint.pdf');pages=[]
for i,q in enumerate(r.pages):
 t=' '.join(q.extract_text().split())
 if ('The actual full good-copy density' in t or 'Physical symmetric support of the full good-copy density' in t or 'Returning to the five-factor' in t or 'further reduction that traces the good' in t) and i>350:pages.append(i+1)
assert pages
pages=list(range(min(pages),max(pages)+1))
for n in pages:
 subprocess.run(['pdftoppm','-f',str(n),'-l',str(n),'-scale-to','1800','-singlefile','-png',str(p/'good-configuration-blueprint.pdf'),str(p/'render'/f'page-{n}')],check=True)
result={'pages':len(r.pages),'physical_pages':pages,'printed_pages':[n-1 for n in pages]};(p/'pdf-page-selection.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
