from pathlib import Path
from pypdf import PdfReader
import json,subprocess
p=Path(__file__).resolve().parent;r=PdfReader(p/'common-density-blueprint.pdf');pages=[]
for i,q in enumerate(r.pages):
 t=' '.join(q.extract_text().split())
 if ('A common density for the two good regions' in t or 'Common good-copy density' in t or 'First actual marginal' in t or 'Second actual marginal' in t or 'Actual component mass' in t or 'retained and discarded coordinates together' in t) and i>350:pages.append(i+1)
assert pages
pages=list(range(min(pages),max(pages)+1))
for n in pages:
 subprocess.run(['pdftoppm','-f',str(n),'-l',str(n),'-scale-to','1800','-singlefile','-png',str(p/'common-density-blueprint.pdf'),str(p/'render'/f'page-{n}')],check=True)
result={'pages':len(r.pages),'physical_pages':pages,'printed_pages':[n-1 for n in pages]};(p/'pdf-page-selection.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
