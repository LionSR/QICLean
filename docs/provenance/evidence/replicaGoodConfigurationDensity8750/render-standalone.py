from pathlib import Path
from pypdf import PdfReader
import json,subprocess
p=Path(__file__).resolve().parent
r=PdfReader(p/'standalone-wrapper.pdf');pages=[]
for i in range(len(r.pages)):
 name='standalone-page-'+str(i+1)+'.png'
 subprocess.run(['pdftoppm','-f',str(i+1),'-l',str(i+1),'-scale-to','1800','-singlefile','-png',str(p/'standalone-wrapper.pdf'),str(p/name[:-4])],check=True)
 pages.append(name)
assert len(r.pages)>=1
print(json.dumps({'pages':len(r.pages),'rendered':pages}))
