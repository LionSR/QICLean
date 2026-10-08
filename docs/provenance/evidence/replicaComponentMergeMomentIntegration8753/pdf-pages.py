"""Locate and render complete component-moment pages for visual inspection."""
from pathlib import Path
import json,subprocess,hashlib,shutil
from pypdf import PdfReader
r=Path.cwd();e=Path(__file__).resolve().parent;pdf=r/'blueprint/print/print.pdf';reader=PdfReader(str(pdf));hits=[]
for i,page in enumerate(reader.pages):
 if 'Actual component exponential merge moment' in page.extract_text():hits.append(i+1)
assert len(hits)==1,hits
pages=sorted(set(hits+[p-1 for p in hits if p>1]+[p+1 for p in hits if p<len(reader.pages)]));out=e/'render';out.mkdir(exist_ok=True)
shutil.copyfile(pdf,out/'complete-blueprint.pdf')
for p in pages:
 subprocess.run(['pdftoppm','-f',str(p),'-l',str(p),'-scale-to','1800','-png','-singlefile',str(pdf),str(out/f'page-{p}')],check=True)
(out/'pages.json').write_text(json.dumps({'pdf_pages':len(reader.pages),'owned_theorem_physical_pages':hits,'rendered_physical_pages':pages,'pdf_sha256':hashlib.sha256(pdf.read_bytes()).hexdigest()},indent=2)+'\n')
print('PDF pages',len(reader.pages),'owned theorem',hits,'complete surrounding pages rendered',pages)
