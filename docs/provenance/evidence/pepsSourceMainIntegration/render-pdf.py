from pathlib import Path
import subprocess,json
p=Path(__file__).resolve().parent
pages=[398,403,407,410,411,412,416]
for n in pages:
 subprocess.run(['pdftoppm','-f',str(n),'-l',str(n),'-scale-to','1800','-png','-singlefile',str(p/'peps-source-main-blueprint.pdf'),str(p/'render'/f'page-{n}')],check=True)
report=json.loads((p/'pdf-page-selection.json').read_text());report['visually_selected_physical_pages']=pages;report['printed_pages']=[n-1 for n in pages];(p/'pdf-page-selection.json').write_text(json.dumps(report,indent=2)+'\n')
print('Rendered seven complete-book pages covering four chapter openings, contraction definition/expansion and original-density conclusion.')
