"""Render the two pages added by the accepted Schur-label contribution."""
from pathlib import Path
import subprocess
p=Path(__file__).resolve().parent
for n in [436,437]:
 subprocess.run(['pdftoppm','-f',str(n),'-l',str(n),'-scale-to','1800','-png','-singlefile',str(p/'peps-source-latest-main-blueprint.pdf'),str(p/'render'/f'page-{n}')],check=True)
print('Rendered physical pages 436–437 of the frozen complete book.')
