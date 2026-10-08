"""Check the exact pinned prebuilt Mathlib dependencies before library verification."""
from pathlib import Path
import hashlib,json,subprocess
root=Path.cwd();package=root/'.lake/packages/mathlib'
manifest=json.loads((root/'lake-manifest.json').read_text())
pin=next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib')
actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=package,text=True).strip()
assert pin==actual=='c55e6e786f49471c72fbddbec5415808896aec1e'
modules=['Mathlib','Mathlib.LinearAlgebra.Matrix.Kronecker','Mathlib.LinearAlgebra.Matrix.Permutation','Mathlib.LinearAlgebra.Matrix.ToLin','Mathlib.Logic.Equiv.Fin.Basic','Mathlib.Data.Fintype.Pi','Mathlib.Analysis.Normed.Algebra.MatrixExponential','Mathlib.LinearAlgebra.Matrix.PosDef']
modules += ['Mathlib.Analysis.Matrix.HermitianFunctionalCalculus', 'Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute', 'Mathlib.Analysis.Matrix.Order', 'Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order']
report={'mathlib_revision':actual,'prebuilt_modules':{}}
for module in modules:
 path=package/'.lake/build/lib/lean'/Path(module.replace('.','/')+'.olean')
 assert path.is_file() and not path.is_symlink(),path
 report['prebuilt_modules'][module]=hashlib.sha256(path.read_bytes()).hexdigest()
print(json.dumps(report,indent=2))
