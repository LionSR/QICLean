"""Verify the pinned prebuilt Mathlib modules used by the concentration proof."""
from pathlib import Path
import hashlib,json,subprocess
root=Path.cwd()
manifest=json.loads((root/'lake-manifest.json').read_text())
rev=next(p['rev'] for p in manifest['packages'] if p['name']=='mathlib')
package=root/'.lake/packages/mathlib'
actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=package,text=True).strip()
assert rev==actual=='c55e6e786f49471c72fbddbec5415808896aec1e'
modules=['Mathlib','Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics']
report={'mathlib_revision':actual,'prebuilt_modules':{}}
for name in modules:
 path=package/'.lake/build/lib/lean'/Path(name.replace('.','/')+'.olean')
 assert path.is_file() and not path.is_symlink(),path
 report['prebuilt_modules'][name]=hashlib.sha256(path.read_bytes()).hexdigest()
print(json.dumps(report,indent=2))
