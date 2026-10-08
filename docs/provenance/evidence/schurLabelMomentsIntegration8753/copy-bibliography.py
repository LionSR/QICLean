from pathlib import Path
import hashlib,json,shutil
root=Path.cwd();source=root/'blueprint/print/print.bbl';target=root/'blueprint/src/web.bbl'
assert source.is_file() and source.stat().st_size>0
shutil.copyfile(source,target)
assert source.read_bytes()==target.read_bytes()
print(json.dumps({'source':str(source.relative_to(root)),'target':str(target.relative_to(root)),'bytes':source.stat().st_size,'sha256':hashlib.sha256(source.read_bytes()).hexdigest()}))
