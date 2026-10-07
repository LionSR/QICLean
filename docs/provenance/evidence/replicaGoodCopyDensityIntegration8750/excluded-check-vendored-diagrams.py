from pathlib import Path
import hashlib,json
p=Path("tex/tenkz");files=sorted(p.rglob("*.sty"));assert files
print(json.dumps({"diagram_source":"vendored in exact released parent; no fetch script on this base","sha256":{str(q):hashlib.sha256(q.read_bytes()).hexdigest() for q in files}},indent=2))
