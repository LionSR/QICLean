from pathlib import Path
import hashlib,json,re
p=Path("blueprint/src/print.tex");s=p.read_text();active=re.sub(r"(?<!\\)%[^\n]*","",s)
assert not re.search(r"\\usepackage(?:\[[^]]*\])?\{tenkz\}",active)
assert not Path("scripts/fetch_tenkz.py").exists()
print(json.dumps({"diagram_scope":"This exact released QIC parent does not load tenkz and has no tenkz fetch step.","print_source":str(p),"sha256":hashlib.sha256(p.read_bytes()).hexdigest()},indent=2))
