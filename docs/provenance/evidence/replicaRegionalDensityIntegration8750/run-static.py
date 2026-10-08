from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent
for name,argv in [("leaf-review",["python3",str(p/"review-leaf.py")]),("prose",["python3","scripts/check_reader_facing_prose.py","--diff-base","91bb14c1"]),("paper-gaps",["texra-blueprint","paper-gaps","check"])]:
 q=subprocess.run([sys.executable,str(p/"capture.py"),name,*argv])
 if q.returncode:raise SystemExit(q.returncode)
