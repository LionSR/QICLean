from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent
strict=["env","LEAN_NUM_THREADS=1","lake","env","lean","-j1","-Dpp.unicode.fun=true","-DrelaxedAutoImplicit=false","-DmaxSynthPendingDepth=3","-Dlinter.mathlibStandardSet=true","-DwarningAsError=true"]
checks=[("cache",["lake","exe","cache","get"]),("guard",["python3",str(p/"mathlib-guard.py")]),("target",["lake","build","QICLean.Analysis.ReplicaRegionalDensity"]),("strict-source",strict+["QICLean/Analysis/ReplicaRegionalDensity.lean"]),("axioms",strict+[str(p/"Axioms.lean")]),("statements",strict+[str(p/"Statements.lean")]),("prose",["python3","scripts/check_reader_facing_prose.py","--diff-base","4fa6d82d"]),("patterns",["python3",str(p/"pattern-scan.py"),"--root","QICLean","--top","5"])]
for name,argv in checks:
 q=subprocess.run([sys.executable,str(p/"capture.py"),name,*argv])
 if q.returncode:raise SystemExit(q.returncode)
