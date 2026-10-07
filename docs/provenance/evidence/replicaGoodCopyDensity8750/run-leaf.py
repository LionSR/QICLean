from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent
strict=['env','LEAN_NUM_THREADS=1','lake','env','lean','-j1','-Dpp.unicode.fun=true','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true','-DwarningAsError=true']
for name,argv in [('cache',['lake','exe','cache','get']),('guard',['python3',str(p/'mathlib-guard.py')]),('target',['lake','build','QICLean.Analysis.ReplicaGoodCopyDensity']),('strict-source',strict+['QICLean/Analysis/ReplicaGoodCopyDensity.lean']),('axioms',strict+[str(p/'Axioms.lean')]),('statements',strict+[str(p/'Statements.lean')]),('prose',['python3','scripts/check_reader_facing_prose.py','--diff-base','3ce1167e'])]:
 q=subprocess.run([sys.executable,str(p/'capture.py'),name,*argv])
 if q.returncode:raise SystemExit(q.returncode)
