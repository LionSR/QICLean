from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent
strict=['env','LEAN_NUM_THREADS=1','lake','env','lean','-j1','-Dpp.unicode.fun=true','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true','-DwarningAsError=true']
checks=[('strict-source',strict+['QICLean/Analysis/ReplicaJointDensity.lean']),('axioms',strict+[str(p/'Axioms.lean')]),('statements',strict+[str(p/'Statements.lean')]),('prose',['python3','scripts/check_reader_facing_prose.py','--diff-base','076b8c48']),('patterns',['python3',str(p/'pattern-scan.py'),'--root','QICLean','--top','5']),('preservation',['python3',str(p/'check-preservation.py')]),('hazards',['python3',str(p/'check-hazards.py')])]
for name,argv in checks:
 result=subprocess.run([sys.executable,str(p/'capture.py'),name,*argv])
 if result.returncode:raise SystemExit(result.returncode)
