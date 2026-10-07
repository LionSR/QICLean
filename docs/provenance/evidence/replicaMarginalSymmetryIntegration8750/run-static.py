from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent
checks=[('prose',['python3','scripts/check_reader_facing_prose.py','--diff-base','032b230b2a18d9715b3741b3bf5d1fe1edc4e08f']),('paper-gaps',['texra-blueprint','paper-gaps','check']),('tenkz',['python3','scripts/fetch_tenkz.py']),('axioms',['env','LEAN_NUM_THREADS=1','lake','env','lean','-j1','-Dpp.unicode.fun=true','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true','-DwarningAsError=true',str(p/'Axioms.lean')]),('provenance',['/Users/siruilu/miniforge3/bin/python3',str(p/'validate-owned.py'),'/Users/siruilu/Local/agentFormalization/TNLean'])]
for name,argv in checks:
 result=subprocess.run([sys.executable,str(p/'capture.py'),name,*argv])
 if result.returncode:raise SystemExit(result.returncode)
