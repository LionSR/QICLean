from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent
checks=[('imports',['python3','scripts/generate_import_aggregators.py','--check']),('paper-gaps',['texra-blueprint','paper-gaps','check']),('tenkz',['python3','scripts/fetch_tenkz.py']),('source-contraction-kernels',['env','LEAN_NUM_THREADS=1','lake','env','lean','-j1','-Dpp.unicode.fun=true','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true','-DwarningAsError=true',str(p/'SourceContractionAxioms.lean')])]
for folder in ['8769-foundations-integration','8769-source-error','8769-source-reduction','8769-source-bridges']:
 checks.append(('provenance-'+folder,['python3','docs/provenance/evidence/'+folder+'/source-audit.py',str(p/'provenance-policy.py')]))
for name,argv in checks:
 q=subprocess.run([sys.executable,str(p/'capture.py'),name,*argv])
 if q.returncode:raise SystemExit(q.returncode)
