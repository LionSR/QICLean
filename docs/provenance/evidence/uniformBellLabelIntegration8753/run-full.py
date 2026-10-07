"""Capture complete library and exposition verification against fixed source bytes."""
import hashlib,json,pathlib,subprocess,time,sys
r=pathlib.Path.cwd();e=r/'docs/provenance/evidence/uniformBellLabelIntegration8753';f=json.loads((e/'source-freeze.json').read_text())
flags=['-DwarningAsError=true','-Dlinter.mathlibStandardSet=true','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3']
commands=[('cache','.', ['lake','exe','cache','get']),('build','.', ['lake','build']),('axioms','.', ['lake','env','lean',*flags,'docs/provenance/evidence/uniformBellLabelIntegration8753/Axioms.lean']),('provenance','.', ['/tmp/qic-density-simplex-provenance-env/bin/python','docs/provenance/evidence/uniformBellLabelIntegration8753/validate-owned.py','/Users/siruilu/Local/agentFormalization/TNLean']),('bbl','.', ['texra-blueprint','bbl']),('pdf','blueprint',['leanblueprint','pdf']),('web','blueprint',['texra-blueprint','web']),('checkdecls','.', ['lake','env','.lake/packages/checkdecls/.lake/build/bin/checkdecls','blueprint/lean_decls']),('imports','.', ['python3','scripts/generate_import_aggregators.py','--check']),('prose','.', ['python3','scripts/check_reader_facing_prose.py','--root','.','--diff-base','0c3485a4','--ci']),('paper-gaps','.', ['texra-blueprint','paper-gaps','check']),('blueprint-sync','.', ['python3','scripts/blueprint_lean_sync.py','--root','.','--update-lean-decls']),('web-render-test','.', ['/Users/siruilu/miniforge3/bin/python3','scripts/test_blueprint_web_render.py','--web-root','blueprint/web'])]
start_at=sys.argv[1] if len(sys.argv)>1 else None
started=start_at is None
for name,wd,argv in commands:
 if not started:
  if name==start_at:started=True
  else:continue
 for p,s in f['files'].items():
  assert hashlib.sha256((r/p).read_bytes()).hexdigest()==s
  assert hashlib.sha256(subprocess.check_output(['git','show',f['source_revision']+':'+p])).hexdigest()==s
 start=time.monotonic();log=e/(name+'.log')
 print('Starting '+name,flush=True)
 with log.open('wb') as out:p=subprocess.run(argv,cwd=r/wd,stdout=out,stderr=subprocess.STDOUT)
 record=dict(kind=name,command=argv,working_directory=wd,source_revision=f['source_revision'],exit_code=p.returncode,elapsed_seconds=time.monotonic()-start,log=str(log.relative_to(r)),sha256=hashlib.sha256(log.read_bytes()).hexdigest())
 (e/(name+'-exit.json')).write_text(json.dumps(record,indent=2)+'\n')
 print(name+': exit '+str(p.returncode)+'; '+log.read_text()[-450:],flush=True)
 if p.returncode:sys.exit(p.returncode)
 if name=='cache':
  art=r/'.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean';assert art.is_file()
  pkg=next(x for x in json.loads((r/'lake-manifest.json').read_text())['packages'] if x['name']=='mathlib');assert pkg['rev']=='c55e6e786f49471c72fbddbec5415808896aec1e'
  (e/'mathlib-guard.json').write_text(json.dumps(dict(package_revision=pkg['rev'],artifact_sha256=hashlib.sha256(art.read_bytes()).hexdigest(),verified_before_build=True),indent=2)+'\n')
