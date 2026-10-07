"""Capture an actual verification command against the frozen mathematical source."""
import hashlib,json,pathlib,subprocess,sys,time
r=pathlib.Path.cwd();e=r/'docs/provenance/evidence/uniformBellLabel8753'
f=json.loads((e/'source-freeze.json').read_text())
for p,s in f['production_sha256'].items():
 assert hashlib.sha256((r/p).read_bytes()).hexdigest()==s
 assert hashlib.sha256(subprocess.check_output(['git','show',f['source_revision']+':'+p])).hexdigest()==s
name=sys.argv[1];argv=sys.argv[2:];start=time.monotonic();log=e/(name+'.log')
with log.open('wb') as out:p=subprocess.run(argv,stdout=out,stderr=subprocess.STDOUT)
(e/(name+'-exit.json')).write_text(json.dumps(dict(source_revision=f['source_revision'],production_sha256=f['production_sha256'],argv=argv,working_directory='.',exit_code=p.returncode,elapsed_seconds=time.monotonic()-start,log=str(log.relative_to(r)),sha256=hashlib.sha256(log.read_bytes()).hexdigest()),indent=2)+'\n')
print(name+': exit '+str(p.returncode));print(log.read_text()[-1800:]);sys.exit(p.returncode)
