"""Record the actual exit and raw output of a source-bound verification command."""
import hashlib,json,pathlib,subprocess,sys,time
root=pathlib.Path.cwd();e=root/'docs/provenance/evidence/replicaSymmetry8750'
freeze=json.loads((e/'source-freeze.json').read_text())
for path,sha in freeze['production_sha256'].items():
    assert hashlib.sha256((root/path).read_bytes()).hexdigest()==sha
    assert hashlib.sha256(subprocess.check_output(['git','show',freeze['source_revision']+':'+path])).hexdigest()==sha
name=sys.argv[1];args=sys.argv[2:];start=time.monotonic();wd=root
if args[:1]==['--cwd']:
    wd=root/args[1];args=args[2:]
log=e/(name+'.log')
with log.open('wb') as f:p=subprocess.run(args,cwd=wd,stdout=f,stderr=subprocess.STDOUT)
record=dict(source_revision=freeze['source_revision'],production_sha256=freeze['production_sha256'],argv=args,cwd=str(wd),exit_code=p.returncode,elapsed_seconds=time.monotonic()-start,log=str(log.relative_to(root)),sha256=hashlib.sha256(log.read_bytes()).hexdigest())
(e/(name+'-exit.json')).write_text(json.dumps(record,indent=2)+'\n')
print(name+': exit '+str(p.returncode)); print(log.read_text()[-1400:])
sys.exit(p.returncode)
