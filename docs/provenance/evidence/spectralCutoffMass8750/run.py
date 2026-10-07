"""Record the actual exit and unmodified output of a verification command."""
import hashlib,json,pathlib,subprocess,sys,time
root=pathlib.Path.cwd();e=root/'docs/provenance/evidence/spectralCutoffMass8750'
name=sys.argv[1];args=sys.argv[2:];start=time.time();wd=root
if args[:1]==['--cwd']:
    wd=root/args[1];args=args[2:]
log=e/(name+'.log')
with log.open('wb') as f: p=subprocess.run(args,cwd=wd,stdout=f,stderr=subprocess.STDOUT)
record=dict(source_revision='8f0020f9670356b79727bb6f23383f9c952c93a5',argv=args,cwd=str(wd),exit_code=p.returncode,elapsed_seconds=time.time()-start,log=str(log.relative_to(root)),sha256=hashlib.sha256(log.read_bytes()).hexdigest())
(e/(name+'-exit.json')).write_text(json.dumps(record,indent=2)+'\n')
print(name+': exit '+str(p.returncode))
sys.exit(p.returncode)
