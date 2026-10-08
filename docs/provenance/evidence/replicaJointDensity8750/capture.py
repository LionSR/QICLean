"""Record one command against the frozen joint-density source."""
from pathlib import Path
import datetime,hashlib,json,subprocess,time,gzip,sys
root=Path.cwd();folder=Path(__file__).resolve().parent
freeze=json.loads((folder/'source-freeze.json').read_text())
for name,digest in freeze['production_sha256'].items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
name,argv=sys.argv[1],sys.argv[2:]
assert not (folder/(name+'-exit.json')).exists(), 'Use a new name for a repeated attempt'
start=time.monotonic();stamp=datetime.datetime.now(datetime.timezone.utc).isoformat();log=folder/(name+'.log')
with log.open('wb') as f: process=subprocess.run(argv,cwd=root,stdout=f,stderr=subprocess.STDOUT)
b=log.read_bytes();entry={'source_revision':freeze['source_revision'],'argv':argv,'cwd':str(root),'started_utc':stamp,'elapsed_seconds':time.monotonic()-start,'exit_code':process.returncode,'log':str(log.relative_to(root)),'sha256':hashlib.sha256(b).hexdigest()}
(folder/(name+'-exit.json')).write_text(json.dumps(entry,indent=2)+'\n')
(folder/(name+'.log.gz')).write_bytes(gzip.compress(b,mtime=0))
print(name,process.returncode,round(entry['elapsed_seconds'],2),flush=True)
if process.returncode: print(b.decode(errors='replace')[-6000:],flush=True)
raise SystemExit(process.returncode)
