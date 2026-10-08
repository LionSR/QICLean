from pathlib import Path
import datetime,hashlib,json,subprocess,time,gzip
root=Path.cwd();folder=root/'docs/provenance/evidence/pepsSourceMainIntegration'
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
checks=[]
def run(name,argv):
 start=time.monotonic();timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat();log=folder/(name+'.log')
 with log.open('wb') as f: p=subprocess.run(argv,cwd=root,stdout=f,stderr=subprocess.STDOUT)
 b=log.read_bytes();entry={'source_revision':revision,'argv':argv,'cwd':str(root),'started_utc':timestamp,'elapsed_seconds':time.monotonic()-start,'exit_code':p.returncode,'log':str(log.relative_to(root)),'sha256':hashlib.sha256(b).hexdigest()}
 (folder/(name+'-exit.json')).write_text(json.dumps(entry,indent=2)+'\n');(folder/(name+'.log.gz')).write_bytes(gzip.compress(b,mtime=0));checks.append(entry)
 print(name,p.returncode,round(entry['elapsed_seconds'],2),flush=True)
 if p.returncode: print(b.decode(errors='replace')[-6000:],flush=True);raise SystemExit(p.returncode)

import sys
if sys.argv[1] == 'full-build':
 subprocess.run(['python3',str(folder/'mathlib-guard.py')],cwd=root,stdout=subprocess.DEVNULL,check=True)
run(sys.argv[1],sys.argv[2:])
