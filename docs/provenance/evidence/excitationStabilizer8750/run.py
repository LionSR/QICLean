from pathlib import Path
import datetime,hashlib,json,subprocess,time,gzip
root=Path.cwd();folder=root/'docs/provenance/evidence/excitationStabilizer8750'
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
checks=[]
def run(name,argv):
 start=time.monotonic();timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat();log=folder/(name+'.log')
 with log.open('wb') as f: p=subprocess.run(argv,cwd=root,stdout=f,stderr=subprocess.STDOUT)
 b=log.read_bytes();entry={'source_revision':revision,'argv':argv,'cwd':str(root),'started_utc':timestamp,'elapsed_seconds':time.monotonic()-start,'exit_code':p.returncode,'log':str(log.relative_to(root)),'sha256':hashlib.sha256(b).hexdigest()}
 (folder/(name+'-exit.json')).write_text(json.dumps(entry,indent=2)+'\n');(folder/(name+'.log.gz')).write_bytes(gzip.compress(b,mtime=0));checks.append(entry)
 print(name,p.returncode,round(entry['elapsed_seconds'],2),flush=True)
 if p.returncode: print(b.decode(errors='replace')[-6000:],flush=True);raise SystemExit(p.returncode)
run('cache',['lake','exe','cache','get'])
run('guard',['python3','-c',"from pathlib import Path;import subprocess,hashlib;p=Path('.lake/packages/mathlib');assert subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()=='c55e6e786f49471c72fbddbec5415808896aec1e';o=p/'.lake/build/lib/lean/Mathlib.olean';assert o.is_file();print('Exact pinned Mathlib prebuilt artifact',hashlib.sha256(o.read_bytes()).hexdigest())"])
run('target',['lake','build','QICLean.Analysis.ReplicaExcitationSymmetry'])
options=['-DwarningAsError=true','-Dlinter.mathlibStandardSet=true','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3']
run('strict-source',['lake','env','lean',*options,'QICLean/Analysis/ReplicaExcitationSymmetry.lean'])
run('axioms',['lake','env','lean',*options,'docs/provenance/evidence/excitationStabilizer8750/Axioms.lean'])
(folder/'verification.json').write_text(json.dumps({'source_revision':revision,'commands':checks},indent=2)+'\n')
