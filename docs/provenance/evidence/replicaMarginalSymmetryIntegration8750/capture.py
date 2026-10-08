import hashlib,json,pathlib,subprocess,sys,time
root=pathlib.Path.cwd()
name,*command=sys.argv[1:]
folder='replicaMarginalSymmetryIntegration8750';kind='verification';where='.'
evidence=root/'docs/provenance/evidence'/folder
start=time.monotonic()
with (evidence/(name+'.log')).open('wb') as log:
 p=subprocess.run(command,cwd=root/where,stdout=log,stderr=subprocess.STDOUT)
record={'kind':kind,'command':command,'working_directory':where,'exit_code':p.returncode,'elapsed_seconds':round(time.monotonic()-start,2),'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'log':str((evidence/(name+'.log')).relative_to(root)),'sha256':hashlib.sha256((evidence/(name+'.log')).read_bytes()).hexdigest()}
(evidence/(name+'-exit.json')).write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
sys.exit(p.returncode)
