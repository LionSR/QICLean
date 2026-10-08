import datetime, hashlib, json, pathlib, subprocess, sys, time
root=pathlib.Path(__file__).resolve().parents[4]
e=root/'docs/provenance/evidence/replicaPhysicalLabelMomentIntegration8750'
freeze=json.loads((e/'source-freeze.json').read_text())
for item in freeze['files']:
    data=(root/item['path']).read_bytes()
    assert hashlib.sha256(data).hexdigest()==item['sha256']
    assert data==subprocess.check_output(['git','show',freeze['source_revision']+':'+item['path']],cwd=root)
name=sys.argv[1];cmd=sys.argv[2:];cwd=root
if cmd[0]=='@blueprint':
    cwd=root/'blueprint';cmd=cmd[1:]
start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic()
with (e/(name+'.log')).open('wb') as log:
    result=subprocess.run(cmd,cwd=cwd,stdout=log,stderr=subprocess.STDOUT)
data=(e/(name+'.log')).read_bytes()
record={'source_revision':freeze['source_revision'],'command':cmd,'cwd':str(cwd),'started_utc':start,'elapsed_seconds':round(time.monotonic()-t,3),'exit_code':result.returncode,'log':str((e/(name+'.log')).relative_to(root)),'sha256':hashlib.sha256(data).hexdigest()}
(e/(name+'-exit.json')).write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record));sys.exit(result.returncode)
