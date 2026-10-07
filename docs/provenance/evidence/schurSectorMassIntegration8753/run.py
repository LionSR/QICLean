"""Capture actual source-bound commands; compress large raw output losslessly."""
import gzip,hashlib,json,pathlib,shutil,subprocess,sys,time
root=pathlib.Path.cwd();e=root/'docs/provenance/evidence/schurSectorMassIntegration8753'
freeze=json.loads((e/'source-freeze.json').read_text())
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
for path,digest in freeze['production_sha256'].items():
    assert sha(root/path)==digest
    assert hashlib.sha256(subprocess.check_output(['git','show',freeze['source_revision']+':'+path])).hexdigest()==digest
name=sys.argv[1];args=sys.argv[2:];wd=root
if args[:1]==['--cwd']:wd=root/args[1];args=args[2:]
log=e/(name+'.log');start=time.monotonic()
with log.open('wb') as f:p=subprocess.run(args,cwd=wd,stdout=f,stderr=subprocess.STDOUT)
rawsha=sha(log);size=log.stat().st_size
with log.open('rb') as f:f.seek(max(0,size-1400));tail=f.read().decode(errors='replace')
if size>200000:
    zipped=pathlib.Path(str(log)+'.gz')
    with log.open('rb') as src,zipped.open('wb') as out,gzip.GzipFile(filename='',mode='wb',fileobj=out,mtime=0) as z:shutil.copyfileobj(src,z)
    log.unlink();log=zipped
record=dict(source_revision=freeze['source_revision'],argv=args,cwd=str(wd),exit_code=p.returncode,elapsed_seconds=time.monotonic()-start,log=str(log.relative_to(root)),sha256=sha(log),uncompressed_sha256=rawsha,uncompressed_bytes=size,compressed=log.suffix=='.gz',deterministic_gzip_mtime=0 if log.suffix=='.gz' else None)
(e/(name+'-exit.json')).write_text(json.dumps(record,indent=2)+'\n')
print(name+': exit '+str(p.returncode));print(tail)
sys.exit(p.returncode)
