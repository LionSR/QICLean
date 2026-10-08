from pathlib import Path
import argparse,gzip,hashlib,json,subprocess
q=argparse.ArgumentParser();q.add_argument('--git',action='store_true');args=q.parse_args();r=Path.cwd();p=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(q):
 return q.read_bytes() if q.exists() else gzip.decompress(Path(str(q)+'.gz').read_bytes())
m=json.loads((p/'manifest.json').read_text())
for row in m['files']:
 b=read(r/row['path']);assert sha(b)==row['sha256'],row['path']
 if args.git and not row.get('compressed_only'):assert b==subprocess.check_output(['git','show','HEAD:'+row['path']]),row['path']
for c in m['commands']:
 assert c['exit_code']==0 and c['source_revision']==m['source_revision'];assert sha(read(r/c['log']))==c['sha256']
for c in m['excluded_commands']:assert c['exit_code']!=0 and sha(read(r/c['log']))==c['sha256']
for row in json.loads((p/'compression.json').read_text()):
 raw=read(r/row['raw']);z=(r/row['archive']).read_bytes();assert sha(raw)==row['raw_sha256'];assert sha(z)==row['archive_sha256'];assert gzip.compress(raw,mtime=0)==z
for row in json.loads((p/'parent-preservation.json').read_text())['files']:assert sha((r/row['path']).read_bytes())==row['sha256'],row['path']
subprocess.run(['python3',str(p/'source-check.py')],check=True)
print('Verified',len(m['files']),'portable bindings,',len(m['commands']),'successful source-bound commands, exact parent and original mathematical source. No full-library or rendering claim.')
