"""Validate exact source bytes, the two kernel reports, and all recorded evidence."""
from pathlib import Path
import gzip,hashlib,json,re,subprocess
root=Path.cwd();folder=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((folder/'verification.json').read_text())
tracked=lambda name:subprocess.run(['git','ls-files','--error-unmatch',name],check=True,stdout=subprocess.DEVNULL)
for item in manifest['commands']:
 assert item['exit_code']==0,item
 assert sha(root/item['log'])==item['sha256']
 tracked(item['log'])
for attempt in manifest['excluded_attempts']:
 assert not attempt['claimed_as_successful_verification']
 assert attempt['record']['exit_code']!=0
 for name,digest in [(attempt['record']['log'],attempt['record']['sha256']),(attempt['snapshot'],attempt['snapshot_sha256'])]:
  assert sha(root/name)==digest
  tracked(name)
for name,digest in manifest['file_hashes'].items():
 assert sha(root/name)==digest,name
 tracked(name)
for item in json.loads((folder/'compression.json').read_text()):
 raw=root/item['path'];gz=root/item['gzip_path']
 assert sha(raw)==item['sha256'] and sha(gz)==item['gzip_sha256']
 assert gzip.decompress(gz.read_bytes())==raw.read_bytes()
 tracked(item['path']);tracked(item['gzip_path'])
leaf=root/'docs/provenance/evidence/replicaPrevector8753'
freeze=json.loads((leaf/'source-freeze.json').read_text())
for name,digest in freeze['files'].items():
 assert sha(root/name)==digest
 assert (root/name).read_bytes()==subprocess.check_output(['git','show',f"{freeze['revision']}:{name}"])
preservation=json.loads((folder/'parent-preservation.json').read_text())
for key in ['production_files','evidence_and_exposition']:
 for name,digest in preservation[key].items():assert sha(root/name)==digest,name
kernel=folder/('axioms-final.log' if (folder/'axioms-final.log').exists() else 'axioms.log')
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",kernel.read_text(),re.S)
assert len(reports)==2 and {n for n,_ in reports}==set(manifest['owned_declarations'])
for name,axioms in reports:assert {a.strip() for a in axioms.split(',')}<={'propext','Classical.choice','Quot.sound'}
if (folder/'native-targets.json').exists():
 native=json.loads((folder/'native-targets.json').read_text())
 assert native['contains_all_active_fragment_targets'] and not native['missing']
 assert set(native['owned_declarations'])==set(manifest['owned_declarations'])
 assert sha(root/native['native_list'])==native['native_list_sha256']
 print(native['fragment_declarations'],'active fragment targets and',native['native_declarations'],'native names checked')
print(len(manifest['commands']),'zero-exit final commands;',len(manifest['excluded_attempts']),'honest excluded attempts;',len(manifest['file_hashes']),'tracked file hashes')
print(len(preservation['production_files']),'inherited production files;',len(preservation['evidence_and_exposition']),'inherited documentation/blueprint files preserved')
print('Four frozen source/exposition/ledger files and the two standard-kernel reports pass.')
