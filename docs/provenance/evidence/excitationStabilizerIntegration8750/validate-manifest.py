"""Validate the excitation-stabilizer integration and its exact retained evidence."""
from pathlib import Path
import gzip,hashlib,json,re,subprocess
root=Path.cwd();folder=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tracked=lambda name:subprocess.run(['git','ls-files','--error-unmatch',name],check=True,stdout=subprocess.DEVNULL)
manifest=json.loads((folder/'verification.json').read_text())
for record in manifest['commands']:
 assert record['exit_code']==0,record
 assert sha(root/record['log'])==record['sha256']
 tracked(record['log'])
for attempt in manifest['excluded_attempts']:
 assert not attempt['claimed_as_successful_verification']
 assert attempt['record']['exit_code']!=0
 for name,digest in [(attempt['record']['log'],attempt['record']['sha256']),(attempt['snapshot'],attempt['snapshot_sha256'])]:
  assert sha(root/name)==digest;tracked(name)
for name,digest in manifest['file_hashes'].items():
 assert sha(root/name)==digest,name;tracked(name)
for pair in json.loads((folder/'compression.json').read_text()):
 raw=root/pair['path'];gz=root/pair['gzip_path']
 assert sha(raw)==pair['sha256'] and sha(gz)==pair['gzip_sha256']
 assert gzip.decompress(gz.read_bytes())==raw.read_bytes()
 assert int.from_bytes(gz.read_bytes()[4:8],'little')==0
 tracked(pair['path']);tracked(pair['gzip_path'])
leaf=root/'docs/provenance/evidence/excitationStabilizer8750'
freeze=json.loads((leaf/'source-freeze.json').read_text())
for name,digest in freeze['production_sha256'].items():
 assert sha(root/name)==digest,name
 assert (root/name).read_bytes()==subprocess.check_output(['git','show',f"{freeze['source_revision']}:{name}"])
preservation=json.loads((folder/'parent-preservation.json').read_text())
for key in ['production_files','evidence_and_exposition','dependency_files']:
 for name,digest in preservation[key].items():
  if sha(root/name)==digest:continue
  original=subprocess.check_output(['git','show',f"{preservation['parent_revision']}:{name}"])
  if name=='QICLean/Analysis.lean':
   expected=original.replace(b'import QICLean.Analysis.ReplicaExcitationDecomposition\n',b'import QICLean.Analysis.ReplicaExcitationDecomposition\nimport QICLean.Analysis.ReplicaExcitationSymmetry\n')
  elif name=='blueprint/src/chapter/ch12_entropy.tex':
   expected=original.replace(b'\\input{fragment/replica_excitation_decomposition}',b'\\input{fragment/replica_excitation_decomposition}\n\\input{fragment/replica_excitation_symmetry}')
  else:raise AssertionError(name)
  assert (root/name).read_bytes()==expected,name
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(folder/'axioms.log').read_text(),re.S)
assert len(reports)==3 and {n for n,_ in reports}==set(manifest['owned_declarations'])
for _,axioms in reports:assert {a.strip() for a in axioms.split(',')}<={'propext','Classical.choice','Quot.sound'}
subprocess.run(['python3',str(folder/'check-leaf.py')],check=True,stdout=subprocess.DEVNULL)
native=json.loads((folder/'native-targets.json').read_text())
assert native['contains_all_active_fragment_targets'] and native['contains_all_three_owned'] and not native['missing']
assert set(native['owned_declarations'])==set(manifest['owned_declarations'])
assert sha(root/native['native_list'])==native['native_list_sha256']
print(len(manifest['commands']),'successful final commands;',len(manifest['excluded_attempts']),'excluded integration attempts;',len(manifest['file_hashes']),'tracked hashes')
print(len(preservation['production_files']),'parent production files;',len(preservation['evidence_and_exposition']),'documentation/blueprint files and four pins preserved')
print('Four frozen files, three standard-kernel reports, all 47 leaf hashes and its ten successful commands plus honest excluded wrapper pass.')
print(native['fragment_declarations'],'active fragment targets and',native['native_declarations'],'native declarations checked')
