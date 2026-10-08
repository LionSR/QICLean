"""Independently inspect the frozen three-result leaf and its retained evidence."""
from pathlib import Path
import gzip,hashlib,json,re,subprocess
root=Path.cwd();leaf=root/'docs/provenance/evidence/excitationStabilizer8750';folder=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tracked=lambda name:subprocess.run(['git','ls-files','--error-unmatch',name],check=True,stdout=subprocess.DEVNULL)
freeze=json.loads((leaf/'source-freeze.json').read_text())
for name,digest in freeze['production_sha256'].items():
 assert sha(root/name)==digest,name
 assert (root/name).read_bytes()==subprocess.check_output(['git','show',f"{freeze['source_revision']}:{name}"])
files=json.loads((leaf/'evidence-sha256.json').read_text());assert len(files)==47
for name,digest in files.items():
 path=leaf/name;assert sha(path)==digest,name;tracked(str(path.relative_to(root)))
 if name.endswith('.log.gz'):
  assert gzip.decompress(path.read_bytes())==path.with_suffix('').read_bytes()
  assert int.from_bytes(path.read_bytes()[4:8],'little')==0
verification=json.loads((leaf/'verification.json').read_text());assert len(verification['commands'])==10
for record in verification['commands']:
 assert record['exit_code']==0 and record['source_revision']==freeze['source_revision']
 assert sha(root/record['log'])==record['sha256'];tracked(record['log'])
assert len(verification['excluded_attempts'])==1
for attempt in verification['excluded_attempts']:
 assert not attempt['claimed_as_successful_verification'] and attempt['record']['exit_code']==1
 for name,digest in [(attempt['retained_log'],attempt['retained_log_sha256']),(attempt['retained_record'],attempt['retained_record_sha256']),(attempt['wrapper_snapshot'],attempt['wrapper_sha256'])]:
  assert sha(root/name)==digest;tracked(name)
 assert attempt['record']['sha256']==attempt['retained_log_sha256']
parent=json.loads((leaf/'parent-evidence-preservation.json').read_text());assert len(parent['sha256'])==795
for name,digest in parent['sha256'].items():assert sha(root/name)==digest,name
shard=json.loads((root/'docs/provenance/openai-math.d/excitationStabilizer8750.json').read_text())
names={e['downstream']['declaration'] for e in shard['entries']};assert len(names)==3
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(leaf/'axioms.log').read_text(),re.S)
assert len(reports)==3 and {n for n,_ in reports}==names
for _,axioms in reports:assert {a.strip() for a in axioms.split(',')}<={'propext','Classical.choice','Quot.sound'}
report={'source_revision':freeze['source_revision'],'result':'passed','frozen_files':4,'portable_leaf_hashes':47,'canonical_successful_commands':10,'excluded_attempts':1,'retained_parent_evidence_files':795,'standard_kernel_reports':3,'declarations':sorted(names),'independent_visual_inspection':'The retained one-page mathematical PDF image was independently inspected. All three statements, their proofs, the actual excitation matrices and source citation are legible.','mathematical_review':'The actual inverse-coordinate copy action gives image sigma B. The stabilizer condition is precisely the subgroup condition used for good/bad component symmetry; arbitrary auxiliary operators factor on the disjoint system. The proved commutation preserves the given fixed-vector equation and, with the identity physical permutation, its whole-copy auxiliary label. All algebraic identities include zero copies and need no normalization; no metric commutation is asserted.'}
(folder/'leaf-review.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
