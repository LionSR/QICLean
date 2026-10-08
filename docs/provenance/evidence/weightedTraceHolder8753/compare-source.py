"""Compare exact signatures and proof bodies with the authoritative pre-refactoring source."""
from pathlib import Path
import hashlib,json,re,subprocess
root=Path.cwd();e=Path(__file__).resolve().parent
freeze=json.loads((e/'source-freeze.json').read_text());base=freeze['authoritative_parent_revision']
sha=lambda data:hashlib.sha256(data).hexdigest()
def declaration(text,name):
 m=re.search(r'^theorem '+re.escape(name)+r'\b',text,re.M);assert m,name
 rest=text[m.start():];stop=re.search(r'\n(?:/-|end\b|namespace\b|variable\b|(?:private )?(?:theorem|lemma|def)\b)',rest)
 if stop:rest=rest[:stop.start()]
 assert ':= by' in rest,name
 signature,body=rest.split(':= by',1);return signature.strip(),body.strip()
old=[('QICLean/Representation/SchurSurprisal.lean','joint_hom_fst','PermutationRepresentation.joint_hom_fst'),('QICLean/Representation/SchurSurprisal.lean','joint_hom_snd','PermutationRepresentation.joint_hom_snd'),('QICLean/Representation/GroupedLabelEntropy.lean','groupedCopies_labelEntropy_bounds','TensorPower.groupedCopies_labelEntropy_bounds'),('QICLean/Representation/MergeExponential.lean','exp_mergeDeficit_eq_sum','PermutationRepresentation.exp_mergeDeficit_eq_sum'),('QICLean/Representation/MergeExponential.lean','re_trace_mul_exp_mergeDeficit_eq_sum','PermutationRepresentation.re_trace_mul_exp_mergeDeficit_eq_sum'),('QICLean/Representation/MergeExponential.lean','posSemidef_mergeDeficit','PermutationRepresentation.posSemidef_mergeDeficit')]
rows=[]
for path,short,full in old:
 before=subprocess.check_output(['git','show',base+':'+path]).decode();after=(root/path).read_text();bs,bb=declaration(before,short);as_,ab=declaration(after,short);assert bs==as_,full
 rows.append({'path':path,'declaration':full,'signature_byte_identical':True,'signature_sha256':sha(bs.encode()),'old_proof_body_sha256':sha(bb.encode()),'new_proof_body_sha256':sha(ab.encode()),'proof_body_byte_identical':bb==ab,'refresh_reason':'Direct public proof simplification.' if bb!=ab else 'Unchanged public body; its actual private marginal helpers were simplified.'})
notices=[]
for path in ['docs/provenance/openai-math.d/groupedLabelEntropy8750.json','docs/provenance/openai-math.d/mergeExponential8750.json','docs/provenance/openai-math.d/mergeDeficitPositivity8753.json']:
 data=(root/path).read_bytes();assert data==subprocess.check_output(['git','show',base+':'+path]);notices.append({'path':path,'sha256':sha(data),'preserved':'Whole original provenance record and historical verification; fresh child verification is separate.'})
for row in freeze['files']:
 assert sha((root/row['path']).read_bytes())==row['sha256']
(e/'source-comparison.json').write_text(json.dumps({'authoritative_parent_revision':base,'source_revision':freeze['source_revision'],'refreshed_declarations':rows,'original_provenance_preserved':notices,'new_declarations':json.loads((e/'public-declarations.json').read_text())['new'],'scope':'Five frozen Lean files, exposition and ledger only; no broad parent semantic audit is claimed.'},indent=2)+'\n')
for p in (root/'output/pdf').glob('*.pdf'):
 pass
preserve=json.loads((e/'saved-pdf-preservation.json').read_text())
for row in preserve['files']:assert sha((root/row['path']).read_bytes())==row['sha256']
for branch,revision in preserve['published_branches'].items():assert subprocess.check_output(['git','rev-parse',branch],text=True).strip()==revision
print('All six old signatures exact; direct and private-helper proof changes classified; original provenance, published refs and saved PDFs preserved.')
