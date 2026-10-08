"""Validate fixed regional-density proofs, inherited evidence and their complete-book inclusion."""
from pathlib import Path
import gzip,hashlib,io,json,re,subprocess,tarfile
r=Path.cwd();p=Path(__file__).resolve().parent
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();tracked=set(subprocess.check_output(['git','ls-files'],text=True).splitlines())
m=json.loads((p/'verification.json').read_text())
for c in m['commands']:
 assert c['source_revision']==m['inclusion_revision']
 assert c['exit_code']==0 and sha(r/c['log'])==c['sha256'] and c['log'] in tracked
for e in m['excluded_attempts']:
 assert not e['claimed_as_successful_verification'] and e['record']['exit_code'] != 0
 assert sha(r/e['record']['log'])==e['record']['sha256'] and e['record']['log'] in tracked
for n,h in m['file_hashes'].items():assert n in tracked and sha(r/n)==h,n
for q in json.loads((p/'compression.json').read_text()):
 raw=r/q['path'];gz=r/q['gzip_path'];assert q['path'] in tracked and q['gzip_path'] in tracked
 assert sha(raw)==q['sha256'] and sha(gz)==q['gzip_sha256']
 assert gzip.decompress(gz.read_bytes())==raw.read_bytes() and int.from_bytes(gz.read_bytes()[4:8],'little')==0
parent=json.loads((p/'parent-preservation.json').read_text());archive=tarfile.open(fileobj=io.BytesIO(subprocess.check_output(['git','archive',parent['parent_revision']])))
for n,h in parent['sha256'].items():
 original=archive.extractfile(n).read();assert hashlib.sha256(original).hexdigest()==h,n
 now=(r/n).read_bytes()
 if n=='QICLean/Analysis.lean':
  addition=b'import QICLean.Analysis.ReplicaRegionalDensity\n';assert now.count(addition)==1;assert now.replace(addition,b'')==original,n
 elif n=='blueprint/src/chapter/ch12_entropy.tex':
  addition=b'\\input{fragment/replica_regional_density}\n';assert now.count(addition)==1;assert now.replace(addition,b'')==original,n
 else:assert now==original,n
leaf=r/'docs/provenance/evidence/replicaRegionalDensity8750'
subprocess.run(['python3',str(leaf/'validate-manifest.py'),'--allow-inclusion'],check=True,stdout=subprocess.DEVNULL)
inventory=json.loads((leaf/'verification.json').read_text());assert all(n in tracked for n in inventory['file_hashes'])
freeze=json.loads((leaf/'source-freeze.json').read_text())
assert freeze['source_revision']==m['mathematical_source_revision']
for n,h in freeze['production_sha256'].items():assert sha(r/n)==h,n
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(p/'axioms.log').read_text(),re.S)
assert len(reports)==1 and {n for n,_ in reports}==set(m['owned_declarations'])
for _,a in reports:assert {s.strip() for s in a.split(',')}<={'propext','Classical.choice','Quot.sound'}
n=json.loads((p/'native-targets.json').read_text());assert n['contains_all_active_fragment_targets'] and n['contains_the_owned'] and not n['missing']
assert set(n['owned_declarations'])==set(m['owned_declarations']);assert sha(r/n['native_list'])==n['native_list_sha256']
w=json.loads((p/'web-inspection.json').read_text());assert not w['errors'] and len(w['proofs'])==1 and all(q['height']>0 for q in w['proofs']) and w['mobile_page_width']<=361
for q in w['mobile_equation_scrolls']:assert abs(q['maximum']-q['scrollLeft'])<=1
assert json.loads((p/'pdf-page-selection.json').read_text())['pages']==m['complete_pdf_pages']
v=json.loads((p/'visual-inspection.json').read_text());assert v['result']=='passed' and v['complete_proof_visible']
print(len(m['commands']),'successful commands;',len(m['excluded_attempts']),'excluded attempts;',len(m['file_hashes']),'tracked hashes')
print(len(parent['sha256']),'parent files unchanged except the exact two inclusion lines; four frozen mathematical/exposition files and all',len(inventory['file_hashes']),'leaf hashes preserved.')
print('Nine original leaf checks, preserved parent evidence, one fresh standard-kernel report,',n['fragment_declarations'],'active fragment targets and',n['native_declarations'],'native declarations pass.')
