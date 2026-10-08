"""Verify the immutable mathematics and corrected complete-book evidence."""
from pathlib import Path
import gzip,hashlib,json,re,subprocess
r=Path.cwd();p=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
tracked=set(subprocess.check_output(['git','ls-files'],text=True).splitlines())
m=json.loads((p/'verification.json').read_text())
assert m['mathematical_source_revision']=='05dc00486525e0e79413afb806c221eb98787204'
assert m['inclusion_revision']=='69b31fc6bbb94576c69def6d42d3153b39afcf04'
assert m['exposition_revision']=='7840e716185f9d477c3c135192f3ec0573813e14'
for c in m['commands']+m['initial_visual_attempt']['commands']:
 assert c['exit_code']==0 and c['source_revision'] in [m['inclusion_revision'],m['exposition_revision']]
 assert c['log'] in tracked and sha((r/c['log']).read_bytes())==c['sha256']
for n,h in m['file_hashes'].items():assert n in tracked and sha((r/n).read_bytes())==h,n
for q in json.loads((p/'compression-revised.json').read_text()):
 raw=r/q['path'];gz=r/q['gzip_path']
 assert q['path'] in tracked and q['gzip_path'] in tracked
 assert sha(raw.read_bytes())==q['sha256'] and sha(gz.read_bytes())==q['gzip_sha256']
 assert gzip.decompress(gz.read_bytes())==raw.read_bytes() and int.from_bytes(gz.read_bytes()[4:8],'little')==0
initial=json.loads((p/'initial-book-verification.json').read_text())
assert not initial['claimed_as_complete_final_verification'] and initial['visual_review_result']=='failed'
for n,h in initial['file_hashes'].items():assert sha((r/n).read_bytes())==h,n
assert json.loads((p/'visual-inspection-initial.json').read_text())['result']=='failed'
subprocess.run(['python3',str(p/'review-historical-leaf.py')],check=True,stdout=subprocess.DEVNULL)
subprocess.run(['python3',str(p/'check-preservation-revised.py')],check=True,stdout=subprocess.DEVNULL)
freeze=json.loads((p/'source-freeze.json').read_text());expo=json.loads((p/'exposition-freeze.json').read_text())
for n,h in freeze['production_sha256'].items():
 old=subprocess.check_output(['git','show',freeze['source_revision']+':'+n]);assert sha(old)==h,n
 if n!=expo['path']:assert (r/n).read_bytes()==old,n
assert sha((r/expo['path']).read_bytes())==expo['sha256']
assert (r/expo['path']).read_bytes()==subprocess.check_output(['git','show',expo['revision']+':'+expo['path']])
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(p/'axioms.log').read_text(),re.S)
assert len(reports)==2 and {n for n,_ in reports}==set(m['owned_declarations'])
for _,a in reports:assert {s.strip() for s in a.split(',')}<={'propext','Classical.choice','Quot.sound'}
n=json.loads((p/'native-targets-revised.json').read_text());assert n['contains_all_active_fragment_targets'] and n['contains_the_owned'] and not n['missing']
assert set(n['owned_declarations'])==set(m['owned_declarations']) and sha((r/n['native_list']).read_bytes())==n['native_list_sha256']
w=json.loads((p/'web-inspection-revised.json').read_text());assert not w['errors'] and len(w['proofs'])==1 and all(q['height']>0 for q in w['proofs']) and w['mobile_page_width']<=361
for q in w['mobile_equation_scrolls']:assert abs(q['maximum']-q['scrollLeft'])<=1
v=json.loads((p/'visual-inspection-revised.json').read_text());assert v['result']=='passed' and v['complete_definition_visible'] and v['complete_proof_visible'] and v['definition_coordinate_order_preserved']
for n,h in v['inspected_files'].items():assert sha((r/n).read_bytes())==h
assert json.loads((p/'pdf-page-selection-revised.json').read_text())['pages']==m['complete_pdf_pages']
print(len(m['commands']),'final successful commands;',len(m['initial_visual_attempt']['commands']),'preserved initial book commands;',len(m['file_hashes']),'tracked hashes.')
print('Two exact standard-kernel reports;',n['fragment_declarations'],'active fragment targets;',n['native_declarations'],'native declarations; complete PDF/web definition and proof visible.')
print('Unchanged mathematical source and historical leaf evidence; only the exact two inclusion lines and authorized exposition child differ from the leaf parent.')
