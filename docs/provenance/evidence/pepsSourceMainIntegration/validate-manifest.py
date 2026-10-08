"""Check the fixed PEPS-main integration and literal mechanical-verification evidence."""
from pathlib import Path
import gzip,hashlib,io,json,re,subprocess,tarfile
root=Path.cwd();p=Path(__file__).resolve().parent
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
tracked=set(subprocess.check_output(['git','ls-files'],text=True).splitlines())
m=json.loads((p/'verification.json').read_text())
for c in m['commands']:
 assert c['source_revision']==m['source_revision'] and c['exit_code']==0,c
 assert sha(root/c['log'])==c['sha256'] and c['log'] in tracked
for e in m['excluded_attempts']:
 assert not e['claimed_as_successful_final_verification']
 c=e['record'];assert sha(root/c['log'])==c['sha256'] and c['log'] in tracked
 assert c['exit_code']==e['actual_exit_code']
for n,h in m['file_hashes'].items():assert n in tracked and sha(root/n)==h,n
for c in json.loads((p/'compression.json').read_text()):
 raw=root/c['path'];gz=root/c['gzip_path']
 assert c['path'] in tracked and c['gzip_path'] in tracked
 assert sha(raw)==c['sha256'] and sha(gz)==c['gzip_sha256']
 assert gzip.decompress(gz.read_bytes())==raw.read_bytes() and int.from_bytes(gz.read_bytes()[4:8],'little')==0
freeze=json.loads((p/'source-freeze.json').read_text())
archive=tarfile.open(fileobj=io.BytesIO(subprocess.check_output(['git','archive',freeze['source_revision']])))
for n,h in freeze['sha256'].items():
 assert sha(root/n)==h and (root/n).read_bytes()==archive.extractfile(n).read(),n
j=json.loads((p/'parent-compatibility.json').read_text())
for key in ['incoming_changed_production_sha256','main_existing_production_sha256','identical_toolchain_configuration_and_dependencies_sha256']:
 for n,h in j[key].items():assert sha(root/n)==h,n
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",(p/'source-contraction-kernels.log').read_text(),re.S)
assert len(reports)==8 and {n for n,_ in reports}==set(m['fresh_kernel_declarations'])
for _,a in reports:assert {x.strip() for x in a.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'}
ci=json.loads((p/'ci-source-regressions.json').read_text());assert ci['count']==21 and len(ci['tests'])==21
for item in ci['tests']:
 c=json.loads((p/(item['name']+'-exit.json')).read_text());assert c in m['commands'] and c['argv']==item['argv']
assert (root/'.github/workflows/pr-ci.yml').read_bytes()==subprocess.check_output(['git','show',m['source_revision']+':.github/workflows/pr-ci.yml'])
policy=(p/'provenance-policy.py').read_bytes();assert policy==subprocess.check_output(['git','-C','/Users/siruilu/Local/agentFormalization/TNLean','show','4e9d9c898a4401d51cf1eeeabcea8572242387fe:scripts/check_openai_provenance.py'])
n=json.loads((p/'native-targets.json').read_text());assert n['contains_all_source_targets'] and n['contains_all_active_fragment_targets'] and not n['missing']
assert len(n['source_chapters'])==4 and n['source_declarations']==240 and n['native_declarations']==3617
assert sha(root/n['native_list'])==n['native_list_sha256']
w=json.loads((p/'web-inspection.json').read_text());assert len(w['entries'])==9
for e in w['entries']:
 assert not e['desktop']['errors'] and not e['mobile']['errors'] and e['mobile']['width']<=361
 if e['anchor'].startswith('thm:'):assert e['desktop']['proofs'] and all(q['height']>0 for q in e['desktop']['proofs'])
s=json.loads((p/'equation-scroll-inspection.json').read_text());assert len(s['entries'])==9 and s['equation_scrollers_reach_right_endpoint']
for e in s['entries']:
 assert e['page_width']<=361
 for q in e['local_equation_scrolls']:assert abs(q['scrollLeft']-q['maximum'])<=1
assert json.loads((p/'pdf-page-selection.json').read_text())['pdf_pages']==445
print(len(m['commands']),'successful final commands;',len(m['excluded_attempts']),'excluded attempts;',len(m['file_hashes']),'tracked evidence hashes')
print('All',len(freeze['sha256']),'source files and',len(j['incoming_changed_production_sha256']),'incoming /',len(j['main_existing_production_sha256']),'main proof files unchanged.')
print('Exact 21 CI regressions, eight fresh standard-kernel reports, four inherited provenance packets and 240 native source-chapter targets pass.')
print('Complete PDF/web/native and nine complete desktop/mobile entries, with local equation scroll endpoints, pass.')
