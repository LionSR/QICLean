"""Check source and text-packet integrity with the standard library; no render or Lean."""
from pathlib import Path
import argparse, hashlib, json, subprocess
parser=argparse.ArgumentParser();parser.add_argument('--source-revision');args=parser.parse_args()
HERE=Path(__file__).resolve().parent
ROOT=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=HERE,text=True).strip())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((HERE/'focus-manifest.json').read_text());v=json.loads((HERE/'verification.json').read_text())
r=json.loads((HERE/'visual-review.json').read_text());c=json.loads((HERE/'commands.json').read_text())
t=json.loads((HERE/'source-transfer.json').read_text())
assert t['render_source_revision']==m['source_revision'] and not t['rerender_performed']
assert v['status']==r['status']=='passed'
assert m['source_revision']==v['source_revision']==r['source_revision']
assert m['source_sha256']==v['source_sha256']
for name,digest in (m['source_sha256']|m['fixture_source_sha256']).items():
    data=subprocess.check_output(['git','show',args.source_revision+':'+name],cwd=ROOT) if args.source_revision else (ROOT/name).read_bytes()
    if name==t['changed_path'] and hashlib.sha256(data).hexdigest()==t['current_source_sha256']:
        normalized=data.decode()
        for before,after in t['exact_reverse_replacements']:
            assert normalized.count(before)==1
            normalized=normalized.replace(before,after)
        data=normalized.encode()
    assert hashlib.sha256(data).hexdigest()==digest,name
for key,want in {'production_modules':4,'production_lines':639,'explicitly_named_public_declarations':50,'generated_public_instances':2,'public_constants':52,'source_inspected_consumers':24,'source_inspected_axiom_guards':52,'blueprint_entries':14,'proofs':10,'checked_markers':24,'equation_labels':15,'all_labels':33,'pdf_pages':7,'html_pages':6,'pdf_declaration_links':52,'html_chapter_declaration_links':52,'html_all_declaration_links':156,'explicit_dependency_edges':24,'diagrams':0}.items():assert v['counts'][key]==want,key
assert len(v['declarations'])==len(set(v['declarations']))==52
assert len(v['artifact_sha256'])==17
assert r['pdf_review']['pages_directly_viewed']==list(range(1,8))
for name in ['unlinked_public_constants','missing_internal_anchors','missing_label_anchors','duplicate_html_ids','tex_box_reference_warnings','curly_math_prime_serialization']:assert not v[name],name
for name,record in c['replay_scripts'].items():assert sha(HERE/name)==record['published_sha256'],name
for name,digest in json.loads((HERE/'packet-sha256.json').read_text()).items():assert sha(HERE/name)==digest,name
for p in HERE.iterdir():
    if p.is_file():
        text=p.read_text();assert not any(prefix in text for prefix in ['/'+'workspace/scratch/','/'+'root/']),p.name
print('PASS: 4 frozen modules, 52 public links (50 named + 2 generated), 33 labels, 7 reviewed PDF pages, 6 static HTML pages, 17 hashed artifacts, exact current-source transfer, and text-packet integrity')
