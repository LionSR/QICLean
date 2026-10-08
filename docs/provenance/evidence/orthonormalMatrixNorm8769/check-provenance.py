#!/usr/bin/env python3
"""Check the one new QIC declaration with the unchanged canonical provenance policy."""
import argparse,hashlib,importlib.util,json,re,subprocess
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--upstream-root',type=Path,required=True);a=ap.parse_args();root=a.root.resolve();out=root/'docs/provenance/evidence/orthonormalMatrixNorm8769';spec=importlib.util.spec_from_file_location('policy',out/'canonical/check_openai_provenance.py');policy=importlib.util.module_from_spec(spec);spec.loader.exec_module(policy)
ledger=policy.read_json(root/'docs/provenance/openai-math.d/8769-orthonormal-matrix-norm.json');schema=policy.read_json(out/'canonical/openai-math.schema.json');n=policy.validate([ledger],schema,{'LionSR/QICLean':root,'openai/math':a.upstream_root.resolve()},scan=False);assert n==1
entry=ledger['entries'][0];text=(root/entry['downstream']['path']).read_text();code,_=policy.lean_parts(text);original,_=policy.lean_parts((out/'source-original.lean').read_text());assert re.findall(r'\S+',code)==re.findall(r'\S+',original);assert not re.search(r'\b(sorry|admit|axiom|unsafeCast|native_decide)\b',code)
assert set(policy.declarations(text))=={entry['downstream']['declaration']}
ids=set();names=set();count=0
for p in (root/'docs/provenance/openai-math.d').glob('*.json'):
 for e in policy.read_json(p)['entries']:
  key=(e['downstream']['repository'],e['downstream']['declaration']);assert e['id'] not in ids,e['id'];assert key not in names,key;ids.add(e['id']);names.add(key);count+=1
print('Canonical scoped provenance valid: 1 exact-source declaration, manuscript label checked.')
print(f'Collision check: {count} QIC entries. Other entries were not revalidated.')
print('Original proof tokens preserved; no proof placeholders or additional axioms.')
