#!/usr/bin/env python3
"""Validate the ten new exact-source QIC provenance entries without compiling Lean."""
import sys
sys.dont_write_bytecode=True
import argparse,hashlib,importlib.util,json,re
from pathlib import Path
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--upstream-root',type=Path,required=True);a=ap.parse_args();root=a.root.resolve();out=root/'docs/provenance/evidence/physicalTraceHelpers8769';spec=importlib.util.spec_from_file_location('policy',out/'canonical/check_openai_provenance.py');policy=importlib.util.module_from_spec(spec);spec.loader.exec_module(policy)
ledger=policy.read_json(root/'docs/provenance/openai-math.d/8769-physical-trace-helpers.json');schema=policy.read_json(out/'canonical/openai-math.schema.json');n=policy.validate([ledger],schema,{'LionSR/QICLean':root,'openai/math':a.upstream_root.resolve()},scan=False);assert n==10
byfile={}
for e in ledger['entries']:byfile.setdefault(e['downstream']['path'],set()).add(e['downstream']['declaration'])
for path,names in byfile.items():
 text=(root/path).read_text();code,_=policy.lean_parts(text);assert not re.search(r'\b(sorry|admit|axiom|unsafeCast|native_decide)\b',code);assert set(policy.declarations(text))==names
for old,new in [('PhysicalBasisInvariance','Channel/PartialTraceBasisInvariance'),('PhysicalBlockTraceNorm','Channel/PartialTraceBlocks')]:
 before=policy.lean_parts((out/'original-sources'/(old+'.lean')).read_text())[0];after=policy.lean_parts((root/'QICLean'/(new+'.lean')).read_text())[0];assert before.split()==after.split()
old=[]
for name in ['GaussianSourceIntegrability','SourceGaussianMoments']:
 s=(out/'original-sources'/(name+'.lean')).read_text().split('namespace ProbabilityTheory',1)[1].split('end ProbabilityTheory',1)[0];old+=policy.lean_parts(s)[0].split()
s=(root/'QICLean/Probability/MatrixTraceNormIntegrability.lean').read_text().split('namespace ProbabilityTheory',1)[1].split('end ProbabilityTheory',1)[0];assert old==policy.lean_parts(s)[0].split()
ids=set();names=set();count=0
for p in (root/'docs/provenance/openai-math.d').glob('*.json'):
 for e in policy.read_json(p)['entries']:
  key=(e['downstream']['repository'],e['downstream']['declaration']);assert e['id'] not in ids;assert key not in names;ids.add(e['id']);names.add(key);count+=1
print('Canonical scoped provenance valid: 10 exact-source declarations, manuscript labels checked.')
print(f'Collision check: {count} QIC entries. Other entries were not revalidated.')
print('All ten theorem token streams preserved; no proof placeholders or additional axioms.')
