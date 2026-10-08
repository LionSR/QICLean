"""Verify the original component-moment ledger against the retained policy."""
from pathlib import Path
import importlib.util,json
r=Path.cwd();e=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('provenance_policy',e/'provenance-policy.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
ledger=m.read_json(r/'docs/provenance/openai-math.d/mergeDeficitPositivity8753.json')
count=m.validate([ledger],m.read_json(e/'provenance-schema.json'),{'LionSR/QICLean':r},scan=False)
assert count==4
print('Passed the four-entry original component-moment provenance against the retained TNLean policy.')
