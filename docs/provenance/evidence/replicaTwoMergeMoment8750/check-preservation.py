from pathlib import Path
import json,hashlib,subprocess,gzip
root=Path.cwd();e=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256((root/p).read_bytes()).hexdigest()
records=json.loads(gzip.decompress((e/'inherited-byte-preservation.json.gz').read_bytes()))['records']
for row in records:assert sha(row['path'])==row['sha256'],row['path']
allowed={r['path'] for r in json.loads((e/'merge-resolutions.json').read_text())['allowed_source_differences']}
sources=json.loads(gzip.decompress((e/'two-deficit-parent-source-comparison.json.gz').read_bytes()))
for row in sources['rows']:
 if row['path'] not in allowed:assert sha(row['path'])==row['parent_sha256'],row['path']
assert (root/'QICLean/Entropy/FilterMoment.lean').read_bytes()==subprocess.check_output(['git','show','b5ba8ae2:QICLean/Entropy/FilterMoment.lean'])
for row in json.loads((e/'preexisting-output-preservation.json').read_text())['files']:
 assert sha(row['path'])==row['sha256']
print('Preserved',len(records),'inherited files and',len(sources['rows']),'parent source comparisons with only exact recorded exceptions.')
