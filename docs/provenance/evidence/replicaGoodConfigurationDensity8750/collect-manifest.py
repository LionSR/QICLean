"""Collect the frozen full-good configuration command and file inventory."""
from pathlib import Path
import json,hashlib,gzip,subprocess
r=Path.cwd();p=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
f=json.loads((p/'source-freeze.json').read_text());all_checks=[json.loads(q.read_text()) for q in sorted(p.glob('*-exit.json'))];checks=[c for c in all_checks if c['exit_code']==0 and c['source_revision']==f['source_revision']];historical=[c for c in all_checks if c['exit_code']==0 and c['source_revision']!=f['source_revision']];excluded=[c for c in all_checks if c['exit_code']!=0];compressed=[]
for c in all_checks:
 q=r/c['log'];raw=q.read_bytes();z=Path(str(q)+'.gz');assert gzip.decompress(z.read_bytes())==raw
 compressed.append({'raw':c['log'],'raw_sha256':sha(raw),'gzip':str(z.relative_to(r)),'gzip_sha256':sha(z.read_bytes()),'mtime':0})
(p/'compression.json').write_text(json.dumps(compressed,indent=2)+'\n')
files={str(q.relative_to(r)):sha(q.read_bytes()) for q in sorted(p.rglob('*')) if q.is_file() and q != p/'verification.json' and q.name not in ['standalone-wrapper.aux','standalone-wrapper.out','standalone-wrapper.log']}
f=json.loads((p/'source-freeze.json').read_text());files.update(f['production_sha256']);n='docs/provenance/openai-math.d/replicaGoodConfigurationDensity8750.json';files[n]=sha((r/n).read_bytes())
m={'source_revision':f['source_revision'],'declarations':['TensorPower.fiveFactorCopiesEquiv','Matrix.replicaGoodConfigurationMarginal','Matrix.symProj_mul_replicaGoodConfigurationMarginal'],'checks':checks,'excluded_checks':excluded,'historical_checks':historical,'file_hashes':files,'inventory_exclusions':['verification.json: self inventory','standalone-wrapper.aux/out/log: local TeX auxiliaries; stdout is recorded separately'],'scope':'Two original definitions and one actual full-good density support theorem. All good Y retained; no inherited mathematical audits repeated.'}
(p/'verification.json').write_text(json.dumps(m,indent=2)+'\n');print(len(checks),'actual commands;',len(files),'portable file hashes')
