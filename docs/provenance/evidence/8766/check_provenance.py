"""Check the issue-owned QIC polar ledger with the pinned external TNLean policy."""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, types

parser = argparse.ArgumentParser()
parser.add_argument('--root', type=Path, required=True)
parser.add_argument('--policy-root', type=Path, required=True,
                    help='TNLean Git checkout containing the pinned policy commit')
args = parser.parse_args()
root, policy_root = args.root.resolve(), args.policy_root.resolve()
policy = 'a05ef8f8db19f28e987bf3ce599c5f284f96921f'
def blob(path):
    return subprocess.check_output(['git', 'show', policy + ':' + path], cwd=policy_root)
source = blob('scripts/check_openai_provenance.py')
schema = blob('docs/provenance/openai-math.schema.json')
checker = types.ModuleType('pinned_openai_provenance')
checker.__file__ = '<pinned external provenance validator>'
exec(compile(source, checker.__file__, 'exec'), checker.__dict__)
ledger = json.loads((root/'docs/provenance/openai-math.d/8766.json').read_text())
manifest = json.loads((root/'docs/provenance/evidence/8766/validation.json').read_text())
assert {row['verification']['revision'] for row in ledger['entries']} == {manifest['verified_source_revision']}
# The pinned per-entry and schema checks run unchanged. Repository-wide scanning
# would require certifying unrelated issue ledgers; owned-module coverage follows.
assert checker.validate([ledger], json.loads(schema), {'LionSR/QICLean': root}, scan=False) == 6
sys.path.insert(0, str(root/'scripts'))
from blueprint_lean_sync import collect_file_lean_decls
private = []
for path in {row['downstream']['path'] for row in ledger['entries']}:
    declarations = collect_file_lean_decls(root/path, root/'QICLean')
    public = {d.fqn for d in declarations if not d.is_private}
    recorded = {row['downstream']['declaration'] for row in ledger['entries'] if row['downstream']['path'] == path}
    assert public == recorded
    expected_ids = {row['id'] for row in ledger['entries'] if row['downstream']['path'] == path}
    assert set(checker.ID_RE.findall((root/path).read_text())) == expected_ids
    private.extend({'source_name':d.fqn, 'path':path, 'line':d.line} for d in declarations if d.is_private)
assert len(private) == 1 and private[0]['source_name'] == 'Matrix.norm_toEuclideanCLM_unitary'
print(json.dumps({'status':'passed', 'verified_source_revision':manifest['verified_source_revision'], 'source_publication':manifest['source_publication'], 'repository':'LionSR/QICLean', 'public_theorems':6, 'private_helpers':private, 'policy_revision':policy, 'policy_sha256':hashlib.sha256(source).hexdigest(), 'schema_sha256':hashlib.sha256(schema).hexdigest(), 'checks':['schema', 'exact QIC source bytes', 'declaration and notice identity', 'log hashes', 'exact named raw axiom output', 'all public declarations and provenance IDs in the two owned modules'], 'limits':['This validates only issue 8766; unrelated issue 8765 evidence and repository-wide notice coverage are not certified.', 'Pinned policy code is unchanged; QIC is supplied as an explicit repository root.', 'No Lean build, remote action, full QIC root or complete CI run is performed by this script.']}, indent=2))
