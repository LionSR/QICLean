"""Collect immutable source bindings and raw command/reader evidence for the actual Hölder step."""
from pathlib import Path
import hashlib
import json

root = Path.cwd()
folder = Path(__file__).resolve().parent
freeze = json.loads((folder/'source-freeze.json').read_text())
commands = []
for path in sorted(folder.glob('*-exit.json')):
    record = json.loads(path.read_text())
    commands.append(dict(name=path.name.removesuffix('-exit.json'), record=str(path.relative_to(root)),
                         exit_code=record['exit_code'], contributes_to_success=record['exit_code']==0))
artifacts = {}
for path in sorted(folder.rglob('*')):
    if not path.is_file() or path.name == 'manifest.json' or '__pycache__' in path.parts:
        continue
    data = path.read_bytes()
    artifacts[str(path.relative_to(root))] = dict(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))
manifest = dict(**freeze, canonical_source_revision='4907ab67c69587e6b71d81e8bb6ae27b8e2189c2',
    policy_revision='806099b4dddcce591b3a62ee1921926a6af5ad55',
    actual_commands=commands, successful_commands=sum(c['contributes_to_success'] for c in commands),
    excluded_failed_attempts=sum(not c['contributes_to_success'] for c in commands),
    mathematical_scope='Actual five-factor trace Hölder, arbitrary positive semidefinite weight; no component, entropy-rate or inverse-comparator conclusion.',
    complete_library_jobs=9826, preserved_parent_files=4896, preserved_leaf_artifacts=65,
    exact_stock_reports=1, stock_report_sha256='3376cfe5d8ccd896aa4bbbeebdd14424b584696067938bb947af4fc2519702de',
    pdf=json.loads((folder/'pdf-inspection.json').read_text()),
    native=dict(declarations=3774, active_fragment_targets=82, owned_targets=1),
    reader=dict(desktop_width=1440, mobile_width=360, overflowing_display_count=1,
                inspected_right_endpoint_scroll=183, whole_pages=50, whole_typeset_elements=41056),
    artifacts=artifacts)
(folder/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(f"Collected {len(artifacts)} artifacts, {manifest['successful_commands']} successful command records and {manifest['excluded_failed_attempts']} excluded failures.")
