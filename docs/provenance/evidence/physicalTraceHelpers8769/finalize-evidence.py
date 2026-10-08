#!/usr/bin/env python3
"""Run scoped provenance checks and finalize the physical-trace evidence manifest."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import time

root = Path('/Users/siruilu/Local/agentFormalization/QICLean/worktrees/physical-trace-helpers')
out = root / 'docs/provenance/evidence/physicalTraceHelpers8769'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
shutil.copy2('/tmp/validate-qic-physical-trace-evidence.py', out / 'validate-evidence.py')
shutil.copy2(Path(__file__), out / 'finalize-evidence.py')
command = ['uv', 'run', '--no-project', '--with', 'jsonschema==4.26.0', 'python',
           str(out / 'check-provenance.py'), '--root', str(root),
           '--upstream-root', '/private/tmp/tnlean-openai-math-audit.git']
env = os.environ.copy()
env['PYTHONDONTWRITEBYTECODE'] = '1'
start = time.monotonic()
result = subprocess.run(command, cwd=root, env=env, capture_output=True, text=True)
(out / 'provenance.log').write_text(result.stdout + result.stderr)
(out / 'provenance-command.json').write_text(json.dumps({
    'command': command, 'cwd': str(root), 'returncode': result.returncode,
    'seconds': round(time.monotonic() - start, 3), 'log_sha256': sha(out / 'provenance.log'),
}, indent=2) + '\n')
print(result.stdout + result.stderr)
assert result.returncode == 0
(out / 'manifest.json').write_text(json.dumps({
    'sha256': {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*'))
               if p.is_file() and p.name != 'manifest.json' and '__pycache__' not in p.parts},
}, indent=2) + '\n')
result = subprocess.run(['python3', str(out / 'validate-evidence.py'), '--root', str(root)],
                        capture_output=True, text=True)
print(result.stdout + result.stderr)
assert result.returncode == 0
