#!/usr/bin/env python3
"""Fresh, source-hashed critical-target check after the October 5 reset.

This checks only the explicitly listed target closure. It is not a full
999-module build, and never relabels a historical transcript as fresh.
"""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess

root = Path('/workspace/shared/sticky-recovery-20261005')
repo = Path('/workspace/scratch/5f2524fd4117/4dstickykakeya')
manifest = json.loads((root / 'critical-source-manifest.json').read_text())
log = root / 'critical-targets-build.log'
status = root / 'critical-targets-status.json'
if log.exists():
    raise SystemExit('Refusing to overwrite an existing fresh transcript')

def source_changes():
    return [m for m, entry in manifest['sources'].items()
            if hashlib.sha256((repo / entry['path']).read_bytes()).hexdigest()
            != entry['sha256']]

if source_changes():
    raise SystemExit('Prepared source hashes changed before this build')

command = ['bash', '-c',
           'source /workspace/scratch/5f2524fd4117/lean-tools/environment.sh\n'
           'exec ./scripts/build-bounded.sh "$@"',
           'critical-targets', *manifest['roots']]
state = {'state': 'running', 'source_commit': manifest['source_commit'],
         'project_module_count': manifest['project_module_count'],
         'full_project_build': False, 'command': command,
         'executor_start_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
status.write_text(json.dumps(state, indent=2) + '\n')
with log.open('w') as stream:
    stream.write(json.dumps(state, indent=2) + '\n')
    stream.flush()
    result = subprocess.run(command, cwd=repo, stdout=stream,
                            stderr=subprocess.STDOUT, check=False)
    changes = source_changes()
    state.update(state='passed' if result.returncode == 0 and not changes else 'failed',
                 exit_code=result.returncode, changed_sources=changes,
                 executor_finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    stream.write('\n' + json.dumps(state, indent=2) + '\n')
status.write_text(json.dumps(state, indent=2) + '\n')
print(json.dumps(state, indent=2))
raise SystemExit(0 if state['state'] == 'passed' else 1)
