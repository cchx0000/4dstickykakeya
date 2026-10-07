#!/usr/bin/env python3
"""Compile four disjoint prerequisite modules when their canonical imports exist.

No second Lake graph is started. Outputs live in the staging import path,
and none of these four sources is targeted by the active critical graph.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

repo = Path('/workspace/scratch/5f2524fd4117/4dstickykakeya')
work = Path('/workspace/shared/sticky-recovery-20261005')
outroot = work / 'olean'
outroot.mkdir(exist_ok=True)
toolchain = '/workspace/scratch/5f2524fd4117/lean-tools/lean-4.33.1-linux/bin'
modules = ['native_coarse_ancestor_counts', 'native_dense_retained_unit_parent',
           'native_padded_source_ad_lower', 'native_local_parent_cells']
modules = ['Theorems.Thm_StickyKakeya4_' + m for m in modules]
critical = json.loads((work / 'critical-source-manifest.json').read_text())['sources']
assert not set(modules).intersection(critical)
parser = argparse.ArgumentParser()
parser.add_argument('--attempt', type=int, default=2)
options = parser.parse_args()
directory = work / f'verification/staging-prerequisites-attempt{options.attempt:02d}'
directory.mkdir(exist_ok=False)
env = os.environ.copy()
env['PATH'] = toolchain + ':' + env.get('PATH', '')
env['LEAN_NUM_THREADS'] = '1'
base = subprocess.check_output([toolchain + '/lake', 'env', 'printenv', 'LEAN_PATH'],
                              cwd=repo, env=env, text=True).strip()
env['LEAN_PATH'] = str(outroot) + ':' + base
state = {m: {'state': 'waiting'} for m in modules}
def record():
    (directory / 'status.json').write_text(json.dumps(state, indent=2) + '\n')
def ready(source):
    for m in re.findall(r'^import\s+(\S+)', source.read_text(), re.M):
        if m.startswith(('Theorems.', 'Definitions.', 'Solutions.')):
            rel = Path(*m.split('.')).with_suffix('.olean')
            if not (outroot / rel).exists() and not (repo / '.lake/build/lib/lean' / rel).exists():
                return False
    return True
def refresh_overlay():
    target = outroot / 'Theorems'
    target.mkdir(exist_ok=True)
    for artifact in (repo / '.lake/build/lib/lean/Theorems').glob('*.olean*'):
        try:
            (target / artifact.name).symlink_to(artifact)
        except FileExistsError:
            pass
record()
remaining = list(modules)
while remaining:
    progressed = False
    for module in remaining[:]:
        rel = Path(*module.split('.'))
        source = repo / rel.with_suffix('.lean')
        if not ready(source):
            continue
        sha = hashlib.sha256(source.read_bytes()).hexdigest()
        output = outroot / rel.with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        refresh_overlay()
        command = ['python3', str(repo / 'scripts/lean-slot.py'), '--slots', '2',
                   '--lock-dir', str(repo / '.lake/global-lean-locks'), '--', toolchain + '/lean',
                   '-j1', '-DautoImplicit=false', '-DwarningAsError=true', '-R', str(repo),
                   '-o', str(output), str(source)]
        state[module] = {'state': 'running', 'source_sha256': sha, 'command': command,
                         'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
        record()
        with (directory / (rel.name + '.log')).open('w') as log:
            log.write('COMMAND ' + json.dumps(command) + '\nSOURCE_SHA256 ' + sha + '\n')
            log.flush()
            r = subprocess.run(command, cwd=repo, env=env, stdout=log,
                               stderr=subprocess.STDOUT, check=False)
            log.write('\nEXIT_CODE=' + str(r.returncode) + '\n')
        unchanged = hashlib.sha256(source.read_bytes()).hexdigest() == sha
        passed = r.returncode == 0 and unchanged
        state[module].update(state='passed' if passed else 'failed', exit_code=r.returncode,
                             source_unchanged=unchanged,
                             finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
        record()
        print(module, state[module]['state'], flush=True)
        if not passed:
            raise SystemExit(1)
        remaining.remove(module)
        progressed = True
    if remaining and not progressed:
        critical_status = json.loads((work / 'critical-targets-status.json').read_text())
        if critical_status['state'] == 'failed':
            raise SystemExit('Critical graph failed before prerequisites became available')
        time.sleep(5)
print('All four staging prerequisites passed fresh strict compilation', flush=True)
