#!/usr/bin/env python3
"""Strict source and imported-axiom checks, sharing the canonical build cap."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
from staging_overlay import prepare_overlay

p = argparse.ArgumentParser()
p.add_argument('--source', type=Path, required=True)
p.add_argument('--namespace', required=True)
p.add_argument('--attempt', type=int, required=True)
p.add_argument('--source-root', type=Path, help='Isolated source root for reconciled recovery')
p.add_argument('--artifact-root', type=Path, help='Isolated artifact root for reconciled recovery')
p.add_argument('--source-only', action='store_true', help='Defer independent axiom audit to an explicit batch')
args = p.parse_args()
repo = Path('/workspace/scratch/5f2524fd4117/4dstickykakeya')
work = Path('/workspace/shared/sticky-recovery-20261005')
source = args.source.resolve()
root = args.source_root.resolve() if args.source_root else work / 'live'
root.relative_to(work)
artifact_root = args.artifact_root.resolve() if args.artifact_root else work / 'olean'
artifact_root.relative_to(work)
relative = source.relative_to(root)
module = '.'.join(relative.with_suffix('').parts)
output = artifact_root / relative.with_suffix('.olean')
output.parent.mkdir(parents=True, exist_ok=True)
stem = source.stem.removeprefix('Thm_StickyKakeya4_')
directory = work / 'verification' / f'{stem}-attempt{args.attempt:02d}'
directory.mkdir(parents=True, exist_ok=False)
source_bytes = source.read_bytes()
text = source_bytes.decode()
source_hash = hashlib.sha256(source_bytes).hexdigest()
(directory / "SourceSnapshot.lean").write_bytes(source_bytes)
names = [args.namespace + '.' + m for m in re.findall(
    r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:theorem|lemma|def)\s+([A-Za-z0-9_]+)', text, re.M)]
if not names:
    raise SystemExit('No declared public names found; supply an explicit audit instead')
readback = root / f'{stem}_readback.lean'
readback.write_text('import ' + module + '\nset_option autoImplicit false\n'
                    + '\n'.join('#print axioms ' + n for n in names) + '\n')
toolchain = '/workspace/scratch/5f2524fd4117/lean-tools/lean-4.33.1-linux/bin'
env = os.environ.copy()
env['PATH'] = toolchain + ':' + env.get('PATH', '')
env['LEAN_NUM_THREADS'] = '1'
lean_path = subprocess.check_output([toolchain + '/lake', 'env', 'printenv', 'LEAN_PATH'],
                                    cwd=repo, env=env, text=True).strip()
registry = work / 'extra-olean-roots.json'
extra_roots = json.loads(registry.read_text()) if registry.exists() else []
for extra_root in extra_roots:
    Path(extra_root).resolve().relative_to(work)
own_roots = [str(artifact_root)] if artifact_root != work / 'olean' else []
for overlay_root in [*own_roots, *extra_roots]:
    prepare_overlay(work, Path(overlay_root), module if Path(overlay_root)==artifact_root else None, module, artifact_root)
env['LEAN_PATH'] = ':'.join(dict.fromkeys([*own_roots, *extra_roots, str(work / 'olean')])) + ':' + lean_path
for artifact in (repo / '.lake/build/lib/lean/Theorems').glob('*.olean*'):
    destination = work / 'olean/Theorems' / artifact.name
    try:
        destination.symlink_to(artifact)
    except FileExistsError:
        pass
for overlay_root in [*own_roots, *extra_roots]:
    prepare_overlay(work, Path(overlay_root), module if Path(overlay_root)==artifact_root else None, module, artifact_root)
output_locks = work / 'staging-output-locks'
output_locks.mkdir(exist_ok=True)
output_lock = output_locks / (hashlib.sha256(str(output).encode()).hexdigest() + '.lock')
prefix = ['flock', str(output_lock), 'python3', str(work / 'staging_slot_pool.py'),
          '--repo', str(repo), '--', toolchain + '/lean', '-j1',
          '-DautoImplicit=false', '-DwarningAsError=true', '-R', str(root)]
state = {'module': module, 'source': str(source), 'source_sha256': source_hash,
         'source_root': str(root), 'olean_root': str(artifact_root), 'olean_path': str(output),
         'names': names, 'state': 'running',
         'executor_started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}

def write_state():
    (directory / 'result.json').write_text(json.dumps(state, indent=2) + '\n')

def run(command, name):
    with (directory / name).open('w') as out:
        out.write('COMMAND ' + json.dumps(command) + '\nSOURCE_SHA256 ' + source_hash + '\n')
        out.flush()
        r = subprocess.run(command, cwd=repo, env=env, stdout=out,
                           stderr=subprocess.STDOUT, check=False)
        out.write('\nEXIT_CODE=' + str(r.returncode) + '\n')
    return r.returncode

write_state()
state['source_exit_code'] = run(prefix + ['-o', str(output), str(source)], 'source.log')
if args.source_only and state['source_exit_code'] == 0:
    unchanged = hashlib.sha256(source.read_bytes()).hexdigest() == source_hash
    state['source_unchanged'] = unchanged
    state['olean_sha256'] = hashlib.sha256(output.read_bytes()).hexdigest()
    state['state'] = 'source_passed' if unchanged else 'failed'
    state['source_execution_complete_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    state['independent_axiom_audit_pending'] = True
    write_state()
    print(json.dumps(state, indent=2), flush=True)
    raise SystemExit(0 if unchanged else 1)
if state['source_exit_code'] == 0:
    state['readback_exit_code'] = run(prefix + [str(readback)], 'axioms.log')
    ax = (directory / 'axioms.log').read_text()
    axioms = {n: [v.strip() for v in raw.split(',') if v.strip()]
              for n, raw in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", ax, re.S)}
    axioms.update({n: [] for n in re.findall(r"'([^']+)' does not depend on any axioms", ax)})
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    state['missing_names'] = sorted(set(names) - set(axioms))
    state['extra_axioms'] = {n: sorted(set(a) - allowed) for n, a in axioms.items()
                             if set(a) - allowed}
    state['axioms'] = axioms
    state['olean_sha256'] = hashlib.sha256(output.read_bytes()).hexdigest()
unchanged = hashlib.sha256(source.read_bytes()).hexdigest() == source_hash
state['source_unchanged'] = unchanged
passed = (state['source_exit_code'] == 0 and state.get('readback_exit_code') == 0
          and not state.get('missing_names') and not state.get('extra_axioms') and unchanged)
state['state'] = 'passed' if passed else 'failed'
state['executor_finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
write_state()
print(json.dumps({k: v for k, v in state.items() if k != 'axioms'}, indent=2), flush=True)
raise SystemExit(0 if passed else 1)
