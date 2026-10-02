#!/usr/bin/env python3
"""Build project modules dependency-first to bound concurrent Lean processes.

Run with no arguments for every project module, or give one/more module names.
Dependencies outside this repository are delegated to Lake. Failures block only
transitive dependents; unrelated modules continue. JSON records exact outcomes.
"""
from __future__ import annotations
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LOGS = ROOT / 'verification' / 'build-logs'
LOGS.mkdir(parents=True, exist_ok=True)
modules = {
    str(p.relative_to(ROOT).with_suffix('')).replace('/', '.'): p
    for directory in ('Definitions', 'Theorems', 'Solutions')
    for p in (ROOT / directory).glob('*.lean')
}
deps = {
    name: [imp for imp in re.findall(r'^import\s+(\S+)', path.read_text(), re.M)
           if imp in modules]
    for name, path in modules.items()
}
selected = sys.argv[1:] or list(modules)
unknown = set(selected) - modules.keys()
if unknown:
    sys.exit('Unknown project modules: ' + ', '.join(sorted(unknown)))
order: list[str] = []
visited: set[str] = set()
visiting: set[str] = set()
def visit(name: str) -> None:
    if name in visited:
        return
    if name in visiting:
        raise RuntimeError('Import cycle at ' + name)
    visiting.add(name)
    for dep in deps[name]:
        visit(dep)
    visiting.remove(name)
    visited.add(name)
    order.append(name)
for name in selected:
    visit(name)
status: dict[str, dict] = {}
for index, name in enumerate(order, 1):
    blocked = [dep for dep in deps[name] if status[dep]['status'] != 'passed']
    if blocked:
        status[name] = {'status': 'blocked', 'dependencies': blocked}
        print(f'[{index}/{len(order)}] BLOCKED {name}: {", ".join(blocked)}', flush=True)
    else:
        result = subprocess.run(['lake', 'build', name], cwd=ROOT,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True)
        logfile = LOGS / (name + '.log')
        logfile.write_text(result.stdout)
        label = 'passed' if result.returncode == 0 else 'failed'
        status[name] = {'status': label, 'exit_code': result.returncode,
                        'log': str(logfile.relative_to(ROOT))}
        print(f'[{index}/{len(order)}] {label.upper()} {name}', flush=True)
        if result.returncode:
            print(result.stdout[-12000:], flush=True)
    (LOGS / 'status.json').write_text(json.dumps(status, indent=2) + '\n')
sys.exit(1 if any(s['status'] != 'passed' for s in status.values()) else 0)
