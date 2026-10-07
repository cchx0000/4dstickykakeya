"""Complete an isolated Lean namespace overlay without touching its own artifacts."""
import json
import fcntl
import os
import tempfile
from pathlib import Path

def prepare_overlay(work, root, own_module=None, output_module=None, output_root=None):
    work=Path(work);root=Path(root)
    if root==work/'olean':return
    root.resolve().relative_to(work.resolve());root.mkdir(parents=True,exist_ok=True)
    # Only overlay bookkeeping is serialized. Active Lean output is untouched.
    with (root/'.overlay-bookkeeping.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        return _prepare_overlay_locked(work,root,own_module,output_module,output_root)

def _prepare_overlay_locked(work, root, own_module=None, output_module=None, output_root=None):
    work=Path(work);root=Path(root);base=work/'olean'
    if root==base:return
    root.resolve().relative_to(work.resolve());root.mkdir(parents=True,exist_ok=True)
    ledger=root/'OWN_MODULES.json'
    owned=set(json.loads(ledger.read_text())) if ledger.exists() else set()
    if own_module:
        owned.add(own_module)
        # Atomic publication also protects readers started before this lock fix.
        with tempfile.NamedTemporaryFile(mode='w',dir=root,prefix='.owned-',suffix='.json',delete=False) as pending:
            pending.write(json.dumps(sorted(owned),indent=2)+'\n')
            pending.flush();os.fsync(pending.fileno());pending_path=Path(pending.name)
        os.replace(pending_path,ledger)
    def owner(rel):
        s=str(rel)
        for ext in ['.olean.server','.olean.private','.olean','.ilean','.ir']:
            if s.endswith(ext):return s[:-len(ext)].replace('/','.')
        return None
    def link(rel,src):
        if owner(rel) in owned:return
        dest=root/rel;dest.parent.mkdir(parents=True,exist_ok=True)
        try:dest.symlink_to(src)
        except FileExistsError:pass
    for src in base.rglob('*'):
        rel=src.relative_to(base)
        if owner(rel) is not None:link(rel,src)
    if output_module and output_root:
        rel=Path(*output_module.split('.'))
        for ext in ['.olean','.olean.server','.olean.private','.ilean','.ir']:
            file=rel.with_suffix(ext);link(file,Path(output_root)/file)
