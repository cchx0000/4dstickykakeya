#!/usr/bin/env python3
"""Dedicated third compiler slot for future strict staging jobs only.
Canonical frozen builds continue to use their unchanged slots one and two.
The outer staging flock still allows only one staging compiler in total.
"""
import argparse,datetime,fcntl,os,pathlib
p=argparse.ArgumentParser();p.add_argument('--lock-file',required=True);p.add_argument('command',nargs=argparse.REMAINDER);a=p.parse_args();cmd=a.command[1:] if a.command[:1]==['--'] else a.command
if not cmd:p.error('command required')
lock=pathlib.Path(a.lock_file);lock.parent.mkdir(parents=True,exist_ok=True)
fd=os.open(lock,os.O_CREAT|os.O_WRONLY,0o600);fcntl.flock(fd,fcntl.LOCK_EX);os.set_inheritable(fd,True)
print('Dedicated staging slot 3 acquired UTC: '+datetime.datetime.now(datetime.timezone.utc).isoformat(),flush=True)
print('Memory at admission: '+'; '.join(x for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith(('MemTotal:','MemAvailable:'))),flush=True)
os.execvp(cmd[0],cmd)
