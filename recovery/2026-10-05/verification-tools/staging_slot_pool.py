#!/usr/bin/env python3
"""Future strict staging jobs: at most two single-thread compilers, in slots 2/3.
The original slot-3 outer lock and all existing queued commands are unchanged.
Slot 1 remains available for independent immutable import closure checks.
"""
import argparse,datetime,fcntl,os,pathlib,time
p=argparse.ArgumentParser();p.add_argument('--repo',required=True);p.add_argument('command',nargs=argparse.REMAINDER);a=p.parse_args();cmd=a.command[1:] if a.command[:1]==['--'] else a.command
if not cmd:p.error('command required')
repo=pathlib.Path(a.repo);locks=repo/'.lake/global-lean-locks';locks.mkdir(parents=True,exist_ok=True)
def available_kb():
    for line in pathlib.Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):return int(line.split()[1])
    return 0
while True:
    for slot in [2,3]:
        if available_kb()<3*1024*1024:continue
        outer=repo/'.lake'/('staging-lean-second.lock' if slot==2 else 'staging-lean.lock')
        fds=[]
        try:
            for lock in [outer,locks/(str(slot)+'.lock')]:
                fd=os.open(lock,os.O_CREAT|os.O_WRONLY,0o600);fds.append(fd)
                fcntl.flock(fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError:
            for fd in reversed(fds):os.close(fd)
            continue
        for fd in fds:os.set_inheritable(fd,True)
        print('Staging pool slot '+str(slot)+' acquired UTC: '+datetime.datetime.now(datetime.timezone.utc).isoformat(),flush=True)
        print('Memory at admission: '+'; '.join(x for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith(('MemTotal:','MemAvailable:'))),flush=True)
        os.execvp(cmd[0],cmd)
    time.sleep(0.2)
