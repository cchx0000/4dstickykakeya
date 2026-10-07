"""Future strict attempts: report actual lock acquisition before invoking Lean."""
import sys,fcntl,subprocess,datetime,json,os
from pathlib import Path
outlock,slotlock,*cmd=sys.argv[1:]
with open(outlock,'a') as a, open(slotlock,'a') as b:
 fcntl.flock(a,fcntl.LOCK_EX);fcntl.flock(b,fcntl.LOCK_EX)
 print('LOCK_ACQUIRED_UTC '+datetime.datetime.now(datetime.timezone.utc).isoformat(),flush=True)
 print('SHARED_SLOT '+Path(slotlock).stem,flush=True)
 p=subprocess.Popen(cmd)
 print('LEAN_PID '+str(p.pid),flush=True)
 code=p.wait()
 print('LEAN_FINISHED_UTC '+datetime.datetime.now(datetime.timezone.utc).isoformat()+' EXIT_CODE='+str(code),flush=True)
 sys.exit(code)
