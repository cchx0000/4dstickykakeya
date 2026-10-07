from pathlib import Path
import datetime,json,re,subprocess,sys,time
w=Path('/workspace/shared/sticky-recovery-20261006');r=Path('/workspace/scratch/5f2524fd4117/4dstickykakeya')
state=w/'RESET1003_INTERFACE_RUN.json'
def save(phase,**kw):
 t=state.with_suffix('.tmp');t.write_text(json.dumps({'phase':phase,'updated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),**kw},indent=2)+'\n');t.replace(state)
save('waiting_for_validated_cache')
while not (w/'CACHE_READY_RESET1003.json').exists():
 p=w/'RESET1003_DEPENDENCY_STATUS.json'
 if p.exists():
  d=json.loads(p.read_text())
  if 'failed' in d.get('phase','') or 'blocked' in d.get('phase',''):save('blocked_by_dependency_validation',dependency=d);sys.exit(1)
 time.sleep(5)
old=sorted((r/'recovery/2026-10-06').glob('DEPENDENCY_PROGRESS_*.json'))[-1]
oldtargets=json.loads(old.read_text())['targets']
def closure(roots):
 seen=set()
 def walk(m):
  if m in seen:return
  seen.add(m);p=r/(m.replace('.','/')+'.lean')
  for q in re.findall(r'^import ((?:Theorems|Definitions|Solutions)\.[A-Za-z0-9_.]+)',p.read_text(),re.M):walk(q)
 for m in roots:walk(m)
 return seen
priority='Theorems.Thm_StickyKakeya4_native_reference_XY_grid_linear'
original=closure(oldtargets);assert priority in original
targets=[priority,*[x for x in oldtargets if x!=priority]]
assert closure(targets)==original
save('running_same_prerequisite_union',targets=targets,total_modules=len(original),priority='exact frame/point prerequisite first; same closure as interrupted attempt')
q=subprocess.run([sys.executable,str(w/'run_dependency_pool.py'),*targets])
if q.returncode:save('targeted_dependency_failure',exit_code=q.returncode);sys.exit(q.returncode)
save('first_prerequisite_union_passed',total_modules=len(original))
