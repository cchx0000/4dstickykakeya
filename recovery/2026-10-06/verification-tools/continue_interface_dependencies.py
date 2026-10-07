"""Continue disjoint prerequisite batches only after the current DAG reaches success."""
from pathlib import Path
import json,subprocess,time,datetime,sys
w=Path('/workspace/shared/sticky-recovery-20261006');current=w/'dependency-slice-20261006T070030-pool/status.json';state=w/'interface-continuation-status.json';log=w/'interface-continuation.log'
def save(phase,**kw):state.write_text(json.dumps({'phase':phase,'updated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),**kw},indent=2)+'\n')
save('waiting_for_current_dag',current_status=str(current))
while True:
 try:d=json.loads(current.read_text())
 except (OSError,ValueError):time.sleep(2);continue
 if d['state']=='passed':break
 if d['state']=='failed':save('blocked_by_failed_current_dag',current_status=str(current));sys.exit(1)
 time.sleep(2)
batches=[('window_three_modules',['Theorems.Thm_StickyKakeya4_native_window_quotient_transport','Theorems.Thm_StickyKakeya4_native_half_scale_interpolation']),('native_reference_coherence',json.loads((w/'next-native-coherence-targets.json').read_text())+['Theorems.Thm_StickyKakeya4_native_post_graph_XY_hook_data'])]
for name,roots in batches:
 save(name,targets=roots)
 with log.open('a') as f:
  f.write('\nSTART '+name+' '+datetime.datetime.now(datetime.timezone.utc).isoformat()+'\n');f.flush();q=subprocess.run([sys.executable,str(w/'run_dependency_pool.py'),*roots],stdout=f,stderr=subprocess.STDOUT)
 if q.returncode:save('failed',batch=name,exit_code=q.returncode);sys.exit(q.returncode)
save('passed_all_requested_interfaces')
