from pathlib import Path
import datetime,json,subprocess,sys,time
w=Path('/workspace/shared/sticky-recovery-20261006');status=w/'RESET1003_WINDOW_CONTINUATION.json'
def save(phase,**kw):
 t=status.with_suffix('.tmp');t.write_text(json.dumps({'phase':phase,'updated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),**kw},indent=2)+'\n');t.replace(status)
save('waiting_for_first_targeted_union')
while True:
 d=json.loads((w/'RESET1003_INTERFACE_RUN.json').read_text())
 if d['phase']=='first_prerequisite_union_passed':break
 if 'failure' in d['phase'] or 'blocked' in d['phase']:save('blocked',prior=d);sys.exit(1)
 time.sleep(5)
targets=['Theorems.Thm_StickyKakeya4_native_window_quotient_transport',
 'Theorems.Thm_StickyKakeya4_native_half_scale_interpolation',
 *json.loads((w/'next-native-coherence-targets.json').read_text())]
save('running_window_and_consumer_prerequisites',targets=targets)
q=subprocess.run([sys.executable,str(w/'run_dependency_pool.py'),*targets])
save('passed' if q.returncode==0 else 'failed',exit_code=q.returncode)
raise SystemExit(q.returncode)
