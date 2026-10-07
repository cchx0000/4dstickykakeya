from pathlib import Path
import datetime,json,subprocess,time,sys
w=Path('/workspace/shared/sticky-recovery-20261006');o=w/'runtime-20261006T1519';status=o/'CONTINUATION_STATUS.json';first=w/'dependency-slice-20261006T152206-pool/status.json'
def save(state,**kw):
 p=status.with_suffix('.tmp');p.write_text(json.dumps({'state':state,'updated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),**kw},indent=2)+'\n');p.replace(status)
save('waiting_for_isolated_first_prerequisites',first_status=str(first))
while True:
 d=json.loads(first.read_text())
 if d['state']=='passed':break
 if d['state']=='failed':save('blocked_on_failed_prerequisite',first_status=str(first));sys.exit(1)
 time.sleep(5)
xs=['Theorems.Thm_StickyKakeya4_native_window_quotient_transport','Theorems.Thm_StickyKakeya4_native_half_scale_interpolation',*json.loads((w/'next-native-coherence-targets.json').read_text())]
front=['Theorems.Thm_StickyKakeya4_native_planar_lemma53','Theorems.Thm_StickyKakeya4_native_paid_third_record_readback','Theorems.Thm_StickyKakeya4_native_window_coefficient_comparison','Theorems.Thm_StickyKakeya4_original_tube_slice_occupancy'];targets=front+[x for x in xs if x not in front];assert set(targets)==set(xs)
save('running_isolated_remaining_targets',targets=targets)
r=subprocess.run(['python3',str(w/'run_dependency_pool_1519.py'),*targets]);save('passed' if r.returncode==0 else 'failed',exit_code=r.returncode);sys.exit(r.returncode)
