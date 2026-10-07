from pathlib import Path
import datetime,json,hashlib,subprocess,sys,time
w=Path('/workspace/shared/sticky-recovery-20261006');status=w/'output-admission-continuation-status.json'
inputs=['native_variable_retention_coarse_selection-attempt01','native_effective_output_threshold-attempt03']
def save(state,**kw):status.write_text(json.dumps({'state':state,'updated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),**kw},indent=2)+'\n')
save('waiting_for_verified_core_imports',inputs=inputs)
while True:
 ready=True
 for a in inputs:
  p=w/'verification'/a/'result.json'
  if not p.exists():ready=False;continue
  d=json.loads(p.read_text())
  if d['state']=='failed':save('blocked_by_core_failure',failed=a);sys.exit(1)
  if d['state']!='passed':ready=False;continue
  assert hashlib.sha256(Path(d['source']).read_bytes()).hexdigest()==d['source_sha256']
  assert hashlib.sha256(Path(d['olean_path']).read_bytes()).hexdigest()==d['olean_sha256']
 if ready:break
 time.sleep(5)
save('strict_attempt_started')
a=subprocess.run([sys.executable,str(w/'verify_recovered_source.py'),'--source',str(w/'live/Theorems/Thm_StickyKakeya4_native_output_scale_coarse_admission.lean'),'--namespace','NativeOutputScaleCoarseAdmission','--attempt','1','--slot','2'])
save('passed' if a.returncode==0 else 'failed',exit_code=a.returncode)
