from pathlib import Path
import json,hashlib,time,subprocess,sys,datetime
w=Path('/workspace/shared/sticky-recovery-20261006');r=Path('/workspace/scratch/5f2524fd4117/4dstickykakeya');target='Theorems.Thm_StickyKakeya4_native_reference_XY_grid_linear';state=w/'packed-frame-continuation-status.json';pool=w/'dependency-slice-20261006T104804-pool/status.json'
def save(s,**kw):state.write_text(json.dumps({'state':s,'updated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),**kw},indent=2)+'\n')
save('waiting_for_exact_dependency',target=target)
while True:
 d=json.loads(pool.read_text());md=next((x for x in d['modules'] if x['module']==target and x.get('exit_code')==0),None)
 if md:
  p=r/(target.replace('.','/')+'.lean');q=r/'.lake/build/lib/lean'/(target.replace('.','/')+'.olean')
  if hashlib.sha256(p.read_bytes()).hexdigest()==md['source_sha256'] and hashlib.sha256(q.read_bytes()).hexdigest()==md['olean_sha256']:break
 if d['state']=='failed':save('blocked_by_dependency_failure');sys.exit(1)
 time.sleep(2)
save('strict_attempt_started',target=target)
a=subprocess.run([sys.executable,str(w/'verify_recovered_source.py'),'--source',str(w/'live/Theorems/Thm_StickyKakeya4_native_packed_frame_isometry.lean'),'--namespace','NativePackedFrameIsometry','--attempt','1','--slot','2'])
save('passed' if a.returncode==0 else 'failed',exit_code=a.returncode)
