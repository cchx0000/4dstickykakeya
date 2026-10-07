from pathlib import Path
import json,time,subprocess,datetime
w=Path('/workspace/shared/sticky-recovery-20261006'); first=w/'dependency-slice-20261006T202254-pool/status.json'; out=w/'higher-grid-continuation-2042.json'
def save(state,**kw):
 out.write_text(json.dumps({'state':state,'updated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),**kw},indent=2)+'\n')
save('waiting_for_existing_four_target_slice',first=str(first))
while True:
 d=json.loads(first.read_text())
 if d['state']=='passed':break
 if d['state']=='failed':save('blocked_on_existing_slice',first=str(first));raise SystemExit(1)
 time.sleep(5)
save('running_single_missing_higher_grid_prerequisite')
p=subprocess.run(['python3',str(w/'run_dependency_pool_single_20261006T2021.py'),'Theorems.Thm_StickyKakeya4_original_representative_grid_comparison'])
save('passed' if p.returncode==0 else 'failed',exit_code=p.returncode);raise SystemExit(p.returncode)
