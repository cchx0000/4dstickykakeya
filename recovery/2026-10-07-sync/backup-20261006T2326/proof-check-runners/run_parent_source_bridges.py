from pathlib import Path
import datetime,hashlib,json,subprocess,sys,time
w=Path('/workspace/shared/sticky-recovery-20261006')
jobs=[
 {'dependency':'native_retention_output_power-attempt02','source':'native_source_output_window','namespace':'NativeSourceOutputWindow','slot':'2'},
 {'dependency':'native_truncated_retention_coarse_selection-attempt01','source':'native_truncated_output_scale_admission','namespace':'NativeTruncatedOutputScaleAdmission','slot':'3'}]
pending=list(jobs);active={};results=[]
def save():
 p=w/'parent-source-bridges-status.json'
 p.write_text(json.dumps({'updated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
   'pending':pending,'active':list(active),'results':results},indent=2)+'\n')
while pending or active:
 for j in list(pending):
  p=w/'verification'/j['dependency']/'result.json'
  if not p.exists():continue
  d=json.loads(p.read_text())
  if d['state']=='failed':
   results.append({'source':j['source'],'state':'blocked_by_dependency_failure','dependency':j['dependency']});pending.remove(j);continue
  if d['state']!='passed':continue
  assert hashlib.sha256(Path(d['source']).read_bytes()).hexdigest()==d['source_sha256']
  assert hashlib.sha256(Path(d['olean_path']).read_bytes()).hexdigest()==d['olean_sha256']
  p=subprocess.Popen([sys.executable,str(w/'verify_recovered_source.py'),'--source',
    str(w/'live/Theorems'/('Thm_StickyKakeya4_'+j['source']+'.lean')),
    '--namespace',j['namespace'],'--attempt','1','--slot',j['slot']])
  active[j['source']]=p;pending.remove(j)
 for s,p in list(active.items()):
  if p.poll() is not None:
   results.append({'source':s,'state':'passed' if p.returncode==0 else 'failed','exit_code':p.returncode});del active[s]
 save()
 if pending or active:time.sleep(5)
print(json.dumps(results))
