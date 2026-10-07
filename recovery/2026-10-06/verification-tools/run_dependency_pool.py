"""Exact dependency DAG, fresh hash reuse, one-thread Lean, shared three-slot bound."""
import concurrent.futures as cf,datetime,fcntl,hashlib,json,os,pathlib,re,subprocess,sys,threading,time
repo=pathlib.Path('/workspace/scratch/5f2524fd4117/4dstickykakeya');work=pathlib.Path('/workspace/shared/sticky-recovery-20261006');tool=pathlib.Path('/workspace/scratch/5f2524fd4117/lean-tools/lean-4.33.1-linux/bin');targets=sys.argv[1:];sources={};deps={};order=[]
def walk(m):
 if m in sources:return
 s=repo/pathlib.Path(*m.split('.')).with_suffix('.lean')
 if not s.exists():raise RuntimeError('Missing prerequisite '+m)
 sources[m]=s;deps[m]=re.findall(r'^import ((?:Theorems|Definitions|Solutions)\.[A-Za-z0-9_.]+)',s.read_text(),re.M)
 for d in deps[m]:walk(d)
 order.append(m)
for t in targets:walk(t)
run=work/('dependency-slice-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S')+'-pool');run.mkdir();locks=work/'global-lean-locks';locks.mkdir(exist_ok=True);out=repo/'.lake/build/lib/lean';env=os.environ.copy();env['PATH']=str(tool)+':'+env.get('PATH','');env['LEAN_NUM_THREADS']='1';env['MATHLIB_CACHE_DIR']=str(work/'mathlib-cache');env['LEAN_PATH']=subprocess.check_output([str(tool/'lake'),'env','printenv','LEAN_PATH'],cwd=repo,env=env,text=True).strip()
known={}
for p in sorted(work.glob('dependency-slice-*/status.json')):
 try:d=json.loads(p.read_text())
 except (OSError,ValueError):continue
 for e in d.get('modules',[]):
  if e.get('exit_code')==0 and e.get('source_unchanged'):known[e['module']]=e
completed={};pending=set(order);active={};stateLock=threading.Lock();manifest={'state':'running','scope':'explicit restored interface prerequisite DAG; not a full build','targets':targets,'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'total_modules':len(order),'lean_threads_per_process':1,'shared_max_lean_processes':3,'modules':[],'active':{}}
def save():
 with stateLock:
  manifest['modules']=[completed[m] for m in order if m in completed];manifest['completed']=len(completed);manifest['active']=dict(active)
  tmp=run/'status.json.tmp';tmp.write_text(json.dumps(manifest,indent=2)+'\n');tmp.replace(run/'status.json')
for m in order:
 s=sources[m];dest=out/pathlib.Path(*m.split('.')).with_suffix('.olean');sh=hashlib.sha256(s.read_bytes()).hexdigest();old=known.get(m)
 if old and old['source_sha256']==sh and dest.exists() and hashlib.sha256(dest.read_bytes()).hexdigest()==old.get('olean_sha256') and all(d in completed for d in deps[m]):
  e=dict(old);e['reused_fresh_source_check']=old.get('log');completed[m]=e;pending.remove(m)
save();print(json.dumps({'status':str(run/'status.json'),'total':len(order),'reused':len(completed),'remaining':len(pending)}),flush=True)
def build(m):
 s=sources[m];sh=hashlib.sha256(s.read_bytes()).hexdigest();dest=out/pathlib.Path(*m.split('.')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);start=time.monotonic();handle=None;slot=None
 while handle is None:
  for k in (1,2,3):
   h=(locks/(str(k)+'.lock')).open('a')
   try:fcntl.flock(h.fileno(),fcntl.LOCK_EX|fcntl.LOCK_NB);handle=h;slot=k;break
   except BlockingIOError:h.close()
  if handle is None:time.sleep(.1)
 cmd=[str(tool/'lean'),'-j1','-DautoImplicit=false','-R',str(repo),'-o',str(dest),str(s)];lp=run/(m+'.log')
 try:
  with lp.open('w') as log:
   log.write('COMMAND '+json.dumps(cmd)+'\nSHARED_SLOT '+str(slot)+'\nSOURCE_SHA256 '+sh+'\n');log.flush();q=subprocess.run(cmd,cwd=repo,env=env,stdout=log,stderr=subprocess.STDOUT,pass_fds=(handle.fileno(),));log.write('\nEXIT_CODE='+str(q.returncode)+'\n')
 finally:fcntl.flock(handle.fileno(),fcntl.LOCK_UN);handle.close()
 e={'module':m,'source_sha256':sh,'source_unchanged':hashlib.sha256(s.read_bytes()).hexdigest()==sh,'exit_code':q.returncode,'log':str(lp),'elapsed_seconds':round(time.monotonic()-start,3),'shared_slot':slot}
 if q.returncode==0:e['olean_sha256']=hashlib.sha256(dest.read_bytes()).hexdigest()
 return e
failed=False
with cf.ThreadPoolExecutor(max_workers=3) as pool:
 jobs={}
 while pending or jobs:
  if not failed:
   for m in order:
    if len(jobs)>=3:break
    if m in pending and all(d in completed and completed[d]['exit_code']==0 for d in deps[m]):
     pending.remove(m);active[m]={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};jobs[pool.submit(build,m)]=m
  save()
  if not jobs:
   if pending and not failed:raise RuntimeError('Dependency scheduler blocked')
   break
  done,_=cf.wait(jobs,return_when=cf.FIRST_COMPLETED)
  for job in done:
   m=jobs.pop(job);e=job.result();completed[m]=e;active.pop(m,None);failed=failed or e['exit_code']!=0 or not e['source_unchanged'];print(m,e['exit_code'],e['elapsed_seconds'],flush=True)
  save()
manifest['state']='failed' if failed else 'passed';manifest['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();manifest['unbuilt']=sorted(pending);save();print(json.dumps({'state':manifest['state'],'completed':len(completed),'total':len(order),'status':str(run/'status.json')}),flush=True);raise SystemExit(1 if failed else 0)
