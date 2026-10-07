"""Build only explicit project prerequisite closures after official cache restore."""
import datetime,hashlib,json,os,pathlib,re,subprocess,sys
repo=pathlib.Path('/workspace/scratch/5f2524fd4117/4dstickykakeya')
work=pathlib.Path('/workspace/shared/sticky-recovery-20261006')
tool=pathlib.Path('/workspace/scratch/5f2524fd4117/lean-tools/lean-4.33.1-linux/bin')
targets=sys.argv[1:]
order=[];seen=set()
def walk(module):
    if module in seen:return
    source=repo/pathlib.Path(*module.split('.')).with_suffix('.lean')
    if not source.exists():raise RuntimeError('Missing prerequisite '+module)
    seen.add(module)
    for dep in re.findall(r'^import ((?:Theorems|Definitions|Solutions)\.[A-Za-z0-9_.]+)',source.read_text(),re.M):walk(dep)
    order.append((module,source))
for target in targets:walk(target)
run=work/('dependency-slice-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S'));run.mkdir()
env=os.environ.copy();env['PATH']=str(tool)+':'+env.get('PATH','');env['LEAN_NUM_THREADS']='1';env['MATHLIB_CACHE_DIR']=str(work/'mathlib-cache')
leanpath=subprocess.check_output([str(tool/'lake'),'env','printenv','LEAN_PATH'],cwd=repo,env=env,text=True).strip();env['LEAN_PATH']=leanpath
locks=work/'global-lean-locks';locks.mkdir(exist_ok=True)
out=repo/'.lake/build/lib/lean'
known={}
for prior in sorted(work.glob('dependency-slice-*/status.json')):
 try:d=json.loads(prior.read_text())
 except (OSError,ValueError):continue
 for entry in d.get('modules',[]):
  if entry.get('exit_code')==0 and entry.get('source_unchanged'):known[entry['module']]=entry
manifest={'state':'running','scope':'explicit prerequisite closure, not a full project build','targets':targets,'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'modules':[]}
state=run/'status.json'
state.write_text(json.dumps(manifest,indent=2)+'\n')
for module,source in order:
    sh=hashlib.sha256(source.read_bytes()).hexdigest();dest=out/pathlib.Path(*module.split('.')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
    prior=known.get(module)
    if prior and prior['source_sha256']==sh and dest.exists() and hashlib.sha256(dest.read_bytes()).hexdigest()==prior.get('olean_sha256'):
        entry=dict(prior);entry['reused_fresh_source_check']=prior.get('log');manifest['modules'].append(entry);state.write_text(json.dumps(manifest,indent=2)+'\n');print(module,'reused fresh hash-verified artifact',flush=True);continue
    command=['flock',str(locks/'1.lock'),str(tool/'lean'),'-j1','-DautoImplicit=false','-R',str(repo),'-o',str(dest),str(source)]
    logpath=run/(module+'.log')
    with logpath.open('w') as log:
        log.write('COMMAND '+json.dumps(command)+'\nSOURCE_SHA256 '+sh+'\n');log.flush()
        result=subprocess.run(command,cwd=repo,env=env,stdout=log,stderr=subprocess.STDOUT);log.write('\nEXIT_CODE='+str(result.returncode)+'\n')
    unchanged=sh==hashlib.sha256(source.read_bytes()).hexdigest()
    entry={'module':module,'source_sha256':sh,'source_unchanged':unchanged,'exit_code':result.returncode,'log':str(logpath)}
    if result.returncode==0:entry['olean_sha256']=hashlib.sha256(dest.read_bytes()).hexdigest()
    manifest['modules'].append(entry);state.write_text(json.dumps(manifest,indent=2)+'\n');print(module,result.returncode,flush=True)
    if result.returncode or not unchanged:
        manifest['state']='failed';state.write_text(json.dumps(manifest,indent=2)+'\n');raise SystemExit(1)
manifest['state']='passed';manifest['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();state.write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({'status':str(state),'count':len(order),'state':'passed'}))
