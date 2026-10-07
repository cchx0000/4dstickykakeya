from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys,time
w=Path('/workspace/shared/sticky-recovery-20261006')
r=Path('/workspace/scratch/5f2524fd4117/4dstickykakeya')
d=Path('/workspace/shared/lean-dependency-warmup-20261006-reset1003')
base=Path('/workspace/scratch/5f2524fd4117/selected-recovery-20261006T1022')
cache=base/'cache-extracted/project-cache-20261006T0945'
state=w/'RESET1003_DEPENDENCY_STATUS.json'
def save(phase,**kw):
 x={'phase':phase,'updated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),**kw}
 t=state.with_suffix('.tmp');t.write_text(json.dumps(x,indent=2)+'\n');t.replace(state)
save('waiting_for_official_cache')
while True:
 x=json.loads((d/'status.json').read_text())
 if x['state']=='passed':break
 if x['state']=='failed':save('blocked_by_dependency_setup',result=x);sys.exit(1)
 time.sleep(5)
pins=[]
for pkg in json.loads((r/'lake-manifest.json').read_text())['packages']:
 if pkg['type']!='git':raise RuntimeError('Unexpected non-git dependency')
 actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r/'.lake/packages'/pkg['name'],text=True).strip()
 assert actual==pkg['rev'],(pkg['name'],actual,pkg['rev'])
 pins.append({'name':pkg['name'],'commit':actual})
(w/'RESET1003_DEPENDENCY_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
env=os.environ.copy();tool=Path('/workspace/scratch/5f2524fd4117/lean-tools/lean-4.33.1-linux/bin')
env['PATH']=str(tool)+':'+env.get('PATH','')
env.update(STICKY_LEAN_BINARY=str(tool/'lean'),STICKY_BUILD_JOBS='2',STICKY_LEAN_THREADS='1',
 STICKY_GLOBAL_LOCK_DIR='/workspace/shared/sticky-recovery-20261006-reset1003/global-lean-locks',
 MATHLIB_CACHE_DIR='/workspace/shared/sticky-recovery-20261006-reset1003/mathlib-cache')
save('building_only_required_external_bsg',dependency_pins_verified=True)
with (w/'RESET1003_BSG_DEPENDENCY.log').open('w') as log:
 q=subprocess.run(['bash','scripts/lake-bounded.sh','build',
   '+LeanFormalizations.Combinatorics.Additive.BalogSzemerediGowers:olean'],cwd=d,env=env,stdout=log,stderr=subprocess.STDOUT)
if q.returncode:save('external_bsg_failed',exit_code=q.returncode);sys.exit(q.returncode)
save('preparing_restored_lake_environment')
with (w/'RESET1003_LAKE_ENV.log').open('w') as log:
 q=subprocess.run(['bash',str(d/'scripts/lake-bounded.sh'),'--dir',str(r),'env','python3','-c',
  'import os,pathlib;print("FINAL_LEAN_PATH="+":".join(str(pathlib.Path(p).resolve()) for p in os.environ["LEAN_PATH"].split(":")))'],cwd=d,env=env,stdout=log,stderr=subprocess.STDOUT)
if q.returncode:save('restored_lake_environment_failed',exit_code=q.returncode);sys.exit(q.returncode)
save('independent_cache_only_import',artifact_count=453)
q=subprocess.run([sys.executable,str(w/'check_project_cache.py'),str(cache),'20261006T1003-restored'],env=env)
if q.returncode:save('cache_import_failed',exit_code=q.returncode);sys.exit(q.returncode)
record={'state':'passed','artifact_count':453,'cache_directory':str(cache),
 'cache_import_receipt':str(w/'cache-import-check-20261006T1003-restored/status.json'),
 'source_compilation_scope':'cache reuse is not fresh source compilation',
 'dependency_pins_verified':pins,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
(w/'CACHE_READY_RESET1003.json').write_text(json.dumps(record,indent=2)+'\n')
save('passed',**record)
