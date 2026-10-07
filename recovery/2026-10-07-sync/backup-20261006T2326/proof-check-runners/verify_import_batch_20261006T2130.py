"""Independent imported axiom gate for frozen source-passed staging files.

Never converts source-only success into a completed receipt before the new
Lean process exits and every original declaration and hash is checked.
"""
import argparse,datetime,hashlib,json,os,pathlib,re,shutil,subprocess
p=argparse.ArgumentParser();p.add_argument('--stamp',required=True);p.add_argument('--slot',choices=['1','2','3'],default='2');p.add_argument('attempts',nargs='+');a=p.parse_args()
w=pathlib.Path('/workspace/shared/sticky-recovery-20261006');r=pathlib.Path('/workspace/scratch/5f2524fd4117/4dstickykakeya');tool=pathlib.Path('/workspace/scratch/5f2524fd4117/lean-tools/lean-4.33.1-linux/bin')
run=w/'verification'/('import-batch-'+a.stamp);run.mkdir(exist_ok=False)

def write_json(path,data):
 tmp=path.with_suffix(path.suffix+'.tmp');tmp.write_text(json.dumps(data,indent=2)+'\n');tmp.replace(path)
records=[]
for name in a.attempts:
 v=w/'verification'/name;d=json.loads((v/'result.json').read_text())
 assert d['state'] in ['source_passed_pending_readback','readback_running'],name
 d['previous_readback_batch']=d.get('readback_batch')
 d['recovery_note']='New isolated import after transport loss; former incomplete import has unknown terminal state'
 assert hashlib.sha256((pathlib.Path('/workspace/shared/sticky-recovery-20261006/runtime-20261006T1519/olean')/pathlib.Path(*d['module'].split('.')).with_suffix('.olean')).read_bytes()).hexdigest()==d['olean_sha256']
 assert d['source_exit_code']==0 and d['source_unchanged'] and d['artifact_unchanged']
 assert hashlib.sha256(pathlib.Path(d['source']).read_bytes()).hexdigest()==d['source_sha256']
 assert hashlib.sha256(pathlib.Path(d['olean_path']).read_bytes()).hexdigest()==d['olean_sha256']
 records.append((v,d))
modules=[d['module'] for v,d in records];assert len(modules)==len(set(modules))
names=[n for v,d in records for n in d['names']];assert len(names)==len(set(names))
readback=run/'Readback.lean';readback.write_text(''.join('import '+m+'\n' for m in modules)+'set_option autoImplicit false\n'+''.join('#print axioms '+n+'\n' for n in names))
env=os.environ.copy();env['PATH']=str(tool)+':'+env.get('PATH','');env['LEAN_NUM_THREADS']='1';env['MATHLIB_CACHE_DIR']=str(w/'mathlib-cache');base=subprocess.check_output([str(tool/'lake'),'env','printenv','LEAN_PATH'],cwd=r,env=env,text=True).strip().split(':');canonical=(r/'.lake/build/lib/lean').resolve();filtered=[x for x in base if (r/x).resolve()!=canonical];assert all((r/x).resolve()!=canonical for x in filtered);env['LEAN_PATH']=':'.join([str(pathlib.Path('/workspace/shared/sticky-recovery-20261006/runtime-20261006T1519/olean')),*filtered])
locks=w/'global-lean-locks';cmd=['python',str(w/'run_locked_lean.py'),str(locks/('import-batch-'+a.stamp+'.lock')),str(locks/(a.slot+'.lock')),str(tool/'lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true','-R',str(run),str(readback)]
manifest={'state':'running','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'modules':modules,'names':names,'command':cmd,'canonical_project_fallback_removed':True,'lean_path':env['LEAN_PATH'],'scope':'Fresh independent imported axiom gate after separate strict source compilations; frozen hashes checked before and after'}
(run/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
for v,d in records:
 d.update(state='readback_running',readback_batch=str(run));write_json(v/'result.json',d)
with (run/'axioms.log').open('w') as log:
 log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush();q=subprocess.run(cmd,cwd=r,env=env,stdout=log,stderr=subprocess.STDOUT);log.write('\nEXIT_CODE='+str(q.returncode)+'\n')
text=(run/'axioms.log').read_text();ax={n:[x.strip() for x in vals.split(',') if x.strip()] for n,vals in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)};ax.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",text)});allowed={'propext','Classical.choice','Quot.sound'};results=[]
for v,d in records:
 shutil.copy2(run/'axioms.log',v/'axioms.log');shutil.copy2(readback,v/'BatchReadback.lean')
 d['readback_exit_code']=q.returncode;d['axioms']={n:ax[n] for n in d['names'] if n in ax};d['missing_names']=sorted(set(d['names'])-set(ax));d['extra_axioms']={n:sorted(set(vals)-allowed) for n,vals in d['axioms'].items() if set(vals)-allowed}
 d['source_unchanged']=hashlib.sha256(pathlib.Path(d['source']).read_bytes()).hexdigest()==d['source_sha256'];d['artifact_unchanged']=hashlib.sha256(pathlib.Path(d['olean_path']).read_bytes()).hexdigest()==d['olean_sha256']
 d['state']='passed' if q.returncode==0 and not d['missing_names'] and not d['extra_axioms'] and d['source_unchanged'] and d['artifact_unchanged'] else 'failed';d['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();write_json(v/'result.json',d);results.append({'attempt':v.name,'state':d['state'],'declarations':len(d['names'])})
manifest.update(state='passed' if all(x['state']=='passed' for x in results) else 'failed',exit_code=q.returncode,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),results=results);(run/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(manifest));raise SystemExit(0 if manifest['state']=='passed' else 1)
