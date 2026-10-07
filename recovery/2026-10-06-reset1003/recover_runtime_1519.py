from pathlib import Path
import json,hashlib,shutil,datetime,re
w=Path('/workspace/shared/sticky-recovery-20261006');r=Path('/workspace/scratch/5f2524fd4117/4dstickykakeya');o=w/'runtime-20261006T1519';o.mkdir(exist_ok=False);out=o/'olean';out.mkdir();records={}
def accept(m,src,art,sh,oh,evidence,scope):
 if not src.exists() or not art.exists():return
 if hashlib.sha256(src.read_bytes()).hexdigest()!=sh or hashlib.sha256(art.read_bytes()).hexdigest()!=oh:return
 dest=out/Path(*m.split('.')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(art,dest)
 records[m]={'module':m,'source':str(src),'source_sha256':sh,'olean_path':str(dest),'olean_sha256':oh,'source_unchanged':True,'exit_code':0,'evidence':str(evidence),'scope':scope}
cp=w/'project-cache-20261006T1315';cm=json.loads((cp/'CACHE_MANIFEST.json').read_text())
for e in cm['artifacts']:accept(e['module'],r/e['source_path'],cp/e['olean_path'],e['source_sha256'],e['olean_sha256'],w/'cache-import-check-20261006T1315/status.json','hash-checked independently imported cache reuse')
for p in sorted(w.glob('dependency-slice-*/status.json')):
 d=json.loads(p.read_text())
 for e in d.get('modules',[]):
  if e.get('exit_code')==0 and e.get('source_unchanged'):
   m=e['module'];rel=Path(*m.split('.'));accept(m,r/rel.with_suffix('.lean'),r/'.lake/build/lib/lean'/rel.with_suffix('.olean'),e['source_sha256'],e['olean_sha256'],p,'completed prerequisite compilation or explicitly recorded validated reuse')
for p in sorted((w/'verification').glob('*/result.json')):
 d=json.loads(p.read_text())
 if d.get('source_exit_code')==0 and d.get('olean_sha256') and d.get('state') in ['passed','source_passed_pending_readback','readback_running']:
  accept(d['module'],Path(d['source']),Path(d['olean_path']),d['source_sha256'],d['olean_sha256'],p,'strict source success; imported gate '+d['state'])
for m,e in records.items():
 src=Path(e['source']);ds=re.findall(r'^import ((?:Theorems|Definitions|Solutions)\.[A-Za-z0-9_.]+)',src.read_text(),re.M);missing=[x for x in ds if x not in records]
 if missing:raise RuntimeError((m,missing))
manifest={'state':'hashes_and_project_closure_verified','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'artifact_count':len(records),'output_directory':str(out),'artifacts':list(records.values()),'scope':'Only prior terminal source-success artifacts copied to independent output; pending old executions excluded; no fresh compilation claimed'};(o/'BASELINE_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
for f in ['verify_recovered_source.py','verify_import_batch.py','run_dependency_pool.py','run_locked_lean.py','continue_windows_reset1003.py']:
 shutil.copy2(w/f,o/('old-'+f))
print(json.dumps({'new_overlay':str(out),'known_artifacts':len(records)}))
