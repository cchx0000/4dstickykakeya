"""Save only fresh hash-matched project artifacts with complete project import closure."""
from pathlib import Path
import json,hashlib,subprocess,re,shutil,datetime,sys,platform
w=Path('/workspace/shared/sticky-recovery-20261006');r=Path('/workspace/scratch/5f2524fd4117/4dstickykakeya');out=w/('project-cache-'+sys.argv[1]);out.mkdir();records={};active=set()
for p in sorted(w.glob('dependency-slice-*/status.json')):
 d=json.loads(p.read_text());active.update(d.get('active',{}))
 for x in d.get('modules',[]):
  if x.get('exit_code')==0 and x.get('source_unchanged'):
   z=dict(x);z['artifact_path']=str(r/'.lake/build/lib/lean'/Path(*x['module'].split('.')).with_suffix('.olean'));z['evidence']=str(p);records[x['module']]=z
for p in sorted((w/'verification').glob('*/result.json')):
 d=json.loads(p.read_text())
 if d.get('state')=='passed' and d.get('artifact_unchanged') and d.get('source_unchanged'):
  z=dict(d);z['artifact_path']=d['olean_path'];z['evidence']=str(p);records[d['module']]=z
valid={};excluded={}
for m,d in records.items():
 s=r/Path(*m.split('.')).with_suffix('.lean');a=Path(d['artifact_path'])
 if m in active:excluded[m]='active output is excluded';continue
 if not s.exists() or not a.exists():excluded[m]='canonical source or output absent';continue
 if hashlib.sha256(s.read_bytes()).hexdigest()!=d['source_sha256']:excluded[m]='source hash mismatch';continue
 raw=a.read_bytes()
 if hashlib.sha256(raw).hexdigest()!=d.get('olean_sha256'):excluded[m]='artifact hash mismatch';continue
 d['project_imports']=re.findall(r'^import ((?:Theorems|Definitions|Solutions)\.[A-Za-z0-9_.]+)',s.read_text(),re.M);valid[m]=(d,raw)
while True:
 bad={m:[x for x in d['project_imports'] if x not in valid] for m,(d,b) in valid.items()};bad={m:x for m,x in bad.items() if x}
 if not bad:break
 for m,x in bad.items():valid.pop(m);excluded[m]={'incomplete_project_imports':x}
items=[]
for m,(d,raw) in sorted(valid.items()):
 rel=Path(*m.split('.')).with_suffix('.olean');p=out/'lib/lean'/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
 items.append({'module':m,'source_path':str(Path(*m.split('.')).with_suffix('.lean')),'source_sha256':d['source_sha256'],'olean_path':str(Path('lib/lean')/rel),'olean_sha256':d['olean_sha256'],'project_imports':d['project_imports'],'project_import_artifact_hashes':{x:valid[x][0]['olean_sha256'] for x in d['project_imports']},'original_check_evidence':d['evidence'],'scope':'compiled in this executor, reusable cache only; not a new proof check on restore'})
compiler=Path('/workspace/scratch/5f2524fd4117/lean-tools/lean-4.33.1-linux/bin/lean');lake=(r/'lake-manifest.json').read_bytes();(out/'lake-manifest.json').write_bytes(lake);(out/'lean-toolchain').write_bytes((r/'lean-toolchain').read_bytes())
manifest={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'project_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip(),'compiler_version':subprocess.check_output([str(compiler),'--version'],text=True).strip(),'compiler_sha256':hashlib.sha256(compiler.read_bytes()).hexdigest(),'system':platform.system(),'architecture':platform.machine(),'lake_manifest_sha256':hashlib.sha256(lake).hexdigest(),'project_closure_complete':True,'artifact_count':len(items),'artifact_bytes':sum(len(b) for d,b in valid.values()),'artifacts':items,'excluded':excluded,'restore_requirement':'Verify compiler, dependency pins, every source and artifact hash, and full project import closure before reuse. Historical receipts remain historical; cache reuse is not fresh compilation.'}
(out/'CACHE_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({'directory':str(out),'count':len(items),'bytes':manifest['artifact_bytes'],'excluded':len(excluded)}))
