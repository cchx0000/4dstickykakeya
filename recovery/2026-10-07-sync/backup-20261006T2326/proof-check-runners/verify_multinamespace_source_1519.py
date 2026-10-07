"""Fresh strict source and independent import gates in the recovered executor."""
import argparse,datetime,hashlib,json,os,pathlib,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--source',type=pathlib.Path,required=True);p.add_argument('--manifest',type=pathlib.Path,required=True);p.add_argument('--attempt',type=int,required=True);p.add_argument('--slot',choices=['2','3'],default='2');p.add_argument('--defer-readback',action='store_true');a=p.parse_args()
w=pathlib.Path('/workspace/shared/sticky-recovery-20261006');r=pathlib.Path('/workspace/scratch/5f2524fd4117/4dstickykakeya');tool=pathlib.Path('/workspace/scratch/5f2524fd4117/lean-tools/lean-4.33.1-linux/bin');source=a.source.resolve();relative=source.relative_to(w/'live');module='.'.join(relative.with_suffix('').parts);stem=source.stem.removeprefix('Thm_StickyKakeya4_');out=pathlib.Path('/workspace/shared/sticky-recovery-20261006/runtime-20261006T1519/olean')/relative.with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
v=w/'verification'/f'{stem}-attempt{a.attempt:02d}';v.mkdir(parents=True,exist_ok=False)
raw=source.read_bytes();sh=hashlib.sha256(raw).hexdigest();(v/'SourceSnapshot.lean').write_bytes(raw)
manifest_raw=a.manifest.read_bytes();manifest=json.loads(manifest_raw)
assert manifest['source_sha256']==sh,'Manifest does not describe these exact source bytes'
names=[n for unit in manifest['units'] for n in unit['declarations']]
assert names and len(names)==len(set(names))==manifest['declaration_count']
# This candidate uses explicit named namespaces; named sections do not add
# declaration prefixes. Check every source declaration against the manifest,
# rather than accepting a list that could silently omit a new public theorem.
stack=[];found=[];seen_namespaces=[]
pattern=r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:theorem|lemma|def)\s+([A-Za-z0-9_]+)'
for line in raw.decode().splitlines():
 ns=re.match(r'^namespace\s+([A-Za-z0-9_.]+)\s*$',line)
 if ns:stack.append(ns.group(1));seen_namespaces.append('.'.join(stack));continue
 en=re.match(r'^end\s+([A-Za-z0-9_.]+)\s*(?:--.*)?$',line)
 if en and stack and en.group(1)==stack[-1]:stack.pop();continue
 decl=re.match(pattern,line)
 if decl:
  assert stack,'Public declaration outside the explicit namespace manifest'
  found.append('.'.join([*stack,decl.group(1)]))
assert not stack,'Unclosed namespace in declaration scanner'
assert found==names,{'scanned':found,'manifest':names}
assert seen_namespaces==manifest['namespaces']
(v/'DeclarationsManifest.json').write_bytes(manifest_raw)

readback=v/'Readback.lean';readback.write_text('import '+module+'\nset_option autoImplicit false\n'+''.join('#print axioms '+n+'\n' for n in names))
env=os.environ.copy();env['PATH']=str(tool)+':'+env.get('PATH','');env['LEAN_NUM_THREADS']='1';env['MATHLIB_CACHE_DIR']=str(w/'mathlib-cache');base=subprocess.check_output([str(tool/'lake'),'env','printenv','LEAN_PATH'],cwd=r,env=env,text=True).strip().split(':');canonical=(r/'.lake/build/lib/lean').resolve();base=[x for x in base if (r/x).resolve()!=canonical];env['LEAN_PATH']=':'.join([str(pathlib.Path('/workspace/shared/sticky-recovery-20261006/runtime-20261006T1519/olean')),*base])
locks=w/'global-lean-locks';locks.mkdir(exist_ok=True);outputlock=locks/(hashlib.sha256(str(out).encode()).hexdigest()+'.lock')
prefix=['python',str(w/'run_locked_lean.py'),str(outputlock),str(locks/(a.slot+'.lock')),str(tool/'lean'),'-j1','-DautoImplicit=false','-DwarningAsError=true']
s={'state':'running','module':module,'source':str(source),'source_sha256':sh,'olean_path':str(out),'names':names,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'executor_epoch':'20261006T1003','scope':'fresh isolated output check after1510 transport loss; old incomplete attempts remain unknown; prior validated artifacts reused by exact hash'}
s['declarations_manifest_sha256']=hashlib.sha256(manifest_raw).hexdigest()
s['declaration_coverage']='Exact namespace-qualified source declaration sequence equals the frozen manifest'
def save():
 tmp=v/'result.json.tmp';tmp.write_text(json.dumps(s,indent=2)+'\n');tmp.replace(v/'result.json')
def run(cmd,name):
 with (v/name).open('w') as log:
  log.write('COMMAND '+json.dumps(cmd)+'\nSOURCE_SHA256 '+sh+'\n');log.flush();q=subprocess.run(cmd,cwd=r,env=env,stdout=log,stderr=subprocess.STDOUT);log.write('\nEXIT_CODE='+str(q.returncode)+'\n');return q.returncode
save();s['source_exit_code']=run(prefix+['-R',str(w/'live'),'-o',str(out),str(source)],'source.log')
if s['source_exit_code']==0 and a.defer_readback:
 s['olean_sha256']=hashlib.sha256(out.read_bytes()).hexdigest();s['artifact_unchanged']=True;s['source_unchanged']=hashlib.sha256(source.read_bytes()).hexdigest()==sh
 s['state']='source_passed_pending_readback' if s['source_unchanged'] else 'failed';s['source_finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();print(json.dumps(s,indent=2));raise SystemExit(0 if s['source_unchanged'] else 1)
if s['source_exit_code']==0:
 s['olean_sha256']=hashlib.sha256(out.read_bytes()).hexdigest();s['state']='readback_running';save();s['readback_exit_code']=run(prefix+['-R',str(v),str(readback)],'axioms.log');text=(v/'axioms.log').read_text();ax={n:[x.strip() for x in vals.split(',') if x.strip()] for n,vals in re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S)};ax.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",text)});s['axioms']=ax;s['missing_names']=sorted(set(names)-set(ax));allowed={'propext','Classical.choice','Quot.sound'};s['extra_axioms']={n:sorted(set(vals)-allowed) for n,vals in ax.items() if set(vals)-allowed}
s['artifact_unchanged']=('olean_sha256' in s and out.exists() and hashlib.sha256(out.read_bytes()).hexdigest()==s['olean_sha256']);s['source_unchanged']=hashlib.sha256(source.read_bytes()).hexdigest()==sh;s['state']='passed' if s['source_exit_code']==0 and s.get('readback_exit_code')==0 and not s.get('missing_names') and not s.get('extra_axioms') and s['source_unchanged'] and s['artifact_unchanged'] else 'failed';s['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();print(json.dumps({k:v for k,v in s.items() if k!='axioms'},indent=2));raise SystemExit(0 if s['state']=='passed' else 1)
