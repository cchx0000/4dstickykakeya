from pathlib import Path
import datetime,hashlib,json,re,shutil,subprocess,sys
w=Path('/workspace/shared/sticky-recovery-20261006');r=Path('/workspace/scratch/5f2524fd4117/4dstickykakeya')
e=r/'recovery/2026-10-06-reset1003';stamp=sys.argv[1];added=[]
# Reject duplicate declaration owners before canonical installation.
owners={}
for ledger in [r/'recovery/2026-10-06/fresh-checks',e/'fresh-checks']:
 for receipt in ledger.glob('*/PASSED_ATTEMPT.json'):
  prior=json.loads(receipt.read_text()); owner=Path(prior['source']).name
  for name in prior['names']:
   assert name not in owners or owners[name]==owner,(name,owners.get(name),owner)
   owners[name]=owner
for p in sorted((w/'verification').glob('*/result.json')):
 d=json.loads(p.read_text())
 if d.get('state')!='passed' or d.get('executor_epoch')!='20261006T1003':continue
 s=Path(d['source']);a=Path(d['olean_path'])
 if not s.exists() or hashlib.sha256(s.read_bytes()).hexdigest()!=d['source_sha256']:continue
 assert hashlib.sha256(a.read_bytes()).hexdigest()==d['olean_sha256']
 assert d['source_unchanged'] and d['artifact_unchanged'] and not d['missing_names'] and not d['extra_axioms']
 stem=s.stem.removeprefix('Thm_StickyKakeya4_');dest=r/'Theorems'/s.name;hist=e/'fresh-checks'/stem
 previous=hist/'PASSED_ATTEMPT.json'
 if previous.exists():kind=json.loads(previous.read_text())['canonical_scope']
 elif dest.exists():kind='rechecked_existing_canonical_source'
 else:kind='new_canonical_module';added.append(s.name)
 for name in d['names']:
  assert name not in owners or owners[name]==s.name,('duplicate declaration owner',name,owners.get(name),s.name)
  owners[name]=s.name
 if dest.exists():assert dest.read_bytes()==s.read_bytes(),s
 else:shutil.copy2(s,dest)
 hist.mkdir(parents=True,exist_ok=True)
 for old in sorted((w/'verification').glob(stem+'-attempt*')):
  if not (hist/old.name).exists():shutil.copytree(old,hist/old.name)
 if d.get('readback_batch'):
  batch=Path(d['readback_batch']);target=e/'import-batches'/batch.name
  if not target.exists():
   target.parent.mkdir(parents=True,exist_ok=True);shutil.copytree(batch,target)
 d['canonical_scope']=kind;previous.write_text(json.dumps(d,indent=2)+'\n')
records=[json.loads(p.read_text()) for p in (e/'fresh-checks').glob('*/PASSED_ATTEMPT.json')]
old=[json.loads(p.read_text()) for p in (r/'recovery/2026-10-06/fresh-checks').glob('*/PASSED_ATTEMPT.json')]
new=[d for d in records if d['canonical_scope']=='new_canonical_module']
nm=len(old)+len(new);nd=sum(len(x['names']) for x in [*old,*new])
count=sum(len(list((r/x).glob('*.lean'))) for x in ['Definitions','Theorems','Solutions'])
s=json.loads((r/'verification/final-status.json').read_text())
s.update(generated_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),current_project_module_count=count,
 verified_oct6_modules=nm,verified_oct6_declarations=nd,
 fresh_strict_modules=len(records),fresh_strict_declarations=sum(len(x['names']) for x in records),
 current_cache_import_validation='453 hash-matched artifacts independently imported after reset; not source recompilation',
 scope='Post-reset fresh source/import receipts are separate from the restored pre-reset receipts and validated artifact reuse. The full project has not been rebuilt; the final theorem remains unfinished.')
fresh=set();cached=set()
for p in w.glob('dependency-slice-*/status.json'):
 d=json.loads(p.read_text())
 for x in d.get('modules',[]):
  if x.get('exit_code')!=0:continue
  (fresh if x.get('source_compiled_in_current_executor') else cached).add(x['module'])
s['fresh_prerequisite_slice_modules']=len(fresh);s['reused_project_prerequisite_modules']=len(cached)
if (e/'cache578-validation/status.json').exists():
 cache578=json.loads((e/'cache578-validation/status.json').read_text())
 assert cache578['state']=='passed'
 s['current_snapshot_cache_import_artifacts']=578
 s['current_snapshot_cache_import_scope']='578-artifact independent cache-only import; not 578 new source compilations'
 s['current_snapshot_cache_import_receipt']='recovery/2026-10-06-reset1003/cache578-validation/status.json'
if (e/'cache767-validation/status.json').exists():
 cache767=json.loads((e/'cache767-validation/status.json').read_text());assert cache767['state']=='passed'
 s['current_snapshot_cache_import_artifacts']=767
 s['current_snapshot_cache_import_scope']='767-artifact independent cache-only import; not 767 new source compilations'
 s['current_snapshot_cache_import_receipt']='recovery/2026-10-06-reset1003/cache767-validation/status.json'
if (e/'cache974-validation/status.json').exists():
 cache974=json.loads((e/'cache974-validation/status.json').read_text());assert cache974['state']=='passed'
 s['current_snapshot_cache_import_artifacts']=974
 s['current_snapshot_cache_import_scope']='974-artifact independent cache-only import; not 974 new source compilations'
 s['current_snapshot_cache_import_receipt']='recovery/2026-10-06-reset1003/cache974-validation/status.json'
s['active_source_budget_audit']={'state':'not closed','issue':'Converting the baseline quotient cost from epsilon to reference r can create a c versus c^3 parameter cycle','candidate':'Keep baseline mass and menu costs at epsilon; verify raw third-core and reference-native/profile parameters on one actual source','scope':'Certified local selection and cutoff results are unchanged; no complete actual parameter join claimed','audit':'docs/SAME_Q_FINE_WEIGHT_AND_REMEMBERED_HEIGHT.md','original_incidence_candidate':'docs/ORIGINAL_INCIDENCE_HEIGHT_NORMALIZATION.md; actual raw lower and height adapter verified, capacity/source join still in progress','rejected_degree_transfer':'docs/GLOBAL_TO_PARENT_DEGREE_SCALE_AUDIT.md; fixed1/8 window does not allow arbitrary small parent-degree loss'}
(r/'verification/final-status.json').write_text(json.dumps(s,indent=2)+'\n')
(e/f'CHECKPOINT_{stamp}.json').write_text(json.dumps(s,indent=2)+'\n')
for n in ['CACHE_READY_RESET1003.json','RESET1003_DEPENDENCY_PINS.json','RESET1003_DEPENDENCY_STATUS.json',
 'RESET1003_INTERFACE_RUN.json','RESET1003_PLANNED_CANONICAL_CLOSURE.json']:
 p=w/n
 if p.exists():shutil.copy2(p,e/n)
runtime=w/'runtime-20261006T1519'
if runtime.exists():
 target=e/'transport-recovery-1519';target.mkdir(exist_ok=True)
 for name in ['BASELINE_MANIFEST.json','DISCONNECT_RECOVERY_AUDIT.json','TRANSPORT_EVENT_1808.json']:
  if (runtime/name).exists():shutil.copy2(runtime/name,target/name)
check=w/'cache-import-check-20261006T1003-restored'
if check.exists() and not (e/check.name).exists():shutil.copytree(check,e/check.name)
for p in w.glob('*.py'):
 if p.name in ['verify_recovered_source.py','run_dependency_pool.py','validate_reset1003_dependencies.py',
  'integrate_reset1003_passed.py','resume_targeted_interfaces_reset1003.py','continue_windows_reset1003.py',
  'run_packed_frame_when_ready.py','run_locked_lean.py','check_project_cache.py',
  'verify_import_batch.py','run_parent_source_bridges.py','verify_recovered_source_1519.py',
  'verify_import_batch_1519.py','verify_multinamespace_source_1519.py','run_dependency_pool_1519.py','recover_runtime_1519.py',
  'continue_windows_1519.py','snapshot_project_cache_1519.py','check_project_cache_1519.py','run_dependency_pool_single_20261006T2021.py','continue_higher_grid_20261006T2042.py','snapshot_project_cache_20261006T2054.py','check_project_cache_20261006T2057.py','package_cache974.py','verify_import_batch_20261006T2130.py']:
  shutil.copy2(p,e/p.name)
for fn in ['README.md','CURRENT_MILESTONES.md']:
 p=r/fn;x=p.read_text()
 x=x.replace('Official dependency caches are being restored before a new independent cache-only import. No new source compilation or post-reset import pass is claimed yet.',
 'Official dependencies are restored and453 archived project artifacts passed an independent cache-only import after all compiler, dependency, source and artifact hashes were checked. Fresh post-reset source/import results are listed separately in verification/final-status.json.')
 x=x.replace('## 2026-10-06 complete recovery and new source geometry','## 2026-10-06 checkpoint before the10:03 reset')
 x=re.sub(r'The current tree has [\d,]+ project modules', 'That pre-reset checkpoint contains1,628 project modules',x,1)
 marker='Fresh post-reset source/import results are listed separately in verification/final-status.json.'
 x=re.sub(r'The live tree now contains[\d,]+ project modules;[\d,]+ public declarations have fresh source and independent-import checks in this executor\.\n\n','',x)
 if marker in x:x=x.replace(marker,marker+f'\n\nThe live tree now contains{count:,} project modules;{s["fresh_strict_declarations"]:,} public declarations have fresh source and independent-import checks in this executor.',1)
 p.write_text(x)
subprocess.run(['git','diff','--check'],cwd=r,check=True)
subprocess.run(['git','add','Theorems','recovery/2026-10-06-reset1003','README.md','CURRENT_MILESTONES.md','verification/final-status.json'],cwd=r,check=True)
if subprocess.run(['git','diff','--cached','--quiet'],cwd=r).returncode:
 name=subprocess.check_output(['git','show','-s','--format=%an','HEAD'],cwd=r,text=True).strip()
 email=subprocess.check_output(['git','show','-s','--format=%ae','HEAD'],cwd=r,text=True).strip()
 subprocess.run(['git','-c','user.name='+name,'-c','user.email='+email,'commit','--quiet','-m',
  'Preserve fresh actual-source geometry checks after verified cache restoration'],cwd=r,check=True)
print(json.dumps({'commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip(),
 'modules':count,'new_modules_this_call':added,'current_executor_checked_declarations':s['fresh_strict_declarations'],
 'verified_oct6_declarations':nd,'current_source_prerequisites':len(fresh),'reused_prerequisites':len(cached)}))
