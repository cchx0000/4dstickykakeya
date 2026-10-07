from pathlib import Path
import json,hashlib,shutil,subprocess,datetime,re,sys
w=Path('/workspace/shared/sticky-recovery-20261006');r=Path('/workspace/scratch/5f2524fd4117/4dstickykakeya');e=r/'recovery/2026-10-06';stamp=sys.argv[1];new={}
for p in sorted((w/'verification').glob('*/result.json')):
 d=json.loads(p.read_text());s=Path(d['source']);dest=r/'Theorems'/s.name
 if d['state']!='passed' or not s.exists() or hashlib.sha256(s.read_bytes()).hexdigest()!=d['source_sha256']:continue
 if dest.exists():
  assert dest.read_bytes()==s.read_bytes(),s
  stem=s.stem.removeprefix('Thm_StickyKakeya4_')
  if not (e/'fresh-checks'/stem/'PASSED_ATTEMPT.json').exists():
   out=Path(d['olean_path']);assert hashlib.sha256(out.read_bytes()).hexdigest()==d['olean_sha256'];assert not d['missing_names'] and not d['extra_axioms'] and d['source_unchanged'] and d['artifact_unchanged']
   hist=e/'fresh-restored-prerequisite-checks'/stem;hist.mkdir(parents=True,exist_ok=True)
   for v in sorted((w/'verification').glob(stem+'-attempt*')):
    if not (hist/v.name).exists():shutil.copytree(v,hist/v.name)
   (hist/'PASSED_ATTEMPT.json').write_text(json.dumps(d,indent=2)+'\n')
  continue
 out=Path(d['olean_path']);assert hashlib.sha256(out.read_bytes()).hexdigest()==d['olean_sha256'];assert not d['missing_names'] and not d['extra_axioms'] and d['source_unchanged'] and d['artifact_unchanged'];new[s.name]=(p,d,s,dest)
for name,(p,d,s,dest) in new.items():
 shutil.copy2(s,dest);stem=s.stem.removeprefix('Thm_StickyKakeya4_');hist=e/'fresh-checks'/stem;hist.mkdir(parents=True)
 for v in sorted((w/'verification').glob(stem+'-attempt*')):shutil.copytree(v,hist/v.name)
 (hist/'PASSED_ATTEMPT.json').write_text(json.dumps(d,indent=2)+'\n')
records=[json.loads(p.read_text()) for p in (e/'fresh-checks').glob('*/PASSED_ATTEMPT.json')];count=sum(len(list((r/f).glob('*.lean'))) for f in ['Definitions','Theorems','Solutions']);decls=sum(len(d['names']) for d in records)
statuspath=r/'verification/final-status.json';status=json.loads(statuspath.read_text());status.update(generated_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),current_project_module_count=count,fresh_strict_modules=len(records),fresh_strict_declarations=decls,scope='October6 checks are fresh; October5 source and verification receipts restored exactly. Full merged graph not freshly rebuilt; targeted interface dependency DAG remains separately recorded.')
deps=set()
for sp in w.glob('dependency-slice-*/status.json'):
 try: sd=json.loads(sp.read_text())
 except (OSError,ValueError):continue
 for md in sd.get('modules',[]):
  if not isinstance(md,dict):continue
  if md.get('exit_code')!=0 or not md.get('source_unchanged'):continue
  src=r/(md['module'].replace('.','/')+'.lean')
  if src.exists() and hashlib.sha256(src.read_bytes()).hexdigest()==md['source_sha256']:deps.add(md['module'])
status['fresh_prerequisite_slice_modules']=len(deps)
statuspath.write_text(json.dumps(status,indent=2)+'\n');(e/f'FRESH_CHECKPOINT_{stamp}.json').write_text(json.dumps(status,indent=2)+'\n')
for fn in ['README.md','CURRENT_MILESTONES.md']:
 p=r/fn;s=p.read_text();s=re.sub(r'merged with all \d+ new October6 modules',f'merged with all {len(records)} new October6 modules',s,1);s=re.sub(r'The current tree has [\d,]+ project modules',f'The current tree has {count:,} project modules',s,1);s=re.sub(r'The \d+ new October6 public declarations',f'The {decls} new October6 public declarations',s,1);s=re.sub(r'the full [\d,]+-module tree has not been rebuilt here',f'the full {count:,}-module tree has not been rebuilt here',s,1);s=re.sub(r'Targeted prerequisite closures have checked \d+ distinct modules',f'Targeted prerequisite closures have checked {len(deps)} distinct modules',s,1);p.write_text(s)
for n in ['run_dependency_pool.py','make_current_backup.py','verify_recovered_source.py','run_locked_lean.py','run_packed_frame_when_ready.py','continue_interface_dependencies.py','integrate_current_passed.py']:shutil.copy2(w/n,e/'verification-tools'/n)
for receipt in w.glob('backup-*-receipt.json'):shutil.copy2(receipt,e/receipt.name)
for manifest in w.glob('backup-*-manifest.json'):shutil.copy2(manifest,e/manifest.name)
for n in ['CACHE_PARTS_SHA256.json','REASSEMBLE_CACHE_README.txt','LIBRARY_RECEIPTS.json']:shutil.copy2(w/'cache-delivery-20261006T0734'/n,e/('CACHE_DELIVERY_0734_'+n))
pool=w/'dependency-slice-20261006T070030-pool/status.json';d=json.loads(pool.read_text());(e/f'DEPENDENCY_PROGRESS_{stamp}.json').write_text(json.dumps(d,indent=2)+'\n')
subprocess.run(['git','diff','--check'],cwd=r,check=True);subprocess.run(['git','add','Theorems','recovery/2026-10-06','README.md','CURRENT_MILESTONES.md','verification/final-status.json'],cwd=r,check=True)
name=subprocess.check_output(['git','show','-s','--format=%an','HEAD'],cwd=r,text=True).strip();email=subprocess.check_output(['git','show','-s','--format=%ae','HEAD'],cwd=r,text=True).strip();subprocess.run(['git','-c','user.name='+name,'-c','user.email='+email,'commit','--quiet','-m','Preserve actual isometric transport and recovered interface build progress'],cwd=r,check=True)
print(json.dumps({'commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip(),'modules':count,'fresh_modules':len(records),'declarations':decls,'new':list(new)}))
