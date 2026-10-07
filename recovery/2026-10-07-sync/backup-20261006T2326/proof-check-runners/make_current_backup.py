from pathlib import Path
import json,subprocess,hashlib,shutil,tarfile,sys
w=Path('/workspace/shared/sticky-recovery-20261006');r=Path('/workspace/scratch/5f2524fd4117/4dstickykakeya');stamp=sys.argv[1];o=w/('backup-'+stamp);o.mkdir()
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip();status=json.loads((r/'verification/final-status.json').read_text());n=status['current_project_module_count'];nm=status.get('verified_oct6_modules',status['fresh_strict_modules']);nd=status.get('verified_oct6_declarations',status['fresh_strict_declarations']);deps=status['fresh_prerequisite_slice_modules']
subprocess.run(['git','bundle','create',str(o/'project-history.bundle'),'--all'],cwd=r,check=True)
p=subprocess.run(['git','bundle','verify',str(o/'project-history.bundle')],cwd=r,text=True,capture_output=True);(o/'bundle-verification.txt').write_text(p.stdout+p.stderr);assert p.returncode==0
shutil.copy2(r/'verification/final-status.json',o/'CURRENT_VERIFICATION_STATUS.json');cnt=0;pending_records=[]
for srcdir in [*w.glob('reconstructed-*'),w/'live',w/'consumer-drafts']:
 if not srcdir.is_dir():continue
 for src in srcdir.rglob('*.lean'):
  dest=o/'pending-source-snapshots'/srcdir.name/src.relative_to(srcdir);dest.parent.mkdir(parents=True,exist_ok=True)
  before=src.stat();raw=src.read_bytes();after=src.stat();dest.write_bytes(raw);cnt+=1
  pending_records.append({'path':str(dest.relative_to(o)),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'source_unchanged_during_copy':(before.st_size,before.st_mtime_ns)==(after.st_size,after.st_mtime_ns),'scope':'Pending source snapshot; only matching canonical verification receipts establish proof status'})
(o/'PENDING_SOURCE_MANIFEST.json').write_text(json.dumps(pending_records,indent=2)+'\n')
# Preserve declared-name manifests and parameter receipts needed to resume
# consolidated source gates. These are task-produced drafts, not certificates.
for root in [w/'consumer-drafts',w/'live',*w.glob('htotal-source-*')]:
 if not root.is_dir():continue
 for src in root.rglob('*'):
  if src.is_file() and src.suffix in ['.json','.md']:
   dest=o/'pending-source-provenance'/root.name/src.relative_to(root);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dest)
for src in [*w.glob('window-*.json'),*w.glob('live/*.md'),*w.glob('live/*STATUS.json'),*[w/n for n in ['current-graph-rank-cap-manifest.json','actual_reference_frontend_manifest.json','actual_reference_one_T_manifest.json','actual_raw_whole_Y_total_manifest.json','current-rank-one-angular-bound-manifest.json','actual_reference_one_T_geometry_manifest.json','actual_reference_one_T_geometry_draft_receipt.json'] if (w/n).exists()]]:
 dest=o/'pending-source-provenance'/src.name;dest.parent.mkdir(exist_ok=True);shutil.copy2(src,dest)
# Preserve unfinished gate evidence and the exact local runners, separately from
# committed verified declarations. No credentials or transfer URLs are included.
if (w/'verification').exists():
 shutil.copytree(w/'verification',o/'pending-check-receipts')
helpers=['verify_recovered_source.py','run_dependency_pool.py','run_locked_lean.py',
 'run_packed_frame_when_ready.py','run_merged_quotient_when_ready.py',
 'run_output_admission_when_ready.py','resume_targeted_interfaces_reset1003.py',
 'continue_windows_reset1003.py','make_current_backup.py','integrate_reset1003_passed.py',
 'verify_import_batch.py','run_parent_source_bridges.py','verify_recovered_source_1519.py',
 'verify_import_batch_1519.py','verify_multinamespace_source_1519.py','run_dependency_pool_1519.py','recover_runtime_1519.py',
 'continue_windows_1519.py','snapshot_project_cache_1519.py','check_project_cache_1519.py','run_dependency_pool_single_20261006T2021.py','continue_higher_grid_20261006T2042.py','snapshot_project_cache_20261006T2054.py','check_project_cache_20261006T2057.py','package_cache974.py','verify_import_batch_20261006T2130.py']
for name in helpers:
 src=w/name
 if src.exists():
  dest=o/'proof-check-runners'/name;dest.parent.mkdir(exist_ok=True);shutil.copy2(src,dest)
for name in ['next-native-coherence-targets.json','RESET1003_PLANNED_CANONICAL_CLOSURE.json',
 'output-admission-continuation-status.json','merged-quotient-continuation-status.json',
 'packed-frame-continuation-status.json']:
 src=w/name
 if src.exists():
  dest=o/'pending-source-provenance'/name;dest.parent.mkdir(exist_ok=True);shutil.copy2(src,dest)
(o/'README.txt').write_text(f'Current recovery checkpoint {head}\nThe canonical recovered project has {n} modules: exact restored1559 checkpoint plus {nm} new October6 modules ({nd} public declarations). Strict source and independent imported axioms are archived in Git history. Those records span the original October6 executor and the reset1003 executor; CURRENT_VERIFICATION_STATUS.json distinguishes them exactly. This executor has freshly compiled {deps} distinct project prerequisites; validated cache reuse is recorded separately; no project-wide build is claimed.\nThe full1559 checkpoint, its historical proof records, and99 pending-source snapshots have been restored and merged exactly; historical checks are not relabeled as new checks.\nPending-source-snapshots are unverified unless their exact hashes are certified in committed fresh-checks records.\nOriginal final dimension-four theorem and kappa=0 remain unfinished. GitHub publication remains blocked by its prior approval.\nRestore committed project: git clone project-history.bundle\n')
cache=None
if len(sys.argv)>2:
 cache=Path(sys.argv[2]);shutil.copytree(cache,o/'verified-project-cache');cm=json.loads((cache/'CACHE_MANIFEST.json').read_text());assert cm['project_closure_complete']
 with (o/'README.txt').open('a') as f:f.write(f"This archive also contains {cm['artifact_count']} hash-verified project olean artifacts. Verify CACHE_MANIFEST.json, exact compiler and dependency pins, every source/artifact hash and project import closure before reuse. Cached artifacts are an acceleration aid; the committed proof sources and check receipts remain authoritative. Cache reuse is not fresh compilation.\n")
out=w/f'4dstickykakeya-recovered{n}-verified{nd}-{stamp}.tar.gz'
with tarfile.open(out,'w:gz') as tf:tf.add(o,arcname=o.name)
d={'path':str(out),'bytes':out.stat().st_size,'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'source_commit':head,'canonical_modules':n,'verified_oct6_declarations':nd,'current_executor_fresh_declarations':status['fresh_strict_declarations'],'pending_snapshots':cnt,'verified_cache_artifacts':(cm['artifact_count'] if cache else 0)};(w/f'backup-{stamp}-manifest.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d))
