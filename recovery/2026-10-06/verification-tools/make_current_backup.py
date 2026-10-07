from pathlib import Path
import json,subprocess,hashlib,shutil,tarfile,sys
w=Path('/workspace/shared/sticky-recovery-20261006');r=Path('/workspace/scratch/5f2524fd4117/4dstickykakeya');stamp=sys.argv[1];o=w/('backup-'+stamp);o.mkdir()
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip();status=json.loads((r/'verification/final-status.json').read_text());n=status['current_project_module_count'];nm=status['fresh_strict_modules'];nd=status['fresh_strict_declarations'];deps=status['fresh_prerequisite_slice_modules']
subprocess.run(['git','bundle','create',str(o/'project-history.bundle'),'--all'],cwd=r,check=True)
p=subprocess.run(['git','bundle','verify',str(o/'project-history.bundle')],cwd=r,text=True,capture_output=True);(o/'bundle-verification.txt').write_text(p.stdout+p.stderr);assert p.returncode==0
shutil.copy2(r/'verification/final-status.json',o/'CURRENT_VERIFICATION_STATUS.json');cnt=0
for srcdir in [*w.glob('reconstructed-*'),w/'live',w/'consumer-drafts']:
 if not srcdir.is_dir():continue
 for src in srcdir.rglob('*.lean'):
  dest=o/'pending-source-snapshots'/srcdir.name/src.relative_to(srcdir);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dest);cnt+=1
for src in [*w.glob('window-*.json'),*w.glob('live/*.md'),*w.glob('live/*STATUS.json')]:
 dest=o/'pending-source-provenance'/src.name;dest.parent.mkdir(exist_ok=True);shutil.copy2(src,dest)
(o/'README.txt').write_text(f'Current recovery checkpoint {head}\nThe canonical recovered project has {n} modules: exact restored1559 checkpoint plus {nm} new October6 modules ({nd} public declarations). Strict source and independent imported axioms are archived in Git history. Targeted closures have checked {deps} distinct prerequisites; no project-wide build is claimed.\nThe full1559 checkpoint, its historical proof records, and99 pending-source snapshots have been restored and merged exactly; historical checks are not relabeled as new checks.\nPending-source-snapshots are unverified unless their exact hashes are certified in committed fresh-checks records.\nOriginal final dimension-four theorem and kappa=0 remain unfinished. GitHub publication remains blocked by its prior approval.\nRestore committed project: git clone project-history.bundle\n')
cache=None
if len(sys.argv)>2:
 cache=Path(sys.argv[2]);shutil.copytree(cache,o/'verified-project-cache');cm=json.loads((cache/'CACHE_MANIFEST.json').read_text());assert cm['project_closure_complete']
 with (o/'README.txt').open('a') as f:f.write(f"This archive also contains {cm['artifact_count']} hash-verified project olean artifacts. Verify CACHE_MANIFEST.json, exact compiler and dependency pins, every source/artifact hash and project import closure before reuse. Cached artifacts are an acceleration aid; the committed proof sources and check receipts remain authoritative. Cache reuse is not fresh compilation.\n")
out=w/f'4dstickykakeya-recovered{n}-fresh{nd}-{stamp}.tar.gz'
with tarfile.open(out,'w:gz') as tf:tf.add(o,arcname=o.name)
d={'path':str(out),'bytes':out.stat().st_size,'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'source_commit':head,'canonical_modules':n,'new_fresh_declarations':nd,'pending_snapshots':cnt,'verified_cache_artifacts':(cm['artifact_count'] if cache else 0)};(w/f'backup-{stamp}-manifest.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d))
