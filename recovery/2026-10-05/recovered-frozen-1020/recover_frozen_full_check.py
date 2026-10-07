import datetime,hashlib,json,os,pathlib,re,shutil,subprocess
w=pathlib.Path('/workspace/shared/sticky-recovery-20261005');r=pathlib.Path('/workspace/scratch/5f2524fd4117/4dstickykakeya');out=w/'recovered-frozen-1020'
out.mkdir(exist_ok=False); (out/'live/Solutions').mkdir(parents=True); (out/'olean/Solutions').mkdir(parents=True)
manifest=json.loads((w/'frozen-full-source-manifest.json').read_text()); old=json.loads((w/'frozen-full-targets-status.json').read_text());oldlog=(w/'frozen-full-targets-build.log').read_text()
done=set(re.findall(r'(?:Built|Replayed) ([A-Za-z][\w.]*)',oldlog)) & set(manifest['roots']);missing=sorted(set(manifest['roots'])-done)
assert missing==['Solutions.Sol_StickyKakeya4_selector_closure','Solutions.Sol_StickyKakeya4_sticky_kakeya_four_dimensional'],missing
assert not any(hashlib.sha256((r/e['path']).read_bytes()).hexdigest()!=e['sha256'] for e in manifest['sources'].values())
for name in ['frozen-full-source-manifest.json','frozen-full-targets-status.json','frozen-full-targets-build.log']:shutil.copy2(w/name,out/('original-'+name))
for p in (r/'.lake/build/lib/lean/Solutions').glob('*'):
 if p.is_file():(out/'olean/Solutions'/p.name).symlink_to(p)
for module in missing:
 rel=pathlib.Path(*module.split('.')).with_suffix('.lean');shutil.copy2(r/rel,out/'live'/rel)
lean='/workspace/scratch/5f2524fd4117/lean-tools/lean-4.33.1-linux/bin/lean'; env=os.environ.copy();env['PATH']=str(pathlib.Path(lean).parent)+':'+env['PATH'];env['LEAN_NUM_THREADS']='1'
basepath=subprocess.check_output([str(pathlib.Path(lean).parent/'lake'),'env','printenv','LEAN_PATH'],cwd=r,env=env,text=True).strip();env['LEAN_PATH']=str(out/'olean')+':'+basepath
prefix=['flock',str(r/'.lake/global-lean-locks/1.lock'),lean,'-j1','-DautoImplicit=false','-DwarningAsError=true']
state={'state':'running','kind':'recovered complete verification; not original Lake exit zero','original_attempt':'terminal unknown after exec-server transport disconnection','source_commit':manifest['source_commit'],'frozen_modules':len(manifest['roots']),'original_built':len(done),'isolated_missing':missing,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':[]}
def save(): (out/'status.json').write_text(json.dumps(state,indent=2)+'\n')
def run(label,cmd):
 log=out/(label+'.log');rec={'label':label,'command':cmd,'start_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};state['checks'].append(rec);save()
 with log.open('w') as f:
  f.write('COMMAND '+json.dumps(cmd)+'\n');f.flush();p=subprocess.run(cmd,cwd=r,env=env,stdout=f,stderr=subprocess.STDOUT);f.write('\nEXIT_CODE='+str(p.returncode)+'\n')
 rec.update(exit_code=p.returncode,finish_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());save()
 if p.returncode:raise RuntimeError(label+' failed')
save()
try:
 for module in missing:
  rel=pathlib.Path(*module.split('.'));run(module.split('.')[-1]+'-source',prefix+['-R',str(out/'live'),'-o',str((out/'olean'/rel).with_suffix('.olean')),str((out/'live'/rel).with_suffix('.lean'))])
 roots=[m for m in manifest['roots'] if not m.startswith('Solutions.')]
 p=out/'FrozenTheoremsReadback.lean';p.write_text(''.join('import '+m+'\n' for m in roots)+'\n#check StickyKakeya4.sticky_kakeya_four_dimensional\n#print axioms StickyKakeya4.sticky_kakeya_four_dimensional\n')
 run('frozen-theorem-aggregate',prefix+[str(p)])
 for module in [m for m in manifest['roots'] if m.startswith('Solutions.')]:
  p=out/(module.split('.')[-1]+'Readback.lean');p.write_text('import '+module+'\n#check Nat\n');run(module.split('.')[-1]+'-import',prefix+[str(p)])
 changes=[m for m,e in manifest['sources'].items() if hashlib.sha256((r/e['path']).read_bytes()).hexdigest()!=e['sha256']]
 assert not changes,changes
 artifacts={}
 for module in manifest['roots']:
  rel=pathlib.Path(*module.split('.')).with_suffix('.olean');p=(out/'olean'/rel if module in missing else r/'.lake/build/lib/lean'/rel)
  assert p.exists(),str(p);artifacts[module]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
 (out/'artifact-manifest.json').write_text(json.dumps(artifacts,indent=2)+'\n');state.update(state='passed',changed_sources=[],artifact_count=len(artifacts),finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
except Exception as exc:state.update(state='failed',error=str(exc),finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());save();raise
save();print(json.dumps({k:v for k,v in state.items() if k!='checks'},indent=2))
