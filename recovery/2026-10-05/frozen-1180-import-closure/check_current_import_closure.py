import datetime,hashlib,json,os,pathlib,subprocess
w=pathlib.Path('/workspace/shared/sticky-recovery-20261005');r=pathlib.Path('/workspace/scratch/5f2524fd4117/4dstickykakeya');out=w/'frozen-1180-import-closure-attempt03';out.mkdir(exist_ok=False)
hashfile=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((w/'recovered-frozen-1020/artifact-manifest.json').read_text());oldsrc=json.loads((w/'frozen-full-source-manifest.json').read_text())['sources'];oldstatus=json.loads((w/'recovered-frozen-1020/status.json').read_text());assert oldstatus['state']=='passed'
verified={}
for p in (r/'recovery/2026-10-05/verified').glob('*/result.json'):
 d=json.loads(p.read_text())
 if 'module' in d:verified[d['module']]=d
roots={'.'.join(p.relative_to(r).with_suffix('').parts):p for folder in ['Definitions','Theorems','Solutions'] for p in (r/folder).glob('*.lean')};assert len(roots)==1180,len(roots)
entries={};overlay=out/'olean';overlay.mkdir()
for m,src in sorted(roots.items()):
 sh=hashfile(src)
 if m in old:
  assert sh==oldsrc[m]['sha256'];art=pathlib.Path(old[m]['path']);ah=old[m]['sha256'];proof='recovered-frozen-1020'
 else:
  d=verified[m];assert d['state']=='passed' and sh==d['source_sha256'] and not d['extra_axioms'] and not d['missing_names'];art=pathlib.Path(d.get('olean_path',w/'olean'/pathlib.Path(*m.split('.')).with_suffix('.olean')));ah=d['olean_sha256'];proof=d.get('axiom_batch','individual imported audit in canonical verified record')
 assert hashfile(art)==ah,(m,'artifact changed')
 rel=pathlib.Path(*m.split('.'));dst=overlay/rel;dst.parent.mkdir(exist_ok=True)
 artifacts={}
 for ext in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  p=art.with_suffix(ext)
  if p.exists():dst.with_suffix(ext).symlink_to(p);artifacts[ext]={'path':str(p),'sha256':hashfile(p)}
 entries[m]={'source':str(src),'source_sha256':sh,'artifacts':artifacts,'source_and_import_gate':proof}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip();state={'state':'running','source_commit':head,'module_count':len(entries),'kind':'unified import closure of individually source-verified immutable artifacts; not a new Lake full build','prior_solutions':'8 unchanged source/artifact roots retain recovered1020 independent import results','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(out/'manifest.json').write_text(json.dumps(entries,indent=2)+'\n');(out/'status.json').write_text(json.dumps(state,indent=2)+'\n')
p=out/'AllCurrentTheorems.lean';p.write_text(''.join('import '+m+'\n' for m in roots if not m.startswith('Solutions.'))+'\n#print axioms StickyKakeya4.sticky_kakeya_four_dimensional\n#print axioms NativeFixedZeroOriginalTheorem.sticky_kakeya_four_dimensional_of_fixed_zero\n')
tool='/workspace/scratch/5f2524fd4117/lean-tools/lean-4.33.1-linux/bin';env=os.environ.copy();env['PATH']=tool+':'+env['PATH'];env['LEAN_NUM_THREADS']='1';base=subprocess.check_output([tool+'/lake','env','printenv','LEAN_PATH'],cwd=r,env=env,text=True).strip();env['LEAN_PATH']=str(overlay)+':'+base
cmd=['flock',str(r/'.lake/global-lean-locks/1.lock'),tool+'/lean','-j1','-DautoImplicit=false','-DwarningAsError=true',str(p)];state['command']=cmd
with (out/'import.log').open('w') as log:
 log.write('COMMAND '+json.dumps(cmd)+'\n');log.flush();run=subprocess.run(cmd,cwd=r,env=env,stdout=log,stderr=subprocess.STDOUT);log.write('\nEXIT_CODE='+str(run.returncode)+'\n')
changes=[]
for m,d in entries.items():
 if hashfile(pathlib.Path(d['source']))!=d['source_sha256']:changes.append(m+':source')
 for ext,a in d['artifacts'].items():
  if hashfile(pathlib.Path(a['path']))!=a['sha256']:changes.append(m+ext)
state.update(state='passed' if run.returncode==0 and not changes else 'failed',exit_code=run.returncode,changed_sources_or_artifacts=changes,finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat());(out/'status.json').write_text(json.dumps(state,indent=2)+'\n');print(json.dumps(state,indent=2));raise SystemExit(0 if state['state']=='passed' else 1)
