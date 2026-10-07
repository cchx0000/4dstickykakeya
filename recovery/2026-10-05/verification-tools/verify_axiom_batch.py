#!/usr/bin/env python3
"""Independently import strictly source-checked modules once; preserve per-module audits."""
import argparse,datetime,hashlib,json,os,pathlib,re,shutil,subprocess
from staging_overlay import prepare_overlay
p=argparse.ArgumentParser();p.add_argument('attempt_dirs',nargs='+',type=pathlib.Path);args=p.parse_args()
r=pathlib.Path('/workspace/scratch/5f2524fd4117/4dstickykakeya');w=pathlib.Path('/workspace/shared/sticky-recovery-20261005');tool='/workspace/scratch/5f2524fd4117/lean-tools/lean-4.33.1-linux/bin'
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
hashfile=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
entries=[];modules=set();names=set()
for d in args.attempt_dirs:
 d=d.resolve();d.relative_to(w/'verification');s=json.loads((d/'result.json').read_text())
 assert s['state']=='source_passed' and s['source_exit_code']==0 and s['independent_axiom_audit_pending']
 src=pathlib.Path(s['source']);out=pathlib.Path(s.get('olean_path',w/'olean'/pathlib.Path(*s['module'].split('.')).with_suffix('.olean')))
 assert hashfile(src)==s['source_sha256'] and hashfile(out)==s['olean_sha256'];assert s['module'] not in modules;assert not(names&set(s['names']))
 modules.add(s['module']);names.update(s['names']);entries.append((d,s,src,out))
group=w/'verification'/('axiom-batch-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f'));group.mkdir()
readback=group/'AggregateReadback.lean';readback.write_text(''.join('import '+x[1]['module']+'\n' for x in entries)+'\nset_option autoImplicit false\n'+''.join('#print axioms '+n+'\n' for n in sorted(names)))
env=os.environ.copy();env['PATH']=tool+':'+env.get('PATH','');env['LEAN_NUM_THREADS']='1';leanpath=subprocess.check_output([tool+'/lake','env','printenv','LEAN_PATH'],cwd=r,env=env,text=True).strip();extra=json.loads((w/'extra-olean-roots.json').read_text()) if (w/'extra-olean-roots.json').exists() else [];env['LEAN_PATH']=':'.join(dict.fromkeys([*[s['olean_root'] for _,s,_,_ in entries if s.get('olean_root',str(w/'olean'))!=str(w/'olean')],*extra,str(w/'olean')]))+':'+leanpath
for root in dict.fromkeys([*[s['olean_root'] for _,s,_,_ in entries if s.get('olean_root',str(w/'olean'))!=str(w/'olean')],*extra]):
 prepare_overlay(w,pathlib.Path(root))
cmd=['flock',str(r/'.lake/global-lean-locks/1.lock'),tool+'/lean','-j1','-DautoImplicit=false','-DwarningAsError=true','-R',str(group),str(readback)]
manifest={'state':'running','started_utc':now(),'command':cmd,'readback_sha256':hashfile(readback),'modules':[{'module':s['module'],'source_sha256':s['source_sha256'],'olean_sha256':s['olean_sha256'],'names':s['names']} for _,s,_,_ in entries]};(group/'batch.json').write_text(json.dumps(manifest,indent=2)+'\n')
for d,s,_,_ in entries:
 s['state']='readback_running';s['axiom_batch']=str(group);(d/'result.json').write_text(json.dumps(s,indent=2)+'\n')
with (group/'axioms.log').open('w') as log:
 log.write('COMMAND '+json.dumps(cmd)+'\nREADBACK_SHA256 '+hashfile(readback)+'\n');log.flush();run=subprocess.run(cmd,cwd=r,env=env,stdout=log,stderr=subprocess.STDOUT);log.write('\nEXIT_CODE='+str(run.returncode)+'\n')
text=(group/'axioms.log').read_text();pairs=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",text,re.S);noax=re.findall(r"'([^']+)' does not depend on any axioms",text);ax={n:[a.strip() for a in raw.split(',') if a.strip()] for n,raw in pairs};ax.update({n:[] for n in noax});emitted=[n for n,_ in pairs]+noax;allowed={'propext','Classical.choice','Quot.sound'};all_pass=True
for d,s,src,out in entries:
 unchanged=hashfile(src)==s['source_sha256'] and hashfile(out)==s['olean_sha256'];s['readback_exit_code']=run.returncode;s['source_unchanged']=hashfile(src)==s['source_sha256'];s['artifact_unchanged']=unchanged;s['missing_names']=sorted(set(s['names'])-set(ax));s['duplicate_names']=[n for n in s['names'] if emitted.count(n)!=1 and n in ax];s['axioms']={n:ax[n] for n in s['names'] if n in ax};s['extra_axioms']={n:sorted(set(ax[n])-allowed) for n in s['names'] if n in ax and set(ax[n])-allowed};passed=run.returncode==0 and unchanged and not s['missing_names'] and not s['duplicate_names'] and not s['extra_axioms'];s['state']='passed' if passed else 'failed';s['independent_axiom_audit_pending']=False;s['executor_finished_utc']=now();all_pass &= passed
 for f in ['AggregateReadback.lean','axioms.log','batch.json']:shutil.copy2(group/f,d/f)
 (d/'result.json').write_text(json.dumps(s,indent=2)+'\n')
manifest.update(state='passed' if all_pass else 'failed',finished_utc=now(),exit_code=run.returncode);(group/'batch.json').write_text(json.dumps(manifest,indent=2)+'\n')
for d,_,_,_ in entries:shutil.copy2(group/'batch.json',d/'batch.json')
print(json.dumps({'group':str(group),'state':manifest['state'],'modules':len(entries),'declarations':len(names),'exit_code':run.returncode},indent=2));raise SystemExit(0 if all_pass else 1)
