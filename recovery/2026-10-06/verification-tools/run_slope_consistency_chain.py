from pathlib import Path
import json,subprocess,sys,datetime
w=Path('/workspace/shared/sticky-recovery-20261006')
items=[('noisy_affine_image_count','NoisyAffineImageCount'),
 ('scalar_katz_tao_slope_bound','ScalarKatzTaoSlopeBound'),
 ('nested_plane_quantization','NestedPlaneQuantization'),
 ('native_same_point_slope_consistency','NativeSamePointSlopeConsistency')]
state={'scope':'first three sources exactly restored canonical prerequisites; last is new same-physical-point Step3 bridge','state':'running','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':[]}
def save():(w/'slope-consistency-chain-status.json').write_text(json.dumps(state,indent=2)+'\n')
save()
for stem,namespace in items:
 state['active']=stem;save()
 q=subprocess.run([sys.executable,str(w/'verify_recovered_source.py'),'--source',str(w/'live/Theorems'/('Thm_StickyKakeya4_'+stem+'.lean')),'--namespace',namespace,'--attempt','1','--slot','2'])
 state['checks'].append({'stem':stem,'exit_code':q.returncode});save()
 if q.returncode:state['state']='failed';save();sys.exit(q.returncode)
state['state']='passed';state['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
