from pathlib import Path
import json,subprocess,time,os
src=Path('/work/universality-20261007T0209-src');out=Path('/work/universality-20261007T0209-build');manifest=json.loads((src/'source-manifest.json').read_text());rows=[]
for name in manifest['order']+['SOnlyUniversalityReplay']:
 start=time.monotonic();result=subprocess.run(['/opt/lean/bin/lean','-j2','-M1536','-o',str(out/(name+'.olean')),str(src/(name+'.lean'))],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(out/(name+'.log')).write_text(result.stdout);rows.append({'module':name,'exit_code':result.returncode,'seconds':time.monotonic()-start});(out/'build-records.json').write_text(json.dumps(rows,indent=2)+'\n');print(name,result.returncode,flush=True)
 if result.returncode:print(result.stdout,flush=True);raise SystemExit(result.returncode)
