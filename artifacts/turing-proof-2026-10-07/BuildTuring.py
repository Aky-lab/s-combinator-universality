from pathlib import Path
import json,subprocess,time
src=Path('/src');out=Path('/work');manifest=json.loads((src/'source-manifest.json').read_text());rows=[]
for name in manifest['order']+['SOnlyTuringUniversalityReplay']:
 start=time.monotonic();r=subprocess.run(['/opt/lean/bin/lean','-j2','-M1536','-o',str(out/(name+'.olean')),str(src/(name+'.lean'))],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(out/(name+'.log')).write_text(r.stdout);rows.append({'module':name,'exit_code':r.returncode,'seconds':time.monotonic()-start});(out/'build-records.json').write_text(json.dumps(rows,indent=2)+'\n');print(name,r.returncode,flush=True)
 if r.returncode:print(r.stdout,flush=True);raise SystemExit(r.returncode)
