"""Fresh direct Lean elaboration in verified dependency order; no build hooks."""
import hashlib,json,os,re,subprocess,time
from pathlib import Path
work=Path('/work');source=work/'PureSFormal';out=work/'.lake/build/lib/lean';logs=work/'build-module-logs-second';logs.mkdir(exist_ok=False)
modules=json.loads((work/'build-modules.json').read_text());assert len(modules)==423 and len(set(modules))==423
assert (out/'PureSFormal').exists()
start=time.monotonic();records=json.loads((work/'build-progress-first.json').read_text())['records'][:38]
assert all(x['exit_code']==0 for x in records)
for row in records:
 old=out/(row['module'].replace('.','/')+'.olean');assert old.is_file()
 row['reused_fresh_attempt_1']=True;row['olean_sha256_before_resume']=hashlib.sha256(old.read_bytes()).hexdigest()
for index,module in enumerate(modules[38:],39):
 assert re.fullmatch(r'PureSFormal(?:\.[A-Za-z_][A-Za-z_0-9]*)+',module)
 relative=Path(module.replace('.','/'));input=work/(str(relative)+'.lean');output=out/(str(relative)+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
 command=['/opt/lean/bin/lean','-j2','-M3072','-o',str(output),str(input)]
 begun=time.monotonic();timed_out=False
 with (logs/(module+'.log')).open('w') as log:
  try:result=subprocess.run(command,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,close_fds=True,timeout=300);status=result.returncode
  except subprocess.TimeoutExpired:status=124;timed_out=True
 record={'module':module,'exit_code':status,'seconds':time.monotonic()-begun,'timed_out':timed_out}
 records.append(record)
 (work/'build-progress.json').write_text(json.dumps({'completed':index,'total':len(modules),'elapsed_seconds':time.monotonic()-start,'last':record,'records':records},indent=2)+'\n')
 print(f'{index}/{len(modules)} {module}: exit={status} {record["seconds"]:.3f}s',flush=True)
 if status or not output.is_file():raise SystemExit(status or 125)
print('BUILD_COMPLETE '+json.dumps({'modules':len(modules),'elapsed_seconds':time.monotonic()-start}),flush=True)
