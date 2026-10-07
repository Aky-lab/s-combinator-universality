"""Trusted per-invocation guard inside the isolated PID/proc namespace."""
import json,os,signal,subprocess,sys,time
from pathlib import Path
name,seconds,cap,*command=sys.argv[1:];seconds=float(seconds);cap=int(cap)
start=time.monotonic();peak=virtual_peak=0;reason=None;process=None
try:
 process=subprocess.Popen(command,stdin=subprocess.DEVNULL,close_fds=True)
 while process.poll() is None:
  rss=virtual=count=0
  for p in Path('/proc').iterdir():
   if not p.name.isdigit():continue
   try:
    fields={line.split(':',1)[0]:line.split(':',1)[1].strip() for line in (p/'status').read_text().splitlines() if ':' in line}
    rss+=int(fields.get('VmRSS','0 kB').split()[0])*1024
    virtual+=int(fields.get('VmSize','0 kB').split()[0])*1024;count+=1
   except FileNotFoundError:pass
  peak=max(peak,rss);virtual_peak=max(virtual_peak,virtual)
  if rss>cap:reason='sampled aggregate RSS cap'
  if count>128:reason='process count cap'
  if time.monotonic()-start>seconds:reason='wall clock cap'
  if reason:process.kill();break
  time.sleep(0.05)
 code=process.wait() if reason is None else 124
finally:
 if process is not None and process.poll() is None:process.kill();process.wait()
 report={'command':command,'exit_code':locals().get('code',125),'stop_reason':reason,'elapsed_seconds':time.monotonic()-start,'sampled_peak_namespace_rss_bytes':peak,'sampled_peak_namespace_virtual_bytes':virtual_peak,'sampled_namespace_rss_cap_bytes':cap,'sample_interval_seconds':0.05}
 Path('/work/guard-'+name+'.json').write_text(json.dumps(report,indent=2)+'\n')
 print('RESOURCE_GUARD '+json.dumps(report),flush=True)
raise SystemExit(code)
