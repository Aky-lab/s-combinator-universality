"""Run the approved pinned proof check with public-only mounts and no sockets."""
import errno,json,os,platform,resource,struct,subprocess,sys,time
from pathlib import Path
BASE=Path('/workspace/shared/s-formal-replay')
TOOLCHAIN=BASE/'toolchain/lean-4.33.1-linux'
if platform.machine()!='x86_64': raise SystemExit('Unsupported seccomp architecture')
def filter_fd():
 LD,EQ,GE,RET=0x20,0x15,0x35,0x06
 ALLOW,DENY,KILL=0x7fff0000,0x00050000|errno.EPERM,0x80000000
 rules=[(LD,0,0,4),(EQ,1,0,0xc000003e),(RET,0,0,KILL),(LD,0,0,0),(GE,0,1,0x40000000),(RET,0,0,DENY)]
 deny={41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,101,155,165,166,248,249,250,272,288,299,303,304,307,308,310,311,425,426,427,438}
 for n in sorted(deny):rules.extend(((EQ,0,1,n),(RET,0,0,DENY)))
 rules.append((RET,0,0,ALLOW))
 fd=os.memfd_create('formal-replay-seccomp',os.MFD_CLOEXEC)
 os.write(fd,b''.join(struct.pack('HBBI',*row) for row in rules));os.lseek(fd,0,0)
 return fd

def limits():
 resource.setrlimit(resource.RLIMIT_AS,(32*1024**3,32*1024**3))
 resource.setrlimit(resource.RLIMIT_CORE,(0,0))
 resource.setrlimit(resource.RLIMIT_STACK,(64*1024**2,64*1024**2))

def process_totals(pid):
 pending=[pid]; seen=set(); rss=vsize=threads=0
 while pending:
  current=pending.pop()
  if current in seen:continue
  seen.add(current)
  if len(seen)>512:raise RuntimeError('process-count monitor cap')
  proc=Path('/proc')/str(current)
  try:
   fields={line.split(':',1)[0]:line.split(':',1)[1].strip() for line in (proc/'status').read_text().splitlines() if ':' in line}
   rss+=int(fields.get('VmRSS','0 kB').split()[0])*1024
   vsize+=int(fields.get('VmSize','0 kB').split()[0])*1024
   threads+=int(fields.get('Threads','0'))
   for task in (proc/'task').iterdir():
    try:pending.extend(int(x) for x in (task/'children').read_text().split())
    except FileNotFoundError:pass
  except FileNotFoundError:continue
 return rss,vsize,threads,len(seen)

def run(name,command,seconds):
 assert name and all(x.isalnum() or x in '-_' for x in name)
 fd=filter_fd()
 argv=['/usr/bin/bwrap','--unshare-user','--unshare-pid','--unshare-uts','--unshare-ipc','--die-with-parent','--new-session','--cap-drop','ALL','--clearenv',
       '--setenv','PATH','/opt/lean/bin:/usr/bin:/bin','--setenv','HOME','/work/home','--setenv','TMPDIR','/tmp','--setenv','LEAN_NUM_THREADS','2',
       '--setenv','LEAN_SYSROOT','/opt/lean','--setenv','LEAN_PATH','/work/.lake/build/lib/lean:/work/formal-build',
       '--ro-bind','/usr','/usr','--ro-bind','/lib','/lib','--ro-bind','/lib64','/lib64','--proc','/proc','--dev','/dev','--tmpfs','/tmp',
       '--ro-bind',str(TOOLCHAIN),'/opt/lean','--bind',str(BASE/'work'),'/work']
 source=BASE/'source'
 if source.exists():
  argv.extend(('--ro-bind',str(source/'PureSFormal'),'/work/PureSFormal'))
  for config in ('lakefile.toml','lake-manifest.json','lean-toolchain'):
   argv.extend(('--ro-bind',str(source/config),'/work/'+config))
 if (BASE/'freeze-build').exists():
  argv.extend(('--ro-bind',str(BASE/'work/.lake/build/lib/lean'),'/work/.lake/build/lib/lean'))
 if (BASE/'freeze-formal').exists():
  argv.extend(('--ro-bind',str(BASE/'work/formal-build'),'/work/formal-build'))
  argv.extend(('--ro-bind',str(BASE/'work/SOnly38.lean'),'/work/SOnly38.lean'))
 for helper in ('ResourceGuard.py','SOnlyGenericReplay.lean','SOnlyTypeAudit.lean'):
  argv.extend(('--ro-bind',str(BASE/'work'/helper),'/work/'+helper))
 argv.extend(('--ro-bind',str(BASE/'work/bridges-20261007T0043'),'/work/bridges-20261007T0043'))
 argv.extend(('--chdir','/work','--seccomp',str(fd),*command))
 log=BASE/'logs'/f'{name}.log';start=time.monotonic();status=None;reason=None
 peak_rss=peak_virtual=peak_threads=peak_processes=0
 try:
  with log.open('w') as out:
   process=subprocess.Popen(argv,pass_fds=(fd,),close_fds=True,env={},stdin=subprocess.DEVNULL,stdout=out,stderr=subprocess.STDOUT,preexec_fn=limits)
   while process.poll() is None:
    try:
     rss,virtual,threads,count=process_totals(int(os.readlink("/proc/self")))
     peak_rss=max(peak_rss,rss);peak_virtual=max(peak_virtual,virtual)
     peak_threads=max(peak_threads,threads);peak_processes=max(peak_processes,count)
     if rss>4*1024**3:reason='launcher sampled RSS budget'
     if time.monotonic()-start>seconds:reason='wall-clock budget'
    except (OSError,RuntimeError) as error:reason='monitor failure: '+str(error)
    if reason:
     process.kill();process.wait();break
    time.sleep(0.05)
   status=process.wait() if reason is None else 124
 finally:os.close(fd)
 report={'name':name,'command':command,'exit_code':status,'stop_reason':reason,'elapsed_seconds':time.monotonic()-start,'sampled_peak_aggregate_rss_bytes':peak_rss,'sampled_peak_aggregate_virtual_bytes':peak_virtual,'sampled_peak_threads':peak_threads,'sampled_peak_processes':peak_processes,'timeout_seconds':seconds,'per_process_address_space_cap_bytes':32*1024**3,'outer_monitor_scope':'launcher only; namespace RSS is enforced by ResourceGuard when used','monitor_interval_seconds':0.05,'lean_num_threads_environment':2}
 (BASE/'logs'/f'{name}.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(report),flush=True);print(log.read_text()[-10000:],flush=True)
 return status
if __name__=='__main__':
 name,seconds,*command=sys.argv[1:]
 raise SystemExit(run(name,command,int(seconds)))
