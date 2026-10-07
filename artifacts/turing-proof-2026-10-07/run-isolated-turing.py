from pathlib import Path
import importlib.util,os,subprocess,json,sys
B=Path('/workspace/shared/s-formal-replay');src=B/'work/turing-20261007T0300-src';out=B/'work/turing-20261007T0300-build'
spec=importlib.util.spec_from_file_location('isolation',B/'run_isolated_universality.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
stage=sys.argv[1]
command={'build':['/usr/bin/python3','/src/BuildTuring.py'],'audit':['/opt/lean/bin/lean','-j2','-M2048','/src/SOnlyTuringUniversalityAudit.lean'],'replay':['/opt/lean/bin/leanchecker','--fresh','-v','SOnlyTuringUniversalityReplay']}[stage]
fd=m.filter_fd()
receipt=out/(stage+'-receipts'); receipt.mkdir(exist_ok=True)
search='/work:/deps' if stage=='build' else '/proof:/deps'
mount=['--bind',str(out),'/work'] if stage=='build' else ['--ro-bind',str(out),'/proof','--bind',str(receipt),'/work']
args=['/usr/bin/bwrap','--unshare-user','--unshare-pid','--unshare-uts','--unshare-ipc','--die-with-parent','--new-session','--cap-drop','ALL','--clearenv','--setenv','PATH','/opt/lean/bin:/usr/bin:/bin','--setenv','HOME','/tmp','--setenv','TMPDIR','/tmp','--setenv','LEAN_NUM_THREADS','2','--setenv','LEAN_SYSROOT','/opt/lean','--setenv','LEAN_PATH',search,'--ro-bind','/usr','/usr','--ro-bind','/lib','/lib','--ro-bind','/lib64','/lib64','--proc','/proc','--dev','/dev','--tmpfs','/tmp','--ro-bind',str(m.TOOLCHAIN),'/opt/lean','--ro-bind',str(src),'/src','--ro-bind',str(B/'work/.lake/build/lib/lean'),'/deps',*mount,'--ro-bind',str(B/'work/ResourceGuard.py'),'/ResourceGuard.py','--chdir','/src','--seccomp',str(fd),'/usr/bin/python3','/ResourceGuard.py','turing-'+stage,'600','4294967296',*command]
try:
 with (out/('turing-'+stage+'.txt')).open('w') as log:
  r=subprocess.run(args,pass_fds=(fd,),env={},stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,preexec_fn=m.limits,timeout=660)
 (out/('turing-'+stage+'-run.json')).write_text(json.dumps({'exit_code':r.returncode,'stage':stage,'command':command},indent=2)+'\n')
 print('EXIT',r.returncode);print((out/('turing-'+stage+'.txt')).read_text()[-3500:])
finally:os.close(fd)
raise SystemExit(r.returncode)
