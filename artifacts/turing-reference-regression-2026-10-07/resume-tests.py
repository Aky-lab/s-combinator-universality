from pathlib import Path
import sys,unittest,re,json,time,hashlib
root=Path('/workspace/shared/s-combinator-universality');sys.path.insert(0,str(root));sys.path.insert(0,str(root/'tests'))
log=Path('/tmp/s-turing-all-tests.log').read_text()
headers=list(re.finditer(r'^(test\S+) \(([^)]+)\)(.*)$',log,re.M));done=[];pending=[]
for i,m in enumerate(headers):
 ident=m.group(2) if m.group(2).endswith('.'+m.group(1)) else m.group(2)+'.'+m.group(1)
 tail=log[m.end():headers[i+1].start() if i+1<len(headers) else len(log)]
 result=m.group(3).strip()
 if re.search(r'\.\.\. ok$|^ok$',m.group(3)+tail,re.M):done.append(ident)
 elif result.startswith('skipped '):raise AssertionError(('unexpected skip',ident,result))
 elif result in ['FAIL','ERROR'] or re.search(r'^(FAIL|ERROR)$',tail,re.M):raise AssertionError(('failed case before interruption',ident))
 else:pending.append(ident)
def flatten(suite):
 for x in suite:
  if isinstance(x,unittest.TestSuite):yield from flatten(x)
  else:yield x
cases=list(flatten(unittest.defaultTestLoader.discover(str(root/'tests'))));ids=[t.id() for t in cases]
assert len(ids)==721,len(ids)
assert done==ids[:len(done)],(len(done),next(((a,b) for a,b in zip(done,ids) if a!=b),None))
assert pending==ids[len(done):len(done)+len(pending)],pending
state={'total_test_methods':721,'completed_before_interruption':len(done),'remaining':len(cases)-len(done),'prefix_log':'/tmp/s-turing-all-tests.log','prefix_sha256':hashlib.sha256(Path('/tmp/s-turing-all-tests.log').read_bytes()).hexdigest(),'first_resumed_test':ids[len(done)],'last_resumed_test':ids[-1],'prefix_had_no_terminal_summary':True,'prefix_process_id_unavailable_after_runtime_interruption':True,'status':'running'}
out=Path('/workspace/shared/s-turing-test-resume.json');out.write_text(json.dumps(state,indent=2)+'\n');print(json.dumps(state),flush=True)
begin=time.monotonic();result=unittest.TextTestRunner(verbosity=2).run(unittest.TestSuite(cases[len(done):]));state.update(status='passed' if result.wasSuccessful() else 'failed',resumed_test_count=result.testsRun,resumed_seconds=time.monotonic()-begin,failures=len(result.failures),errors=len(result.errors),all_721_test_methods_passed=result.wasSuccessful() and result.testsRun==state['remaining']);out.write_text(json.dumps(state,indent=2)+'\n');sys.exit(0 if result.wasSuccessful() else 1)
