from pathlib import Path
import json,hashlib,sys
B=Path('/workspace/shared/s-formal-replay');src=B/'work/turing-20261007T0300-src';out=B/'work/turing-20261007T0300-build'
def check(root,rows):
 for r in rows:
  p=root/r['path'];b=p.read_bytes();assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'],str(p)
 return len(rows)
def row(p,root):
 b=p.read_bytes();return {'path':str(p.relative_to(root)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
manifest=json.loads((src/'source-manifest.json').read_text());counts={}
for name,root,file in [('pinned_sources',B/'source',B/'source-manifest.json'),('pinned_dependency_outputs',B/'work/.lake/build/lib/lean',B/'outputs-after-replay.json'),('official_toolchain',B/'toolchain',B/'toolchain-manifest.json')]:
 counts[name]=check(root,json.loads(file.read_text()))
counts['project_sources']=check(src,manifest['modules'])
# The older 56 live project files remain unchanged; 11 extension files are separately frozen.
live=Path('/workspace/shared/s-combinator-universality/formal');old=json.loads((B/'work/universality-20261007T0209-src/source-manifest.json').read_text())
counts['live_base_sources']=check(live,old['modules'])
counts['live_extension_sources']=check(Path('/workspace/shared/s-tm-extension'),[r for r in manifest['modules'] if r['module'] in manifest['extension_modules']])
identity=out/'source-output-identity.json'
if sys.argv[1]=='before':
 rows=[row(src/r['path'],src) | {'root':'source'} for r in manifest['modules']]
 rows.append(row(src/'SOnlyTuringUniversalityReplay.lean',src)|{'root':'source'})
 rows +=[row(p,out)|{'root':'output'} for p in sorted(out.glob('*.olean'))]
 assert len(rows)==136,len(rows)
 identity.write_text(json.dumps(rows,indent=2)+'\n')
else:
 rows=json.loads(identity.read_text())
 for r in rows: check(src if r['root']=='source' else out,[r])
counts['final_source_output_wrapper_files']=len(rows)
result={'all_checks_passed':True,'counts':counts,'phase':sys.argv[1]}
(out/(sys.argv[1]+'-integrity.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
