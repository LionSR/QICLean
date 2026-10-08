from pathlib import Path
import gzip,hashlib,json,re,subprocess
r=Path.cwd();p=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):return p.read_bytes() if p.exists() else gzip.decompress(Path(str(p)+'.gz').read_bytes())
f=json.loads((p/'source-freeze.json').read_text())
for row in f['files']:
 b=(r/row['path']).read_bytes();assert sha(b)==row['sha256'];assert b==subprocess.check_output(['git','show',f['source_revision']+':'+row['path']])
for row in json.loads((p/'historical-bindings.json').read_text()):assert sha(read(r/row['path']))==row['sha256']
original=(p/'historical/lower-pin/LowerPin.lean').read_bytes();freeze=json.loads((p/'historical/lower-pin/freeze.json').read_text());assert sha(original)==freeze['source_sha256']
assert sha((p/'historical/lower-pin-approved-env.json').read_bytes())==freeze['approved_environment_sha256']
def body(text,name):
 start=re.search(r'^theorem '+re.escape(name)+r'\b',text,re.M).start();s=text[start:];stop=re.search(r'\n(?:/-|end\b|namespace\b|(?:private )?(?:theorem|lemma|def)\b)',s)
 if stop:s=s[:stop.start()]
 return s.split(':= by',1)[1].strip()
current=(r/'QICLean/Analysis/InverseCompressionLowerBound.lean').read_text()
for name in ['mul_conjTranspose_le_smul_one_of_conjTranspose_mul_le','PosDef.inv_smul_projection_le_of_compression_inv_le']:assert body(current,name)==body(original.decode(),name),name
for path in ['QICLean/Analysis/InverseCompressionLowerBound.lean','QICLean/Analysis/SpectralExponentialDrop.lean']:assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafeCast)\b',(r/path).read_text())
original_revision=json.loads((p/'source-freeze-original.json').read_text())['source_revision']
for row in f['files']:
 old=subprocess.check_output(['git','show',original_revision+':'+row['path']])
 now=(r/row['path']).read_bytes()
 if row['path']=='QICLean/Analysis/InverseCompressionLowerBound.lean':
  assert now==old.decode().replace('`A⁻¹ᐟ² * P`','the inverse square root of A times P').encode()
 else:assert now==old
reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(p/'corrected-axioms.log').read_text(),re.S)
assert [n for n,_ in reports]==json.loads((p/'declarations.json').read_text())
for n,ax in reports:assert [s.strip() for s in ax.split(',')]==['propext','Classical.choice','Quot.sound'],n
print('Seven frozen source files, original lower-pin proof bodies/environment, historical text bindings, four exact standard-only kernel reports and integrity all pass.')
