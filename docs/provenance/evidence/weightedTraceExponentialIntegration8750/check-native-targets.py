from pathlib import Path
import json,re
root=Path.cwd();e=Path(__file__).resolve().parent;names=(root/'blueprint/lean_decls').read_text().splitlines()
expected=['Matrix.PosSemidef.re_trace_mul_exp_add_le_half_sum']
for name in expected:assert names.count(name)==1,(name,names.count(name))
fragment='weighted_trace_exponential';inputs=[]
for p in [root/'blueprint/src/content.tex',*sorted((root/'blueprint/src/chapter').glob('*.tex'))]:
 if '\\input{fragment/'+fragment+'}' in p.read_text():inputs.append(str(p.relative_to(root)))
assert inputs==['blueprint/src/chapter/ch13_schur_labels.tex'],inputs
active=set(re.findall(r"\\lean\{([^}]+)\}",(root/'blueprint/src/fragment'/ (fragment+'.tex')).read_text()));assert active==set(expected)
(e/'native-targets.json').write_text(json.dumps({'declaration_lines':len(names),'unique_declarations':len(set(names)),'owned_declarations':expected,'unique_fragment_input':inputs,'each_occurs_once':True},indent=2)+'\n')
print('Native declarations:',len(names),'; the owned target and unique chapter input checked.')
