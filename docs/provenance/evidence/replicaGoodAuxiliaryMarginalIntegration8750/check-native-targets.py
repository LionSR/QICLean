from pathlib import Path
import json,re
root=Path.cwd();e=Path(__file__).resolve().parent
names=(root/'blueprint/lean_decls').read_text().splitlines();expected=['TensorPower.goodBadCopiesEquiv','Matrix.replicaGoodAuxiliaryMarginal','Matrix.commute_replicaGoodAuxiliaryMarginal_copyPerm']
for name in expected:assert names.count(name)==1,(name,names.count(name))
fragment='replica_good_auxiliary_marginal';inputs=[]
for p in [root/'blueprint/src/content.tex',*sorted((root/'blueprint/src/chapter').glob('*.tex'))]:
 if '\\input{fragment/'+fragment+'}' in p.read_text():inputs.append(str(p.relative_to(root)))
assert inputs==['blueprint/src/chapter/ch12_entropy.tex'],inputs
active=set(re.findall(r"\\lean\{([^}]+)\}",(root/'blueprint/src/fragment'/ (fragment+'.tex')).read_text()));assert active==set(expected)
(e/'native-targets.json').write_text(json.dumps({'declaration_lines':len(names),'unique_declarations':len(set(names)),'owned_declarations':expected,'unique_fragment_input':inputs,'each_occurs_once':True},indent=2)+'\n')
print('Native declarations:',len(names),'; all three owned targets and unique chapter input checked.')
