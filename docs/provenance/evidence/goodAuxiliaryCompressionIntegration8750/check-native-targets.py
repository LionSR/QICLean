from pathlib import Path
import json
root=Path.cwd();e=root/'docs/provenance/evidence/goodAuxiliaryCompressionIntegration8750';text=(root/'blueprint/lean_decls').read_text();names=text.splitlines();expected=['TensorPower.copyPerm_groupedGood_labelEntropy_compression','Matrix.replicaExcitationComponent_goodAuxiliary_labelEntropy_lower']
for name in expected:assert names.count(name)==1,(name,names.count(name))
fragments=['good_auxiliary_label_compression','replica_good_auxiliary_label_bound']
content=(root/'blueprint/src/content.tex').read_text()
for f in fragments:assert content.count('\\input{fragment/'+f+'}')==1
(e/'native-targets.json').write_text(json.dumps({'declaration_lines':len(names),'unique_declarations':len(set(names)),'owned_declarations':expected,'fragment_inputs':fragments,'each_occurs_once':True},indent=2)+'\n');print('Native declaration lines:',len(names),'; both owned declarations and fragment inputs occur exactly once.')
