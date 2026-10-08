from pathlib import Path
import hashlib,json,re
root=Path('/Users/siruilu/Local/agentFormalization/QICLean/worktrees/physical-trace-helpers');b=Path('/private/tmp/qic-physical-trace-helpers');b.mkdir(exist_ok=True);original=b/'original-sources';original.mkdir(exist_ok=True)
sha=lambda data:hashlib.sha256(data).hexdigest()
spec=[('PhysicalBasisInvariance','QICLean/Channel/PartialTraceBasisInvariance.lean','eq:compression-exterior-contraction',['Matrix.rectangularTraceNorm_partialTraceRight_isometries','OrthonormalBasis.tensorProduct_basisChange','OrthonormalBasis.tensorProduct_rankOne_basisChange','OrthonormalBasis.rectangularTraceNorm_partialTrace_sum_rankOne_basis_eq']),('PhysicalBlockTraceNorm','QICLean/Channel/PartialTraceBlocks.lean','eq:compression-total-error',['Matrix.eq_sum_single_kronecker_submatrix','Matrix.rectangularTraceNorm_le_sum_submatrix','Matrix.submatrix_partialTraceRight','Matrix.integral_rectangularTraceNorm_le_sum_submatrix'])]
rows=[];preserved=[]
for name,rel,label,names in spec:
 p=Path('/tmp')/(name+'.lean');data=p.read_bytes();(original/p.name).write_bytes(data);s=data.decode().replace('TNLean contributors','QICLean contributors')
 notice='/-!\nSource: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,\n'+label+'.\nManuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.\nIndependently formalized; no upstream Lean proof text reused.\n'
 for i,n in enumerate(names,1):
  ident='p09-qic-'+Path(rel).stem.lower()+f'-{i:02}';notice+=f'\nProvenance-ID: {ident}\nDownstream declaration:\n{n}\n';rows.append({'id':ident,'path':rel,'declaration':n,'paper_label':label})
 notice+='\n-/\n\n';s=s.replace('noncomputable section',notice+'noncomputable section',1);dst=root/rel;assert not dst.exists();dst.write_text(s);preserved.append({'path':rel,'original':p.name,'original_sha256':sha(data),'production_sha256':sha(dst.read_bytes()),'scope':'All noncomment tokens preserved.'})
chunks=[]
for name in ['GaussianSourceIntegrability','SourceGaussianMoments']:
 p=Path('/tmp')/(name+'.lean');data=p.read_bytes();(original/p.name).write_bytes(data);s=data.decode();chunks.append(s.split('namespace ProbabilityTheory\n',1)[1].split('end ProbabilityTheory',1)[0].strip())
rel='QICLean/Probability/MatrixTraceNormIntegrability.lean';label='eq:compression-block-second-moment';names=['ProbabilityTheory.integrable_rectangularTraceNorm_sum','ProbabilityTheory.integrable_rectangularTraceNorm_sum_of_memLp_two']
notice='/-!\nSource: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,\n'+label+'.\nManuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.\nIndependently formalized; no upstream Lean proof text reused.\n'
for i,n in enumerate(names,1):
 ident='p09-qic-matrixtracenormintegrability'+f'-{i:02}';notice+=f'\nProvenance-ID: {ident}\nDownstream declaration:\n{n}\n';rows.append({'id':ident,'path':rel,'declaration':n,'paper_label':label})
notice+='\n-/\n\n'
s='''/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.WeightedSourceError

/-!
# Integrability of finite matrix trace-norm sums

For a finite measure, pairwise integrable products of scalar coefficients give
an integrable trace norm for each finite fixed matrix combination. In particular,
square-integrability of every coefficient suffices. Independence and covariance
values are not required.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 434–549.
-/

'''+notice+'''noncomputable section
open MeasureTheory
open scoped Matrix ComplexConjugate

namespace ProbabilityTheory

'''+ '\n\n'.join(chunks)+'\n\nend ProbabilityTheory\n';dst=root/rel;assert not dst.exists();dst.write_text(s);preserved.append({'path':rel,'originals':['GaussianSourceIntegrability.lean','SourceGaussianMoments.lean'],'production_sha256':sha(dst.read_bytes()),'scope':'The two ProbabilityTheory theorem blocks preserve all noncomment tokens; TN-specific consumers are excluded.'})
(b/'declarations.json').write_text(json.dumps(rows,indent=2)+'\n');(b/'source-preservation.json').write_text(json.dumps({'base_revision':'b2521d2a2843d824ce85a4d94bf4b60d322d6c6f','sources':preserved},indent=2)+'\n')
old=json.loads(Path('/private/tmp/qic-source-transport-expansion/env.json').read_text());out=b/'artifacts';out.mkdir(exist_ok=True);chosen={}
for prefix in old['LEAN_PATH'].split(':'):
 p=Path(prefix)
 for f in [*p.glob('QICLean.*'),*((p/'QICLean').rglob('*') if (p/'QICLean').exists() else [])]:
  if f.is_file():chosen.setdefault(str(f.relative_to(p)),f)
for rel,p in chosen.items():
 t=out/rel;t.parent.mkdir(parents=True,exist_ok=True);assert not t.exists();t.symlink_to(p.resolve())
cfg={**old,'LEAN_PATH':str(out)+':'+':'.join(old['LEAN_PATH'].split(':')[1:]),'source_root':str(root),'output_root':str(out)};(b/'env.json').write_text(json.dumps(cfg,indent=2)+'\n');(b/'preparation.json').write_text(json.dumps({'base_revision':'b2521d2a2843d824ce85a4d94bf4b60d322d6c6f','read_only_links':len(chosen),'no_lake_directory':not (root/'.lake').exists()},indent=2)+'\n');print('PREPARED',len(rows),'DECLARATIONS',len(chosen),'READONLY LINKS')
