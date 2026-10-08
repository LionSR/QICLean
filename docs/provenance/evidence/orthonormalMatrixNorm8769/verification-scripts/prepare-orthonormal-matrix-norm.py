from pathlib import Path
import hashlib,json,os,re,shutil
root=Path('/Users/siruilu/Local/agentFormalization/QICLean/worktrees/orthonormal-matrix-norm');out=Path('/private/tmp/qic-orthonormal-matrix-norm');out.mkdir(exist_ok=True);art=out/'artifacts';art.mkdir(exist_ok=True)
src=Path('/tmp/OrthonormalMatrixNorm.lean');assert hashlib.sha256(src.read_bytes()).hexdigest()=='5a573d1fe0ad1a2cb8032ca839cafc434a5757445a800a6bef3f82783bb9182f'
text=src.read_text();notice='''/-
Provenance-ID: p09-qic-orthonormal-matrix-norm
Downstream declaration: ContinuousLinearMap.norm_toMatrix_orthonormal
Source: September 24, 2026.
Label: eq:compression-exterior-contraction
A general coordinate identity used in the proof of polynomial-PEPS Theorem 5.2.
Independently formalized; no upstream Lean proof text reused.
-/
''';text=text.replace('theorem norm_toMatrix_orthonormal',notice+'theorem norm_toMatrix_orthonormal');target=root/'QICLean/Analysis/OrthonormalMatrixNorm.lean';assert not target.exists();target.write_text(text)
chapter=root/'blueprint/src/chapter/ch01_orthonormal_matrix_norm.tex';chapter.write_text(r'''\section{Operator norms in orthonormal coordinates}

\begin{theorem}[Operator norm in orthonormal coordinates]
    \label{thm:operator_norm_orthonormal_coordinates}
    \lean{ContinuousLinearMap.norm_toMatrix_orthonormal}
    \leanok
    Let $E$ and $F$ be inner-product spaces over $\mathbb K=\R$ or $\C$,
    with finite orthonormal bases $(e_j)_{j\in J}$ and $(f_i)_{i\in I}$.
    For a continuous linear map $T:E\to F$, let
    $M_{ij}=\langle f_i,Te_j\rangle$ be its matrix in these bases.
    The Euclidean operator norm of $M$ equals the operator norm of $T$:
    $\|M\|_{2\to2}=\|T\|$.
    The two basis index sets may have different cardinalities, and either
    may be empty.
\end{theorem}

\begin{proof}\leanok
    Let $U:E\to\mathbb K^J$ and $V:F\to\mathbb K^I$ be the coordinate
    isometries. The linear map represented by $M$ is $VTU^{-1}$.
    Composition on either side with a surjective linear isometry preserves
    the operator norm, so $\|M\|_{2\to2}=\|VTU^{-1}\|=\|T\|$.
\end{proof}
''')
p=root/'blueprint/src/chapter/ch01_deconstructing_quantum.tex';s=p.read_text().replace('\\input{chapter/ch01_states}','\\input{chapter/ch01_states}\n\\input{chapter/ch01_orthonormal_matrix_norm}');p.write_text(s)
p=root/'docs/tactic_patterns.md';s=p.read_text();insert='''### Operator norm in orthonormal coordinates — promoted (2026-10-08)

- **Pattern:** Identify the matrix of a continuous linear map in finite
  orthonormal input and output bases, then transfer its operator-norm bound.
- **Result:** `ContinuousLinearMap.norm_toMatrix_orthonormal` in
  `QICLean/Analysis/OrthonormalMatrixNorm.lean` gives equality of norms.
  It reuses Mathlib's Euclidean matrix norm and invariance under composition
  with linear isometric equivalences. Rectangular matrices and empty bases
  require no separate cases.
- **Consumers:** TNLean's `Word.norm_preparedMatrix_le_one`,
  `Word.norm_freeSourceMatrix_le_one`, and the new
  `Word.norm_physicalOutputMatrix_le_one` in `ExteriorSourceContraction`.
- **Decision:** The third application justifies one general equality. The
  prepared TNLean refactor removes the two older coordinate-vector proofs;
  it will be applied together with the dependency update. No custom tactic
  or duplicate coordinate-norm theorem is introduced.

''';s=s.replace('## Candidates',insert+'## Candidates');p.write_text(s)
# Read-only ancestor artifact links, never a package cache copy.
cfg=json.loads(Path('/private/tmp/tnlean-source-main-integration/env.json').read_text());paths=[Path(p) for p in cfg['LEAN_PATH'].split(':')];count=0
for base in paths:
 for p in ([base/'QICLean.olean'] if (base/'QICLean.olean').exists() else [])+list((base/'QICLean').rglob('*.olean')):
  rel=p.relative_to(base);dst=art/rel
  if dst.exists():continue
  dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(p.resolve());count+=1
for rel in ['QICLean/Analysis.olean','QICLean.olean']:
 p=art/rel
 if p.is_symlink():p.unlink()
cfg['LEAN_PATH']=str(art)+':'+cfg['LEAN_PATH'];cfg['source_root']=str(root);cfg['output_root']=str(art);(out/'env.json').write_text(json.dumps(cfg,indent=2)+'\n')
(out/'source-original.lean').write_bytes(src.read_bytes());(out/'preparation.json').write_text(json.dumps({'base_revision':'4be0ef429c5048cf1bf4f5b7afd5b9f7b9361ca0','original_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'production_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'readonly_ancestor_links':count,'no_lake_directory_created':not (root/'.lake').exists()},indent=2)+'\n')
print('PREPARED',count,'READONLY_LINKS')
