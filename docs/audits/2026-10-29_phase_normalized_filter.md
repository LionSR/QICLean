# Phase-aligned normalization of an actual filtered vector

`Channel/FilterNormalization.lean` proves the normalization step used in AKLV's
varying-target argument. It constructs the actual normalized image of a given
operator and chooses its phase explicitly. A second result derives the actual
Schmidt rank of the same normalized vector. Physical construction of that
operator and the changing sequence of targets remain separate.

## Exact statement

Let \(K\Gamma=\Gamma\) with \(\|\Gamma\|=1\). Suppose every unit
\(v\perp\Gamma\) satisfies \(Kv\perp\Gamma\) and \(\|Kv\|^2\le\delta\).
For every input \(x\) with \(a=\langle\Gamma,x\rangle\ne0\), the actual image
\(Kx\) is nonzero. There is a scalar \(c\), \(|c|=1\), such that

\[
\psi=c\,\frac{Kx}{\|Kx\|},\qquad \|\psi\|=1,
\qquad
\|\psi-\Gamma\|^2
 \le\frac{2\delta\|x-a\Gamma\|^2}{|a|^2}.
\]

The input is not required to be normalized. The real parameter \(\delta\)
is not assumed nonnegative. Its product with the squared perpendicular norm
is nonnegative because it bounds \(\|K(x-a\Gamma)\|^2\).
For a bipartite operator, the same actual normalized vector has

\[
\operatorname{SR}(\psi)
 \le\operatorname{OSR}(K)\operatorname{SR}(x).
\]

The phase scalar is constructed from a minimizing angle returned by the
existing phase-error theorem. It is not supplied, and an arbitrary normalized
vector with the desired error is not assumed. Retaining this phase is necessary:
normalization alone preserves a scalar phase along the fixed target line.

## Reused mathematical results

Set \(v=x-a\Gamma\), \(w=Kv\), and \(y=Kx\). The existing homogeneous
perpendicular-shrinking theorem gives \(w\perp\Gamma\) and
\(\|w\|^2\le\delta\|v\|^2\). Thus

\[
y=a\Gamma+w,\qquad \|y\|^2=|a|^2+\|w\|^2>0.
\]

The existing normalized phase-error theorem is applied to the orthogonal
complement matrix \(I-|\Gamma\rangle\langle\Gamma|\), with energy zero and
unit gap. Its gap defect is identically zero and its energy on \(y\) is
\(\|w\|^2\). This gives phase error at most
\(2\|w\|^2/\|y\|^2\), and the displayed bound follows.
The rank result reuses scalar invariance of Schmidt rank and
`Matrix.schmidtRank_mulVec_le`; no decomposition or rank witness is supplied.

Source: [AKLV, arXiv:1301.1162v1](https://arxiv.org/abs/1301.1162v1),
Definition 2.1, `def:AGSP`, lines 296–314, and the normalized filtering steps
in Lemma 6.3, `l:5`, lines 1023–1048. These are auxiliary normalization and
rank statements, not the physical filter, initial product-vector construction,
or complete approximation sequence of that lemma.

## Verification

Production SHA-256:
`bf15e6ed42af69e80028977e66156340f0fdf4a60cfc135a3ee6d6a33039389d`.
The actual named module passes strict private checking in 4.86 seconds,
with strict implicit arguments, Mathlib standard linters, warnings as errors,
and the default heartbeat limit. Imported foundation inspection of both
public declarations passes in 11.84 seconds and reports only `propext`,
`Classical.choice`, and `Quot.sound`. Inspection commands remain under `/tmp`;
no permanent fixture is added. The Channel pattern scan reports existing
unrelated repetitions; none of its reported blocks involves the new module.

The read-only provider is TNLean documentation revision
`6cc25953751a659592a3d211b95d37e3e0a575ee`, with mathematical sources
`c9516b84af92761e3863f632188b5655f43cd35f`, and checked QICLean package
`92ceaab6274f9cb9bf226c20d144c4d0d83a5f83`. Fourteen imported QICLean source
and object hashes, the manifest and the toolchain are guarded before and after
checking. The new source and object hashes are also checked during imported
foundation inspection.

The contribution worktree has no `.lake` directory. Existing artifacts remain
read only, and all new objects are temporary. No provider, dependency pin,
shared cache or Mathlib source is changed. Ordinary module and compiled-blueprint
checks remain with common integration; no duplicate ordinary build is queued.
The existing entropy chapter contains the new mathematical entry, so no chapter
registration change is needed. The generated import aggregators are left to
integration. Further private elaboration is paused for the coordinated provider
advance.
