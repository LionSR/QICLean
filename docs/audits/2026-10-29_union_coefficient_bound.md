# Signed coefficients with a prescribed union

Let W be a finite family of finite subsets of an arbitrary type. Suppose
there is an injective map μ on the actual family W with μ(I) in I. For
every finite U, the new theorem proves

\[
\left|\sum_{\varnothing\ne\mathcal F\subseteq W,\ \bigcup\mathcal F=U}
 (-1)^{|\mathcal F|+1}\right|\le2^{|U|}.
\]

The Lean conclusion uses the norm of this integer sum, viewed as a real
number. The chosen-element map is defined on the subtype W, rather than
on all finite subsets of the ambient type. Thus an empty family over an
empty ambient type is included without a hidden nonempty-type assumption.

## Proof and application scope

Restrict W to V = {I in W | I is contained in U}. The chosen-element map
restricts to an injection V into U, so |V| ≤ |U|. Every contributing family
is a subset of V. Its number is at most 2^|V| ≤ 2^|U|. Each sign has norm
one, so the triangle inequality proves the coefficient bound. The proof
uses Mathlib's existing injective cardinality bound and powerset count.
No new family of cluster operators or alternative selector is defined.

This is an auxiliary finite count for a corrected interaction-label
cluster estimate related to ALVV, arXiv:1602.08828v2,
`thm:cluster-approx`, source lines 1270–1291 and 1935–1968. The printed
spatial approximation theorem remains distinct; its obstructions are
documented at
https://sirui-lu.com/TNLean/paper-gaps/alvv16_cluster_approximation.pdf.

For bad windows of exactly one fixed positive length, the first label
is the intended chosen element. Constructing that marker in the actual
finite interval family, and identifying the component cutoff with the
bad-window event, are subsequent geometric steps. This theorem does not
assume those identifications and does not itself prove them.

The exact finite inclusion–exclusion formula is already available in
Mathlib as `Finset.indicator_biUnion_eq_sum_powerset`. Its composition with
TNLean's existing `clusterOp` and `clusterPart` identities, the corrected
operator-norm tail with b = 2(exp β − 1), and the spatial cut and MPO
consequences remain subsequent work. The actual supplied lower-energy
normalization must be retained when the coefficient estimate is combined
with the checked mandatory-label norm theorem.

## Declaration and checks

The new public declaration is
`Finset.norm_sum_powerset_biUnion_sign_le_two_pow`, in
`QICLean/Algebra/UnionCoefficientBound.lean`. Its hypotheses explicitly
state the marker's membership and injectivity. It assumes no bound on
the coefficient being estimated.

Private checks used the fixed QICLean worktree at
`4175de302e6b580d1bbb4a022f57424ab9f05e73`, with fully warmed production
objects and fresh source, build-input and object hashes. The actual module
passed strict checks in 10.21 seconds. A separate importing module audited
the theorem's foundations and found only `propext`, `Classical.choice`
and `Quot.sound`. The reader-facing prose check and repeated-tactic scan
passed. The mathematical chapter compiled twice as a standalone page,
with a resolved equation reference and no overfull boxes, and was
visually inspected.

All new objects and the temporary imported audit are under `/tmp`.
No provider source, dependency, object or cache was changed, no
TNLean-dependent elaboration was run, and no Mathlib source was rebuilt.
Ordinary common-library compilation and the compiled blueprint declaration
check remain integration checks. No persistent per-theorem fixture is
included in the patch.
