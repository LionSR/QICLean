# An energy-normalized mandatory-label operator bound

For Hermitian complex matrices H and h_i, i in a finite set S, suppose
||h_i|| ≤ 1 and H ≥ λI. The new analytic theorem proves, for every t ≥ 0,

\[
e^{t\lambda}\left\|\sum_{T\subseteq S}(-1)^{|T|}
 e^{-t(H-\sum_{i\in T}h_i)}\right\|
 \le (e^t-1)^{|S|}.
\]

The norm is the Hilbert-space operator norm. The real number λ is any
supplied spectral lower bound, rather than necessarily the exact minimum.
The background H need not equal the sum of the selected terms. Hermiticity
and the norm bound are required only for labels in S. No locality,
positivity of the individual h_i, uniqueness of a ground vector, or finite
ambient label type is assumed.

## Proof and mathematical scope

The finite powerset identities yield the exact differential recursion

\[
(R_S^H)'(s)=-H R_S^H(s)
 -\sum_{i\in S}h_iR_{S\setminus\{i\}}^{H-h_i}(s).
\]

For nonempty S the alternating sum vanishes at zero. Differentiating
 e^(−(t−s)H)R_S^H(s) and applying the fundamental theorem of calculus gives
the actual Duhamel integral. This identity and the continuity and
integrability of its integrand are proved in the module, not supplied as
hypotheses. Every semigroup time used in the norm estimate is nonnegative.
No estimate on the growing exponential e^(+sH) is used.

The bound H − h_i ≥ (λ − 1)I follows from h_i ≤ I. Strong induction on S
bounds the Duhamel integrand by

\[
e^{-t\lambda}|S| e^s(e^s-1)^{|S|-1}.
\]

The integral is evaluated using the explicitly proved primitive
(e^s − 1)^|S|. The resulting unnormalized bound is multiplied by e^(tλ),
whose product with e^(−tλ) is exactly one. The semigroup estimate itself
uses the scalar spectral lower bound and functional calculus on the fixed
Hermitian matrix. Operator monotonicity of the exponential is not used.

The statement includes S empty, t = 0, and an empty matrix index type.
In the empty-label case it reduces to the spectral semigroup norm bound.
The proof never introduces a nonempty-matrix hypothesis or assumes that
the norm of the identity equals one in the trivial matrix algebra.
For scalar identity interactions h_i = I and H = |S|I, the normalized
bound is attained, so its dependence on t and |S| cannot be improved in
this generality.

This is a corrected auxiliary mandatory-label estimate for ALVV,
arXiv:1602.08828v2, `thm:cluster-approx`, source lines 1270–1291 and
1935–1968 of `local_alg_arxiv_v2.tex`. It does not prove the false printed
spatial approximation theorem. The two obstructions to that theorem remain
documented in the TNLean-owned note:
https://sirui-lu.com/TNLean/paper-gaps/alvv16_cluster_approximation.pdf.
The module and its public theorem cite both the source and that note.
No copy of the note is added to QICLean.

No public cluster operator is introduced. Private proof notation abbreviates
the explicit finite sum in the public conclusion. The later tensor-network
application must retain the interaction-label cutoff and reuse TNLean's
existing `clusterPart`, `clusterOp`, exact-support expansion and component
factorization. The finite corrected tail, spatial cut factorization,
operator Schmidt rank bound, MPO construction and efficient evaluation
remain subsequent obligations.

## Declaration and verification

The public declaration is
`Matrix.norm_sum_powerset_exp_sub_le_of_lower_bound` in
`Analysis/MandatoryExponentialNorm.lean`. Its conclusion contains the actual
finite alternating sum. Its hypotheses do not include a norm bound on that
sum, a successful approximation, or any integral or recursion identity.

Private checks used the fully warmed QICLean production objects at
`15a60a1bebe726ee6536ae75570e8243b9f310c4`, directly from the companion
foundations worktree. They did not use the advancing TNLean package or
provider. Production sources, build inputs and objects were hashed before
and after checks. All new objects were written under `/tmp`. No provider
source, dependency, build object or cache was changed, and no Mathlib source
was rebuilt.

The final actual-module check passed the repository's strict flags in
4.74 seconds. A separate module imported that compiled object and audited
the public theorem: its only foundations were `propext`, `Classical.choice`
and `Quot.sound`. This audit includes all transitive private proof
components. The reader-facing prose check and repeated-tactic scan passed.
The mathematical chapter compiled twice as a standalone page, with
resolved equation references and no overfull boxes, and was visually
inspected. Ordinary common-library compilation and the compiled blueprint
declaration check remain integration checks.

No temporary audit command or per-theorem fixture is included in the
source patch. The earlier checked helper artifact and both comparison
patches remain separately preserved.

## Completed integration checks

Mathematical revision `a81cad04c854c6816788abdd3c4bdaab414501fa` passed
the full 10,355-job library build, strict checks of the two changed source
and aggregator files, and an imported inspection of the public theorem.
Only propext, Classical.choice and Quot.sound occur. Source synchronization,
compiled blueprint declaration checks, prose, proof-integrity and timing
checks also passed. No job reached the 25-second warning threshold.
The new leaf module affects no existing regression according to the
repository's dependency selection. The preceding shared-source revision
15a60 separately passed all 181 affected regressions; those sources are
unchanged here. Mathlib was not rebuilt and no modified-worktree cache
artifacts were copied. The complete local record is
`/tmp/qiclean-mandatory-norm-gates.json`.
