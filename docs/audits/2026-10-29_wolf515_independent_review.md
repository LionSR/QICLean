# Independent review of the convex Ando--Lieb milestone

Reviewed implementation: `7f5c728f11df92e06032dea632a779ce271584d2`.
The separate native reviewer was `/root/wolf515_independent_audit`; it read the
primary PDF, printed pages 86--87, the actual source and Lean declarations,
and the power and concavity proofs used by the implementation.

**Verdict: pass for the invertible-domain milestone.** No mathematical or
documentation defect requiring correction was found. The original production
proofs and statements are preserved. The subsequent audit commit adds the
independent regression checks and this review record.

## Exact statement and source comparison

For every fixed complex matrix $K$, the theorem proves joint convexity of
$\Re\operatorname{tr}(K^\dagger A^xKB^y)$ for the entire closed region
$1\leq x\leq2$, $1-x\leq y\leq0$, on $A\geq0$, $B>0$.
Both mixing endpoints are allowed. There is no commutation, Hermiticity,
positivity, invertibility, or normalization restriction on $K$.

Only powers of the positive definite second argument are cancelled against
negative powers. The powers multiplied on the potentially singular first
argument have nonnegative exponents. The independent fixtures verify the
complete lower exponent edge and both mixing endpoints with semidefinite first
arguments, in addition to the original vertex and empty-dimension fixtures.

Wolf's Equation (5.48) uses the transpose on the right tensor factor.
The reviewer independently proved the tensor/trace identity with independent
real exponents, $(B^\top)^q$, and the vectorization of $K^\top$, without
commutation assumptions. It also proved that the trace has zero imaginary
part, so taking its real part does not weaken the source scalar assertion.

The source explicitly permits the word “positive” to mean semidefinite
at Chapter 5 lines 55--60. Consequently this is an invertible-second-argument
milestone, not completion of every singular interpretation of the printed
statement. The domain note and numbering coverage already state this accurately.
At $y=0$, a larger domain with singular second arguments is mathematically
available but is not formally packaged by these declarations. For $y<0$,
no extended-real or support-dependent singular extension is asserted.

## Independent proof-integrity and compatibility checks

The reviewer traversed actual types and bodies of all four public results,
including opaque bodies: 59,779 constants, only `propext`, `Classical.choice`,
and `Quot.sound`, no missing constants, and no QICLean opaque declarations.
The 54 upstream implementation opaques had available bodies and were traversed;
they were not treated as new assumptions. The permanent regression is
`QICLeanTest/Analysis/LiebConvexityIndependentAudit.lean`.

Independent strict elaboration passed for production, the original regression,
the complete closure traversal, and the semantic fixtures. The coordinator
also strictly elaborated all 13 actual QICLean dependency modules, with standard
Mathlib linters and warnings as errors. A fresh strict check of the integrated
independent regression passed. All checks used Lean 4.35.0-rc3 and cached
Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`, without a Mathlib rebuild.

Supplementary seeded floating-point checks passed for 3,584 convex inequalities
and 512 tensor/trace identities, including noncommuting matrices, arbitrary
complex $K$, singular first arguments, and exponent/mixing boundaries.
These numerical checks supplement the exact Lean checks and are not a proof.

The original commits remain in the isolated worktree. Neither existing
production declarations nor dependency pins were changed by the audit.
The full repository build and full compiled Blueprint check remain separate
validation gates. The earlier standalone-note rendering limitation remains
the unavailable local TeX package `dsfont.sty`.

Fresh source and review logs are retained in `/tmp/wolf515-independent/`, and
the strict dependency-module results are in
`/tmp/wolf515-strict-dependencies-summary.log`.
