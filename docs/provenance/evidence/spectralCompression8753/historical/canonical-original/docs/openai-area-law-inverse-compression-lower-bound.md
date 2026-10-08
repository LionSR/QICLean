# Lower bounds from compressed inverses

For a positive-definite matrix A, an orthogonal projection P and a positive
real c, the compressed-inverse bound \(PA^{-1}P\le cP\) implies
\(c^{-1}P\le A\). This is the abstract implication used after the component
inverse estimate in the September 24, 2026 area-law manuscript,
[Section 7, lines 585–605](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/07-comparators.tex#L585-L605),
equations `comparator:inverse-compression` and `comparator:lower-pin`.

The proof puts \(S=A^{1/2}\) and \(T=S^{-1}P\). The two Gram matrices have
the same operator-norm bound, so \(T^*T\le cI\) gives \(TT^*\le cI\).
Conjugation by \(S\) then gives \(P\le cA\). No commutation between A and P is used; zero projections and empty
ambient coordinate sets are included.

The production proof is the independently authored finite-dimensional
argument first checked by the PEPS contraction coordinator, followed by a
separate mathematical reading and strict check in the pinned QICLean environment.
The original scratch source and its command records are retained as historical
evidence; canonical library and blueprint verification are recorded separately.
The component compression estimate, its exponential constant and passage through
the comparison tree remain distinct obligations. This implication alone does
not establish the area-law comparator.
