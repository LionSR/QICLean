# Independent-copy surprisal concentration

For a fixed density matrix ρ, let S be its von Neumann entropy and let V be
the variance of −log p under its eigenvalue distribution p. The module
`QICLean/Entropy/IidSurprisal.lean` proves that the actual spectral mass of
ρ⊗k outside the surprisal window [kS − w, kS + w] is at most kV/w².
At w = k³⁄⁴ and k > 0, this becomes V/√k.

The first theorem identifies the weighted functional-calculus trace with
the finite product of the canonical eigenvalue distribution. It permits
an arbitrary real test function, any positive semidefinite matrix and
k = 0. The second theorem proves the finite-product Chebyshev estimate.
The third applies it to the actual density-matrix threshold projection;
the fourth gives the explicit rate. There is no supplied eigenbasis,
full-rank assumption or assumed concentration estimate.

Zero eigenvalues carry no spectral mass. Logarithms of products are
expanded only for tuples with nonzero product weight. The scalar density
at k = 0 is included in the first three statements; the fourth requires
k > 0 so that its denominator is positive.

The source is OpenAI, *A two-dimensional area law from a global spectral
gap* (September 24, 2026), `07-comparators.tex`, lines 255–281,
`comparator:high-label`, at mathematical source commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. These theorems justify the
independent-copy concentration step in that passage. Choosing a label
whose dimension has logarithm kS + o(k) and whose mass has a polynomial
lower bound additionally requires the comparison with the Schur label
observable and a finite label count; those conclusions are not asserted
here. Nor is this the physical concentration theorem of Lemma 3.1.

The proofs were independently formalized; no upstream Lean proof text
was reused. The unique mathematical fragment is
`blueprint/src/fragment/iid_surprisal.tex`.
