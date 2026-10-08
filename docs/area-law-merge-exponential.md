# Exponential expansion of merge deficits

For a finite group acting by two commuting permutation representations, with a combined representation equal to their pointwise product, the actual three-label projections form a joint orthogonal resolution. If the logarithmic dimension observables are F_Q, F_E and F_QE, the exponential of b(F_Q + F_E − F_QE) is the literal joint-label sum with coefficient (d_λ d_μ / d_ν)^b. Its real trace pairing with any complex matrix gives the same finite weighted sum.

These are the spectral identities underlying the September 24, 2026 area-law manuscript, `05-replicas.tex` lines 112–115 (`replicas:merge-moment`) and `07-comparators.tex` lines 501–549 (`comparator:merge-moments`). The moment bound uses this expansion together with separate invariance of the actual reduced density matrix. The present identities allow all real exponents and arbitrary complex matrices. The only representation hypotheses are commutation of the separate actions and their literal pointwise product identity.

The proof constructs the joint resolution from the existing label projections and derives nested commutation from centrality. Strict positivity of each irreducible dimension justifies the logarithmic scalar calculation. Labels absent from the ambient representation contribute zero matrices. The identities include empty ambient spaces.

The module is based on the exact published source-chain integration `4be0ef429c5048cf1bf4f5b7afd5b9f7b9361ca0`. It uses the existing orthogonal-resolution exponential theorem and label commutation results. The two proofs are original formalizations of the manuscript calculation; upstream Lean proof text is not reused.
