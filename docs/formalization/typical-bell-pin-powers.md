# Bell projections on finitely many copies

The source passage is `comparator:bell-pin`, lines 283–298 of Section 7 of
*A two-dimensional area law from a global spectral gap* (September 24, 2026),
OpenAI/math commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The statements extend the actual one-copy contraction from
`QICLean/Entropy/TypicalBellPin.lean` without changing its vectors or projection.

Let Ω be a vector on A × B. Select a set E of eigenvectors of its actual
first marginal, let z be the sum of the selected eigenvalues, and write d = |E|.
The sole mathematical premise of the pin and normalization results is z > 0.
In particular, Ω need not have unit norm. The Bell vector β, projection
P = |β⟩⟨β|, and vectors pre and post are exactly the existing one-copy
constructions. The product vector on k copies is written literally as
the coefficient function x ↦ ∏ⱼ v(xⱼ); no new public vector definition is added.

The one-copy coefficient $c=\sqrt z/d$ gives
$(P\otimes I)^{\otimes k}\mathrm{pre}^{\otimes k}
=c^k\mathrm{post}^{\otimes k}$.
The repeated β has unit norm, and the finite Kronecker product of P is
its rank-one orthogonal projection. Simultaneous permutations of the AC copies
fix the repeated β. This last assertion needs no selected-mass hypothesis.
All results include k = 0, where the configuration type has one element and
the empty products are one.

The disjoint-operator theorem uses the canonical grouping of the copies
as (AC)ᵏ × (Rᵏ × Bᵏ). The two finite-function product equivalences are explicit
in the theorem statement; no supplied coordinate equality is assumed.
Any matrix Λ on Rᵏ lifts as I ⊗ (Λ ⊗ I). Kronecker multiplication derives its
commutation with $P^{\otimes k}\otimes I$, and hence the same $c^k$ identity after applying Λ.
The result therefore applies in particular to an auxiliary label projection,
without requiring Λ to be a projection in the more general theorem.

These results prove the finite-copy contraction, the repeated Bell projection,
its simultaneous-copy invariance, and the disjoint auxiliary factor in the
cited passage. They do not establish commutation with the spectral metrics,
the choice of Schur label, its probability estimate, or the subsequent norm
inequality. Those require their own representation-theoretic and spectral
arguments. The unique blueprint fragment states the five proved assertions
with the same hypotheses and coordinates.

The finite-product identities are independently derived from Mathlib's
finite distributivity and reindexing theorems. Related circuit statements in
TNLean are downstream and are not imported or copied. The private statements
here neither duplicate their public names nor introduce a competing product
vector definition.
