# Finite-product regional entropy

The generic quantum-information layer is owned by QICLean. Its site type is any
finite type `V`, its local basis types are a dependent finite family `β : V → Type`,
and its pure state is `ψ : EuclideanSpace ℂ ((v : V) → β v)`. Only results requiring
normalization assume `‖ψ‖ = 1`; local dimensions need not be uniform or positive by
an extra hypothesis.

## Physical definitions

- `FiniteProduct.Configuration β R` is the product of local bases over region `R`.
  An empty region has exactly one configuration.
- `FiniteProduct.reducedMatrix` is the ordinary partial trace of an arbitrary
  matrix after splitting region and complement configurations.
- `FiniteProduct.reducedPure` specializes it to the rank-one matrix `|ψ⟩⟨ψ|`.
- `FiniteProduct.entropy` is the existing canonical `vonNeumannEntropy` of that
  positive semidefinite reduced matrix.
- `FiniteProduct.mutualInformation` is the regional entropy combination. On
  disjoint regions, `mutualInformation_eq_matrix` identifies it with canonical
  matrix `mutualInformation` of `jointMatrix`, rather than postulating entropy
  properties of an abstract state.

## Core results

`entropy_compl` proves pure-state complement symmetry, including the entrywise
complex conjugation in the complementary Gram matrix. `entropy_union_le` proves
normalized disjoint-union subadditivity by actual partial-trace composition and
the existing strong-subadditivity result. Empty and full regions have zero entropy.

`entropy_le_remainder_add_half_sum` formalizes the exact normalized-state
[area-law Lemma 11.1](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/10-geometry.tex#L26-L69).
It accepts two separate finite totally ordered families, the complete disjoint
partition, and a bound on each tile's information with the entire exterior-plus-
earlier-same-family union. Its conclusion has exactly the coefficient `1/2`.
No Hamiltonian, gap, geometric, smallness, nonemptiness, or error-sign assumption
is added. The exact-information theorem precedes the error-substitution corollary.

`Entropy.OrderedSetFunction` contains the finite-order algebraic helper. It is not
itself a physical entropy theorem and does not replace the normalized-state result.

## Conditional-cell boundary

`FiniteProductConditional` exposes the actual regional conditional-information
entropy expression, the identity
`I(X:C|Z) = I(X:C ∪ Z) - I(X:Z)`, its upper bound by `I(X:C ∪ Z)` when `X` and `Z`
are disjoint and the state is normalized, a finite ordered CMI chain identity, and
pure-state conditioning duality.
It makes no claim that an ordinary `I(X:C)` estimate survives arbitrary conditioning.
Canonical tripartite identification and the exceptional-site dimension bound
remain interface work. The geometric PEPS conditional-cell argument remains a
separate consumer; this batch does not complete that theorem.

## Downstream ownership

TNLean owns finite lattice domains, Hamiltonians and geometric decompositions.
Its two-family consumer uses the existing `OrderedTwoFamilyPartition`, retains
its original order inside each label, and proves equality with the model's
already-defined regional entropy. It contains no second definition of a lattice
model and no copy of the generic QICLean proof.

## Provenance and validation

All proofs in this batch are independently written from the mathematical paper
and existing Mathlib/QICLean APIs. No OpenAI Lean proof text is copied or adapted.
Source notices and the issue 8760 ledger distinguish this from code reuse.
Validation evidence is recorded separately from mathematical completeness claims.
