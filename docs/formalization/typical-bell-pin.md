# The one-copy Bell contraction

The source passage is Section 7, `comparator:bell-pin`, lines 247–290 of
*A two-dimensional area law from a global spectral gap* (September 24, 2026),
OpenAI/math commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The vectors preceding the contraction are defined at `comparator:prevector`,
lines 130–141. The present result proves the one-copy contraction before
applying tensor powers or the complementary label projection.

Let Ω be any vector on A × B. Its actual first marginal determines the
orthonormal eigenvectors and the selected spectral embedding J. For a selected
set E, let z be the sum of its eigenvalues and d = |E|. The sole mathematical
premise is z > 0. The ambient vector need not have norm one.

The auxiliary pair is the existing uniform maximally entangled vector, transported
from `Fin d` to E through the canonical finite equivalence. The Bell vector is
β = (J ⊗ I)u, and its outer product is P = |β⟩⟨β|. The isometry of J gives
‖β‖ = 1 and P² = P = P†. The complementary compressed vector is the existing
χ = z⁻¹ᐟ²(J† ⊗ I)Ω, constructed from the same actual spectral embedding.

After ordering the factors as AC × RB, the prevector has coefficients
Ω(a,b)u(c,r), and the postvector is β ⊗ χ. Direct contraction gives
(P ⊗ I)pre = (√z/d)post. The proof expands the actual finite matrix coefficients;
it takes neither a Schmidt expansion nor the target contraction as a premise.
The factor d⁻¹ comes from the two uniform-pair coefficients, and √z cancels the
normalization of χ.

The tensor-power identity, disjoint label projection, permutation invariance,
and the estimates involving the spectral metric are subsequent results. No
claim about those parts of the source is attached to this one-copy theorem.
The separate blueprint fragment states the same one-copy assertion with all
assumptions explicit.
