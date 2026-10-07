# Typical spectral truncation on a physical region

The mathematical reference is OpenAI, *A two-dimensional area law from a global
spectral gap* (September 24, 2026), at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The selected vector is
specified in `07-comparators.tex`, lines 240–247, and the disjoint-region entropy
estimate is equation `comparator:post-marginal`.

The construction uses the existing finite-product configuration spaces and
canonical region/complement equivalence. The original actual marginal on a fixed
region X determines its selected spectral projection. The normalized projected
vector is transported back to the original global configuration space once;
it depends only on X and the selected eigenvalue indices.

Every disjoint observed region B satisfies both the positive-semidefinite marginal
bound and the entropy estimate for this same vector. The proof further decomposes the configurations on the complement of X
into B and the complement of their union. These changes of coordinates preserve
the actual X marginal and commute with the spectral truncation. The two partial
traces of the three-factor density are the existing actual regional reduction
on B. The result therefore follows from the verified three-factor estimate.
The entropy theorem assumes only a unit original vector, disjoint regions, and
positive selected mass. The marginal-order theorem requires only disjoint regions
and positive selected mass. Empty regions and arbitrary finite local basis types are allowed.

The normalization and selected X marginal are also proved directly, with only
positive selected mass. All coordinate and marginal identities used in the
entropy proof are established internally. No supplied coordinate certificate,
full-rank condition, or assumed marginal or entropy conclusion occurs.

The designated-support marginal tails of QICLean PR 595 and the local-operator
lifts of PR 603 address different constructions. This module reuses the existing
FiniteProduct reductions and introduces no further regional-density or local-lift
definition. Root imports and shared blueprint inclusion belong to the integration
branch.

Codex (GPT-6) assisted the independently written formalization. No upstream Lean
proof text was copied or adapted.
