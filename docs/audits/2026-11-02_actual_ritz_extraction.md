# Variational extraction from the actual compressed Hamiltonian

The contribution is based on QICLean `ba01733099b5a18bed5c9bfb62f95f175b4c9b57`
and the equal-dimension symmetry leaf `2d81c505cd213bc32170a121c59472a0dd63d637`.
The original symmetric operator determines its actual ordered eigenbasis.
The variational dimension argument bounds its low eigenvalues from a uniform
trial-space quadratic-form bound. The span of its actual lowest r vectors
has dimension r, including r=0 and repeated eigenvalues, and the energy bound
holds throughout that span.

The candidate-space compression is the actual orthogonal projection composed
with the original operator and the candidate inclusion. Its symmetry and mixed
forms are derived. Mapping its selected eigenvectors back to the original space
gives an actual subspace of the candidate, with the same dimension and uniform
energy bound. No compressed operator, eigenbasis, selected subspace or output
energy estimate is supplied as a premise.

For a Hermitian original matrix, the original gap gives the quadratic-form
lower bound on the full original ground-space complement. The actual Ritz
space is chosen from H, W and the ground rank before the trial space is
introduced. A ground-rank trial space with energy at most mu+epsilon gives
both directed closeness bounds with exactly epsilon/gamma. The reverse bound
uses equal-dimensional symmetry. Ground-state uniqueness and a gap cap are
not assumed.

This is the variational final-extraction auxiliary in ALVV Figure fig:algo1
and the last step of t:alg1. A suitable trial-space energy bound remains an
explicit input. Its derivation from the same recursively constructed root,
physical filtering and actual collective trimming must be composed separately.
No independent MPS approximation, final algorithm, joint adaptive probability
or computational cost theorem is asserted here.

## Verification

The actual three modules were checked separately against immutable warmed
TNLean `5fc343a57d` and its own QICLean `ba01733099b` dependency:

| Module | Strict private seconds |
| --- | ---: |
| RitzSubspace | 4.794 |
| RitzCompression | 4.272 |
| RitzGroundSpace | 4.85 |

An imported inspection covers all twelve new public declarations and the
previous equal-dimension symmetry theorem. All thirteen use only `propext`,
`Classical.choice` and `Quot.sound`; this check passed in 4.172 seconds
over seven selected QICLean source-object pairs. Its temporary source was
deleted. The manifest records all names, attributes, source and object hashes.

The proofs reuse the existing real spectral quadratic-form identity and
closed-spectral-span energy bound, including application to the negative
operator for the upper-index variational bound. They also reuse Mathlib's
basis dimension, subtype transport and projection results. The tactic scan
finds no new repeated block meeting the three-occurrence, two-file threshold.
No new tactic is introduced.

Selected source, object and root-input hashes remain fixed before and after
every check. The isolated source tree has no Lake directory. No common
provider, dependency cache or artifact was changed or copied, and Mathlib was
not rebuilt. Ordinary combined library, changed-source, imported foundation
and compiled blueprint gates remain required, especially after replacing the
existing closeness core by its separately checked strengthened source.
