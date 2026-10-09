# Symmetry of exact excitation components

The three results in `Analysis/ReplicaExcitationSymmetry.lean` establish the component symmetry used in the September 24, 2026 OpenAI area-law manuscript, `07-comparators.tex`, lines 441–456, at source revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

A physical permutation sends the exact excitation matrix for B to the matrix for its image σB. A permutation preserving B therefore commutes with the sector projection, including any auxiliary spectator system. A vector fixed by the simultaneous physical and auxiliary action retains this fixedness after projection. Permutations within B or its complement give the two group symmetries; the identity physical permutation also preserves each fixed whole-copy auxiliary label.

These are algebraic identities for the actual matrices, valid without normalizing the one-copy vector and including zero copies. For a unit vector, the established excitation-sector result identifies these matrices as orthogonal projections. No metric commutation, inverse-metric estimate, comparator bound or area law is asserted here.
