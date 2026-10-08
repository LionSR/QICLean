# Coherent matrix-frame operator bounds

This batch supplies finite-dimensional, phase-sensitive matrix estimates for
coherent encoders. It is an extension motivated by the discussion and outlook
of [Malz–Styliaris–Wei–Cirac](https://arxiv.org/html/2307.01696v2), not a claim
that the paper states a whole-groundspace operator-norm theorem.

## Scope and ownership

`QICLean.Analysis.MatrixFramePerturbation` owns the generic matrix results:

- An isometry is an operator-norm contraction.
- The Gram defect and the complex cross defect control squared frame error.
- Tensoring an error operator with an identity reference does not add a
  dimension factor to its action on Euclidean vectors.
- The bound applies to a physical operator acting on an encoded input,
  including arbitrary external-reference entanglement.

No circuit structure, tensor-network state, polar-factor definition, or phase
predicate is introduced here. The statements use Mathlib's matrix operator
norm, Euclidean spaces, Kronecker product, and QICLean's existing isometry
predicate. The corresponding tensor-specific construction remains downstream.

## Migration and reuse

`Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one` is moved from
TNLean's `MPS/Preparation/OverlappingBlockGram.lean` with its name and
statement unchanged. The TNLean consumer update must delete its old body
and import this module; keeping both declarations is invalid. No deprecated
alias or second matrix-isometry predicate is added.

Mathlib scouting covered `Analysis/CStarAlgebra/Matrix`,
`LinearAlgebra/Matrix/Kronecker`, and `Analysis/InnerProductSpace/PiL2`.
The proofs reuse `Matrix.l2_opNorm_conjTranspose_mul_self`,
`Matrix.l2_opNorm_conjTranspose`, `Matrix.l2_opNorm_mulVec`,
`EuclideanSpace.norm_sq_eq`, and `Matrix.mul_kronecker_mul`.
The pinned Mathlib also supplies the abstract Hilbert-tensor inequalities
`ContinuousLinearMap.norm_rTensor_le` and `TensorProduct.norm_mapL_le` in
`Analysis/InnerProductSpace/TensorProduct`. No direct rectangular
Euclidean/Kronecker wrapper, or shorter ready-made coordinate transport
from that abstract tensor product, was found in Mathlib or QICLean. The new
concrete matrix proof therefore slices over the reference basis and sums
squared norms. It never estimates physical or reference matrix entries
separately.

## Boundaries

These facts do not prove existence of shallow encoders, an all-accuracy
logarithmic circuit bound, equality of parent-Hamiltonian kernels, or
conversion of separately chosen periodic-state amplitudes. In particular,
absolute overlaps cannot replace the complex cross matrix: independent
column phases would change a coherent logical operation.
