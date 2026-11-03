# A local energy minimum from a tensor vector

Let E and F be complex inner product spaces, with F finite-dimensional,
and let S be a linear subspace of E. For a continuous linear operator A
and a nonzero vector w in S tensor F, the inequality

    Re ⟨(A tensor I)w,w⟩ ≤ c ‖w‖²

implies that there is a unit vector u in S with Re ⟨Au,u⟩ ≤ c.
The operator need not be symmetric, and E need not be finite-dimensional.
For finite-dimensional E and symmetric A, the least eigenvalue of the
actual orthogonal compression of A to S is therefore at most c.
The positive dimension of S is proved from w; it is not an extra premise.

The two public results are
`Submodule.exists_unit_re_inner_le_of_tensor_energy` and
`Submodule.exists_compression_min_eigenvalue_le_of_tensor_energy` in
`QICLean/Analysis/TensorEnergyMinimum.lean`.

## Argument and scope

Expand w along an orthonormal basis of the environmental factor F.
Every slice lies in S, the squared norms of the slices sum to ‖w‖²,
and their real quadratic forms sum to the given tensor quadratic form.
At least one slice is nonzero. If every nonzero slice had Rayleigh
quotient greater than c, summation would contradict the displayed
inequality. Normalize a nonzero slice whose quotient is at most c.
A one-dimensional trial space then gives the compressed eigenvalue bound
by the existing variational theorem.

The result is an auxiliary for regional energy estimation in
Arad–Landau–Vazirani–Vidick, arXiv:1602.08828v2, Figure `fig:algo1`,
line 1631, and its correctness proof at lines 1793–1807. It assumes the
explicit tensor quadratic inequality and proves the local energy
consequence. It does not prove that physical filtering or projection
produces such a tensor vector, and it makes no claim about the source
energy estimation procedure or its running time.

The proof uses the existing tensor slices and norm decomposition from
`TensorProductWeights`, tensor-subspace containment from
`TensorFamilyImage`, Mathlib's invariance of the Rayleigh quotient under
nonzero scalar multiplication, and the actual compression and variational
bound from `RitzCompression` and `RitzSubspace`. No independent spectral
basis or local low-energy witness is assumed.

## Verification

The exact module passed a private strict elaboration in 4.512 seconds,
against the immutable checked TNLean provider
`cd17d76b290c83200b59b48bc816e4856e3c9c1a` and its own QICLean dependency
`0c26d87e4efdd19c85aaa402b4c0b153d3f65657`. Source, imported objects,
build inputs and the prebuilt Mathlib object were guarded before and
after checking. All new objects were written under `/tmp`; no shared
cache or provider source was changed and no Mathlib source was built.
The imported two-theorem foundation audit passed in 4.290 seconds; both
theorems depend only on propext, Classical.choice and Quot.sound.
Source–blueprint synchronization, generated-import consistency,
reader-facing prose and whitespace checks passed. The tactic-pattern
scan found no repeated block requiring abstraction in this contribution.
Exact source and check records are recorded in the accompanying private
manifest. Ordinary combined-library and compiled-blueprint verification
remain integration checks.
