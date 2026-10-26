# Matrix identities for chain gluing

`Matrix.inner_toEuclideanLin_reindex` preserves the finite-complex statement
of the private expectation-transport theorem in
`TNLean/MPS/AreaLaw/ViableSet/Gluing.lean`, commit
`111c9fe461af184e1aa20be8091ec1d1a775a68a`. Its proof now uses Mathlib's
coordinate isometry and matrix-vector transport.

`Matrix.l2_opNorm_one_kronecker` proves norm equality when the identity
factor has a nonempty index set. The matrix itself may have dimension zero.
This strengthens the private reverse inequality in the same TNLean file.
The proof uses the injective identity-tensor star-algebra homomorphism.

After TNLean adopts this QICLean revision, its coordinated import change
can delete both private copies. The other two private theorems in that file,
`inner_comp_symm` and `trace_vecMulVec_star_mul`, can be replaced by
`LinearIsometryEquiv.piLpCongrLeft.inner_map_map` and the existing Mathlib
rank-one multiplication and trace identities. All public chain theorem
statements remain unchanged. The deletion and QICLean pin update are tracked
in TNLean issue #10166.
