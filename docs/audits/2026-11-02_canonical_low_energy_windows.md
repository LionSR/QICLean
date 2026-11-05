# Canonical low-energy spaces after a scalar shift

This note concerns the scalar shift identities needed to identify one
original low-energy window before varying a physical truncation or its
scalar normalization.

For a finite Hermitian matrix H and real s,c, the actual canonical spectral
space of H-sI below c-s equals the actual canonical spectral space of H
below c. Repeated eigenvalues and an empty matrix index are included.
If z is normalized, (H-sI)z=E0*z and H-(s+E0)I is positive semidefinite,
the existing ground-energy theorem gives minEigenvalue(H)=E0+s. Thus the
centered window through E0+eta equals the original canonical window through
minEigenvalue(H)+eta. The minimum-eigenvalue corollary uses a nonempty
matrix index. No spectral gap or simple-ground-state premise is introduced.

The existing `Submodule.spectralSpanLE_eq_of_eigenbases` becomes public by
removing only its private modifier; its proof is unchanged. Both required
matrix results are already public upstream:
`Matrix.IsHermitian.toEuclideanCLM_eigenvectorBasis` and
`Matrix.IsHermitian.minEigenvalue_eq_add_of_centered_ground`.

The supporting source context is ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041, and Proposition
`prop:albootstrap-ld`, lines 1112–1128. The scalar identities do not establish
those physical theorems.
