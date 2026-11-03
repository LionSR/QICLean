# Canonical low-energy spaces after a scalar shift

This bounded source contribution is based on the accepted QICLean revision
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57`, selected by TNLean revision
`5fc343a57d70eefd2902780107851ab9b0753a82`. It introduces only the scalar
shift identities needed to identify one original low-energy window before
varying a physical truncation or its scalar normalization.

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
Neither their modules nor their statements are changed.

The new scalar-shift source is byte-identical to the isolated module in
preserved revision `617f980139d752b335cb66c981409bb7b32b40e1`, with SHA256
`ccc0c30b315b9cf83857e4025c648306c54583e5be241228737ec36b8add70ec`.
No ancestor integration stack is adopted. In particular, this contribution
adds no polynomial-count module, nested sampler, physical low-energy
family or dyadic dimension theorem. It contains no permanent test fixture.

The supporting source context is ALVV, arXiv:1602.08828v2,
Theorem `t:aisgapless`, lines 1027–1041, and Proposition
`prop:albootstrap-ld`, lines 1112–1128. The scalar identities do not establish
those physical theorems.

## Verification

Fresh actual-name strict checks target accepted source revision
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57`. They reuse only selected immutable
compiled dependencies from the warmed QICLean revision
`24a2ee589c5ff8da34a5cc6d8b7026dc7700e929`. Before compilation, the checker
compares every selected existing dependency source byte for byte with the
accepted target, and compares the toolchain, Lake configuration and manifest.
Changed modules are compiled into explicit private import overrides.

The transitive importer check confirms that no additional old importer is
selected above the changed eigenbasis-invariance module. GroundEnergyBounds
and the Euclidean helper do not import that module. The imported foundation
inspection rechecks the changed graph using the two freshly compiled
canonical modules. All selected source/object and input hashes are guarded
before and after each invocation.

- LowEnergyCoordinates passed strict checking in 22.977 seconds.
- ShiftedLowEnergyCoordinates passed strict checking in 23.199 seconds.
- The combined imported inspection of these four public declarations and
  the three independent scalar-count declarations passed in 25.410 seconds.
  Every declaration depends exactly on `propext`, `Classical.choice` and
  `Quot.sound`.

The source hashes are unchanged from the prepared contribution:
`LowEnergyCoordinates` has SHA256
`21b2c0cb5b9f4e6f56023063f6921732a04ab03c7053db4457884e062b64458c`, and
`ShiftedLowEnergyCoordinates` has SHA256
`ccc0c30b315b9cf83857e4025c648306c54583e5be241228737ec36b8add70ec`.
Evidence is below `/tmp/qiclean-alvv-canonical-window-ba017-20261102`
and `/tmp/qiclean-alvv-ba017-public-inspection-20261102`.
The temporary inspection source and its diagnostic commands were deleted
after use. No permanent fixture is included.

No ordinary library build or compiled blueprint check has been run for
this contribution; both remain coordinated integration gates. No cache,
provider source or provider artifact was changed, no Mathlib source was
compiled, and the source worktree has no Lake directory.
