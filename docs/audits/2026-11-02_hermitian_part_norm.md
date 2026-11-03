# Operator norm of the Hermitian part

The existing real-linear Hermitian-part map is contractive in operator norm.
Consequently its application to an approximant cannot increase its distance
from a Hermitian target. The proof uses the triangle inequality, invariance
of the norm under adjoint, real-linearity, and the fact that a Hermitian
matrix is fixed by this map. No new structure or normalization is introduced.

These are elementary auxiliary estimates for the Hermitian approximation
used in ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff` and `t:aisefficient`,
lines 1262–1268 and 1412–1420. They do not construct a Hamiltonian or establish
the efficient-filter theorem.

The contribution starts at QICLean revision
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57`. Its Mathlib-only module passed a
fresh strict actual-name check in 4.581 seconds. The imported audit of both
public declarations passed in 4.666 seconds; each uses only `propext`,
`Classical.choice` and `Quot.sound`. The checks read exact fully warmed
TNLean `5fc343a57d` and its own QICLean package `ba017330`, guarding selected
sources, objects and build inputs. All outputs are temporary. No provider or
dependency cache was changed and no Mathlib source was rebuilt. The isolated
worktree has no `.lake` directory.

The mathematical book entry is included. Ordinary integrated full-build and
complete-book checks remain pending. No Lean test fixture is introduced;
foundation commands are confined to a temporary audit.
