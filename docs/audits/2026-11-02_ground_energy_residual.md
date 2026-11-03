# Attained energies from restricted residuals

The existing private `real_eigenvalue_ge_of_unit_residual` is moved from LowEnergyCluster
to the thin shared GroundEnergyResidual module, with its statement and proof unchanged.
Its visibility becomes public. Both old public cluster theorems keep their signatures and
reuse it through the new import; the existing LowEnergyOrder import is retained.

New results prove actual eigenvector membership below a spectral cutoff and derive the
energy difference bound by the norm of the actual restricted residual. The matrix form
requires a positive-semidefinite original lower bound and a normalized actual eigenvector
of the second matrix. It derives the lower quadratic form and spectral membership.
It does not assume a successful spectral comparison, a residual estimate, a gap, an
energy-shift bound or uniqueness. An empty matrix index is permitted; the unit-vector
hypothesis itself excludes that case when applied.

These generic auxiliaries support ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255,
and `t:aisefficient`, lines 1373–1392. They do not complete the physical soft comparison,
GEN or a runtime theorem. The source's false cluster estimate remains unchanged.

## Verification

Private strict actual-module checks used immutable TNLean f7bae89a06741bb61820b50cd4b421a2d42951e7
and its own QICLean package 00ca963e4a79afd68d9d6f875dd468a21f1dccdd. Selected source/object
hashes, configurations, warmed Mathlib and changed-importer closures were guarded. Only
objects under /tmp were written. No cache or provider source was changed, and no Mathlib
source was built. GroundEnergyResidual passed in 4.881 seconds; the re-elaborated existing
LowEnergyCluster importer passed in 5.767 seconds.

The imported audit covers all four new public declarations and both affected old public
cluster theorems. It passed in 4.319 seconds; all six use only propext, Classical.choice
and Quot.sound. No audit commands or fixtures are committed.

Generated imports, source-to-blueprint synchronization, added-prose and whitespace checks
pass. The unchanged expectation estimate is recorded as a promoted shared lemma in the
tactic ledger, with its two existing cluster consumers and new restricted-residual consumer.
Ordinary combined builds and compiled blueprint checks remain required after adoption.
