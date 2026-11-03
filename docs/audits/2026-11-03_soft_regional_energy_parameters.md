# Explicit parameters for the regional-energy auxiliary

The three theorems in `QICLean/Analysis/SoftRegionalEnergyParameters.lean`
verify the residual, norm and precision estimates needed when a separate
actual soft regional energy operator is combined with the corrected hard
polynomial improving family.

The fixed soft parameters are `t = 768`, `m = 12`, and tail cutoff
`T = 384`. They give residual less than `1/16`. If `ell >= 21` and the
actual count satisfies `D >= 50 * ell^2`, the norm expression
`768 * (1 + log 12) + 4 * ell + 14`, plus one, is at most `D`.
At the existing precision `a = 3 / (32 * D^12 * s^5)` and
`tau = a^2 / 2^20`, the target comparison is at most
`1 / (1024 * (D + 1))`. The exact one-word error
`Delta / (1 - 1/4)^2`, with `Delta = 1 / (200000 * D^12)`, is at most
`1 / (100 * (D + 1))`.

These statements are scalar auxiliaries, not the literal soft-generation
procedure of ALVV, arXiv:1602.08828v2, Figure `fig:generate`, lines
1348–1361. That procedure constructs its polynomial from the soft
Hamiltonian and uses soft order four in its DG and LD parameter choices.
Here the already constructed hard polynomial and its accuracy-dependent
hard clipping threshold remain unchanged. The soft threshold 768 belongs
only to the separately constructed regional energy operator. No efficient
algorithm or running time is concluded. The physical composition must
retain the actual untrimmed ordered-word image returned by its improving
family; these scalar estimates alone construct no subspace.

## Verification

Private actual-name checking used the immutable, fully built TNLean
provider `e2706cbe715c49745d4399d37dabe3d2559cc494` and its own QICLean
package `de8a9d1286709f39d8c37d4d52d6e336925863e5`. The selected module has
only Mathlib imports. Guarded strict checking passed in 4.339 seconds
with the default proof budgets and all package linters. The imported
three-declaration foundation inspection passed in 4.062 seconds; each
declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.
The temporary inspection source was then deleted. No Mathlib source,
ordinary library build or shared cache mutation was invoked.

The chapter is registered immediately after the regional-energy
comparison chapter. Source declaration synchronization, generated imports,
reader prose and whitespace checks pass. Its one-page mathematical reader
was rendered and visually inspected. Canonical ordinary compilation and
compiled blueprint declaration checking remain for coordinated integration.

The machine-readable manifest and immutable private outputs are recorded
outside the repository under `/tmp/qiclean-soft-regional-energy-parameters-20261103`.
