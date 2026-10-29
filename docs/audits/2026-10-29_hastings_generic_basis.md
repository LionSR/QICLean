# Finite-dimensional spectral refinement and basis construction

The contribution transfers the preserved generic Hastings basis proofs at TNLean
`1659116509dc8cec5d4a2aec8ddd131cc88da31d` into the shared namespace
`ApproximateDiagonalization`. The common provider remained read-only at TNLean
`7f87bdc8f1b2354be4950ad515dedda7ee9bec96`, QICLean
`ec3434f7d6fbdfc5318dc55934feb9532e239b81`.

The theorem constructs an actual orthonormal basis by strong induction on the
dimension. It chooses a maximal-spread original operator, constructs a proper
spectral projection when necessary, and treats scalar terminal spaces directly.
The two compression cross terms are retained. For fixed dimension n the bound
uses the coefficient sqrt(n^3 C (1+2n^3)^n) and n iterated square roots of the
kernel. It assumes neither a separated basis nor an inverse-spacing or
condition-number bound. Zero weights and empty operator families are included.
Completeness used for adjoints is derived from finite dimensionality by Mathlib.
No TNLean import or physical geometric hypothesis occurs in the companion.

## Verification

All nine actual named modules passed private strict checks with the package's
implicit-variable settings, Mathlib standard linters and warnings as errors.
All 84 public definitions and theorems were imported and inspected: only
`propext`, `Classical.choice` and `Quot.sound` occur; some require fewer.
The Mathlib artifacts were read in place. New outputs exist only under /tmp;
no cache was copied, initialized or mutated and no Mathlib source was built.
The 94 selected provider source/object pairs were hashed before and after checks.

The combined spectral file was split into coherent compression and spectral
modules; their private times were 17.11 and 14.59 seconds. Later host contention
makes private wall times unsuitable as quiet compilation benchmarks. Ordinary
full-library, compiled-blueprint and timing gates remain integration obligations.
Source blueprint synchronization and the added-prose check passed. The manual
foundation inspection also checks every new blueprint declaration name against
the actual imported modules, but is not a full compiled-book check.

Logs: `/tmp/tnlean-hastings-basis-private-checks.log`,
`/tmp/tnlean-hastings-basis-offdiagonal-checks.log`,
`/tmp/tnlean-hastings-basis-generic-checks.log`,
`/tmp/tnlean-hastings-basis-refinement-checks.log`,
`/tmp/tnlean-hastings-basis-recursive-checks.log`,
`/tmp/tnlean-hastings-basis-final-generic-checks.log`, and
`/tmp/tnlean-hastings-basis-generic-foundation-audit.log`.
Earlier failed extraction checks used an incorrect Mathlib import path or lacked
the local derived completeness instance; both were corrected before the final
module checks. There are no proof holes or extra mathematical hypotheses.

## Exact mathematical sources

- `QICLean/Analysis/ApproximateDiagonalization/CommutatorEntries.lean`: `8033e93565a841bc6989052324bc05487049c590ba65dee028e67e75f9a8276c`
- `QICLean/Analysis/ApproximateDiagonalization/CompressionCommutator.lean`: `011e7392814cfebe503b8dcffe970a1a80435775823f7bbb9d0c7c79f15a2aed`
- `QICLean/Analysis/ApproximateDiagonalization/DecayKernel.lean`: `85325304ebdd114a6645f506fe4725f907e6424a4f5d0ce0763aa1754050ad6a`
- `QICLean/Analysis/ApproximateDiagonalization/OffDiagonal.lean`: `ccc83e14788888a6aa1b630461e1eb3f01dc1763284482c3a699a38dd7fb9c51`
- `QICLean/Analysis/ApproximateDiagonalization/OffDiagonalFamily.lean`: `141e8ecad0e5e4b20c51f0ed0d901ba1ab189741efc7ec5a0ed2d7a406391dda`
- `QICLean/Analysis/ApproximateDiagonalization/Recursive.lean`: `48caf4655f46f7a16829c18a4dd0f69daf219395f1de0bd1bac6c4feb469b339`
- `QICLean/Analysis/ApproximateDiagonalization/Refinement.lean`: `36607ec66613d54e4b81ff6b985d3d1c33ac1aa02f22220d8b1e38df9482d35b`
- `QICLean/Analysis/ApproximateDiagonalization/SpectralSplit.lean`: `51e4d3c8060e13bc28b06ec3659e92e012b82aae8caa9d45e396ec199c604bd4`
- `QICLean/Analysis/ApproximateDiagonalization/WeightedKernel.lean`: `8d47c37b7e3efb1cb7c35fe55c5757556639ea40f1bb698eb8522d27e01911fa`
