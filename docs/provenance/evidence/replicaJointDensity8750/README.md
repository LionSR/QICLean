# Actual joint density on the good physical and auxiliary copies

The frozen source defines the literal partial trace of the actual excitation
component, retaining the good physical region and good auxiliary coordinates.
Its product theorem assumes only that the prescribed one-copy ground vector is
unit. No auxiliary independence, permutation fixedness or density certificate
is assumed. Zero components, zero copies and empty good sets are included.

`source-freeze.json` binds the four production and exposition files to source
commit 05dc0048. `verification.json` records the successful source-bound checks
and the separate preparatory commands. The two exact imported kernel reports
include the public definition and the product theorem. Their only axioms are
`propext`, `Classical.choice` and `Quot.sound`.

`prerequisite-merge-preservation.json` records both released parents and the
exact two conflict resolutions. All #643 production and provenance files are
unchanged. The sole production difference from #640 is the already accepted
SupportedMarginalTails helper extraction inherited from #643. All #640
provenance files are preserved. `parent-preservation.json` inventories every
tracked file at the resolved merge, allowing only the new cumulative ledger
append. The existing untracked output directory is untouched.

The commands captured before the mathematical freeze are preparatory records,
not source-bound verification claims. Every actual exit is preserved, and raw
logs have deterministic gzip companions. No command failed in this leaf.
The source passage is Section 7, lines 520–549 of the September 24, 2026
OpenAI area-law manuscript; this contribution establishes the density product
identity, while auxiliary symmetry and merge-moment bounds are separate results.
