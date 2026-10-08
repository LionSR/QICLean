# Actual restoration ground component

Source checkpoint: `e5c117077301d44a34f66660bdfb85d1ec7390a2`.
Base checkpoint: `1d3a6f8020a1c6759cb2ac63bdb875bd8ea83d03`.

The independent source is the September 24, 2026 area-law manuscript,
`09-amplification.tex`, lines 417–446, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The implementation uses the
existing restoring operators and copied vector, without upstream Lean proof text.

## Mathematical contract

The physical vector lies in `(X × Y) × Z`. Its reduced density is defined by
tracing the actual outer product over `Z`. The physical ground outer product
is extended by both ancillary identities in the existing `s,e,X,Y,Z` order.
For a unit physical vector, that matrix is proved to be an orthogonal projection.

The actual projected restoring vector is proved coordinatewise to equal
`1_{s∈E} (sqrt p_s)⁻¹ M(e,s) Ω(a,z)`, where
`M = partialTraceRight ((I ⊗ T) ρXY Q)` and `ρXY` is the actual reduced density.
This identity is established for arbitrary physical vectors and arbitrary
`Q,T`, requiring only unit `s` and `X` blanks. It is not assumed as a certificate.
For unit `Ω` and positive selected probabilities, its squared norm is the sum
over selected `x` and **all** `y` of `‖M(y,x)‖² / p_x`.

For the trace bound, `Q,T` are orthogonal projections, `Q` commutes with
`ρXY`, and the actual `X` marginal equals the real diagonal `diag p`.
The existing order theorem proves `0 ≤ M ≤ ρX`; the singular sandwich theorem
proves `M ρX⁺ M ≤ M`. The new diagonal support-inverse theorem identifies
`ρX⁺ = diag(p⁻¹)`, including zero diagonal entries. Expanding its trace and
restricting the weighted column sum proves the complete chain through `≤ 1`.
No full-rank assumption or commutation between `Q` and `I ⊗ T` is added.

The coefficient helper permits selected zero weights because Lean's reciprocal
of zero is zero. The physical squared-norm and final bound theorems require
strictly positive selected probabilities, as in the source.

## Checked source and regressions

- `Analysis/RestoringCoefficientBound.lean`: 124 lines, six declarations.
- `Entropy/RestoringGroundComponent.lean`: 330 lines, fourteen declarations.
- Two existing private vector lemmas are promoted with descriptive names;
  their proof bodies are preserved. `RestoringVectors.lean` has 467 lines.
- Fourteen new consumers include a singular noncommuting matrix pair, a full-row
  sum of one versus an incorrect selected-row sum of one half, the remote ground
  coordinate, independent complex blank phases, and a non-real off-diagonal
  physical coefficient equal to `+i` rather than its conjugate.
- Twenty-two new axiom guards and the raw inventory report exactly
  `propext`, `Classical.choice`, and `Quot.sound`.

The [check manifest](evidence/restoring-ground-component/checks.json) records
eleven successful checks: a focused native build, strict checks of the three
affected production modules, strict checks of six consumer/guard files, and
the raw axiom driver. All strict checks use the repository's explicit implicit
argument settings and treat warnings as errors. Source hashes match the stated
checkpoint. The [summary](evidence/restoring-ground-component/summary.json)
also records unchanged Lean, Lake, and dependency pins.

The seven-module restoration stack now contains 1,740 production lines,
76 public declarations, 44 consumer examples, and 76 axiom guards. These totals
combine this extension with the previously checked five-module checkpoint;
they do not claim a fresh repository-wide build.

## Blueprint and scope

Two direct mathematical leaves cover all twenty new declarations and both
promoted vector declarations. Their declaration sets match the source exactly.
The parent integration owns aggregate imports, chapter routing, and final
web/PDF rendering; those stages are not claimed by this source checkpoint.

This finishes the physical ground-component coefficient identity and bound.
Typical-projector existence, the Poisson step, full amplification, and locality
remain outside this result. No placeholder, new axiom, or unchecked native
decision procedure is introduced.
