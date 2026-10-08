# Singular restoration checkpoint

This is a source recovery checkpoint for the bounded generic restoration work
in TNLean issue #8757. It does not close the amplification theorem.

At local source `0deeb5c3561566d16f930e0c355b09983c97cfc5`:

- `SupportInverseSandwich.lean`: native/strict production, six consumers and
  seven guarded/raw standard-axiom checks pass; the detailed dated audit is
  included alongside this note.
- `RestoringMarginal.lean`: native compilation and strict warning-as-error
  compilation pass. It derives positivity and domination of the actual
  partial-trace marginal without commutation of the two projections. Dedicated
  consumers, axiom guards and rendering remain pending.
- `RestoringOperators.lean`: the actual R₀/B₀ definitions and Gram proof
  candidates are present, but the first native check reports helper proof
  errors. Repair and validation are active. No completed-proof claim is made
  for this module, and its blueprint entries have no checked markers.

The column identity, norm bound, adjoint cancellation and actual ground-vector
coefficient identity remain open within this package. Typical-projector
existence, Poisson products, physical locality and full amplification remain
separate. Source: pinned openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
AreaLaw `09-amplification.tex`, lines 324–446. No upstream Lean proof text was
copied. No toolchain/dependency change, generated binary or LFS asset is included.
