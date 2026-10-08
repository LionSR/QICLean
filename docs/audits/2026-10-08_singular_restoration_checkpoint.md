# Singular restoration checkpoint

This is a source recovery checkpoint for the bounded generic restoration work
in TNLean issue #8757. It does not close the amplification theorem.

## Historical first checkpoint

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

## Checked implementation checkpoint

At integrated source `1d3a6f8020a1c6759cb2ac63bdb875bd8ea83d03`, all five production modules (1,282 lines, 54 public declarations) have passed targeted native and strict compilation. Individual package checks passed 30 consumer examples and 54 standard-axiom guards. The combined integration rerun passed all 20 checks at that exact source head; full hosted CI has not run on this new checkpoint.

The earlier helper errors are repaired. The actual singular support-inverse sandwich, partial-trace marginal order, R₀/B₀ Gram identities, norm bounds, column identity, arbitrary-operator adjoint cancellation and three-projection adjoint-error estimate are proved. Independent source review found no substantive mathematical defect. Core PDF/web rendering passed; the norm/vector extension render is pending.

The exponential norm specialization explicitly assumes the scalar entropy identity. The square-root failure-parameter specialization assumes the three norm-disturbance bounds; neither typical-projector existence nor those disturbance estimates are proved here. The actual ground-component coefficient identity/bound remains active work. Poisson products, locality and full amplification are separate.

## Actual ground-component extension

At integrated source `457c011a74fd255f06d63d342c329067309c467b`, all 27 targeted native/strict/consumer/guard/raw checks pass. The seven-module package now contains 1,740 production lines, 76 public declarations, 44 consumers and 76 standard-axiom guards. The extension contributes 454 new production lines and 20 new declarations, with two existing vector coefficient helpers promoted to public lemmas. Current main `069d282a52376991b892c7bad7a6c343f746d1e0` is integrated without changing toolchain or dependency pins.

The literal physical ground outer product acting on the actual restoring vector has the source coefficient M[y,x]/sqrt(p[x]). Its exact squared norm equals the selected-x/all-y coefficient sum. The support inverse, including zero eigenvalues, yields the complete trace bound through one. The density is constructed from the physical vector; the diagonal-marginal hypothesis records the chosen eigenbasis. No coefficient identity, order conclusion, full-rank premise or Q/T commutation is assumed. A concrete complex off-diagonal consumer returns +i and distinguishes the coefficient from its conjugate. Independent mathematical review found no substantive defect; the complete expanded render passes on all twelve PDF pages, six static HTML pages, 76 package declaration links and 60 labels.

This completes the bounded generic restoration algebra, not the full amplification theorem. Typical-projector existence, derivation of disturbance estimates from failure probabilities, entropy interpretation, Poisson products and locality remain separate.
