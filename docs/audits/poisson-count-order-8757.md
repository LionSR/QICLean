# Independent Poisson counts and uniform ordering

## Scope and source

This package supplies a fixed-time characterization of the concrete atomic word
law used by the amplification development. The source is OpenAI's
*A two-dimensional area law from a global spectral gap*, file
`09-amplification.tex`, pinned at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, lines 49–54 and 237–253.
The source introduces chronological independent clocks; this supporting
characterization does not itself construct their event times or independent
increments. No pathwise clock identification, retained/omitted coupling,
locality bound, or full amplification theorem is asserted here.

## Independently authored result

Five new production modules contain 456 lines and 33 public constants:

- `QICLean/Algebra/WordMultiplicity.lean`: 71 lines; actual occurrence counts
  and the multinomial cardinality derived by polynomial coefficient comparison.
- `QICLean/Probability/PoissonWordCounts.lean`: 99 lines; actual count fibers,
  finite enumeration, exact factorial cardinality and nonemptiness.
- `QICLean/Probability/PoissonWordIndependentCounts.lean`: 105 lines; exact
  fiber mass, joint product-Poisson law, marginals and mutual independence.
- `QICLean/Probability/FiniteUniformConditioning.lean`: 74 lines; finite-event
  equal-atom restriction and uniform conditioning on a non-null event.
- `QICLean/Probability/PoissonWordUniformOrder.lean`: 107 lines; actual conditional
  uniformity, positive-time support, null-event behavior at zero time, and
  reconstruction from independent counts followed by uniform word ordering.

The existing `PoissonWord` law and Mathlib multinomial/probability facts are reused
by import. Their lines are excluded from the authored total. Current main's
representation-theoretic changes are preserved unchanged and also excluded.
No toolchain or dependency pin is changed.

## Mathematical checks

The count fiber for a vector n has cardinality (sum n)! / product(n_i!).
Uniformity is over distinct label words, rather than over distinguishable event
permutations. The factorial multiplicity is accounted for explicitly.
Conditional uniformity requires nonzero event mass. At positive time every
count event has positive mass; at zero time a nonzero count event has zero
conditional measure. The reconstruction proof separates null fibers before
using conditional uniformity. Empty alphabets and the zero count vector are
included throughout.

Read-only independent review of all five modules found no mathematical defect.
The review checked count multiplicities, factorial cancellation, conditioning
hypotheses, reconstruction and the empty-alphabet/zero-time boundary cases.

## Validation and publication

The initial remote recovery checkpoint `fa468c573a32e60cb2ec963ff1305daf450bef93`
has tree `1ca90471883e94408e3a642744daed05b330ed3c`, exactly equal to local
`fe118d31bd87d245a5546dab9cb19ff75d294d76`. At that checkpoint all production
modules passed focused native and warnings-as-errors Lean checks. It was opened
as draft QICLean#680 while final consumers, guards, rendering and hosted CI
were pending.

There are 36 consumer examples and 33 guarded public-constant axiom checks.
They include repeated count (2,1), conditional atom mass 1/3, unequal ambient
mass outside the conditioning event, null-event nonuniformity, zero-time
conditioning, empty alphabets and sampler reconstruction. Raw axiom inspection
for the eleven conditioning/reconstruction declarations reports only propext,
Classical.choice and Quot.sound. Final exact-head receipts and rendered source
hashes accompany the completed validation packet; focused checks alone do not
claim a full hosted CI pass.
