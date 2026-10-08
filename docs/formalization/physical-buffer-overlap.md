# Physical-buffer overlap

This package formalizes the controlled-overlap step in the pinned
[area-law source, lines 355–424](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/02-information.tex#L355-L424),
especially `eq:info-split-overlap` and `eq:info-reset-overlap`.
The endpoint is an operator on two copies of the original purifying register.
It does not assert a full approximate reset or an entropy bound.

## Contract

`Matrix.exists_hermitian_contraction_physicalBuffer_overlap` takes arbitrary
finite basis types `A`, `B`, `Q`, a coefficient vector
`Ω : (A × B) × Q → ℂ`, normalization `star Ω ⬝ᵥ Ω = 1`, a real `b ≥ 0`, and
the canonical relative-entropy bound
`D(ρ_AB ‖ ρ_A ⊗ ρ_B) ≤ b`, where `ρ_AB` is the ordinary partial trace of
`|Ω⟩⟨Ω|` over `Q`. It returns:

- `W : Matrix (Q × Q) (Q × Q) ℂ` with `W.IsHermitian` and L² operator norm at
  most one;
- `z : ℝ` with `Real.exp (-2 * b) ≤ z`;
- the exact complex identity
  `⟨physicalLeftSwap (doubledRegroup Ω), (1 ⊗ W) doubledRegroup Ω⟩ = (z : ℂ)`.

The identity factor fixes both copies of `A × B`. The two physical copies of
`Q` are the input and output indices of `W`; auxiliary purification factors
are absent from the result type. In the paper's notation `A,B` here are `R,C`.

## Construction and intermediate interfaces

1. `Equiv.partialSwap` explicitly sends
   `((a₁,b₁),(a₂,b₂))` to `((a₂,b₁),(a₁,b₂))`.
   `Matrix.partialSwap` is its permutation matrix.
   It is a Hermitian unitary and its L² operator norm is at most one.
2. `Matrix.compressedPartialSwap V` is
   `(V ⊗ V)ᴴ * partialSwap * (V ⊗ V)`.
   It is Hermitian for every `V`; if `Vᴴ * V = 1`, it is a contraction.
   `Matrix.compressedPartialSwap_left_overlap` transports the exact complex
   inner product through that compression, even with an entangled reference.
   This algebraic identity needs neither an isometry nor normalized vectors.
3. `Matrix.norm_product_overlap_pow_four_le_purity` proves
   `|⟨a ⊗ a′, χ⟩|⁴ ≤ Re Tr((Tr_right |χ⟩⟨χ|)²)` for unit `a,a′` and arbitrary
   `χ`. The coefficient-matrix proof uses
   `|⟨a,C conjugate(a′)⟩| ≤ ‖C‖` and
   `‖C‖⁴ = ‖CCᴴ‖² ≤ Tr((CCᴴ)²)`.
4. `Matrix.star_doubled_dotProduct_partialSwap_eq_purity` is the exact complex
   swap identity. `Matrix.physicalLeftSwap_compressedPartialSwap_overlap_eq_purity`
   combines compression, duplication, and the regrouping from `(A × B) × (X × Y)`
   to `(A × X) × (B × Y)`.
5. The final theorem reuses the normalized purification-splitting estimate from
   QICLean #558. Its isometry and normalized product purifications yield distance
   at most `sqrt (2 * (1 - exp (-b/2)))`. Expanding the squared distance gives
   real overlap at least `exp (-b/2)`. The fourth-power estimate then yields
   `(exp (-b/2))⁴ = exp (-2b)`. Purity is real, which proves an exact complex
   equality to the returned real `z`, not just a modulus or real-part inequality.

## Dimensions and normalization

The matrix identities are uniform over all finite basis types, including empty
and singleton types. No square-dimension, positive-dimension, or equal-local-
dimension hypothesis is added. On an empty Hilbert space a unit vector cannot
exist, so normalized conclusions have vacuous hypotheses there. An empty
regional tensor product instead has a singleton configuration basis, representing
a one-dimensional factor; these are different cases and are both permitted.

The product-purity bound normalizes the two product factors, not `χ`. The final
relative-entropy theorem explicitly normalizes `Ω`; its splitting step and
unit-vector distance expansion depend on that hypothesis. The explicit `b ≥ 0`
hypothesis matches the current declaration.

## Scope and attribution

The new proofs are independently written from the pinned mathematical source and
existing Mathlib/QICLean interfaces. Uhlmann's theorem and purification splitting
are reused from QICLean #558; this package does not refactor or reprove that bridge
and copies no OpenAI Lean proof text.

The result expresses buffer support through the literal identity tensor factor
and the original `Q × Q` matrix indices. It does not identify a spatial region in
a lattice, prove source-independent physical locality, build a spectral filter or
polar factor, produce a reset unitary, or finish the area-law entropy theorem.
Those are separate downstream obligations.

## Blueprint and validation

The matching leaf is
`blueprint/src/chapter/ch12_entropy_physical_buffer_overlap.tex`.
Its Tenkz diagram reads left to right as `K`, `F_A`, `K†`, with `K = V ⊗ V`.
The four external legs are original `Q` indices. Each internal leg bundles one
copy of the auxiliary `A ⊗ B`; all ports are explicitly typed physical indices.
The diagram depicts compression and makes no geometric locality assertion.

The three production modules pass native builds and strict warning-as-error
checks. The axiom audit covers all 42 public declarations and finds only subsets
of `propext`, `Classical.choice`, and `Quot.sound` (or no axioms). The matching
blueprint statements and proofs carry `leanok` markers. Rendering and source
checks are separate from this native verification; aggregate and consumer checks
are recorded by the integration task.

Focused Tenkz, PDF, and static HTML validation uses the pinned external rendering
environment and an isolated fixture outside Git. The fixture records exact source
hashes, renderer versions, diagram event streams, and visual-review evidence.
No generated binary is tracked. QICLean's complete-book Tenkz preamble and workflow
integration remain pending; the leaf contains the actual diagram unconditionally.
Focused rendering is not a full-book build, declaration check, live-browser test,
or publication. Remote writes and publication remain held.

The focused validation checks all 42 changed public declarations against the
production source notices: all are covered by the leaf's references, alongside
one reused purification-splitting declaration. These are grouped into seven
mathematical entries with 12 checked statement/proof markers. The 43 declaration
links occur in both PDF annotations and generated HTML.

The actual Tenkz event sweep has one picture, zero hard findings, and zero
advisories. Its three tensors are `K`, `F_A`, and `K†`; the event stream has two
physical inputs, two physical outputs, and four internal physical contractions.
PDF and standalone event records agree. This is a single compression diagram,
so no hard diagram-equation group check is claimed. The six-page focused PDF
and six generated HTML pages have no unresolved internal anchors, duplicate IDs,
missing local diagram image, or leaked metadata; final content pages were
inspected as pixels. Live-browser/MathJax behavior was not tested.

The render uses Tenkz revision `08a6493f3605dcf2ca5b512823ccb2698dfc027b`,
texra-blueprint `0.3.8` at revision
`65434add8b88bc6a22c701521baa3abec2369341`, plasTeX `3.1`, and leanblueprint
`0.0.20`. The target leaf SHA256 is
`bb98535114b0ee29869893ee380d7ffb88cfacd80342ac12061ce838f4be6334`.
The exact pinned paper source SHA256 is
`b88596a7f6f4f0e6b49a030f27ca9ca64aa669941d8393070fddfe49b08e9cab`.
The isolated fixture retains production-source hashes, PDF/HTML/SVG hashes,
event logs, and the pixel-review record. The Tenkz web render uses its supported
XeLaTeX/PDF/Poppler fallback because `dvisvgm` is absent; inherited font-map and
title-page destination warnings do not affect the inspected content.
