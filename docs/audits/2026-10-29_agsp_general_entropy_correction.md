# General approximate-projector entropy correction

Source: AKLV, arXiv:1301.1162v1, Lemma 2.3 (`lem:S`), equation `eq:Sb`,
`1dfrustrated34.tex:339–348`; primary rendering:
<https://arxiv.org/html/1301.1162v1#S2>.
The unique-ground applications are in Sections 4 and 6.1.

The printed uniform estimate lacks an additive logarithmic rank contribution.
The Bell-vector counterexample in
`docs/paper-gaps/aklv13_entropy_small_shrinking.tex` is retained unchanged.
The note now also states the corrected estimate and its proof.

The new result uses a specified actual unit product vector with overlap at least
μ > 0, a unit fixed vector Γ, an actual bipartite operator K fixing Γ,
preservation of Γ-perpendicular, squared shrinking 0 < δ < 1, and actual operator
Schmidt rank at most D. It proves, with natural logarithms,

    S(Γ) ≤ 12 (1 + log(μ⁻¹) / log(δ⁻¹)) log D.

There is no favorable Dδ tradeoff premise. This corrects the printed parameter
dependence; it is not the printed formula or a degenerate-ground-space theorem.
The exact-projection endpoint δ = 0 separately gives Schmidt rank at most D and
entropy at most log D. D = 0 is impossible for a fixed unit vector. For D = 1
and δ < 1 the existing rank-one endpoint gives entropy zero.

## Actual argument

- `Channel/AGSPGeneralTails.lean` applies powers of K to the actual orthogonal
  decomposition of the specified product vector. It retains the exact initial
  coefficient A = (1 − |overlap|²) / |overlap|² and derives the original marginal
  tail at rank D^j bounded by min(1, A δ^j), including empty tails.
- `Analysis/CappedGeometricSum.lean` proves that every finite sum of these capped
  geometric majorants is at most 2 + 3 log(1 + A) / (−log δ). The proof splits at
  the ceiling of log A / (−log δ) when A > 1, and uses A ≤ 2 log(1 + A) otherwise.
- `Channel/AGSPGeneralEntropy.lean` applies the existing arbitrary finite
  rank-tail entropy inequality, with a covering rank schedule D^j, to the actual
  original marginal spectrum. Since log(1 + A) = 2 log(|overlap|⁻¹), the constant
  12 follows from log 2 ≤ log D. Replacing the actual overlap by its lower bound
  has the correct monotonicity direction.

The existing power-contraction and orthogonal-remainder Ky Fan helpers in
`Channel/AGSPGeometricTails.lean` are made public. Their signatures and proof
bytes are preserved. There is no new projector predicate, supplied approximant,
supplied tail, physical consumer, or dependency change.

## Review and validation

Base: accepted QIC main `86b3159b98a1608c5e66a875fa670a9687c9867d`, on Lean
v4.35.0-rc3 and Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`.
The relevant pre-existing AGSP files are unchanged between the former TN pin
`acda92aa70e69b37507e422bceb5414036859fe6`, current TN pin
`14ecc5b64bb61cccb01a6583bbab3252bee1486b`, and this accepted base.

Independent native mathematical and pinned-source API reviews passed: the root
reviewed all three new modules; a second reviewer checked the capped sum and
entropy module; a third checked the complete general-tail module, zero-shrinking
endpoint, and exposed helper proofs. The third reviewer verified the actual
Mathlib source blobs for the raw-matrix/Euclidean action identification against
the pinned revision. These are source reviews, not elaboration results.

Native generated-import checks, full Blueprint/source synchronization, reverse
coverage, active mathematical references, bibliography uniqueness, ChkTeX,
source width, proof-token checks, source-size policy, repeated-tactic scan, and
whitespace checks passed. The two helper proof bodies were compared byte for
byte. Repeated helper reuse is recorded in `docs/tactic_patterns.md`.

No local Lean, Lake, elaboration, build, or compiled Blueprint check was run.
All six new Blueprint entries, covering seven newly public declarations, are
marked `notready`; none claims compiled acceptance. TN issue #9836 remains open
until the replacement has its own acceptance and integration evidence. The
physical changing-target sequence remains owned by TN #10404.
