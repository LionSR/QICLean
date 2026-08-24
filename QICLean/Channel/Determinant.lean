/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Determinant.Basic
import QICLean.Channel.Determinant.Bound
import QICLean.Channel.Determinant.ChoiBound
import QICLean.Channel.Determinant.Composition
import QICLean.Channel.Determinant.HilbertSchmidt
import QICLean.Channel.Determinant.HeisenbergDual
import QICLean.Channel.Determinant.KrausRankTwo
import QICLean.Channel.Determinant.PositiveExtremality
import QICLean.Channel.Determinant.PositiveInverse
import QICLean.Channel.Determinant.UnitaryCharacterization

/-!
# Determinants of quantum channels

Thin module assembling the determinant development for quantum channels from
ten focused sub-modules.

The division follows the same organization as the earlier `Full/` and
`Growth/` developments:

* `QICLean.Channel.Determinant.Basic` — determinant definitions and unitary
  channels.
* `QICLean.Channel.Determinant.Bound` — Wolf Theorem 6.1(1), the determinant
  bound for positive trace-preserving maps.
* `QICLean.Channel.Determinant.ChoiBound` — Wolf Eq. (6.27), the determinant
  of an arbitrary linear map bounded by the purity of its Choi--Jamiolkowski
  operator.
* `QICLean.Channel.Determinant.Composition` — Wolf Eq. (6.22), its exact
  algebraic equality split, and determinant monotonicity under composition.
* `QICLean.Channel.Determinant.HilbertSchmidt` — spectral and Hilbert--Schmidt
  auxiliary lemmas for the rigidity argument.
* `QICLean.Channel.Determinant.HeisenbergDual` — Heisenberg-dual
  multiplicativity from determinant saturation.
* `QICLean.Channel.Determinant.KrausRankTwo` — Wolf's nonnegative-determinant
  proposition for completely positive maps of Kraus rank at most two.
* `QICLean.Channel.Determinant.PositiveExtremality` — Wolf Theorem 6.1 for
  positive trace-preserving maps, including reality, saturation, and the
  transposition sign.
* `QICLean.Channel.Determinant.PositiveInverse` — Wolf's positive-invertible-map
  corollary, including trace preservation and positivity of the inverse.
* `QICLean.Channel.Determinant.UnitaryCharacterization` — Wolf Theorem 6.1(2)
  for CPTP maps.

## Main definitions

* `channelMatrix` — the matrix representation of a channel.
* `channelDet` — the determinant of that matrix representation.
* `unitaryChannel` — conjugation by a unitary matrix.

## Main statements

* `channelDet_eq_linearMap_det` — `channelDet` agrees with `LinearMap.det`.
* `channelDet_comp` — Wolf Equation (6.22), determinant multiplicativity.
* `channelDet_norm_comp_le_of_positive_tracePreserving` — the inequality in
  Wolf's determinant-monotonicity corollary.
* `channelDet_norm_le_one_of_positive_tracePreserving` — Wolf Theorem 6.1(1).
* `channelDet_norm_eq_one_iff_exists_unitary_or_transpose_of_positive_tracePreserving`
  — Wolf Theorem 6.1(2) for positive trace-preserving maps.
* `ChannelDeterminant.Internal.channelDet_transposeLinearMapComplex` — the
  exact determinant of ordinary transposition in Wolf Theorem 6.1(3).
* `ChannelDeterminant.Internal.wolfPositiveInvertibleMaps` — positivity of the
  inverse exactly for unitary conjugation and transpose-conjugation.
* `ChannelDeterminant.Internal.wolfPositiveInvertibleSchwarzMaps` — the
  Schwarz refinement used in Wolf Theorem 6.16, where the transpose branch is
  excluded (and collapses to the unitary branch in dimension one).
* `channelDet_norm_eq_one_iff_exists_unitaryChannel` — Wolf Theorem 6.1(2)
  for CPTP maps.
* `IsKrausCP.channelDet_nonneg_of_choiRank_le_two` — nonnegativity for
  completely positive maps of Kraus rank at most two.
* `norm_channelDet_le_choiPurity_rpow` — Wolf Eq. (6.27), the Choi bound
  `|det T| ≤ tr[τ† τ]^{d²/2}` for an arbitrary linear map.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.1.1][Wolf2012QChannels]

## Tags

quantum channel, determinant, unitary channel, Wolf theorem
-/
