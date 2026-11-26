/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.FixedPoint.Weighted.AbstractWeightedFixedPoints
import QICLean.Channel.FixedPoint.Stationary.MaximalSupportBasic
import QICLean.Channel.FixedPoint.Weighted.WeightedCornerFixedPoints
import QICLean.Channel.KrausMap.KrausMap

/-!
# The support of a maximum-rank fixed point carries every fixed point

Corollary 6.7 of *Quantum Channels & Operations* (Wolf 2012) quantifies over an arbitrary
maximum-rank fixed-point density matrix. The results here transfer the maximal-support
property from the constructed witness of
`Kraus.exists_maximalSupport_fixedPoint` to every fixed point of maximum rank: if $\rho$
is a positive semidefinite fixed point of the trace-preserving Kraus map $T$ whose rank
bounds the rank of every fixed-point density matrix, then the support projection $Q$ of
$\rho$ satisfies $Q X Q = X$ for every fixed point $X$ of $T$. Consequently conjugation by
$\sqrt{\rho}$ maps the weighted corner carrier of
`Kraus.weightedCornerFixedPointsStarSubalgebra` onto the full fixed-point set at every
such $\rho$, which realizes the conjugated set
$\rho^{-1/2}\,\{X \mid T(X) = X\}\,\rho^{-1/2}$ of the corollary, with the inverse square
root taken on the support of $\rho$.

These declarations are compatibility specializations of the source-general
`IsPositiveMap` results in `AbstractMaximalRank` and
`AbstractWeightedFixedPoints`; the proofs below introduce no independent
Kraus-specific route.

The comparison with the constructed witness $\rho_0$ goes through the rank: the support
projection of a positive semidefinite matrix has the same rank as the matrix, and its
trace is that rank. From $Q_0 \rho Q_0 = \rho$ the rank of $\rho$ is at most that of
$\rho_0$; maximality applied to the normalization of $\rho_0$ gives the reverse
inequality; and two orthogonal projections $P \preceq Q_0$ (in the sense $Q_0 P = P$)
with equal traces are equal, so the support projections coincide.

## Main results

* `Kraus.rank_stationaryProj` -- the support projection of a positive semidefinite matrix
  has the rank of the matrix.
* `Kraus.trace_stationaryProj` -- the trace of the support projection is the rank.
* `Kraus.maximalSupport_of_maximalRank` -- the support of a fixed point of maximum rank
  carries every fixed point.
* `Kraus.exists_weightedCorner_sqrt_eq_of_maximalRank` -- at every fixed point of maximum
  rank, conjugation by the square root maps the weighted corner carrier onto the full
  fixed-point set.
* `Kraus.exists_maximalSupport_fixedPoint`, `Kraus.exists_maximalSupport_weightedCorner_sqrt_eq`:
  maximal-support fixed points for Kraus maps.
-/

section MaximalSupport

/-!
## Maximal-support fixed points for Kraus maps

This file specializes the positive-map maximal-support theorem from
`QICLean.Channel.FixedPoint.Stationary.MaximalSupportBasic` to trace-preserving Kraus maps
and relates the resulting fixed point to the weighted corner algebra.

### Main results

* `Kraus.exists_maximalSupport_fixedPoint` -- a positive semidefinite fixed
  point whose support carries every fixed point of a trace-preserving Kraus map.
* `Kraus.exists_maximalSupport_weightedCorner_sqrt_eq` -- conjugation by the
  square root identifies the weighted corner carrier with the full fixed-point set.

### References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.9 and
  Corollary 6.7.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **A fixed point of maximal support for a Kraus map.** The mean-ergodic image
of the identity is a positive semidefinite fixed point whose support carries every fixed
point of the trace-preserving Kraus map. This is the completely positive specialization
of Wolf, Proposition 6.9, formalized for arbitrary positive trace-preserving maps by
`IsPositiveMap.exists_maximalSupport_fixedPoint`. -/
theorem exists_maximalSupport_fixedPoint (K : Fin d → Mat) (h_tp : IsTP K) :
    ∃ (ρ₀ : Mat) (hρ₀ : ρ₀.PosSemidef), map K ρ₀ = ρ₀ ∧
      ∀ X : Mat, map K X = X → stationaryProj hρ₀ * X * stationaryProj hρ₀ = X := by
  let E : Mat →ₗ[ℂ] Mat := mapLM K
  have hE : IsChannel E := isChannel_mapLM K h_tp
  let hbounded := hE.cp.isPositiveMap.hasBoundedOrbits_of_tracePreserving hE.tp
  let ρ₀ : Mat := LinearMap.meanErgodicProjection (𝕜 := ℂ) (E := Mat)
    E hbounded 1
  have hgeneric : ∃ hρ₀ : ρ₀.PosSemidef, E ρ₀ = ρ₀ ∧
      ∀ X : Mat, E X = X → stationaryProj hρ₀ * X * stationaryProj hρ₀ = X := by
    simpa only [ρ₀, hbounded] using
      hE.cp.isPositiveMap.exists_maximalSupport_fixedPoint hE.tp
  obtain ⟨hρ₀, hfix, hmax⟩ := hgeneric
  refine ⟨ρ₀, hρ₀, ?_, ?_⟩
  · simpa [E] using hfix
  · intro X hX
    apply hmax X
    simpa [E] using hX

/-- **Conjugation by the square root at a fixed point of maximal support.** For a
trace-preserving Kraus map $T$ there is a positive semidefinite fixed point $\rho_0$ such
that every fixed point $X$ of $T$ arises as $X = \sqrt{\rho_0}\, Y \sqrt{\rho_0}$ for a
corner-supported $Y$ with $\sqrt{\rho_0}\, Y \sqrt{\rho_0}$ fixed by $T$: conjugation by
$\sqrt{\rho_0}$ maps the carrier of the weighted corner star-subalgebra
(`Kraus.weightedCornerFixedPointsStarSubalgebra`) onto the full fixed-point set, so that
set realizes, with the inverse square root taken on the support of $\rho_0$,
$$\rho_0^{-1/2}\,\{X \mid T(X) = X\}\,\rho_0^{-1/2}.$$ This is the conjugated
fixed-point set of Corollary 6.7 of *Quantum Channels & Operations* (Wolf 2012), at a
fixed point of maximal support. -/
theorem exists_maximalSupport_weightedCorner_sqrt_eq (K : Fin d → Mat) (h_tp : IsTP K) :
    ∃ (ρ₀ : Mat) (hρ₀ : ρ₀.PosSemidef), map K ρ₀ = ρ₀ ∧
      ∀ X : Mat, map K X = X →
        ∃ Y : Mat, stationaryProj hρ₀ * Y * stationaryProj hρ₀ = Y ∧
          map K (CFC.sqrt ρ₀ * Y * CFC.sqrt ρ₀) = CFC.sqrt ρ₀ * Y * CFC.sqrt ρ₀ ∧
          CFC.sqrt ρ₀ * Y * CFC.sqrt ρ₀ = X := by
  obtain ⟨ρ₀, hρ₀, hfix, hmax⟩ := exists_maximalSupport_fixedPoint K h_tp
  exact ⟨ρ₀, hρ₀, hfix, fun X hX =>
    exists_weightedCorner_sqrt_eq_of_fixedPoint K h_tp hρ₀ hfix hX (hmax X hX)⟩

end Kraus

end MaximalSupport

section MaximalRank

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- **The support projection has the rank of the matrix.** For positive semidefinite
$\rho$ with spectral decomposition $\rho = U\,\mathrm{diag}(\lambda)\,U^{\dagger}$, the
support projection is $U\,\mathrm{diag}(\mathbf 1_{\lambda > 0})\,U^{\dagger}$, and both
ranks count the indices with $\lambda_i \neq 0$, which for nonnegative eigenvalues are
the indices with $\lambda_i > 0$. -/
theorem rank_stationaryProj {ρ : Mat} (hρ_psd : ρ.PosSemidef) :
    (stationaryProj hρ_psd).rank = ρ.rank := by
  have hrank_re :=
    (isOrthogonalProjection_stationaryProj hρ_psd).1.rank_eq_trace_re_of_idem
      (isOrthogonalProjection_stationaryProj hρ_psd).2
  have htrace : (stationaryProj hρ_psd).trace = (ρ.rank : ℂ) := by
    simpa [stationaryProj] using hρ_psd.supportProj_trace
  rw [htrace] at hrank_re
  exact_mod_cast hrank_re

/-- **The trace of the support projection is the rank.** In the spectral decomposition
the support projection is $U\,\mathrm{diag}(\mathbf 1_{\lambda > 0})\,U^{\dagger}$, whose
trace counts the positive eigenvalues, and for a positive semidefinite matrix that count
is the rank. -/
theorem trace_stationaryProj {ρ : Mat} (hρ_psd : ρ.PosSemidef) :
    (stationaryProj hρ_psd).trace = (ρ.rank : ℂ) := by
  simpa [stationaryProj] using hρ_psd.supportProj_trace

/-- **The support of a fixed point of maximum rank carries every fixed point.** Let $T$
be a trace-preserving Kraus map and let $\rho$ be a positive semidefinite fixed point of
$T$ whose rank bounds the rank of every fixed-point density matrix (every positive
semidefinite fixed point of unit trace). Then the support projection $Q$ of $\rho$
satisfies $Q X Q = X$ for every fixed point $X$ of $T$. In Corollary 6.7 of
*Quantum Channels & Operations* (Wolf 2012) the maximum-rank fixed point is a density
matrix; unit trace of $\rho$ itself is not needed for the conclusion and is not assumed
here. The support projection of $\rho$ is compared with that of the constructed maximal
witness through the rank: the two support projections have equal traces and one absorbs
the other, so they coincide. -/
theorem maximalSupport_of_maximalRank
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat} (hρ_psd : ρ.PosSemidef)
    (hρ_fix : map K ρ = ρ)
    (hρ_max : ∀ σ : Mat, σ.PosSemidef → σ.trace = 1 → map K σ = σ → σ.rank ≤ ρ.rank) :
    ∀ X : Mat, map K X = X →
      stationaryProj hρ_psd * X * stationaryProj hρ_psd = X := by
  intro X hX
  exact IsPositiveMap.maximalSupport_of_maximalRank
    (isPositiveMap_mapLM K)
    (isTracePreservingMap_mapLM_of_isTP K h_tp)
    hρ_psd
    (by simpa only [mapLM_apply] using hρ_fix)
    (by
      intro σ hσ hσTrace hσFix
      exact hρ_max σ hσ hσTrace
        (by simpa only [mapLM_apply] using hσFix))
    X
    (by simpa only [mapLM_apply] using hX)

/-- **Conjugation by the square root at every fixed point of maximum rank.** Let $T$ be a
trace-preserving Kraus map and let $\rho$ be a positive semidefinite fixed point of $T$
whose rank bounds the rank of every fixed-point density matrix. Then every fixed point
$X$ of $T$ arises as $X = \sqrt{\rho}\, Y \sqrt{\rho}$ for a corner-supported $Y$ with
$\sqrt{\rho}\, Y \sqrt{\rho}$ fixed by $T$: conjugation by $\sqrt{\rho}$ maps the carrier
of `Kraus.weightedCornerFixedPointsStarSubalgebra` onto the full fixed-point set, which
realizes the set $\rho^{-1/2}\,\{X \mid T(X) = X\}\,\rho^{-1/2}$ of Corollary 6.7 of
*Quantum Channels & Operations* (Wolf 2012) at every fixed point of maximum rank, with
the inverse square root taken on the support of $\rho$. -/
theorem exists_weightedCorner_sqrt_eq_of_maximalRank
    (K : Fin d → Mat) (h_tp : IsTP K) {ρ : Mat} (hρ_psd : ρ.PosSemidef)
    (hρ_fix : map K ρ = ρ)
    (hρ_max : ∀ σ : Mat, σ.PosSemidef → σ.trace = 1 → map K σ = σ → σ.rank ≤ ρ.rank)
    {X : Mat} (hX_fix : map K X = X) :
    ∃ Y : Mat, stationaryProj hρ_psd * Y * stationaryProj hρ_psd = Y ∧
      map K (CFC.sqrt ρ * Y * CFC.sqrt ρ) = CFC.sqrt ρ * Y * CFC.sqrt ρ ∧
      CFC.sqrt ρ * Y * CFC.sqrt ρ = X := by
  simpa only [mapLM_apply] using
    IsPositiveMap.exists_weightedCorner_sqrt_eq_of_maximalRank
      (isPositiveMap_mapLM K)
      (isTracePreservingMap_mapLM_of_isTP K h_tp)
      hρ_psd
      (by simpa only [mapLM_apply] using hρ_fix)
      (by
        intro σ hσ hσTrace hσFix
        exact hρ_max σ hσ hσTrace
          (by simpa only [mapLM_apply] using hσFix))
      (by simpa only [mapLM_apply] using hX_fix)

end Kraus

end MaximalRank
