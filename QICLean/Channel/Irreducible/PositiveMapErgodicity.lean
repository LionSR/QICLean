/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.PositiveSemidefiniteNormalization
import QICLean.Analysis.WeightedCesaroMean
import QICLean.Channel.Irreducible.Ergodicity
import QICLean.Channel.Irreducible.FromSpectral

/-!
# Time averages and ergodicity for positive maps

This file proves Wolf Corollary 6.3 for positive trace-preserving maps.  The
time average is written with Wolf's literal one-indexed convention,

$$
  \frac{1}{N}\sum_{t=1}^{N} T^t(\rho),
$$

and is connected by exact equalities to the zero-indexed Cesàro and Birkhoff
averages used by the finite-dimensional mean-ergodic theorem.  The proof then
identifies the limit with the projection `T∞` from Wolf Equation (6.14).

## Main declarations

* `wolfTimeAverage`: the one-indexed time average in Wolf Equation (6.35).
* `wolfTimeAverage_eq_oneIndexedSum`: its literal expression as a sum over
  `Finset.Icc 1 N`.
* `IsPositiveMap.wolfTimeAverage_tendsto_of_irreducible`: convergence to the
  unique positive-definite stationary state.
* `wolf_corollary_6_3`: irreducibility is equivalent to Wolf's time-average
  characterization.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Corollary 6.3 and
  Equations (6.14), (6.35); local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 723--741.
-/

open Filter Matrix Finset
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius BigOperators

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Wolf's one-indexed time average from Equation (6.35):
`(1 / N) ∑ t ∈ {1, ..., N}, T^t(ρ)`.

The summation variable in `Finset.range N` is zero-indexed, so the exponent
`t + 1` represents Wolf's indices `1, ..., N` exactly. -/
noncomputable def wolfTimeAverage
    (T : Mat →ₗ[ℂ] Mat) (ρ : Mat) (N : ℕ) : Mat :=
  (1 / (N : ℂ)) • ∑ t ∈ Finset.range N, (T ^ (t + 1)) ρ

/-- The internally reindexed finite sum defining Wolf's time average. -/
theorem wolfTimeAverage_eq_reindexedSum
    (T : Mat →ₗ[ℂ] Mat) (ρ : Mat) (N : ℕ) :
    wolfTimeAverage T ρ N =
      (1 / (N : ℂ)) • ∑ t ∈ Finset.range N, (T ^ (t + 1)) ρ :=
  rfl

/-- Wolf's literal one-indexed expression for the time average in Equation
(6.35). -/
theorem wolfTimeAverage_eq_oneIndexedSum
    (T : Mat →ₗ[ℂ] Mat) (ρ : Mat) (N : ℕ) :
    wolfTimeAverage T ρ N =
      (1 / (N : ℂ)) • ∑ t ∈ Finset.Icc 1 N, (T ^ t) ρ := by
  rw [wolfTimeAverage_eq_reindexedSum,
    WeightedCesaro.sum_Icc_one_eq_sum_range]

/-- Wolf's one-indexed average of `ρ` is the zero-indexed Cesàro mean whose
initial matrix is `T ρ`. -/
theorem wolfTimeAverage_eq_cesaroMean
    (T : Mat →ₗ[ℂ] Mat) (ρ : Mat) (N : ℕ) :
    wolfTimeAverage T ρ N = cesaroMean T (T ρ) N := by
  rw [wolfTimeAverage_eq_reindexedSum, cesaroMean_eq]
  congr 1

/-- Wolf's one-indexed average is the Birkhoff average with initial matrix
`T ρ`.  This is the exact bridge to the mean-ergodic projection in Equation
(6.14). -/
theorem wolfTimeAverage_eq_birkhoffAverage
    (T : Mat →ₗ[ℂ] Mat) (ρ : Mat) (N : ℕ) :
    wolfTimeAverage T ρ N =
      birkhoffAverage ℂ T _root_.id N (T ρ) := by
  rw [wolfTimeAverage_eq_cesaroMean,
    cesaroMean_eq_birkhoffAverage]

/-- For an irreducible positive trace-preserving map, Wolf's one-indexed time
average of every density matrix converges to the unique positive-definite
stationary density matrix. -/
theorem IsPositiveMap.wolfTimeAverage_tendsto_of_irreducible [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T) (hIrr : IsIrreducibleMap T)
    {ρ : Mat} (hρ : ρ ∈ densityMatrices D) :
    ∃ σ : Mat,
      σ ∈ densityMatrices D ∧ σ.PosDef ∧ T σ = σ ∧
      (∀ τ : Mat,
        τ ∈ densityMatrices D → T τ = τ → τ = σ) ∧
      Tendsto (fun N => wolfTimeAverage T ρ N) atTop (nhds σ) := by
  obtain ⟨σ, hσ_mem, hσ_pd, hσ_fix, hσ_unique⟩ :=
    hT.exists_unique_density_fixedPoint_of_irreducible T hTP hIrr
  have hTρ_mem : T ρ ∈ densityMatrices D :=
    ⟨hT ρ hρ.1, by rw [hTP, hρ.2]⟩
  let hbounded := hT.hasBoundedOrbits_of_tracePreserving hTP
  let P : Mat →ₗ[ℂ] Mat :=
    LinearMap.meanErgodicProjection (𝕜 := ℂ) (E := Mat) T hbounded
  have hPTρ_mem : P (T ρ) ∈ densityMatrices D := by
    refine ⟨(hT.meanErgodicProjection_isPositiveMap hbounded) (T ρ) hTρ_mem.1, ?_⟩
    rw [hTP.meanErgodicProjection_isTracePreservingMap hbounded, hTρ_mem.2]
  have hPTρ_fix : T (P (T ρ)) = P (T ρ) := by
    have hcomp := congrArg (fun F : Mat →ₗ[ℂ] Mat ↦ F (T ρ))
      hbounded.comp_meanErgodicProjection
    simpa only [P, LinearMap.comp_apply] using hcomp
  have hPTρ_eq : P (T ρ) = σ :=
    hσ_unique (P (T ρ)) hPTρ_mem hPTρ_fix
  have hlimit : Tendsto (fun N => wolfTimeAverage T ρ N) atTop (nhds σ) := by
    simpa only [wolfTimeAverage_eq_birkhoffAverage, P, hbounded, hPTρ_eq] using
      hT.tendsto_birkhoffAverage_meanErgodicProjection_of_tracePreserving hTP (T ρ)
  exact ⟨σ, hσ_mem, hσ_pd, hσ_fix, hσ_unique, hlimit⟩

/-- **Wolf Corollary 6.3 (time-average and ergodicity).**

For a positive trace-preserving map on a nonzero full matrix algebra,
irreducibility is equivalent to the existence of a unique positive-definite
state to which the one-indexed time average of every initial state converges.

The proof follows Wolf's source argument: the average is the mean-ergodic
projection `T∞` from Equation (6.14), and the stationary-state
characterization is the trace-preserving specialization of Theorem 6.4. -/
theorem wolf_corollary_6_3 [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T) :
    IsIrreducibleMap T ↔
      ∃! σ : Mat,
        σ ∈ densityMatrices D ∧ σ.PosDef ∧
        ∀ ρ : Mat, ρ ∈ densityMatrices D →
          Tendsto (fun N => wolfTimeAverage T ρ N) atTop (nhds σ) := by
  constructor
  · intro hIrr
    obtain ⟨σ, hσ_mem, hσ_pd, hσ_fix, hσ_unique⟩ :=
      hT.exists_unique_density_fixedPoint_of_irreducible T hTP hIrr
    have hconv : ∀ ρ : Mat, ρ ∈ densityMatrices D →
        Tendsto (fun N => wolfTimeAverage T ρ N) atTop (nhds σ) := by
      intro ρ hρ
      obtain ⟨τ, hτ_mem, _hτ_pd, hτ_fix, _hτ_unique, hτ_limit⟩ :=
        hT.wolfTimeAverage_tendsto_of_irreducible T hTP hIrr hρ
      have hτ_eq : τ = σ := hσ_unique τ hτ_mem hτ_fix
      simpa only [hτ_eq] using hτ_limit
    refine ⟨σ, ⟨hσ_mem, hσ_pd, hconv⟩, ?_⟩
    intro τ hτ
    have hlimits := tendsto_nhds_unique (hconv σ hσ_mem) (hτ.2.2 σ hσ_mem)
    exact hlimits.symm
  · rintro ⟨σ, hσ, _hσ_unique⟩
    let hbounded := hT.hasBoundedOrbits_of_tracePreserving hTP
    let P : Mat →ₗ[ℂ] Mat :=
      LinearMap.meanErgodicProjection (𝕜 := ℂ) (E := Mat) T hbounded
    have hsource_sigma : Tendsto (fun N => wolfTimeAverage T σ N)
        atTop (nhds σ) := hσ.2.2 σ hσ.1
    have hsource_sigma_birkhoff :
        Tendsto (fun N => birkhoffAverage ℂ T _root_.id N (T σ))
          atTop (nhds σ) := by
      simpa only [wolfTimeAverage_eq_birkhoffAverage] using hsource_sigma
    have hmean_sigma :
        Tendsto (fun N => birkhoffAverage ℂ T _root_.id N (T σ))
          atTop (nhds (P (T σ))) := by
      simpa only [P, hbounded] using
        hT.tendsto_birkhoffAverage_meanErgodicProjection_of_tracePreserving hTP (T σ)
    have hPTsigma : P (T σ) = σ :=
      tendsto_nhds_unique hmean_sigma hsource_sigma_birkhoff
    have hPTsigma_eq_Psigma : P (T σ) = P σ := by
      have hcomp := congrArg (fun F : Mat →ₗ[ℂ] Mat ↦ F σ)
        hbounded.meanErgodicProjection_comp
      simpa only [P, LinearMap.comp_apply] using hcomp
    have hPsigma : P σ = σ := hPTsigma_eq_Psigma.symm.trans hPTsigma
    have hσ_fix : T σ = σ :=
      (hT.meanErgodicProjection_apply_eq_self_iff_of_tracePreserving hTP σ).1 <| by
        simpa only [P, hbounded] using hPsigma
    apply isIrreducibleMap_of_positive_tracePreserving_posDef_fixedPoint_unique
      T hT hTP σ hσ.2.1 hσ_fix
    intro τ hτ_psd hτ_fix
    by_cases hτ_zero : τ = 0
    · exact ⟨0, by simp [hτ_zero]⟩
    let τ₀ : Mat := Matrix.normalizePosSemidef (0 : Fin D) τ
    have hτ₀_mem : τ₀ ∈ densityMatrices D :=
      ⟨Matrix.normalizePosSemidef_posSemidef (0 : Fin D) hτ_psd,
        Matrix.normalizePosSemidef_trace (0 : Fin D) hτ_psd⟩
    have htrace_re_ne : τ.trace.re ≠ 0 := by
      intro htrace_re
      have htrace_zero : τ.trace = 0 := by
        apply Complex.ext
        · simpa using htrace_re
        · simpa using (Complex.nonneg_iff.mp hτ_psd.trace_nonneg).2.symm
      exact hτ_zero (hτ_psd.trace_eq_zero_iff.mp htrace_zero)
    have hτ₀_fix : T τ₀ = τ₀ := by
      simp [τ₀, Matrix.normalizePosSemidef, htrace_re_ne, hτ_fix]
    have haverage_eventually : ∀ᶠ N : ℕ in atTop,
        wolfTimeAverage T τ₀ N = τ₀ := by
      filter_upwards [Filter.eventually_ne_atTop (0 : ℕ)] with N hN
      have hN_complex : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      rw [wolfTimeAverage_eq_birkhoffAverage, hτ₀_fix]
      simpa using
        (show Function.IsFixedPt T τ₀ from hτ₀_fix).birkhoffAverage_eq
          (R := ℂ) _root_.id hN_complex
    have haverage_tendsto_tau₀ :
        Tendsto (fun N => wolfTimeAverage T τ₀ N) atTop (nhds τ₀) :=
      tendsto_const_nhds.congr'
        (haverage_eventually.mono fun _ haverage ↦ haverage.symm)
    have hτ₀_eq : τ₀ = σ :=
      tendsto_nhds_unique haverage_tendsto_tau₀ (hσ.2.2 τ₀ hτ₀_mem)
    refine ⟨(τ.trace.re : ℂ), ?_⟩
    calc
      τ = (τ.trace.re : ℂ) • τ₀ :=
        (Matrix.trace_re_smul_normalizePosSemidef (0 : Fin D) hτ_psd).symm
      _ = (τ.trace.re : ℂ) • σ := by rw [hτ₀_eq]
