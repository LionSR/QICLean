/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Norm.MatrixOperatorSpace
import QICLean.Channel.Determinant.Bound
import QICLean.Channel.KrausMap.KrausMap
import QICLean.Channel.FixedPoint.Stationary.StationaryStates
import QICLean.Channel.Schwarz.RussoDye
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Spectral radius of positive maps — Wolf Proposition 6.1, trace-preserving case

**Wolf Proposition 6.1**: if
$T: M_d(\mathbb{C}) \to M_d(\mathbb{C})$ is positive and $d \ge 1$, then
$\varrho(T) \le \|T(\mathbf 1)\|_\infty$.  If $T$ is unital or
trace-preserving, then $1$ is an eigenvalue, the spectral radius is $1$, and
all eigenvalues lie in the closed unit disk.

The Russo--Dye estimate, Equations (6.2) and (6.3) and the unital case are in
`QICLean.Channel.Schwarz.RussoDye`.  This file proves the
trace-preserving case: a positive trace-preserving map has a positive
semidefinite fixed point, obtained from the Brouwer eigenvector
`exists_posSemidef_eigenvector`, and its eigenvalues lie in the closed unit
disk by the orbit-and-trace bound
`IsPositiveMap.eigenvalue_norm_le_one_of_tracePreserving`.

The norm in these declarations is the matrix C*-operator norm (Wolf's
$\|\cdot\|_\infty$), not the Frobenius norm or Mathlib's row-sum norm.

## Main result

* `IsPositiveMap.eigenvalue_one_exists_of_tracePreserving`: the
  trace-preserving fixed point.
* `IsPositiveMap.spectralRadius_eq_one_of_tracePreserving`: the
  trace-preserving spectral-radius equality.
* `Kraus.eigenvalue_norm_le_one_of_isTP`, `Kraus.spectralRadius_mapLM_le_one_of_isTP`:
  eigenvalue and spectral-radius bounds for trace-preserving Kraus maps.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.1][Wolf2012Quantum]
-/

open scoped Matrix ComplexOrder NNReal
open Matrix

variable {D : ℕ}

namespace IsPositiveMap

/-- **Wolf Proposition 6.1** (eigenvalue-1 existence): For a positive trace-preserving
map on $M_D(\mathbb{C})$ with $D > 0$, there exists a nonzero PSD matrix $\rho$
such that $T(\rho) = \rho$.

This completes the trace-preserving case of Wolf's Proposition 6.1:
combined with `eigenvalue_norm_le_one_of_tracePreserving` (which gives
$|\lambda| \le 1$ for every eigenvalue), we get that the spectral radius is $1$
and $1$ is an eigenvalue.

The proof obtains a PSD eigenvector with eigenvalue $r > 0$ via
`exists_posSemidef_eigenvector` (Perron--Frobenius / Brouwer fixed point),
then forces $r = 1$ by trace preservation.

Source: Wolf, *Quantum Channels & Operations*, Proposition 6.1; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 73--92. -/
theorem eigenvalue_one_exists_of_tracePreserving
    [NeZero D] {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosSemidef ∧ ρ ≠ 0 ∧ T ρ = ρ := by
  -- For a trace-preserving positive map, nonzero PSD matrices cannot be annihilated:
  -- if T(ρ) = 0 then trace preservation gives trace(ρ) = 0,
  -- but a nonzero PSD matrix has positive trace.
  have hNZ : ∀ {ρ : Matrix (Fin D) (Fin D) ℂ}, ρ.PosSemidef → ρ ≠ 0 → T ρ ≠ 0 := by
    intro ρ hρ_psd hρ_ne hzero
    have htr_zero : trace (T ρ) = 0 := by simp [hzero]
    rw [hTP ρ] at htr_zero
    have htr_pos : 0 < trace ρ := by
      have h_nonneg := hρ_psd.trace_nonneg
      have h_ne_zero : trace ρ ≠ 0 := mt hρ_psd.trace_eq_zero_iff.mp hρ_ne
      exact h_nonneg.lt_of_ne h_ne_zero.symm
    exact htr_pos.ne' htr_zero
  -- Get eigenvalue r > 0 with PSD eigenvector (Perron--Frobenius)
  obtain ⟨ρ, r, hρ_psd, hρ_ne, hr_pos, h_eig⟩ :=
    exists_posSemidef_eigenvector (D := D) T hPos (hNZ := hNZ)
  -- Trace preservation forces r = 1
  have hr_one : r = 1 := by
    have htr_eq : trace (T ρ) = trace ρ := hTP ρ
    rw [h_eig, trace_smul, smul_eq_mul] at htr_eq
    have htr_ne_zero : trace ρ ≠ 0 := mt hρ_psd.trace_eq_zero_iff.mp hρ_ne
    field_simp [htr_ne_zero] at htr_eq
    exact_mod_cast htr_eq
  refine ⟨ρ, hρ_psd, hρ_ne, ?_⟩
  simpa [hr_one, one_smul] using h_eig

section TracePreservingSpectral

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- **Wolf Proposition 6.1, trace-preserving case**: a positive
trace-preserving matrix map has spectral radius exactly `1`.

The closed-unit-disk bound is the existing orbit-and-trace result, and the
reverse inequality follows from the existing positive semidefinite fixed
point. -/
theorem spectralRadius_eq_one_of_tracePreserving
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    spectralRadius ℂ
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) T) = 1 := by
  apply le_antisymm
  · exact spectralRadius_le_one_of_forall_eigenvalue_norm_le_one T
      (hT.eigenvalue_norm_le_one_of_tracePreserving hTP)
  · obtain ⟨ρ, _, hρne, hρ⟩ := hT.eigenvalue_one_exists_of_tracePreserving hTP
    have hOne : Module.End.HasEigenvalue T 1 := by
      apply Module.End.hasEigenvalue_of_hasEigenvector
      rw [Module.End.hasEigenvector_iff]
      refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hρne⟩
      simpa only [one_smul] using hρ
    have hOneSpec :
        (1 : ℂ) ∈
          spectrum ℂ (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) T) := by
      rw [AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) T]
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hOne
    rw [spectralRadius_eq_of_unital]
    simpa using (@le_iSup₂ ENNReal ℂ
      (· ∈ spectrum ℂ (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) T)) _
      (fun μ _ ↦ (‖μ‖₊ : ENNReal)) 1 hOneSpec)

end TracePreservingSpectral

end IsPositiveMap

/-!
## Spectral-radius bound for trace-preserving Kraus maps

A trace-preserving finite Kraus map has all eigenvalues in the closed unit
disk: it is a completely positive trace-preserving map, so
`IsPositiveMap.eigenvalue_norm_le_one_of_tracePreserving` applies once the
trivial zero-dimensional case is discharged separately.
-/

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Every eigenvalue of a trace-preserving finite Kraus map has modulus at most one.

This is the trace-preserving form of the spectral bound in Wolf, Proposition 6.1,
obtained from the positive-map bound after discharging the trivial
zero-dimensional case. -/
theorem eigenvalue_norm_le_one_of_isTP
    (K : Fin d → Mat) (hTP : IsTP K)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (mapLM K) μ) :
    ‖μ‖ ≤ 1 := by
  rcases eq_or_ne D 0 with hD0 | hD0
  · subst hD0
    obtain ⟨v, hv, hvne⟩ := hμ.exists_hasEigenvector
    exact absurd (Subsingleton.elim v 0) hvne
  · have : NeZero D := ⟨hD0⟩
    exact (isCPMap_mapLM K).isPositiveMap.eigenvalue_norm_le_one_of_tracePreserving
      (isTracePreservingMap_mapLM_of_isTP K hTP) μ hμ

section OperatorSpace

open scoped TNOperatorSpace

/-- A trace-preserving finite Kraus map has spectral radius at most one. -/
theorem spectralRadius_mapLM_le_one_of_isTP
    (K : Fin d → Mat) (hTP : IsTP K) :
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ)) (mapLM K)) ≤ 1 :=
  spectralRadius_le_one_of_forall_eigenvalue_norm_le_one (mapLM K)
    (fun μ hμ ↦ eigenvalue_norm_le_one_of_isTP K hTP μ hμ)

end OperatorSpace

end Kraus
