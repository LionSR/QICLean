/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixOperatorSpace
import QICLean.Channel.Determinant.Bound
import QICLean.Channel.KrausMap
import QICLean.Channel.PerronFrobenius.Existence
import QICLean.Channel.Schwarz.SchwarzSubnormal
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Spectral radius of positive maps — Wolf Proposition 6.1

**Wolf Proposition 6.1**: if
$T: M_d(\mathbb{C}) \to M_d(\mathbb{C})$ is positive and $d \ge 1$, then
$\varrho(T) \le \|T(\mathbf 1)\|_\infty$.  If $T$ is unital or
trace-preserving, then $1$ is an eigenvalue, the spectral radius is $1$, and
all eigenvalues lie in the closed unit disk.

Wolf invokes the Russo--Dye estimate
$\|T(X)\|_\infty \le \|T(\mathbf 1)\|_\infty\|X\|_\infty$.  No standalone
Russo--Dye theorem is available in the pinned Mathlib.  For finite matrices,
this file derives precisely the estimate needed by Proposition 6.1 from
Wolf's Theorem 5.6 (`schwarz_inequality_commuting_dominant_operator`), taking
the dominant operator to be the identity after normalizing the map.  This
retains the sharp coefficient one and does not use the four-positive-parts
bound.

The norm in these declarations is the matrix C*-operator norm (Wolf's
$\|\cdot\|_\infty$), not the Frobenius norm or Mathlib's row-sum norm.  The
pre-existing trace-preserving results are retained independently.

## Main result

* `IsPositiveMap.norm_apply_le_norm_map_one_mul_norm`: the sharp matrix
  Russo--Dye estimate used by Wolf.
* `IsPositiveMap.eigenvalue_norm_le_norm_map_one` and
  `IsPositiveMap.spectralRadius_le_nnnorm_map_one`: Equations (6.3) and (6.2).
* `eigenvalue_one_of_map_one_eq_one`,
  `IsPositiveMap.eigenvalue_norm_le_one_of_map_one_eq_one`, and
  `IsPositiveMap.spectralRadius_eq_one_of_map_one_eq_one`: the unital case.
* `IsPositiveMap.eigenvalue_one_exists_of_tracePreserving`: the
  trace-preserving fixed point.
* `IsPositiveMap.spectralRadius_eq_one_of_tracePreserving`: the
  trace-preserving spectral-radius equality.
* `spectralRadius_le_of_forall_eigenvalue_nnnorm_le`: the norm-agnostic step
  from pointwise eigenvalue bounds to a spectral-radius bound.
* `Kraus.eigenvalue_norm_le_one_of_isTP`, `Kraus.spectralRadius_mapLM_le_one_of_isTP`:
  eigenvalue and spectral-radius bounds for trace-preserving Kraus maps.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.1][Wolf2012Quantum]
-/

open scoped Matrix ComplexOrder NNReal
open Matrix

variable {D : ℕ}

namespace IsPositiveMap

section RussoDye

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- A nonnegative real multiple of a positive matrix map is positive. -/
private theorem smul_nonneg
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) {c : ℝ} (hc : 0 ≤ c) :
    IsPositiveMap ((c : ℂ) • T) := by
  intro X hX
  have hcC : 0 ≤ (c : ℂ) := by exact_mod_cast hc
  simpa only [LinearMap.smul_apply, Complex.coe_smul] using (hT X hX).smul hcC

/-- The sharp matrix Russo--Dye estimate for a contraction: if `T` is positive and
`‖A‖∞ ≤ 1`, then `‖T A‖∞ ≤ ‖T 1‖∞`.

Here `‖·‖∞` is the matrix C*-algebra (spectral/operator) norm, not the
Frobenius norm.  The proof derives the estimate from Wolf's Theorem 5.6 for a
positive subunital map, after normalizing by `‖T 1‖∞`. -/
theorem norm_apply_le_norm_map_one_of_norm_le_one
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) {A : Matrix (Fin D) (Fin D) ℂ}
    (hA : ‖A‖ ≤ 1) :
    ‖T A‖ ≤ ‖T 1‖ := by
  let c : ℝ := ‖T 1‖
  have hc : 0 ≤ c := norm_nonneg _
  have hAstarA : Aᴴ * A ≤ (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [← CStarAlgebra.norm_le_one_iff_of_nonneg
      (Aᴴ * A) (Matrix.posSemidef_conjTranspose_mul_self A).nonneg,
      Matrix.l2_opNorm_conjTranspose_mul_self]
    nlinarith [norm_nonneg A]
  by_cases hc0 : c = 0
  · have hT1zero : T 1 = 0 := norm_eq_zero.mp (by simpa only [c] using hc0)
    have hSub : T 1 ≤ (1 : Matrix (Fin D) (Fin D) ℂ) := by
      rw [hT1zero]
      exact Matrix.PosSemidef.one.nonneg
    have hKS :=
      KadisonSchwarz.schwarz_inequality_commuting_dominant_operator
        T hT hSub A 1 Matrix.PosSemidef.one (Commute.one_left A) hAstarA
    have hProdLe : (T A)ᴴ * T A ≤ 0 := by
      calc
        (T A)ᴴ * T A = T Aᴴ * T A := by rw [hT.map_conjTranspose]
        _ ≤ T 1 := hKS.1
        _ = 0 := hT1zero
    have hProdEq : (T A)ᴴ * T A = 0 := by
      apply le_antisymm hProdLe
      exact (Matrix.posSemidef_conjTranspose_mul_self (T A)).nonneg
    have hTAzero : T A = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp hProdEq
    simp [hTAzero, c, hc0]
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    let S : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
      ((c⁻¹ : ℝ) : ℂ) • T
    have hSPos : IsPositiveMap S := by
      exact smul_nonneg hT (inv_nonneg.mpr hc)
    have hS1nonneg : 0 ≤ S 1 := by
      exact (hSPos 1 Matrix.PosSemidef.one).nonneg
    have hS1norm : ‖S 1‖ ≤ 1 := by
      have hEq : ‖S 1‖ = 1 := by
        simp [S, c, norm_smul, hc0]
      exact hEq.le
    have hSub : S 1 ≤ (1 : Matrix (Fin D) (Fin D) ℂ) :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg (S 1) hS1nonneg).mp hS1norm
    have hKS :=
      KadisonSchwarz.schwarz_inequality_commuting_dominant_operator
        S hSPos hSub A 1 Matrix.PosSemidef.one (Commute.one_left A) hAstarA
    have hProdLe : (S A)ᴴ * S A ≤ (1 : Matrix (Fin D) (Fin D) ℂ) := by
      calc
        (S A)ᴴ * S A = S Aᴴ * S A := by rw [hSPos.map_conjTranspose]
        _ ≤ S 1 := hKS.1
        _ ≤ 1 := hSub
    have hProdNorm : ‖(S A)ᴴ * S A‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg
        ((S A)ᴴ * S A) (Matrix.posSemidef_conjTranspose_mul_self (S A)).nonneg).mpr hProdLe
    rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hProdNorm
    have hSAnorm : ‖S A‖ ≤ 1 := by
      nlinarith [norm_nonneg (S A)]
    have hScaled : c⁻¹ * ‖T A‖ ≤ 1 := by
      simpa [S, norm_smul, abs_of_nonneg hc] using hSAnorm
    rw [inv_mul_le_iff₀ hcpos] at hScaled
    simpa only [mul_one, c] using hScaled

/-- The sharp matrix Russo--Dye estimate used on Wolf's Proposition 6.1, source line 84:
`‖T A‖∞ ≤ ‖T 1‖∞ ‖A‖∞`.

The norm is the C*-operator norm.  This formalization obtains the estimate as
a consequence of Wolf's Theorem 5.6 with dominant operator `Dom = 1`; it does
not pass through the four-positive-parts bound. -/
theorem norm_apply_le_norm_map_one_mul_norm
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (A : Matrix (Fin D) (Fin D) ℂ) :
    ‖T A‖ ≤ ‖T 1‖ * ‖A‖ := by
  by_cases hA0 : A = 0
  · simp [hA0]
  · have hAnormPos : 0 < ‖A‖ := norm_pos_iff.mpr hA0
    let B : Matrix (Fin D) (Fin D) ℂ := (((‖A‖⁻¹ : ℝ) : ℂ) • A)
    have hBnorm : ‖B‖ ≤ 1 := by
      have hEq : ‖B‖ = 1 := by
        simp [B, norm_smul, hA0]
      exact hEq.le
    have hContract := hT.norm_apply_le_norm_map_one_of_norm_le_one hBnorm
    have hScaled : ‖A‖⁻¹ * ‖T A‖ ≤ ‖T 1‖ := by
      simpa [B, norm_smul, abs_of_nonneg (norm_nonneg A)] using hContract
    rw [inv_mul_le_iff₀ hAnormPos] at hScaled
    simpa only [mul_comm] using hScaled

/-- **Wolf Equation (6.3)**: every eigenvalue `μ` of a positive matrix map
satisfies `|μ| ≤ ‖T 1‖∞`. -/
theorem eigenvalue_norm_le_norm_map_one
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (μ : ℂ) (hμ : Module.End.HasEigenvalue T μ) :
    ‖μ‖ ≤ ‖T 1‖ := by
  obtain ⟨A, hAmem, hAne⟩ := hμ.exists_hasEigenvector
  have hEig : T A = μ • A := Module.End.mem_eigenspace_iff.mp hAmem
  have hBound := hT.norm_apply_le_norm_map_one_mul_norm A
  rw [hEig, norm_smul] at hBound
  exact le_of_mul_le_mul_right hBound (norm_pos_iff.mpr hAne)

end RussoDye

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

end IsPositiveMap

/-- If every eigenvalue of a linear endomorphism of a finite-dimensional complex normed space
has `nnnorm` at most `c`, then its spectral radius (computed after transport to the induced
continuous linear map) is at most `c`.

This is the norm-agnostic passage from an algebraic eigenvalue bound to a
spectral-radius bound. -/
theorem spectralRadius_le_of_forall_eigenvalue_nnnorm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (E : V →ₗ[ℂ] V) (c : ℝ≥0)
    (h : ∀ μ, Module.End.HasEigenvalue E μ → ‖μ‖₊ ≤ c) :
    spectralRadius ℂ (Module.End.toContinuousLinearMap V E) ≤ c := by
  have hSpec : spectrum ℂ (Module.End.toContinuousLinearMap V E) = spectrum ℂ E :=
    AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap V) E
  rw [spectralRadius]
  refine iSup₂_le fun μ hμ ↦ ?_
  have hμE : μ ∈ spectrum ℂ E := hSpec ▸ hμ
  have hEig : Module.End.HasEigenvalue E μ := Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμE
  exact_mod_cast h μ hEig

/-- If every eigenvalue of a linear endomorphism of a finite-dimensional complex normed space
has modulus at most one, then its spectral radius (computed after transport to the induced
continuous linear map) is at most one.

This is the norm-agnostic step of Wolf Proposition 6.1's spectral-radius conclusion: only the
algebraic fact `spectrum = eigenvalues` and the identification of `spectrum` along the
`AlgEquiv` to continuous linear maps are used, so the same argument serves any choice of
operator norm on `V`. -/
theorem spectralRadius_le_one_of_forall_eigenvalue_norm_le_one
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (E : V →ₗ[ℂ] V) (h : ∀ μ, Module.End.HasEigenvalue E μ → ‖μ‖ ≤ 1) :
    spectralRadius ℂ (Module.End.toContinuousLinearMap V E) ≤ 1 :=
  spectralRadius_le_of_forall_eigenvalue_nnnorm_le E 1 fun μ hμ ↦ by
    exact_mod_cast h μ hμ

/-- A unital matrix endomorphism has eigenvalue `1`, with the identity matrix
as an eigenvector. -/
theorem eigenvalue_one_of_map_one_eq_one
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hOne : T 1 = 1) : Module.End.HasEigenvalue T 1 := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
  rw [Module.End.hasEigenvector_iff]
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, one_ne_zero⟩
  simp only [hOne, one_smul]

/-- The norm-agnostic passage from a closed-unit-disk eigenvalue bound and the
eigenvalue `1` to spectral radius exactly `1`. -/
private theorem spectralRadius_eq_one_of_eigenvalue_bounds
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (E : V →ₗ[ℂ] V)
    (hBound : ∀ μ, Module.End.HasEigenvalue E μ → ‖μ‖ ≤ 1)
    (hOne : Module.End.HasEigenvalue E 1) :
    spectralRadius ℂ (Module.End.toContinuousLinearMap V E) = 1 := by
  apply le_antisymm
  · exact spectralRadius_le_one_of_forall_eigenvalue_norm_le_one E hBound
  · have hSpec : spectrum ℂ (Module.End.toContinuousLinearMap V E) = spectrum ℂ E :=
      AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap V) E
    have hOneSpec : (1 : ℂ) ∈ spectrum ℂ (Module.End.toContinuousLinearMap V E) := by
      rw [hSpec]
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp hOne
    rw [spectralRadius]
    simpa using (@le_iSup₂ ENNReal ℂ
      (· ∈ spectrum ℂ (Module.End.toContinuousLinearMap V E)) _
      (fun μ _ ↦ (‖μ‖₊ : ENNReal)) 1 hOneSpec)

namespace IsPositiveMap

section RussoDyeSpectral

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- **Wolf Proposition 6.1, Equation (6.2)**: the spectral radius of a positive
matrix map is at most `‖T 1‖∞`.

The spectral radius is computed for the continuous endomorphism induced by
`T`, using the matrix C*-operator norm. -/
theorem spectralRadius_le_nnnorm_map_one
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) :
    spectralRadius ℂ
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) T) ≤
        ‖T 1‖₊ :=
  spectralRadius_le_of_forall_eigenvalue_nnnorm_le T ‖T 1‖₊ fun μ hμ ↦ by
    exact_mod_cast hT.eigenvalue_norm_le_norm_map_one μ hμ

/-- **Wolf Proposition 6.1, unital case**: every eigenvalue of a positive
unital matrix map lies in the closed unit disk. -/
theorem eigenvalue_norm_le_one_of_map_one_eq_one
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue T μ) :
    ‖μ‖ ≤ 1 := by
  simpa only [hOne, norm_one] using hT.eigenvalue_norm_le_norm_map_one μ hμ

/-- **Wolf Proposition 6.1, unital case**: a positive unital matrix map has
spectral radius exactly `1`.

The upper bound is Equation (6.2), while the reverse inequality follows from
the identity eigenvector. -/
theorem spectralRadius_eq_one_of_map_one_eq_one
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hOne : T 1 = 1) :
    spectralRadius ℂ
      (Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ) T) = 1 :=
  spectralRadius_eq_one_of_eigenvalue_bounds T
    (hT.eigenvalue_norm_le_one_of_map_one_eq_one hOne)
    (eigenvalue_one_of_map_one_eq_one hOne)

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
  apply spectralRadius_eq_one_of_eigenvalue_bounds T
  · exact hT.eigenvalue_norm_le_one_of_tracePreserving hTP
  · obtain ⟨ρ, _, hρne, hρ⟩ := hT.eigenvalue_one_exists_of_tracePreserving hTP
    apply Module.End.hasEigenvalue_of_hasEigenvector
    rw [Module.End.hasEigenvector_iff]
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hρne⟩
    simpa only [one_smul] using hρ

end RussoDyeSpectral

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
