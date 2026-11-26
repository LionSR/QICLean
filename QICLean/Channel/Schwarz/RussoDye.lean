/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Norm.FrobeniusHilbert
import QICLean.Analysis.Norm.MatrixOperatorSpace
import QICLean.Channel.KrausMap.KrausCPTP
import QICLean.Channel.Schwarz.PositiveMapProperties
import QICLean.Channel.Schwarz.SchwarzSubnormal
import QICLean.Spectral.Radius.SpectralRadius
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Russo--Dye estimate and operator-norm bounds for unital maps

**Wolf Proposition 6.1**: if
$T: M_d(\mathbb{C}) \to M_d(\mathbb{C})$ is positive and $d \ge 1$, then
$\varrho(T) \le \|T(\mathbf 1)\|_\infty$; if $T$ is unital, its spectral radius
is $1$.

Wolf invokes the Russo--Dye estimate
$\|T(X)\|_\infty \le \|T(\mathbf 1)\|_\infty\|X\|_\infty$.  No standalone
Russo--Dye theorem is available in the pinned Mathlib.  For finite matrices,
this file derives precisely the estimate needed by Proposition 6.1 from
Wolf's Theorem 5.6 (`schwarz_inequality_commuting_dominant_operator`), taking
the dominant operator to be the identity after normalizing the map.  This
retains the sharp coefficient one and does not use the four-positive-parts
bound.  The trace-preserving case is in
`QICLean.Channel.Peripheral.Spectrum.SpectralRadius`.

A unital completely positive endomorphism of a finite matrix algebra is a
contraction for the matrix operator norm, by the Kadison--Schwarz inequality.
Consequently, every eigenvalue lies in the closed unit disk.

The norm in these declarations is the matrix C*-operator norm (Wolf's
$\|\cdot\|_\infty$), not the Frobenius norm or Mathlib's row-sum norm.

## Main statements

* `IsPositiveMap.norm_apply_le_norm_map_one_mul_norm`: the sharp matrix
  Russo--Dye estimate used by Wolf.
* `IsPositiveMap.eigenvalue_norm_le_norm_map_one` and
  `IsPositiveMap.spectralRadius_le_nnnorm_map_one`: Equations (6.3) and (6.2).
* `eigenvalue_one_of_map_one_eq_one`,
  `IsPositiveMap.eigenvalue_norm_le_one_of_map_one_eq_one`, and
  `IsPositiveMap.spectralRadius_eq_one_of_map_one_eq_one`: the unital case.
* `IsKrausCP.norm_apply_le_of_map_one_eq_one`: operator-norm contractivity of a unital Kraus map.
* `IsKrausCP.eigenvalue_norm_le_one_of_map_one_eq_one`: the spectral bound for a unital Kraus map.
* `IsKrausCP.spectralRadius_frobeniusEuclideanMap_le_one_of_map_one_eq_one`:
  the corresponding bound after Frobenius vectorization.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.1,
  Proposition 6.1][Wolf2012QChannels]
-/

section RussoDyeEstimate

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

end IsPositiveMap

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
    rw [spectralRadius_eq_of_unital]
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

end RussoDyeSpectral

end IsPositiveMap

end RussoDyeEstimate

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal ENNReal
open Matrix

attribute [local instance 1001]
  ContinuousLinearMap.toNormedAddCommGroup
  ContinuousLinearMap.toNormedSpace
  ContinuousLinearMap.toNormedRing
  ContinuousLinearMap.toNormedAlgebra

/-- A unital Kraus completely positive endomorphism is a contraction for the matrix operator norm.
-/
theorem IsKrausCP.norm_apply_le_of_map_one_eq_one
    {α : Type*} [Fintype α] [DecidableEq α]
    {E : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ}
    (hE : IsKrausCP E) (hOne : E 1 = 1) (X : Matrix α α ℂ) :
    ‖E X‖ ≤ ‖X‖ := by
  have hPos : IsPositiveMap E := fun _ hA ↦ hE.map_posSemidef hA
  have hXX :
      Xᴴ * X ≤ (algebraMap ℝ (Matrix α α ℂ)) (‖X‖ ^ 2) := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := X))
  have hEXX :
      E (Xᴴ * X) ≤ (algebraMap ℝ (Matrix α α ℂ)) (‖X‖ ^ 2) := by
    calc
      E (Xᴴ * X) ≤ E ((algebraMap ℝ (Matrix α α ℂ)) (‖X‖ ^ 2)) :=
        hPos.map_le_map hXX
      _ = (algebraMap ℝ (Matrix α α ℂ)) (‖X‖ ^ 2) := by
        rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul_of_tower, hOne]
  have hKS :
      (E X)ᴴ * E X ≤ E (Xᴴ * X) := by
    exact Matrix.le_iff.mpr (hE.kadison_schwarz_of_map_one_eq_one hOne X)
  have hSq : ‖E X‖ ^ 2 ≤ ‖X‖ ^ 2 := by
    have hnorm :
        ‖(E X)ᴴ * E X‖ ≤ ‖X‖ ^ 2 :=
      (CStarAlgebra.norm_le_iff_le_algebraMap
        ((E X)ᴴ * E X) (sq_nonneg ‖X‖)
        ((Matrix.posSemidef_conjTranspose_mul_self (E X)).nonneg)).mpr
          (hKS.trans hEXX)
    rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hnorm
    simpa only [pow_two] using hnorm
  exact (sq_le_sq₀ (norm_nonneg (E X)) (norm_nonneg X)).mp hSq

/-- Every eigenvalue of a unital Kraus completely positive endomorphism has modulus at most one.

This is the unital form of the spectral bound in Wolf, Proposition 6.1. -/
theorem IsKrausCP.eigenvalue_norm_le_one_of_map_one_eq_one
    {α : Type*} [Fintype α] [DecidableEq α]
    {E : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ}
    (hE : IsKrausCP E) (hOne : E 1 = 1)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue E μ) :
    ‖μ‖ ≤ 1 := by
  obtain ⟨X, hXmem, hXne⟩ := hμ.exists_hasEigenvector
  have hEig : E X = μ • X := Module.End.mem_eigenspace_iff.mp hXmem
  have hContract := hE.norm_apply_le_of_map_one_eq_one hOne X
  rw [hEig, norm_smul] at hContract
  have hXpos : 0 < ‖X‖ := norm_pos_iff.mpr hXne
  exact le_of_mul_le_mul_right (by simpa using hContract) hXpos

open scoped Matrix.Norms.Frobenius in
/-- The Frobenius-vectorized form of a unital Kraus completely positive
endomorphism has spectral radius at most one. This statement also covers the
zero-dimensional matrix algebra. -/
theorem IsKrausCP.spectralRadius_frobeniusEuclideanMap_le_one_of_map_one_eq_one
    {α : Type*} [Fintype α] [DecidableEq α]
    {E : Matrix α α ℂ →ₗ[ℂ] Matrix α α ℂ}
    (hE : IsKrausCP E) (hOne : E 1 = 1) :
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (EuclideanSpace ℂ (α × α)))
        (Matrix.frobeniusEuclideanMap E)) ≤ 1 := by
  let V := EuclideanSpace ℂ (α × α)
  let Ê : V →ₗ[ℂ] V := Matrix.frobeniusEuclideanMap E
  have hSpecFrob : spectrum ℂ Ê = spectrum ℂ E := by
    dsimp only [Ê]
    rw [Matrix.frobeniusEuclideanMap_eq_conj]
    exact AlgEquiv.spectrum_eq
      ((Matrix.frobeniusEquivEuclidean α α).toLinearEquiv.conjAlgEquiv ℂ) E
  refine spectralRadius_le_one_of_forall_eigenvalue_norm_le_one Ê fun μ hμ ↦ ?_
  have hμE : μ ∈ spectrum ℂ E :=
    hSpecFrob ▸ Module.End.hasEigenvalue_iff_mem_spectrum.mp hμ
  exact hE.eigenvalue_norm_le_one_of_map_one_eq_one hOne μ
    (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμE)
