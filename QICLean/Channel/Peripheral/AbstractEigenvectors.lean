/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.FixedPoint.AbstractAlgebra
import QICLean.Channel.Irreducible.CollatzWielandt
import QICLean.Channel.Peripheral.Spectrum

/-!
# Peripheral eigenvectors of irreducible positive unital Schwarz maps

The invariant faithful weight is derived from positivity, unitality and
irreducibility using the abstract left Perron theorem. The weighted Schwarz
equality then places every peripheral eigenvector in the multiplicative domain.
No Kraus representation or trace-preservation hypothesis on the original map
is used.

## References

* Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.6, local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 756--803.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace SchwarzMap

variable {D : ℕ}
local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- An irreducible positive unital map has a faithful stationary weight for its
trace adjoint. This is the left Perron argument used in Wolf Theorem 6.6;
unitality fixes the Perron value at one. -/
theorem exists_posDef_traceAdjoint_fixedPoint [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T)
    (hOne : T 1 = 1) (hIrr : IsIrreducibleMap T) :
    ∃ ρ : Mat, ρ.PosDef ∧ Matrix.traceAdjointMap T ρ = ρ := by
  simpa using exists_posDef_traceAdjointMap_eigenvector_at_perron
    T hT hIrr (r := 1) (X := 1) (by norm_num) Matrix.PosDef.one (by simpa using hOne)

/-- The trace adjoint of an irreducible positive unital map has a faithful
stationary density matrix. Trace normalization is derived rather than supplied
as an additional hypothesis in Wolf Theorem 6.6. -/
theorem exists_posDef_traceAdjoint_stationaryState [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T)
    (hOne : T 1 = 1) (hIrr : IsIrreducibleMap T) :
    ∃ ρ : Mat, ρ.PosDef ∧ ρ.trace = 1 ∧ Matrix.traceAdjointMap T ρ = ρ := by
  obtain ⟨ρ, hρ, hfix⟩ := exists_posDef_traceAdjoint_fixedPoint T hT hOne hIrr
  have htr : 0 < ρ.trace := hρ.trace_pos
  refine ⟨ρ.trace⁻¹ • ρ, hρ.smul (inv_pos.mpr htr), ?_, ?_⟩
  · rw [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ htr.ne']
  · rw [map_smul, hfix]

/-- Every fixed point of an irreducible positive unital map is scalar.
This is the eigenvalue-one simplicity step in Wolf Theorem 6.6. -/
theorem fixed_eq_scalar_of_irreducible_unital [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T)
    (hOne : T 1 = 1) (hIrr : IsIrreducibleMap T)
    {X : Mat} (hX : T X = X) : ∃ c : ℂ, X = c • 1 := by
  exact eigenvector_eq_smul_of_irreducible_positive T hT hIrr
    (r := 1) (X := 1) (by norm_num) Matrix.PosDef.one
    (by simpa using hOne) (by simpa using hX)

/-- A peripheral eigenvector attains equality in the Schwarz inequality in the
presence of a faithful adjoint stationary weight. This is the weighted-trace
step of Wolf Theorem 6.6, preceding Equation (6.36). -/
theorem schwarz_equality_of_peripheral_eigenvector
    {n : Type*} [Fintype n]
    (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hT : IsPositiveMap T) (hS : IsSchwarzMap T)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosDef)
    (hρfix : Matrix.traceAdjointMap T ρ = ρ)
    {X : Matrix n n ℂ} {γ : ℂ} (hX : T X = γ • X) (hγ : ‖γ‖ = 1) :
    T (Xᴴ * X) = T Xᴴ * T X := by
  have hphase : star γ * γ = 1 := by
    rw [← starRingEnd_apply, Complex.conj_mul', hγ]
    simp
  have hprod : T Xᴴ * T X = Xᴴ * X := by
    rw [hT.map_conjTranspose, hX, Matrix.conjTranspose_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul, hphase, one_smul]
  have htrace : Matrix.trace (ρ * (T (Xᴴ * X) - T Xᴴ * T X)) = 0 := by
    rw [Matrix.mul_sub, Matrix.trace_sub,
      ← Matrix.trace_traceAdjointMap_mul, hρfix, hprod, sub_self]
  exact sub_eq_zero.mp
    (Matrix.posSemidef_eq_zero_of_posDef_trace_mul_eq_zero (hS X) hρ htrace)

/-- Both one-sided multiplicative identities hold at a peripheral eigenvector.
This is Wolf Equation (6.36) and its adjoint form. -/
theorem mem_multiplicativeDomain_of_peripheral_eigenvector
    {n : Type*} [Fintype n]
    (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hT : IsPositiveMap T) (hS : IsSchwarzMap T)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosDef)
    (hρfix : Matrix.traceAdjointMap T ρ = ρ)
    {X : Matrix n n ℂ} {γ : ℂ} (hX : T X = γ • X) (hγ : ‖γ‖ = 1) :
    X ∈ multiplicativeDomain T := by
  rw [mem_multiplicativeDomain_iff T hS X]
  refine ⟨schwarz_equality_of_peripheral_eigenvector T hT hS hρ hρfix hX hγ, ?_⟩
  have hXstar : T Xᴴ = star γ • Xᴴ := by
    rw [hT.map_conjTranspose, hX, Matrix.conjTranspose_smul]
  simpa using schwarz_equality_of_peripheral_eigenvector
    T hT hS hρ hρfix hXstar (by simpa using hγ)

/-- Every peripheral eigenvalue of an irreducible positive unital Schwarz map
has a unitary eigenvector (Wolf Theorem 6.6). -/
theorem exists_peripheral_unitary [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hS : IsSchwarzMap T) (hIrr : IsIrreducibleMap T)
    {γ : ℂ} (hγ : γ ∈ peripheralEigenvalues T) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ, T (U : Mat) = γ • (U : Mat) := by
  classical
  obtain ⟨ρ, hρ, hρfix⟩ := exists_posDef_traceAdjoint_fixedPoint T hT hOne hIrr
  obtain ⟨X, hXvec⟩ := hγ.1.exists_hasEigenvector
  obtain ⟨hXmem, hXne⟩ := Module.End.hasEigenvector_iff.mp hXvec
  have hX : T X = γ • X := Module.End.mem_eigenspace_iff.mp hXmem
  have hphase : star γ * γ = 1 := by
    rw [← starRingEnd_apply, Complex.conj_mul', hγ.2]
    simp
  have hXXfix : T (Xᴴ * X) = Xᴴ * X := by
    rw [schwarz_equality_of_peripheral_eigenvector T hT hS hρ hρfix hX hγ.2,
      hT.map_conjTranspose, hX, Matrix.conjTranspose_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul, hphase, one_smul]
  obtain ⟨c, hc⟩ := fixed_eq_scalar_of_irreducible_unital T hT hOne hIrr hXXfix
  have hXXne : Xᴴ * X ≠ 0 := fun h => hXne (Matrix.conjTranspose_mul_self_eq_zero.mp h)
  have hcne : c ≠ 0 := by
    intro h
    apply hXXne
    rw [hc, h, zero_smul]
  have hcpos : 0 ≤ c := by
    have hpsd : (c • (1 : Mat)).PosSemidef := hc ▸ Matrix.posSemidef_conjTranspose_mul_self X
    have hdiag : (Matrix.diagonal (fun _ : Fin D => c)).PosSemidef := by
      simpa [Matrix.smul_one_eq_diagonal] using hpsd
    exact Matrix.posSemidef_diagonal_iff.mp hdiag (0 : Fin D)
  have hcreal : c = (c.re : ℂ) := Complex.ext rfl (Complex.nonneg_iff.mp hcpos).2.symm
  have hcrpos : 0 < c.re := by
    have hcrnonneg := (Complex.nonneg_iff.mp hcpos).1
    have hcrne : c.re ≠ 0 := fun h => hcne (by simpa [h] using hcreal)
    exact lt_of_le_of_ne hcrnonneg hcrne.symm
  let a : ℂ := (Real.sqrt c.re : ℂ)
  have hane : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast Real.sqrt_ne_zero'.mpr hcrpos
  have hastar : star a⁻¹ = a⁻¹ := by simp [a]
  have hcsq : c = a * a := by
    calc
      c = (c.re : ℂ) := hcreal
      _ = (((Real.sqrt c.re) ^ 2 : ℝ) : ℂ) := by rw [Real.sq_sqrt hcrpos.le]
      _ = a * a := by simp only [a, pow_two, Complex.ofReal_mul]
  refine ⟨⟨a⁻¹ • X, Matrix.mem_unitaryGroup_iff'.mpr ?_⟩, ?_⟩
  · change (a⁻¹ • X)ᴴ * (a⁻¹ • X) = 1
    rw [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm,
      smul_smul, hc, smul_smul, hastar]
    have hscalar : (a⁻¹ * a⁻¹) * c = 1 := by rw [hcsq]; field_simp
    rw [hscalar, one_smul]
  · change T (a⁻¹ • X) = γ • (a⁻¹ • X)
    rw [map_smul, hX, smul_comm]

/-- All powers of a peripheral unitary satisfy the corresponding eigenvector
identity (Wolf Theorem 6.6(3)). -/
theorem map_powers_of_peripheral_unitary
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hS : IsSchwarzMap T)
    {γ : ℂ} (hγ : ‖γ‖ = 1) (U : Matrix.unitaryGroup (Fin D) ℂ)
    (hU : T (U : Mat) = γ • (U : Mat)) :
    ∀ k : ℕ, T ((U : Mat) ^ k) = γ ^ k • ((U : Mat) ^ k) := by
  have hphase : star γ * γ = 1 := by
    rw [← starRingEnd_apply, Complex.conj_mul', hγ]
    simp
  have hmd : (U : Mat) ∈ rightMultiplicativeDomain T := by
    rw [mem_rightMultiplicativeDomain_iff T hS]
    rw [show (U : Mat)ᴴ * (U : Mat) = 1 from Matrix.UnitaryGroup.star_mul_self U,
      hOne, hT.map_conjTranspose, hU, Matrix.conjTranspose_smul,
      smul_mul_assoc, mul_smul_comm, smul_smul, hphase, one_smul]
    exact (Matrix.UnitaryGroup.star_mul_self U).symm
  intro k
  induction k with
  | zero => simpa using hOne
  | succ k ih =>
    rw [pow_succ, hmd, ih, hU, smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]

/-- Peripheral eigenvalues are closed under products (Wolf Theorem 6.6(1)). -/
theorem peripheralEigenvalues_mul_mem [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hS : IsSchwarzMap T) (hIrr : IsIrreducibleMap T)
    {μ ν : ℂ} (hμ : μ ∈ peripheralEigenvalues T) (hν : ν ∈ peripheralEigenvalues T) :
    μ * ν ∈ peripheralEigenvalues T := by
  obtain ⟨ρ, hρ, hρfix⟩ := exists_posDef_traceAdjoint_fixedPoint T hT hOne hIrr
  obtain ⟨U, hU⟩ := exists_peripheral_unitary T hT hOne hS hIrr hμ
  obtain ⟨V, hV⟩ := exists_peripheral_unitary T hT hOne hS hIrr hν
  have hmd := mem_multiplicativeDomain_of_peripheral_eigenvector T hT hS hρ hρfix hU hμ.2
  refine ⟨hasEigenvalue_of_eigenvector_eq T (μ * ν)
    ((U * V : Matrix.unitaryGroup (Fin D) ℂ) : Mat) ?_ ?_, ?_⟩
  · change T ((U : Mat) * (V : Mat)) = (μ * ν) • ((U : Mat) * (V : Mat))
    rw [hmd.2, hU, hV, smul_mul_assoc, mul_smul_comm, smul_smul]
  · exact (Unitary.isUnit_coe (U := U * V)).ne_zero
  · rw [norm_mul, hμ.2, hν.2, one_mul]

/-- Every peripheral eigenspace has complex dimension one
(Wolf Theorem 6.6(2)). -/
theorem peripheral_eigenspace_finrank_eq_one [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hS : IsSchwarzMap T) (hIrr : IsIrreducibleMap T)
    {γ : ℂ} (hγ : γ ∈ peripheralEigenvalues T) :
    Module.finrank ℂ (Module.End.eigenspace T γ) = 1 := by
  classical
  obtain ⟨ρ, hρ, hρfix⟩ := exists_posDef_traceAdjoint_fixedPoint T hT hOne hIrr
  obtain ⟨U, hU⟩ := exists_peripheral_unitary T hT hOne hS hIrr hγ
  have hmd := mem_multiplicativeDomain_of_peripheral_eigenvector T hT hS hρ hρfix
    (show T (U : Mat)ᴴ = star γ • (U : Mat)ᴴ by
      rw [hT.map_conjTranspose, hU, Matrix.conjTranspose_smul])
    (show ‖star γ‖ = 1 by simpa using hγ.2)
  have hphase : γ * star γ = 1 := by
    rw [mul_comm, ← starRingEnd_apply, Complex.conj_mul', hγ.2]
    simp
  have heq : Module.End.eigenspace T γ = ℂ ∙ (U : Mat) := by
    apply le_antisymm
    · intro X hX
      have hXeq := Module.End.mem_eigenspace_iff.mp hX
      have hfix : T (X * (U : Mat)ᴴ) = X * (U : Mat)ᴴ := by
        rw [hmd.1, hXeq, hT.map_conjTranspose, hU, Matrix.conjTranspose_smul,
          smul_mul_assoc, mul_smul_comm, smul_smul, hphase, one_smul]
      obtain ⟨c, hc⟩ := fixed_eq_scalar_of_irreducible_unital T hT hOne hIrr hfix
      have hXscalar : X = c • (U : Mat) := by
        calc
          X = (X * (U : Mat)ᴴ) * (U : Mat) := by
            rw [Matrix.mul_assoc, show (U : Mat)ᴴ * (U : Mat) = 1 from
              Matrix.UnitaryGroup.star_mul_self U, mul_one]
          _ = c • (U : Mat) := by rw [hc, smul_mul_assoc, one_mul]
      exact Submodule.mem_span_singleton.mpr ⟨c, hXscalar.symm⟩
    · apply Submodule.span_le.mpr
      rintro X rfl
      exact Module.End.mem_eigenspace_iff.mpr hU
  rw [heq]
  exact finrank_span_singleton (Unitary.isUnit_coe (U := U)).ne_zero

end SchwarzMap
