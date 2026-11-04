/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.IrreducibleSchwarz

/-!
# Covariance and eigenvector shifts for Schwarz maps

A peripheral unitary of a positive unital Schwarz map belongs to its
multiplicative domain. Right multiplication by the unitary and left
multiplication by its adjoint intertwine the map with scalar multiples of
itself. Their phase factors cancel under conjugation.

`SchwarzMap.wolf_proposition_6_7` chooses the canonical phase and normalized
unitary from Theorem 6.6 and proves the covariance and both eigenvector-shift
identities. No trace-preservation or complete-positivity assumption is needed.

## References

* Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 6.7,
  Equation (6.38), local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 803--817.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace SchwarzMap

variable {D : ℕ}
local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- A peripheral unitary attains equality in both Schwarz inequalities and
therefore belongs to the multiplicative domain. This is the unitary case of
Wolf Equation (6.36); irreducibility is unnecessary once the unitary is given. -/
theorem mem_multiplicativeDomain_of_peripheral_unitary
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hS : IsSchwarzMap T) {γ : ℂ} (hγ : ‖γ‖ = 1)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hU : T (U : Mat) = γ • (U : Mat)) :
    (U : Mat) ∈ multiplicativeDomain T := by
  have hphase : star γ * γ = 1 := by
    rw [← starRingEnd_apply, Complex.conj_mul', hγ]
    simp
  have hUU : (U : Mat) * (U : Mat)ᴴ = 1 := U.prop.2
  have hUsU : (U : Mat)ᴴ * (U : Mat) = 1 := U.prop.1
  rw [mem_multiplicativeDomain_iff T hS]
  constructor
  · rw [hUsU, hOne, hT.map_conjTranspose, hU,
      conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
      hphase, one_smul, hUsU]
  · rw [hUU, hOne, hT.map_conjTranspose, hU,
      conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_comm γ (star γ), hphase, one_smul, hUU]

/-- Right multiplication by a peripheral unitary shifts the map by its phase
(the adjoint form of Wolf Equation (6.36)). -/
theorem map_mul_peripheral_unitary
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hS : IsSchwarzMap T) {γ : ℂ} (hγ : ‖γ‖ = 1)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hU : T (U : Mat) = γ • (U : Mat))
    (X : Mat) : T (X * (U : Mat)) = γ • (T X * (U : Mat)) := by
  rw [(mem_multiplicativeDomain_of_peripheral_unitary T hT hOne hS hγ U hU).1,
    hU, mul_smul_comm]

/-- Left multiplication by the adjoint peripheral unitary shifts the map by
the conjugate phase (Wolf Equation (6.36)). -/
theorem map_peripheral_unitary_conjTranspose_mul
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hS : IsSchwarzMap T) {γ : ℂ} (hγ : ‖γ‖ = 1)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hU : T (U : Mat) = γ • (U : Mat))
    (X : Mat) : T ((U : Mat)ᴴ * X) = star γ • ((U : Mat)ᴴ * T X) := by
  have h := congrArg Matrix.conjTranspose
    (map_mul_peripheral_unitary T hT hOne hS hγ U hU Xᴴ)
  simpa only [← hT.map_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose, conjTranspose_smul] using h

/-- Covariance in Wolf Proposition 6.7(1), with orientation `U† X U`.
The two scalar phases cancel. -/
theorem map_conj_peripheral_unitary
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hS : IsSchwarzMap T) {γ : ℂ} (hγ : ‖γ‖ = 1)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hU : T (U : Mat) = γ • (U : Mat))
    (X : Mat) : T ((U : Mat)ᴴ * X * (U : Mat)) = (U : Mat)ᴴ * T X * (U : Mat) := by
  rw [map_mul_peripheral_unitary T hT hOne hS hγ U hU,
    map_peripheral_unitary_conjTranspose_mul T hT hOne hS hγ U hU,
    smul_mul_assoc, smul_smul]
  have hphase : γ * star γ = 1 := by
    rw [mul_comm, ← starRingEnd_apply, Complex.conj_mul', hγ]
    simp
  rw [hphase, one_smul]

/-- Both eigenvector-shift identities of Wolf Proposition 6.7(2),
Equation (6.38). The eigenvalue `μ` need not be peripheral. -/
theorem eigenvector_shifts_of_peripheral_unitary
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hS : IsSchwarzMap T) {γ : ℂ} (hγ : ‖γ‖ = 1)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hU : T (U : Mat) = γ • (U : Mat))
    {μ : ℂ} {X : Mat} (hX : T X = μ • X) :
    T ((U : Mat)ᴴ * X) = (star γ * μ) • ((U : Mat)ᴴ * X) ∧
      T (X * (U : Mat)) = (γ * μ) • (X * (U : Mat)) := by
  constructor
  · rw [map_peripheral_unitary_conjTranspose_mul T hT hOne hS hγ U hU,
      hX, mul_smul_comm, smul_smul]
  · rw [map_mul_peripheral_unitary T hT hOne hS hγ U hU,
      hX, smul_mul_assoc, smul_smul]

/-- The shifts in Wolf Equation (6.38) preserve nonzero eigenvectors:
unitarity makes both multiplication maps injective. -/
theorem hasEigenvector_shifts_of_peripheral_unitary
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hS : IsSchwarzMap T) {γ : ℂ} (hγ : ‖γ‖ = 1)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hU : T (U : Mat) = γ • (U : Mat))
    {μ : ℂ} {X : Mat} (hX : Module.End.HasEigenvector T μ X) :
    Module.End.HasEigenvector T (star γ * μ) ((U : Mat)ᴴ * X) ∧
      Module.End.HasEigenvector T (γ * μ) (X * (U : Mat)) := by
  obtain ⟨hXmem, hXne⟩ := Module.End.hasEigenvector_iff.mp hX
  obtain ⟨hLeft, hRight⟩ := eigenvector_shifts_of_peripheral_unitary
    T hT hOne hS hγ U hU (Module.End.mem_eigenspace_iff.mp hXmem)
  constructor
  · refine Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr hLeft, ?_⟩
    intro h
    apply hXne
    exact (Unitary.isUnit_coe (U := U)).star.mul_right_eq_zero.mp h
  · refine Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr hRight, ?_⟩
    intro h
    apply hXne
    exact (Unitary.isUnit_coe (U := U)).mul_left_eq_zero.mp h

/-- **Wolf Proposition 6.7: covariance and eigensystem of irreducible maps.**

Choose the canonical phase `exp(2πi/m)` and normalized unitary of Theorem 6.6.
The map commutes with conjugation by this unitary, and both identities in
Equation (6.38) hold for every eigenvalue. The only map hypotheses are
positivity, unitality, the Schwarz inequality, and irreducibility.
Source: Wolf, local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 803--817. -/
theorem wolf_proposition_6_7 [NeZero D]
    (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hS : IsSchwarzMap T) (hIrr : IsIrreducibleMap T) :
    ∃ m : ℕ, ∃ _hm : 0 < m,
      let γ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑m)
      m ≤ D ^ 2 ∧
      peripheralEigenvalues T = Set.range (fun j : Fin m => γ ^ (j : ℕ)) ∧
      ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
        T (U : Mat) = γ • (U : Mat) ∧ (U : Mat) ^ m = 1 ∧
        (∀ X : Mat, T ((U : Mat)ᴴ * X * (U : Mat)) =
          (U : Mat)ᴴ * T X * (U : Mat)) ∧
        (∀ (μ : ℂ) (X : Mat), T X = μ • X →
          T ((U : Mat)ᴴ * X) = (star γ * μ) • ((U : Mat)ᴴ * X) ∧
          T (X * (U : Mat)) = (γ * μ) • (X * (U : Mat))) := by
  obtain ⟨m, hm, hbound, hperiph, _, U, _, hPow, hUm, _⟩ :=
    wolf_theorem_6_6 T hT hOne hS hIrr
  let γ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑m)
  have hU : T (U : Mat) = γ • (U : Mat) := by simpa using hPow 1
  have hγ : ‖γ‖ = 1 := by simp [γ, Complex.norm_exp]
  exact ⟨m, hm, hbound, hperiph, U, hU, hUm,
    map_conj_peripheral_unitary T hT hOne hS hγ U hU,
    fun _ _ hX => eigenvector_shifts_of_peripheral_unitary T hT hOne hS hγ U hU hX⟩

end SchwarzMap
