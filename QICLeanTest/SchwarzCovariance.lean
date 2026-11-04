/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.SchwarzCovariance
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Source-hypothesis, orientation, nonzero transport, and proof-dependency regressions
for Wolf Proposition 6.7. -/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace SchwarzCovarianceTest

variable {D : ℕ}
local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

-- No irreducibility, supplied state, CP, TP, or nonzero dimension is assumed.
-- The explicit complex conjugate checks the source's left shift orientation.
example (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hS : IsSchwarzMap T) {γ : ℂ} (hγ : ‖γ‖ = 1)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hU : T (U : Mat) = γ • (U : Mat))
    (X : Mat) :
    T ((U : Mat)ᴴ * X * (U : Mat)) = (U : Mat)ᴴ * T X * (U : Mat) ∧
      T ((U : Mat)ᴴ * X) = (starRingEnd ℂ) γ • ((U : Mat)ᴴ * T X) ∧
      T (X * (U : Mat)) = γ • (T X * (U : Mat)) :=
  ⟨SchwarzMap.map_conj_peripheral_unitary T hT hOne hS hγ U hU X,
    SchwarzMap.map_peripheral_unitary_conjTranspose_mul T hT hOne hS hγ U hU X,
    SchwarzMap.map_mul_peripheral_unitary T hT hOne hS hγ U hU X⟩

-- Recover actual nonzero eigenvectors independently of the production
-- nonzero-transport proof. The eigenvalue μ is arbitrary, including zero.
theorem nonzero_shifts (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T)
    (hOne : T 1 = 1) (hS : IsSchwarzMap T) {γ : ℂ} (hγ : ‖γ‖ = 1)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hU : T (U : Mat) = γ • (U : Mat))
    {μ : ℂ} {X : Mat} (hX : T X = μ • X) (hXne : X ≠ 0) :
    Module.End.HasEigenvector T ((starRingEnd ℂ) γ * μ) ((U : Mat)ᴴ * X) ∧
      Module.End.HasEigenvector T (γ * μ) (X * (U : Mat)) := by
  obtain ⟨hLeft, hRight⟩ :=
    SchwarzMap.eigenvector_shifts_of_peripheral_unitary T hT hOne hS hγ U hU hX
  have hLeftNe : (U : Mat)ᴴ * X ≠ 0 := by
    intro h
    apply hXne
    have h' := congrArg (fun Y : Mat => (U : Mat) * Y) h
    simpa only [← mul_assoc, show (U : Mat) * (U : Mat)ᴴ = 1 from U.prop.2,
      one_mul, mul_zero] using h'
  have hRightNe : X * (U : Mat) ≠ 0 := by
    intro h
    apply hXne
    have h' := congrArg (fun Y : Mat => Y * (U : Mat)ᴴ) h
    simpa only [mul_assoc, show (U : Mat) * (U : Mat)ᴴ = 1 from U.prop.2,
      mul_one, zero_mul] using h'
  exact ⟨Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr hLeft, hLeftNe⟩,
    Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr hRight, hRightNe⟩⟩

-- The named transport theorem must accept exactly a nonzero eigenvector.
example (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hS : IsSchwarzMap T) {γ : ℂ} (hγ : ‖γ‖ = 1)
    (U : Matrix.unitaryGroup (Fin D) ℂ) (hU : T (U : Mat) = γ • (U : Mat))
    {μ : ℂ} {X : Mat} (hX : Module.End.HasEigenvector T μ X) :
    Module.End.HasEigenvector T ((starRingEnd ℂ) γ * μ) ((U : Mat)ᴴ * X) ∧
      Module.End.HasEigenvector T (γ * μ) (X * (U : Mat)) :=
  SchwarzMap.hasEigenvector_shifts_of_peripheral_unitary T hT hOne hS hγ U hU hX

-- Source hypotheses alone produce the canonical generator and both shifts.
-- The witness used for covariance is the same normalized unitary.
example [NeZero D] (T : Mat →ₗ[ℂ] Mat) (hT : IsPositiveMap T)
    (hOne : T 1 = 1) (hS : IsSchwarzMap T) (hIrr : IsIrreducibleMap T) :
    ∃ m : ℕ, ∃ _hm : 0 < m,
      let γ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑m)
      m ≤ D ^ 2 ∧
      peripheralEigenvalues T = Set.range (fun j : Fin m => γ ^ (j : ℕ)) ∧
      ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
        (U : Mat) ^ m = 1 ∧
        (∀ X : Mat, T ((U : Mat)ᴴ * X * (U : Mat)) =
          (U : Mat)ᴴ * T X * (U : Mat)) ∧
        (∀ μ : ℂ, ∀ X : Mat, T X = μ • X → X ≠ 0 →
          Module.End.HasEigenvector T ((starRingEnd ℂ) γ * μ) ((U : Mat)ᴴ * X) ∧
          Module.End.HasEigenvector T (γ * μ) (X * (U : Mat))) := by
  obtain ⟨m, hm, hbound, hset, U, hU, hUm, hCov, _⟩ :=
    SchwarzMap.wolf_proposition_6_7 T hT hOne hS hIrr
  refine ⟨m, hm, hbound, hset, U, hUm, hCov, ?_⟩
  intro μ X hX hXne
  exact nonzero_shifts T hT hOne hS (by simp [Complex.norm_exp]) U hU hX hXne

end SchwarzCovarianceTest

-- A non-real phase distinguishes the two orientations: μ = γ = i
-- gives eigenvalue 1 on U†U and eigenvalue -1 on U².
example {D : ℕ} [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsPositiveMap T) (hOne : T 1 = 1) (hS : IsSchwarzMap T)
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (hU : T (U : Matrix (Fin D) (Fin D) ℂ) =
      Complex.I • (U : Matrix (Fin D) (Fin D) ℂ)) :
    Module.End.HasEigenvector T 1 (1 : Matrix (Fin D) (Fin D) ℂ) ∧
      Module.End.HasEigenvector T (-1) ((U : Matrix (Fin D) (Fin D) ℂ) ^ 2) := by
  have hV : Module.End.HasEigenvector T Complex.I
      (U : Matrix (Fin D) (Fin D) ℂ) :=
    Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr hU, (Unitary.isUnit_coe (U := U)).ne_zero⟩
  have hUsU : (U : Matrix (Fin D) (Fin D) ℂ)ᴴ *
      (U : Matrix (Fin D) (Fin D) ℂ) = 1 := U.prop.1
  simpa [pow_two, hUsU] using SchwarzMap.hasEigenvector_shifts_of_peripheral_unitary
    T hT hOne hS (by simp : ‖Complex.I‖ = 1) U hU hV

open Lean Elab Command in
run_cmd do
  let roots := #[``SchwarzMap.mem_multiplicativeDomain_of_peripheral_unitary,
    ``SchwarzMap.map_mul_peripheral_unitary,
    ``SchwarzMap.map_peripheral_unitary_conjTranspose_mul,
    ``SchwarzMap.map_conj_peripheral_unitary,
    ``SchwarzMap.eigenvector_shifts_of_peripheral_unitary,
    ``SchwarzMap.hasEigenvector_shifts_of_peripheral_unitary,
    ``SchwarzMap.wolf_proposition_6_7,
    ``SchwarzCovarianceTest.nonzero_shifts]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in roots do
    let axioms ← Lean.collectAxioms name
    unless axioms.all allowed.contains do
      throwError "Unexpected axioms for {name}: {axioms}"
    logInfo m!"AXIOM AUDIT {name}: {axioms}"
  let env := (← getEnv).setExporting false
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  let mut opaqueCount : Nat := 0
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name
      | throwError "Missing kernel declaration: {name}"
    if info.isUnsafe then
      throwError "Unsafe declaration reachable from theorem: {name}"
    match info with
    | .axiomInfo _ =>
      axioms := axioms.insert name
      unless allowed.contains name do
        throwError "Unexpected transitive axiom: {name}"
    | .opaqueInfo _ => opaqueCount := opaqueCount + 1
    | _ => pure ()
    todo := todo ++ info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      todo := todo ++ value.getUsedConstants
  logInfo m!"DEPENDENCY AUDIT: {seen.size} declarations; axioms {axioms.toArray}"
  logInfo m!"Opaque definitions with checked values: {opaqueCount}"
