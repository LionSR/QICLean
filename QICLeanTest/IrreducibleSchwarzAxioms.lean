/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.IrreducibleSchwarz
import QICLean.Channel.Peripheral.CyclicGroupKraus
import QICLean.Channel.Peripheral.CyclicDecomposition.PeripheralUnitary
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Source-hypothesis and standard-axiom audit for Wolf Theorem 6.6. -/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``SchwarzMap.exists_posDef_traceAdjoint_fixedPoint,
    ``SchwarzMap.exists_posDef_traceAdjoint_stationaryState,
    ``SchwarzMap.fixed_eq_scalar_of_irreducible_unital,
    ``SchwarzMap.schwarz_equality_of_peripheral_eigenvector,
    ``SchwarzMap.mem_multiplicativeDomain_of_peripheral_eigenvector,
    ``SchwarzMap.exists_peripheral_unitary,
    ``SchwarzMap.map_powers_of_peripheral_unitary,
    ``SchwarzMap.peripheralEigenvalues_mul_mem,
    ``SchwarzMap.peripheral_eigenspace_finrank_eq_one,
    ``peripheralEigenvalues_card_le_finrank,
    ``peripheralEigenvalues_eq_range_exp_of_mul_mem,
    ``SchwarzMap.exists_normalized_peripheral_unitary,
    ``SchwarzMap.wolf_theorem_6_6,
    ``Kraus.fixed_eq_scalar_of_irreducible_unital,
    ``Kraus.peripheralEigenvalues_mul_mem_of_irreducible_unital_of_adjoint_fixedPoint,
    ``Kraus.peripheralEigenvalues_eq_range_primitiveRoot,
    ``Kraus.exists_peripheral_unitary_of_irreducible_schwarz,
    ``Kraus.map_powers_of_peripheral_unitary,
    ``Kraus.exists_normalized_peripheral_unitary_of_irreducible_schwarz]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

-- The generic dimension estimate includes the zero-dimensional boundary.
example (T : Matrix (Fin 0) (Fin 0) ℂ →ₗ[ℂ] Matrix (Fin 0) (Fin 0) ℂ) :
    (peripheralEigenvalues_finite T).toFinset.card = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc
    _ ≤ Module.finrank ℂ (Matrix (Fin 0) (Fin 0) ℂ) :=
      peripheralEigenvalues_card_le_finrank T
    _ = 0 := by simp [Module.finrank_matrix]

-- The source hypotheses alone suffice for every clause, with the canonical phase.
example {D : ℕ} [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsPositiveMap T) (hOne : T 1 = 1)
    (hS : IsSchwarzMap T) (hIrr : IsIrreducibleMap T) :
    ∃ m : ℕ, ∃ hm : 0 < m,
      let : NeZero m := ⟨hm.ne'⟩
      let γ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑m)
      m ≤ D ^ 2 ∧
      peripheralEigenvalues T = Set.range (fun j : Fin m => γ ^ (j : ℕ)) ∧
      (∀ μ ∈ peripheralEigenvalues T,
        Module.finrank ℂ (Module.End.eigenspace T μ) = 1) ∧
      ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
        ∃ P : Fin m → Matrix (Fin D) (Fin D) ℂ,
          (∀ k : ℕ, T ((U : Matrix (Fin D) (Fin D) ℂ) ^ k) =
            γ ^ k • ((U : Matrix (Fin D) (Fin D) ℂ) ^ k)) ∧
          (U : Matrix (Fin D) (Fin D) ℂ) ^ m = 1 ∧
          (∀ k : Fin m, IsOrthogonalProjection (P k)) ∧
          (∀ k l : Fin m, k ≠ l → P k * P l = 0) ∧
          (∑ k : Fin m, P k = 1) ∧
          ((U : Matrix (Fin D) (Fin D) ℂ) = ∑ k : Fin m, γ ^ (k : ℕ) • P k) ∧
          (∀ k : Fin m, T (P (k + 1)) = P k) :=
  SchwarzMap.wolf_theorem_6_6 T hT hOne hS hIrr

-- Powers need neither irreducibility nor a supplied faithful invariant weight.
example {D : ℕ}
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hT : IsPositiveMap T) (hOne : T 1 = 1) (hS : IsSchwarzMap T)
    (U : Matrix.unitaryGroup (Fin D) ℂ) {γ : ℂ} (hγ : ‖γ‖ = 1)
    (hU : T (U : Matrix (Fin D) (Fin D) ℂ) = γ • (U : Matrix (Fin D) (Fin D) ℂ)) :
    ∀ k : ℕ, T ((U : Matrix (Fin D) (Fin D) ℂ) ^ k) =
      γ ^ k • ((U : Matrix (Fin D) (Fin D) ℂ) ^ k) :=
  SchwarzMap.map_powers_of_peripheral_unitary T hT hOne hS hγ U hU
