/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Entanglement.SeparableOperationPreservation
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Regression tests for rectangular, unrestricted separable operations. Axiom checks
reject every axiom outside the standard propext/choice/quotient whitelist,
including sorryAx. No state normalization or nonzero-dimension premise is used.
-/

open Matrix QuantumInfo
open scoped Kronecker ComplexOrder

namespace SeparableOperationPreservationTest

/-- All three cones are preserved across unequal input and output dimensions. -/
theorem rectangular
    (S : SeparableOperation (Fin 2) (Fin 3) (Fin 4) (Fin 5))
    (ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ)
    (hpos : ρ.PosSemidef) (hsep : ρ.IsSeparable) (hppt : ρ.IsPPT) :
    (S.map ρ).PosSemidef ∧ (S.map ρ).IsSeparable ∧ (S.map ρ).IsPPT :=
  ⟨S.map_posSemidef hpos, S.map_isSeparable hsep, S.map_isPPT hppt⟩

/-- Zero-dimensional parties are admitted, including a zero output party. -/
theorem zero_dimensions
    (S : SeparableOperation (Fin 0) (Fin 3) (Fin 2) (Fin 0))
    (ρ : Matrix (Fin 0 × Fin 3) (Fin 0 × Fin 3) ℂ)
    (hpos : ρ.PosSemidef) (hsep : ρ.IsSeparable) (hppt : ρ.IsPPT) :
    (S.map ρ).PosSemidef ∧ (S.map ρ).IsSeparable ∧ (S.map ρ).IsPPT :=
  ⟨S.map_posSemidef hpos, S.map_isSeparable hsep, S.map_isPPT hppt⟩

/-- The algebraic identity has no assumptions on its input matrix. -/
theorem arbitrary_sandwich
    (A : Matrix (Fin 4) (Fin 2) ℂ) (B : Matrix (Fin 5) (Fin 3) ℂ)
    (ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) :
    partialTransposeLeft ((A ⊗ₖ B) * ρ * (A ⊗ₖ B)ᴴ) =
      (A.map star ⊗ₖ B) * partialTransposeLeft ρ * (A.map star ⊗ₖ B)ᴴ :=
  Matrix.partialTransposeLeft_product_sandwich A B ρ

/-- Empty shared outcome sets are legitimate unrestricted operations. -/
def emptyOperation (dA dB dAout dBout : ℕ) :
    SeparableOperation (Fin dA) (Fin dB) (Fin dAout) (Fin dBout) where
  Index := Empty
  left := Empty.elim
  right := Empty.elim

theorem empty_map {dA dB dAout dBout : ℕ}
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    (emptyOperation dA dB dAout dBout).map ρ = 0 := by
  simp [SeparableOperation.map_apply, emptyOperation]

/-- Empty operations satisfy the same generic preservation statements. -/
theorem empty_preserves {dA dB dAout dBout : ℕ}
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hpos : ρ.PosSemidef) (hsep : ρ.IsSeparable) (hppt : ρ.IsPPT) :
    let S := emptyOperation dA dB dAout dBout
    (S.map ρ).PosSemidef ∧ (S.map ρ).IsSeparable ∧ (S.map ρ).IsPPT := by
  exact ⟨SeparableOperation.map_posSemidef _ hpos,
    SeparableOperation.map_isSeparable _ hsep, SeparableOperation.map_isPPT _ hppt⟩

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.partialTransposeLeft_product_sandwich,
      ``QuantumInfo.SeparableOperation.map_posSemidef,
      ``QuantumInfo.SeparableOperation.map_isSeparable,
      ``QuantumInfo.SeparableOperation.partialTransposeLeft_map,
      ``QuantumInfo.SeparableOperation.map_isPPT,
      ``rectangular, ``zero_dimensions, ``arbitrary_sandwich,
      ``emptyOperation, ``empty_map, ``empty_preserves] do
    let axs ← Lean.collectAxioms decl
    unless axs.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axs}"
    Lean.logInfo m!"{decl}: {axs}"

end SeparableOperationPreservationTest
