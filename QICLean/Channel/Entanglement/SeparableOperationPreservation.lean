/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Entanglement.SeparableOperation
import QICLean.Channel.Entanglement.Separable

/-!
# Preservation by unrestricted separable operations

Finite product-Kraus operations preserve the positive semidefinite cone, the
separable cone, and positivity of the partial transpose. Input and output local
dimensions may differ (and may be zero). No trace normalization, trace bound,
or LOCC realization is assumed or asserted.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace QuantumInfo.SeparableOperation

variable {dA dB dAout dBout : ℕ}

/-- An unrestricted finite product-Kraus operation preserves positivity. -/
theorem map_posSemidef
    (S : SeparableOperation (Fin dA) (Fin dB) (Fin dAout) (Fin dBout))
    {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    (hρ : ρ.PosSemidef) : (S.map ρ).PosSemidef := by
  rw [map_apply]
  exact Matrix.posSemidef_sum Finset.univ fun i _ =>
    hρ.mul_mul_conjTranspose_same (S.left i ⊗ₖ S.right i)

/-- An unrestricted finite product-Kraus operation preserves the separable cone. -/
theorem map_isSeparable
    (S : SeparableOperation (Fin dA) (Fin dB) (Fin dAout) (Fin dBout))
    {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    (hρ : ρ.IsSeparable) : (S.map ρ).IsSeparable := by
  obtain ⟨ι, _, A, B, hAB, rfl⟩ := hρ
  rw [map_sum]
  apply Matrix.isSeparable_sum
  intro i _
  rw [map_kronecker]
  apply Matrix.isSeparable_sum
  intro j _
  exact Matrix.isSeparable_kronecker
    ((hAB i).1.mul_mul_conjTranspose_same (S.left j))
    ((hAB i).2.mul_mul_conjTranspose_same (S.right j))

/-- Partial transpose of the output is a sum of conjugated local sandwiches. -/
theorem partialTransposeLeft_map
    (S : SeparableOperation (Fin dA) (Fin dB) (Fin dAout) (Fin dBout))
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) :
    partialTransposeLeft (S.map ρ) = ∑ i,
      ((S.left i).map star ⊗ₖ S.right i) * partialTransposeLeft ρ *
        ((S.left i).map star ⊗ₖ S.right i)ᴴ := by
  rw [map_apply, Matrix.partialTransposeLeft_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Matrix.partialTransposeLeft_product_sandwich (S.left i) (S.right i) ρ

/-- Positivity of the partial transpose is preserved without normalization.
`Matrix.IsPPT` means positivity of the partial transpose alone; ordinary
positivity is preserved separately by `map_posSemidef`. -/
theorem map_isPPT
    (S : SeparableOperation (Fin dA) (Fin dB) (Fin dAout) (Fin dBout))
    {ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    (hρ : ρ.IsPPT) : (S.map ρ).IsPPT := by
  rw [Matrix.IsPPT, partialTransposeLeft_map]
  exact Matrix.posSemidef_sum Finset.univ fun i _ =>
    hρ.mul_mul_conjTranspose_same ((S.left i).map star ⊗ₖ S.right i)

end QuantumInfo.SeparableOperation
