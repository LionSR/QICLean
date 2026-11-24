/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.CorrectedSources.CrossingVectors
import QICLean.Circuit.Party.Compression.SourceSampling.SchmidtCoordinates

/-!
# The Schmidt frame of the corrected source slots

A corrected source contributes two Schmidt coordinates. Both of its endpoints
lie among the affected parties. For one branch, the tensor product of the
endpoint Schmidt matrices is an isometry from the product of the pairs of
Schmidt indices to the product of the slot bases.

Source: polynomial-PEPS, Theorem 5.2, `04-compression.tex`, lines 409–434.
-/

open Matrix
open scoped Kronecker ComplexConjugate

namespace QuantumCircuit.Party.SourceCircuit

variable {P : Type} [DecidableEq P] {X Y : P → Type}
  (w : SourceCircuit X Y) (S : Finset w.sourceLocations)

local notation "mask" => correctedMask w S
local notation "slots" => selectedPartialSlots mask w S
local notation "bases" => partialSlotBases mask w

variable
  (E : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.leftBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)
  (F : ∀ e : w.sourceLocations, w.branchLabels e.1 →
    Matrix (w.rightBasis e) (Fin (min (w.sourceDims e).1 (w.sourceDims e).2)) ℂ)

/-- The tensor product of the left and right Schmidt matrices at all selected
slots of a branch, indexed by the slot pairs. -/
noncomputable def correctedSourceFrame (ξ : Choices mask w) :
    Matrix (∀ i : slots, (bases).left i × (bases).right i)
      (PartialSchmidtCoordinates mask w S) ℂ :=
  piKronecker fun i : slots ↦
    E (partialSlotEquiv mask w i).1 (partialSlotChoice mask w ξ i) ⊗ₖ
      F (partialSlotEquiv mask w i).1 (partialSlotChoice mask w ξ i)

/-- The corrected source frame is an isometry when the endpoint frames have
orthonormal columns. -/
theorem conjTranspose_correctedSourceFrame_mul_self
    (hE : ∀ e ξ, (E e ξ)ᴴ * E e ξ = 1) (hF : ∀ e ξ, (F e ξ)ᴴ * F e ξ = 1)
    (ξ : Choices mask w) :
    (w.correctedSourceFrame S E F ξ)ᴴ * w.correctedSourceFrame S E F ξ = 1 := by
  classical
  rw [correctedSourceFrame, conjTranspose_piKronecker, piKronecker_mul]
  rw [← piKronecker_one]
  congr 1
  funext i
  let e := (partialSlotEquiv mask w i).1
  let label := partialSlotChoice mask w ξ i
  change (E e label ⊗ₖ F e label)ᴴ * (E e label ⊗ₖ F e label) = _
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, hE, hF, one_kronecker_one]

/-- A column of the corrected frame is the product of the selected Schmidt
source vectors in slot coordinates. -/
theorem correctedSourceFrame_apply
    (ξ : Choices mask w) (u : PartialSchmidtCoordinates mask w S)
    (a : ∀ i : slots, (bases).left i × (bases).right i) :
    w.correctedSourceFrame S E F ξ a u =
      ∏ i : slots, partialSchmidtSourceVectors mask w S E F ξ u i (a i) := by
  unfold correctedSourceFrame
  rw [piKronecker_apply]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [partialSchmidtSourceVectors, dite_eq_left i.2]
  rfl

/-- The product of corrected frame columns and the exact crossing vectors,
ordered by the affected and exterior sides, has a single Schmidt expansion
with the same orthonormal input frames for all corrected columns. -/
theorem exists_correctedInputFrames
    (hE : ∀ e ξ, (E e ξ)ᴴ * E e ξ = 1) (hF : ∀ e ξ, (F e ξ)ᴴ * F e ξ = 1)
    (ξ : Choices mask w) :
    let C := PartialSchmidtCoordinates mask w S
    let K := ∀ i : slots, (bases).left i × (bases).right i
    let L := ∀ i : w.crossingSlots S, w.crossingSlotBasis S i true
    let R := ∀ i : w.crossingSlots S, w.crossingSlotBasis S i false
    let n := min (Fintype.card L) (Fintype.card R)
    ∃ (lam : Fin n → ℝ) (U : Matrix (K × L) (C × Fin n) ℂ) (V : Matrix R (Fin n) ℂ),
      (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧ Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
      ∀ u (a : K × L) (b : R),
        w.correctedSourceFrame S E F ξ a.1 u * w.sourceCrossingVector S ξ (a.2, b) =
          ∑ j, (Real.sqrt (lam j) : ℂ) * (U a (u, j) * V b j) := by
  intro C K L R n
  obtain ⟨lam, U, V, hlam, hmass, hU, hV, hspec⟩ := w.exists_sourceCrossing_schmidt S ξ
  refine ⟨lam, w.correctedSourceFrame S E F ξ ⊗ₖ U, V, hlam, hmass, ?_, hV, ?_⟩
  · rw [conjTranspose_kronecker, ← mul_kronecker_mul,
      conjTranspose_correctedSourceFrame_mul_self w S E F hE hF ξ, hU, one_kronecker_one]
  · intro u a b
    rw [show w.sourceCrossingVector S ξ (a.2, b) = schmidtFrameVector lam U V (a.2, b) from
      (congrFun hspec (a.2, b)).symm, schmidtFrameVector, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [kroneckerMap_apply]
    ring

end QuantumCircuit.Party.SourceCircuit
