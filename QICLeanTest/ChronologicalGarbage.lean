/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ChronologicalGarbage

/-! Regression checks for actual chronological registers and edge cases. -/

open Matrix
open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

private def phaseGarbage (t : ℕ) : EuclideanSpace ℂ (Fin (t + 1)) :=
  EuclideanSpace.single 0 Complex.I

private theorem phaseGarbage_norm (t : ℕ) : ‖phaseGarbage t‖ = 1 := by
  simp [phaseGarbage]

-- Three chronological inventories have dimensions 1, 2, 3, in that order.
example : Fintype.card (garbageInventory (fun t ↦ Fin (t + 1)) 3) = 6 := by
  simp [garbageInventory]

-- Actual complex phases remain in the accumulated vector, rather than being conjugated.
example : cumulativeGarbageVector phaseGarbage 2 ((PUnit.unit, 0), 0) = -1 := by
  norm_num [cumulativeGarbageVector, euclideanTensorVector, phaseGarbage, Complex.I_mul_I]

-- A zero-length chain has only the unit scalar inventory, even if every future space is empty.
example (γ : (t : ℕ) → EuclideanSpace ℂ (Fin 0)) :
    cumulativeGarbageVector γ 0 PUnit.unit = 1 := rfl

-- Normalized fresh vectors give a genuine unit vector in the actual product inventory.
example : ‖cumulativeGarbageVector phaseGarbage 3‖ = 1 :=
  norm_cumulativeGarbageVector phaseGarbage phaseGarbage_norm 3

-- Arbitrary gates change the working dimensions 1→2→3→4; their inventory also grows.
example (G : (t : ℕ) → Matrix (Fin (t + 2)) (Fin (t + 1)) ℂ)
    (ψ : EuclideanSpace ℂ (Fin 1)) :
    toEuclideanLin (contractionPrefix
      (D := fun t ↦ Fin (t + 1) × garbageInventory (fun s ↦ Fin (s + 1)) t)
      (chronologicalGarbageChain (D := fun t ↦ Fin (t + 1)) G phaseGarbage) 3)
      (euclideanTensorVector ψ (cumulativeGarbageVector phaseGarbage 0)) =
        euclideanTensorVector
          (toEuclideanLin (contractionPrefix (D := fun t ↦ Fin (t + 1)) G 3) ψ)
          (cumulativeGarbageVector phaseGarbage 3) :=
  chronologicalGarbageChain_prefix_vector (D := fun t ↦ Fin (t + 1)) G phaseGarbage ψ 3

-- Idle earlier coordinates are copied exactly; a different earlier coordinate gives zero.
example (A : Matrix (Fin 3 × Fin 4) (Fin 2) ℂ) :
    idleGarbageLift (c := Fin 5) A (2, (3, 1)) (0, 3) = A (2, 1) 0 ∧
      idleGarbageLift (c := Fin 5) A (2, (3, 1)) (0, 4) = 0 := by
  simp [idleGarbageLift]

-- Rectangular replacement maps are amplified without any old-register dimension loss.
example (A A' : Matrix (Fin 3 × Fin 4) (Fin 2) ℂ) :
    ‖idleGarbageLift (c := Fin 5) A - idleGarbageLift A'‖ ≤ ‖A - A'‖ :=
  norm_idleGarbageLift_sub_le A A'

-- An empty fresh register is allowed for arbitrary replacement maps; normalization is not assumed.
example (A : Matrix (Fin 3 × Fin 0) (Fin 2) ℂ) :
    ‖idleGarbageLift (c := Fin 7) A‖ ≤ ‖A‖ := norm_idleGarbageLift_le A

-- Empty working memories support the exact chain identity without a nonempty premise.
example (G : (t : ℕ) → Matrix (Fin 0) (Fin 0) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (Fin 0)) :
    let v := toEuclideanLin (contractionPrefix
      (D := fun t ↦ Fin 0 × garbageInventory (fun _ ↦ Fin 0) t)
      (chronologicalGarbageChain (D := fun _ ↦ Fin 0) G γ) 2)
      (euclideanTensorVector 0 (cumulativeGarbageVector γ 0))
    v = euclideanTensorVector
      (toEuclideanLin (contractionPrefix (D := fun _ ↦ Fin 0) G 2) 0)
      (cumulativeGarbageVector γ 2) := by
  exact chronologicalGarbageChain_prefix_vector (D := fun _ ↦ Fin 0) G γ 0 2

-- A half-norm input and arbitrary actual gates/readout preserve the physical density after discard.
example (G : (t : ℕ) → Matrix (Fin (t + 2)) (Fin (t + 1)) ℂ)
    (K : Matrix (Fin 2 × Fin 3) (Fin 4) ℂ) :
    partialTraceRight (partialTraceRight (euclideanOuterProduct
      (chronologicalGarbageReadout (D := fun t ↦ Fin (t + 1)) G phaseGarbage
        (EuclideanSpace.single (0 : Fin 1) (1 / 2 : ℂ)) 3 K)
      (chronologicalGarbageReadout (D := fun t ↦ Fin (t + 1)) G phaseGarbage
        (EuclideanSpace.single (0 : Fin 1) (1 / 2 : ℂ)) 3 K))) =
      partialTraceRight (euclideanOuterProduct
        (toEuclideanLin (K * contractionPrefix (D := fun t ↦ Fin (t + 1)) G 3)
          (EuclideanSpace.single (0 : Fin 1) (1 / 2 : ℂ)))
        (toEuclideanLin (K * contractionPrefix (D := fun t ↦ Fin (t + 1)) G 3)
          (EuclideanSpace.single (0 : Fin 1) (1 / 2 : ℂ)))) :=
  chronologicalGarbageReadout_discard_density (D := fun t ↦ Fin (t + 1)) G
    phaseGarbage phaseGarbage_norm _ 3 K

-- The originally owned readout register may itself be empty.
example (G : (t : ℕ) → Matrix (Fin (t + 2)) (Fin (t + 1)) ℂ)
    (ψ : EuclideanSpace ℂ (Fin 1)) (K : Matrix (Fin 2 × Fin 0) (Fin 4) ℂ) :
    partialTraceRight (partialTraceRight (euclideanOuterProduct
      (chronologicalGarbageReadout (D := fun t ↦ Fin (t + 1)) G phaseGarbage ψ 3 K)
      (chronologicalGarbageReadout (D := fun t ↦ Fin (t + 1)) G phaseGarbage ψ 3 K))) =
      partialTraceRight (euclideanOuterProduct
        (toEuclideanLin (K * contractionPrefix (D := fun t ↦ Fin (t + 1)) G 3) ψ)
        (toEuclideanLin (K * contractionPrefix (D := fun t ↦ Fin (t + 1)) G 3) ψ)) :=
  chronologicalGarbageReadout_discard_density (D := fun t ↦ Fin (t + 1)) G
    phaseGarbage phaseGarbage_norm ψ 3 K
