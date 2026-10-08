/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ChronologicalGarbageError

/-! Regression checks for actual marked chronological physical-density budgets. -/

open Matrix
open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

private def phaseGarbage (t : ℕ) : EuclideanSpace ℂ (Fin (t + 1)) :=
  EuclideanSpace.single 0 Complex.I

private theorem phaseGarbage_norm (t : ℕ) : ‖phaseGarbage t‖ = 1 := by
  simp [phaseGarbage]

-- No marked stages gives exact ORIGINAL density for arbitrary gates/replacements/readout.
example (G : (t : ℕ) → Matrix (Fin (t + 2)) (Fin (t + 1)) ℂ)
    (A : (t : ℕ) → Matrix (Fin (t + 2) × Fin (t + 1)) (Fin (t + 1)) ℂ)
    (ψ : EuclideanSpace ℂ (Fin 1)) (K : Matrix (Fin 2 × Fin 3) (Fin 4) ℂ) (δ : ℝ) :
    chronologicalGarbageDensity (D := fun t ↦ Fin (t + 1))
      (markedChronologicalGarbageChain (D := fun t ↦ Fin (t + 1)) G A phaseGarbage ∅ δ)
      phaseGarbage ψ 3 K = sourceOnlyReadoutDensity (D := fun t ↦ Fin (t + 1)) G ψ 3 K :=
  chronologicalGarbageDensity_marked_empty (D := fun t ↦ Fin (t + 1)) G A
    phaseGarbage phaseGarbage_norm ψ 3 K δ

-- Zero stages need no normalized fresh vectors, even when all future fresh spaces are empty.
example (G : (t : ℕ) → Matrix (Fin (t + 2)) (Fin (t + 1)) ℂ)
    (A : (t : ℕ) → Matrix (Fin (t + 2) × Fin 0) (Fin (t + 1)) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (Fin 0)) (ψ : EuclideanSpace ℂ (Fin 1))
    (K : Matrix (Fin 2 × Fin 3) (Fin 1) ℂ) (S : Finset ℕ) (δ : ℝ) :
    chronologicalGarbageDensity (D := fun t ↦ Fin (t + 1))
      (markedChronologicalGarbageChain (D := fun t ↦ Fin (t + 1)) G A γ S δ) γ ψ 0 K =
        sourceOnlyReadoutDensity (D := fun t ↦ Fin (t + 1)) G ψ 0 K :=
  chronologicalGarbageDensity_zero (D := fun t ↦ Fin (t + 1)) (B := fun _ ↦ Fin 0)
    (markedChronologicalGarbageChain (D := fun t ↦ Fin (t + 1)) G A γ S δ) G γ ψ K

-- Three stages change memory dimensions 1→2→3→4, but just stage 1 contributes to 4δ.
example (G : (t : ℕ) → Matrix (Fin (t + 2)) (Fin (t + 1)) ℂ)
    (A : (t : ℕ) → Matrix (Fin (t + 2) × Fin (t + 1)) (Fin (t + 1)) ℂ)
    (ψ : EuclideanSpace ℂ (Fin 1)) (K : Matrix (Fin 2 × Fin 3) (Fin 4) ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hG : ∀ t, ‖G t‖ ≤ 1)
    (herror : ‖A 1 - appendGarbageGate (G 1) (phaseGarbage 1)‖ ≤ δ)
    (hψ : ‖ψ‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    rectangularTraceNorm
      (chronologicalGarbageDensity (D := fun t ↦ Fin (t + 1))
        (markedChronologicalGarbageChain (D := fun t ↦ Fin (t + 1)) G A phaseGarbage {1} δ)
        phaseGarbage ψ 3 K - sourceOnlyReadoutDensity (D := fun t ↦ Fin (t + 1)) G ψ 3 K) ≤
      4 * δ := by
  have herr : ∀ t ∈ ({1} : Finset ℕ), ‖A t - appendGarbageGate (G t) (phaseGarbage t)‖ ≤ δ := by
    intro t ht
    have ht' : t = 1 := Finset.mem_singleton.mp ht
    subst t
    exact herror
  simpa using rectangularTraceNorm_chronologicalGarbageDensity_marked_sub_le
    (D := fun t ↦ Fin (t + 1)) G A phaseGarbage phaseGarbage_norm ψ 3 K {1} δ hδ
    hG herr hψ hK

-- The same actual changing-memory circuit satisfies ε/2 using δ=ε/8 for its single marked stage.
example (G : (t : ℕ) → Matrix (Fin (t + 2)) (Fin (t + 1)) ℂ)
    (A : (t : ℕ) → Matrix (Fin (t + 2) × Fin (t + 1)) (Fin (t + 1)) ℂ)
    (ψ : EuclideanSpace ℂ (Fin 1)) (K : Matrix (Fin 2 × Fin 3) (Fin 4) ℂ)
    (ε : ℝ) (hε : 0 ≤ ε) (hG : ∀ t, ‖G t‖ ≤ 1)
    (herror : ‖A 1 - appendGarbageGate (G 1) (phaseGarbage 1)‖ ≤ ε / 8)
    (hψ : ‖ψ‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    rectangularTraceNorm
      (chronologicalGarbageDensity (D := fun t ↦ Fin (t + 1))
        (markedChronologicalGarbageChain (D := fun t ↦ Fin (t + 1)) G A phaseGarbage {1}
          (ε / 8)) phaseGarbage ψ 3 K -
        sourceOnlyReadoutDensity (D := fun t ↦ Fin (t + 1)) G ψ 3 K) ≤ ε / 2 := by
  have herr : ∀ t ∈ ({1} : Finset ℕ),
      ‖A t - appendGarbageGate (G t) (phaseGarbage t)‖ ≤ ε / (8 * ({1} : Finset ℕ).card) := by
    intro t ht
    have ht' : t = 1 := Finset.mem_singleton.mp ht
    subst t
    simpa using herror
  simpa using rectangularTraceNorm_chronologicalGarbageDensity_marked_sub_le_half
    (D := fun t ↦ Fin (t + 1)) G A phaseGarbage phaseGarbage_norm ψ 3 K {1} ε hε
    (by simp) hG herr hψ hK

-- An actual half-norm input and complex garbage; just one gate is rescaled among three stages.
example : rectangularTraceNorm
    (chronologicalGarbageDensity (D := fun _ ↦ Fin 1)
      (markedChronologicalGarbageChain (D := fun _ ↦ Fin 1) (fun _ ↦ 1)
        (fun t ↦ appendGarbageGate 1 (phaseGarbage t)) phaseGarbage {1} (1 / 8))
      phaseGarbage (EuclideanSpace.single (0 : Fin 1) (1 / 2 : ℂ)) 3
      (basisRegisterInjection (0 : Fin 1)) -
      sourceOnlyReadoutDensity (D := fun _ ↦ Fin 1) (fun _ ↦ 1)
        (EuclideanSpace.single (0 : Fin 1) (1 / 2 : ℂ)) 3
        (basisRegisterInjection (0 : Fin 1))) ≤ 1 / 2 := by
  simpa using rectangularTraceNorm_chronologicalGarbageDensity_marked_sub_le_half
    (D := fun _ ↦ Fin 1) (fun _ ↦ 1) (fun t ↦ appendGarbageGate 1 (phaseGarbage t))
    phaseGarbage phaseGarbage_norm (EuclideanSpace.single (0 : Fin 1) (1 / 2 : ℂ)) 3
    (basisRegisterInjection (0 : Fin 1)) {1} 1 (by norm_num) (by simp)
    (fun _ ↦ l2_opNorm_one_le) (by intro t _; simp) (by norm_num)
    (l2_opNorm_le_one_of_conjTranspose_mul_self _
      (basisRegisterInjection_conjTranspose_mul_self (0 : Fin 1)))

-- The physical density budget also permits an empty originally owned register.
example (G : (t : ℕ) → Matrix (Fin (t + 2)) (Fin (t + 1)) ℂ)
    (A : (t : ℕ) → Matrix (Fin (t + 2) × Fin (t + 1)) (Fin (t + 1)) ℂ)
    (ψ : EuclideanSpace ℂ (Fin 1)) (δ : ℝ) (hδ : 0 ≤ δ) (hG : ∀ t, ‖G t‖ ≤ 1)
    (herror : ∀ t ∈ ({1} : Finset ℕ), ‖A t - appendGarbageGate (G t) (phaseGarbage t)‖ ≤ δ)
    (hψ : ‖ψ‖ ≤ 1) :
    rectangularTraceNorm
      (chronologicalGarbageDensity (D := fun t ↦ Fin (t + 1))
        (markedChronologicalGarbageChain (D := fun t ↦ Fin (t + 1)) G A phaseGarbage {1} δ)
        phaseGarbage ψ 3 (0 : Matrix (Fin 2 × Fin 0) (Fin 4) ℂ) -
        sourceOnlyReadoutDensity (D := fun t ↦ Fin (t + 1)) (P := Fin 2) (E := Fin 0)
          G ψ 3 0) ≤ 4 * δ := by
  simpa using rectangularTraceNorm_chronologicalGarbageDensity_marked_sub_le
    (D := fun t ↦ Fin (t + 1)) G A phaseGarbage phaseGarbage_norm ψ 3
    (0 : Matrix (Fin 2 × Fin 0) (Fin 4) ℂ) {1} δ hδ hG herror hψ (by simp)

-- Empty working memory and a zero input remain supported in the ε/2 theorem.
example : rectangularTraceNorm
    (chronologicalGarbageDensity (D := fun _ ↦ Fin 0)
      (markedChronologicalGarbageChain (D := fun _ ↦ Fin 0) (fun _ ↦ 0) (fun _ ↦ 0)
        phaseGarbage {1} (1 / 8)) phaseGarbage 0 3
      (0 : Matrix (Fin 2 × Fin 3) (Fin 0) ℂ) -
      sourceOnlyReadoutDensity (D := fun _ ↦ Fin 0) (P := Fin 2) (E := Fin 3)
        (fun _ ↦ 0) 0 3 0) ≤ 1 / 2 := by
  simpa using rectangularTraceNorm_chronologicalGarbageDensity_marked_sub_le_half
    (D := fun _ ↦ Fin 0) (fun _ ↦ 0) (fun _ ↦ 0) phaseGarbage phaseGarbage_norm 0 3
    (0 : Matrix (Fin 2 × Fin 3) (Fin 0) ℂ) {1} 1 (by norm_num) (by simp)
    (by intro t; simp)
    (by
      intro t _
      have hz : appendGarbageGate (0 : Matrix (Fin 0) (Fin 0) ℂ) (phaseGarbage t) = 0 := by
        ext y x
        exact zero_mul _
      rw [hz]
      norm_num)
    (by simp) (by simp)
