/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FilterFeasibility

/-! Singular, empty, endpoint, and permutation regressions for filter feasibility. -/

open Complex Matrix Entropy
open scoped ComplexOrder Matrix.Norms.L2Operator

-- A rank-one projection is feasible at every positive weight, despite its kernel.
example (a : ℝ) (ha : 0 < a) :
    IsFeasibleFilter 0 a (diagonal ![(1 : ℂ), 0]) ∧
      ¬ (diagonal ![(1 : ℂ), 0]).PosDef := by
  constructor
  · refine ⟨1, ![(1 : ℝ), 0], by simp, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num
    · simp [Fin.sum_univ_two]
    · simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      congr 1
      funext i
      fin_cases i <;> simp [Real.zero_rpow (ne_of_gt (half_pos ha))]
  · intro h
    have := posDef_diagonal_iff.mp h 1
    norm_num at this

-- The trace characterization accepts a singular filter supplied by its eigenvalues.
example {a : ℝ} (ha : 0 < a) {K : Matrix (Fin 2) (Fin 2) ℂ}
    (hK : K.PosSemidef) (hs : ∑ i, hK.isHermitian.eigenvalues i ^ (2 / a) = 1)
    (hker : K.det = 0) : IsFeasibleFilter 0 a K ∧ K.det = 0 :=
  ⟨(isFeasibleFilter_zero_iff_eigenvalues ha hK).mpr hs, hker⟩

-- There is no simplex witness on the empty index set, at any floor or weight.
example (f a : ℝ) (K : Matrix (Fin 0) (Fin 0) ℂ) : ¬ IsFeasibleFilter f a K := by
  rintro ⟨_, y, _, _, hs, _⟩
  simp at hs

-- The full equivalence itself has no hidden nonemptiness premise.
example {a : ℝ} (ha : 0 < a) (K : Matrix (Fin 0) (Fin 0) ℂ) :
    IsFeasibleFilter 0 a K ↔
      K.PosSemidef ∧ (cfc (fun x : ℝ ↦ x ^ (2 / a)) K).trace = 1 :=
  isFeasibleFilter_zero_iff ha

-- An empty physical region has a singleton configuration space, unlike Fin 0.
example (a : ℝ) : IsFeasibleFilter 0 a (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  refine ⟨1, fun _ ↦ 1, by simp, fun _ ↦ zero_le_one, by simp, ?_⟩
  simp

-- The physical endpoint a = 1 is retained.
example (K : Matrix (Fin 2) (Fin 2) ℂ) :
    IsFeasibleFilter 0 1 K ↔
      K.PosSemidef ∧ (cfc (fun x : ℝ ↦ x ^ (2 : ℝ)) K).trace = 1 := by
  simpa using (isFeasibleFilter_zero_iff (a := 1) (K := K) (by norm_num))

-- At a = 0, feasibility does not imply reciprocal trace-power normalization.
example : IsFeasibleFilter 0 0 (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    (cfc (fun x : ℝ ↦ x ^ (2 / (0 : ℝ))) (1 : Matrix (Fin 2) (Fin 2) ℂ)).trace ≠ 1 := by
  constructor
  · refine ⟨1, ![(1 : ℝ), 0], by simp, ?_, by simp [Fin.sum_univ_two], ?_⟩
    · intro i
      fin_cases i <;> norm_num
    · simp
  · have htr :
        (cfc (fun x : ℝ ↦ x ^ (2 / (0 : ℝ)))
          (1 : Matrix (Fin 2) (Fin 2) ℂ)).trace = 2 := by
      simp [Fin.sum_univ_two]
    rw [htr]
    norm_num

-- A nontrivial basis permutation preserves feasibility even for negative parameters.
example (K : Matrix (Fin 2) (Fin 2) ℂ) :
    IsFeasibleFilter (-3) (-2)
        (Matrix.reindex (Equiv.swap 0 1) (Equiv.swap 0 1) K) ↔
      IsFeasibleFilter (-3) (-2) K :=
  isFeasibleFilter_reindex_iff (Equiv.swap 0 1)

-- Positivity uses only the floor sign, and does not require a positive weight.
example {K : Matrix (Fin 2) (Fin 2) ℂ} (hK : IsFeasibleFilter 0 (-2) K) :
    K.PosSemidef := hK.posSemidef le_rfl
