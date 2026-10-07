/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.ComplexGaussian.ProductSourceTransport

/-! Edge-case regressions for GaussianProductSourceTransport in the compression proof. -/

open MeasureTheory Matrix QICLean.ComplexGaussian
open scoped BigOperators ComplexConjugate Kronecker Matrix.Norms.Elementwise

noncomputable section

local instance {m n : Type*} [Fintype m] [Fintype n] : ContinuousENorm (Matrix m n ℂ) :=
  SeminormedAddGroup.toContinuousENorm

private def ketL : Matrix (Fin 2) (Fin 1) ℂ := Matrix.single 1 0 Complex.I
private def ketR : Matrix (Fin 3) (Fin 1) ℂ := Matrix.single 2 0 1
private def braL : Matrix (Fin 4) (Fin 1) ℂ := Matrix.single 3 0 Complex.I
private def braR : Matrix (Fin 5) (Fin 1) ℂ := Matrix.single 4 0 (-1)

-- The genuinely complex embeddings used below are actual column isometries.
example : ketL.conjTranspose * ketL = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [ketL, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply,
    Fin.sum_univ_succ, Complex.I_mul_I]

example : braL.conjTranspose * braL = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [braL, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single_apply,
    Fin.sum_univ_succ, Complex.I_mul_I]

-- Conjugating the bra Schmidt vector is essential: the correct outer-product entry is -1.
example : ambientSchmidtSource (fun _ : Fin 1 ↦ (1 : ℝ))
    (fun _ : Fin 1 ↦ (1 : ℝ)) ketL ketR braL braR (1, 2) (3, 4) = -1 := by
  norm_num [ambientSchmidtSource, ambientSchmidtVector, ketL, ketR, braL, braR,
    Matrix.vecMulVec_apply, Matrix.single_apply, Fin.sum_univ_succ, Complex.I_mul_I]

-- The actual Gaussian sample average has that phase-sensitive ambient expectation.
example : (∫ x, ambientSampledSource 3 (fun _ : Fin 1 ↦ (1 : ℝ))
    (fun _ : Fin 1 ↦ (1 : ℝ)) ketL ketR braL braR x (1, 2) (3, 4)
      ∂law (Fin 3 × (Fin 1 × Fin 1))) = -1 := by
  rw [integral_ambientSampledSource_entry 3 (by decide) _ _ (by simp) (by simp)]
  norm_num [ambientSchmidtSource, ambientSchmidtVector, ketL, ketR, braL, braR,
    Matrix.vecMulVec_apply, Matrix.single_apply, Fin.sum_univ_succ, Complex.I_mul_I]

-- Four different ambient endpoint dimensions and different ket/bra support sizes are allowed.
example (E : Matrix (Fin 4) (Fin 2) ℂ) (F : Matrix (Fin 5) (Fin 2) ℂ)
    (Et : Matrix (Fin 6) (Fin 3) ℂ) (Ft : Matrix (Fin 7) (Fin 3) ℂ)
    (x : Sample (Fin 2 × (Fin 2 × Fin 3))) (j : Fin 2) :
    ambientSourceU 2 (fun _ : Fin 2 ↦ (1 : ℝ)) (fun _ : Fin 3 ↦ (1 : ℝ)) E Et j x ⊗ₖ
      ambientSourceV 2 (fun _ : Fin 2 ↦ (1 : ℝ)) (fun _ : Fin 3 ↦ (1 : ℝ)) F Ft j x =
        sourceTransport E F Et Ft (sourceU 2 (fun _ : Fin 2 ↦ (1 : ℝ))
          (fun _ : Fin 3 ↦ (1 : ℝ)) j x ⊗ₖ sourceV 2 (fun _ : Fin 2 ↦ (1 : ℝ))
            (fun _ : Fin 3 ↦ (1 : ℝ)) j x) :=
  ambientSourceU_kronecker_ambientSourceV _ _ _ _ _ _ _ _ _

-- Zero support weights need no inverse and give genuine ambient matrix integrability.
example (E : Matrix (Fin 4) (Fin 2) ℂ) (F : Matrix (Fin 5) (Fin 2) ℂ)
    (Et : Matrix (Fin 6) (Fin 3) ℂ) (Ft : Matrix (Fin 7) (Fin 3) ℂ) :
    Integrable (ambientSampledSource 2 (fun _ : Fin 2 ↦ (0 : ℝ))
      (fun _ : Fin 3 ↦ (1 : ℝ)) E F Et Ft) (law (Fin 2 × (Fin 2 × Fin 3))) :=
  integrable_ambientSampledSource 2 (by decide) _ _ (by simp) (by simp) _ _ _ _

-- Both actual rectangular Gaussian factors are integrable before taking their product average.
example (E : Matrix (Fin 4) (Fin 2) ℂ) (F : Matrix (Fin 5) (Fin 2) ℂ)
    (Et : Matrix (Fin 6) (Fin 3) ℂ) (Ft : Matrix (Fin 7) (Fin 3) ℂ) (j : Fin 2) :
    Integrable (ambientSourceU 2 (fun _ : Fin 2 ↦ (0 : ℝ))
      (fun _ : Fin 3 ↦ (1 : ℝ)) E Et j) (law (Fin 2 × (Fin 2 × Fin 3))) ∧
    Integrable (ambientSourceV 2 (fun _ : Fin 2 ↦ (0 : ℝ))
      (fun _ : Fin 3 ↦ (1 : ℝ)) F Ft j) (law (Fin 2 × (Fin 2 × Fin 3))) :=
  ⟨integrable_ambientSourceU _ _ _ _ _ _, integrable_ambientSourceV _ _ _ _ _ _⟩

-- The zero-weight unbiasedness statement is an actual matrix-valued Bochner equality.
example : (∫ x, ambientSampledSource 2 (fun _ : Fin 1 ↦ (0 : ℝ))
    (fun _ : Fin 1 ↦ (1 : ℝ)) ketL ketR braL braR x
      ∂law (Fin 2 × (Fin 1 × Fin 1))) = 0 := by
  rw [integral_ambientSampledSource 2 (by decide) _ _ (by simp) (by simp)]
  ext p q
  simp [ambientSchmidtSource, Matrix.vecMulVec_apply, ambientSchmidtVector]

-- Empty ket Schmidt support, with a nonempty bra support, requires no nonempty premise.
example (E : Matrix (Fin 2) (Fin 0) ℂ) (F : Matrix (Fin 3) (Fin 0) ℂ)
    (Et : Matrix (Fin 4) (Fin 1) ℂ) (Ft : Matrix (Fin 5) (Fin 1) ℂ) :
    (∫ x, ambientSampledSource 1 (fun _ : Fin 0 ↦ (0 : ℝ))
      (fun _ : Fin 1 ↦ (1 : ℝ)) E F Et Ft x ∂law (Fin 1 × (Fin 0 × Fin 1))) = 0 := by
  rw [integral_ambientSampledSource 1 (by decide) _ _ (by simp) (by simp)]
  ext p q
  simp [ambientSchmidtSource, Matrix.vecMulVec_apply, ambientSchmidtVector]

-- The paper's common ambient half-spaces allow unequal Schmidt ranks with normalized weights.
example (E : Matrix (Fin 4) (Fin 2) ℂ) (F : Matrix (Fin 5) (Fin 2) ℂ)
    (Et : Matrix (Fin 4) (Fin 3) ℂ) (Ft : Matrix (Fin 5) (Fin 3) ℂ) :
    (∫ x, ambientSampledSource 2 (fun _ : Fin 2 ↦ (1 / 2 : ℝ))
      (fun _ : Fin 3 ↦ (1 / 3 : ℝ)) E F Et Ft x ∂law (Fin 2 × (Fin 2 × Fin 3))) =
        ambientSchmidtSource (fun _ : Fin 2 ↦ (1 / 2 : ℝ))
          (fun _ : Fin 3 ↦ (1 / 3 : ℝ)) E F Et Ft :=
  integral_ambientSampledSource 2 (by decide) _ _ (by norm_num) (by norm_num) _ _ _ _

-- Centering commutes with the real ambient transport of the source matrices.
example (x : Sample (Fin 2 × (Fin 1 × Fin 1))) :
    ambientSourceCorrection 2 (fun _ : Fin 1 ↦ (1 : ℝ))
      (fun _ : Fin 1 ↦ (1 : ℝ)) ketL ketR braL braR x =
        sourceTransport ketL ketR braL braR (sourceCorrection 2
          (fun _ : Fin 1 ↦ (1 : ℝ)) (fun _ : Fin 1 ↦ (1 : ℝ)) x) :=
  ambientSourceCorrection_eq_transport _ _ _ _ _ _ _ _

end
