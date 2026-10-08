/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.IsometricDomainExtension

/-! Boundary regressions for adjoint domain extension and branch-sector embeddings. -/

open Matrix
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

noncomputable section

private def phaseJ : Matrix (Fin 3) (Fin 1) ℂ := Matrix.single 2 0 Complex.I
private def phaseB : Matrix Bool (Fin 1) ℂ := Matrix.single true 0 Complex.I

private theorem phaseJ_isometry : phaseJᴴ * phaseJ = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [phaseJ, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single_apply, Fin.sum_univ_succ, Complex.I_mul_I]

-- A genuine complex rectangular embedding is a column isometry.
example : phaseJᴴ * phaseJ = 1 := phaseJ_isometry

-- The adjoint phase is essential: projecting the source phase yields the real entry one.
example : isometricDomainExtension phaseB phaseJ true 2 = 1 := by
  norm_num [isometricDomainExtension, phaseB, phaseJ, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single_apply, Fin.sum_univ_succ, Complex.I_mul_I]

-- An independently shaped rectangular output preserves the exact operator norm.
example : ‖isometricDomainExtension phaseB phaseJ‖ = ‖phaseB‖ :=
  norm_isometricDomainExtension phaseB phaseJ phaseJ_isometry

-- Actual subnormalized vectors keep their Euclidean norm under a phase-bearing embedding.
example : ‖WithLp.toLp 2 (phaseJ *ᵥ
    (EuclideanSpace.single 0 (1 / 2 : ℂ) : EuclideanSpace ℂ (Fin 1)).ofLp)‖ = 1 / 2 := by
  rw [norm_toLp_mulVec_of_isometry phaseJ phaseJ_isometry]
  norm_num [EuclideanSpace.single]

-- An empty source domain is valid even though the embedding has norm zero, not one.
example (B : Matrix Bool (Fin 0) ℂ) :
    ‖(0 : Matrix (Fin 3) (Fin 0) ℂ)‖ = 0 ∧
      ‖isometricDomainExtension B (0 : Matrix (Fin 3) (Fin 0) ℂ)‖ = 0 := by
  have hJ : ((0 : Matrix (Fin 3) (Fin 0) ℂ)ᴴ * (0 : Matrix (Fin 3) (Fin 0) ℂ) :
      Matrix (Fin 0) (Fin 0) ℂ) = 1 := by
    ext i j
    exact i.elim0
  have hB : B = 0 := by
    ext i j
    exact j.elim0
  constructor
  · exact norm_zero
  · rw [norm_isometricDomainExtension B _ hJ, hB, norm_zero]

-- An empty output gives norm zero while the input and ambient spaces stay nonempty.
example (B : Matrix (Fin 0) (Fin 1) ℂ) :
    ‖isometricDomainExtension B phaseJ‖ = 0 := by
  have hB : B = 0 := by
    ext i j
    exact i.elim0
  rw [norm_isometricDomainExtension B phaseJ phaseJ_isometry, hB, norm_zero]

-- A completely empty ambient/domain pair is handled by the same exact norm theorem.
example (B : Matrix Bool (Fin 0) ℂ) :
    ‖isometricDomainExtension B (0 : Matrix (Fin 0) (Fin 0) ℂ)‖ = 0 := by
  have hJ : (0 : Matrix (Fin 0) (Fin 0) ℂ)ᴴ * (0 : Matrix (Fin 0) (Fin 0) ℂ) = 1 := by
    ext i j
    exact i.elim0
  have hB : B = 0 := by
    ext i j
    exact j.elim0
  rw [norm_isometricDomainExtension B _ hJ, hB, norm_zero]

private abbrev leftDim : Bool → Type
  | false => Fin 1
  | true => Fin 3

private abbrev rightDim : Bool → Type
  | false => Fin 2
  | true => Fin 0

local instance (b : Bool) : Fintype (leftDim b) := by cases b <;> infer_instance
local instance (b : Bool) : DecidableEq (leftDim b) := by cases b <;> infer_instance
local instance (b : Bool) : Fintype (rightDim b) := by cases b <;> infer_instance
local instance (b : Bool) : DecidableEq (rightDim b) := by cases b <;> infer_instance

-- Unequal branch dimensions have genuinely orthogonal canonical sectors.
example : isometricDomainExtension phaseB (sigmaBlockInclusion leftDim false) *
    sigmaBlockInclusion leftDim true = 0 :=
  isometricDomainExtension_sigmaBlockInclusion_mul_of_ne leftDim
    (ξ := false) (ζ := true) (by decide) phaseB

-- Extending a private sector keeps the two memory coordinates unchanged in the norm bound.
example (B : Matrix Bool (leftDim false × Fin 2) ℂ) :
    ‖isometricDomainExtension B
      (sigmaBlockInclusion leftDim false ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))‖ = ‖B‖ :=
  norm_isometricDomainExtension_sigmaBlockInclusion_kronecker_one leftDim false B

-- Both source halves are actually inserted in their dependent common sectors; norm stays one.
example : ‖WithLp.toLp 2
    ((sigmaBlockInclusion leftDim false ⊗ₖ sigmaBlockInclusion rightDim false) *ᵥ
      (EuclideanSpace.single (0, 1) Complex.I :
        EuclideanSpace ℂ (leftDim false × rightDim false)).ofLp)‖ = 1 := by
  rw [norm_sigmaBlockInclusion_kronecker_mulVec leftDim rightDim false]
  simp only [EuclideanSpace.single, PiLp.norm_single, Complex.norm_I]

-- The other branch has an empty source half and still satisfies the same norm identity.
example : ‖WithLp.toLp 2
    ((sigmaBlockInclusion leftDim true ⊗ₖ sigmaBlockInclusion rightDim true) *ᵥ
      (0 : EuclideanSpace ℂ (leftDim true × rightDim true)).ofLp)‖ = 0 := by
  rw [norm_sigmaBlockInclusion_kronecker_mulVec leftDim rightDim true, norm_zero]

end
