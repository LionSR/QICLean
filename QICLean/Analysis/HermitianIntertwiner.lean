/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixSqrt
import QICLean.Algebra.PosSemidefSupport
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Hermitian lifts of rectangular intertwiners

The supporting algebra below does not require injectivity or full support.
The support-inverse specialization uses continuous functional calculus.
-/

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- A Hermitian intertwiner forces commutation with the left Gram matrix. -/
theorem commute_mul_conjTranspose_of_hermitian_intertwiner
    (F : Matrix m n ℂ) (L : Matrix m m ℂ) (K : Matrix n n ℂ)
    (hL : L.IsHermitian) (hK : K.IsHermitian) (hFK : F * K = L * F) :
    Commute L (F * Fᴴ) := by
  have hKF : K * Fᴴ = Fᴴ * L := by
    simpa only [conjTranspose_mul, hK.eq, hL.eq] using
      congrArg Matrix.conjTranspose hFK
  change L * (F * Fᴴ) = (F * Fᴴ) * L
  calc
    L * (F * Fᴴ) = (L * F) * Fᴴ := (Matrix.mul_assoc _ _ _).symm
    _ = (F * K) * Fᴴ := by rw [hFK]
    _ = F * (K * Fᴴ) := Matrix.mul_assoc _ _ _
    _ = F * (Fᴴ * L) := by rw [hKF]
    _ = (F * Fᴴ) * L := (Matrix.mul_assoc _ _ _).symm

omit [Fintype n] in
/-- Algebraic core of the supported lift: a Hermitian generalized inverse
commuting with the generator gives a Hermitian physical generator.
The supplied identities will be discharged by the existing support inverse;
this helper is not the source-facing existence theorem. -/
theorem isHermitian_conjTranspose_mul_mul_mul
    (F : Matrix m n ℂ) (S L : Matrix m m ℂ)
    (hS : S.IsHermitian) (hL : L.IsHermitian) (hSL : Commute S L) :
    (Fᴴ * S * L * F).IsHermitian := by
  change (Fᴴ * S * L * F)ᴴ = Fᴴ * S * L * F
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hS.eq, hL.eq]
  calc
    Fᴴ * (L * (S * F)) = Fᴴ * ((L * S) * F) := by simp only [Matrix.mul_assoc]
    _ = Fᴴ * ((S * L) * F) := by rw [hSL.eq]
    _ = Fᴴ * S * L * F := by simp only [Matrix.mul_assoc]

/-- The supported Hermitian lift intertwines, using only the two support
identities. Neither identity is a tensor-network assumption. -/
theorem mul_supportedHermitianLift
    (F : Matrix m n ℂ) (S L : Matrix m m ℂ)
    (hSL : Commute S L) (hGL : Commute (F * Fᴴ) L)
    (hSupport : (F * Fᴴ) * S * F = F) :
    F * (Fᴴ * S * L * F) = L * F := by
  calc
    F * (Fᴴ * S * L * F) = (F * Fᴴ) * (S * L) * F := by
      simp only [Matrix.mul_assoc]
    _ = (F * Fᴴ) * (L * S) * F := by rw [hSL.eq]
    _ = ((F * Fᴴ) * L) * S * F := by simp only [Matrix.mul_assoc]
    _ = (L * (F * Fᴴ)) * S * F := by rw [hGL.eq]
    _ = L * ((F * Fᴴ) * S * F) := by simp only [Matrix.mul_assoc]
    _ = L * F := by rw [hSupport]

/-- The chosen lift acts by zero on the unused physical support. -/
theorem supportedHermitianLift_mulVec_eq_zero
    (F : Matrix m n ℂ) (S L : Matrix m m ℂ) (v : n → ℂ)
    (hv : F.mulVec v = 0) :
    (Fᴴ * S * L * F).mulVec v = 0 := by
  simp only [← mulVec_mulVec, hv, mulVec_zero]

/-- Commutation passes to the existing positive-semidefinite support inverse.
The proof follows the CFC argument already used in SchurComplement. -/
theorem PosSemidef.commute_supportInv [DecidableEq m]
    {G : Matrix m m ℂ} (hG : G.PosSemidef)
    (L : Matrix m m ℂ) (hLG : Commute L G) :
    Commute L hG.supportInv := by
  have hsqrt : Commute L hG.supportInvSqrt := by
    rw [PosSemidef.supportInvSqrt, ← hG.isHermitian.cfc_eq]
    exact (IsSelfAdjoint.commute_cfc
      (isHermitian_iff_isSelfAdjoint.mp hG.isHermitian) hLG.symm
      (fun x : ℝ => if x ≠ 0 then (Real.sqrt x)⁻¹ else 0)).symm
  change L * (hG.supportInvSqrt * hG.supportInvSqrt) =
    (hG.supportInvSqrt * hG.supportInvSqrt) * L
  calc
    L * (hG.supportInvSqrt * hG.supportInvSqrt) =
        (L * hG.supportInvSqrt) * hG.supportInvSqrt := (Matrix.mul_assoc _ _ _).symm
    _ = (hG.supportInvSqrt * L) * hG.supportInvSqrt := by rw [hsqrt.eq]
    _ = hG.supportInvSqrt * (L * hG.supportInvSqrt) := Matrix.mul_assoc _ _ _
    _ = hG.supportInvSqrt * (hG.supportInvSqrt * L) := by rw [hsqrt.eq]
    _ = (hG.supportInvSqrt * hG.supportInvSqrt) * L := (Matrix.mul_assoc _ _ _).symm

/-- A commuting Hermitian action on the left Gram matrix has a Hermitian
right lift, chosen to act trivially on the kernel of the rectangular matrix.
No rank or nonempty-index assumption is imposed. -/
theorem exists_hermitian_intertwiner_of_commute_mul_conjTranspose
    (F : Matrix m n ℂ) (L : Matrix m m ℂ) (hL : L.IsHermitian)
    (hLG : Commute L (F * Fᴴ)) :
    ∃ K : Matrix n n ℂ, K.IsHermitian ∧ F * K = L * F ∧
      ∀ v : n → ℂ, F.mulVec v = 0 → K.mulVec v = 0 := by
  classical
  let hG : (F * Fᴴ).PosSemidef := posSemidef_self_mul_conjTranspose F
  have hSL : Commute hG.supportInv L := (hG.commute_supportInv L hLG).symm
  have hSupport : (F * Fᴴ) * hG.supportInv * F = F := by
    rw [hG.self_mul_supportInv]
    exact supportProj_mul_conjTranspose_mul_self F
  refine ⟨Fᴴ * hG.supportInv * L * F,
    isHermitian_conjTranspose_mul_mul_mul F _ L hG.supportInv_isHermitian hL hSL,
    mul_supportedHermitianLift F _ L hSL hLG.symm hSupport, ?_⟩
  exact supportedHermitianLift_mulVec_eq_zero F _ L

/-- A Hermitian left action commutes with the left Gram matrix exactly when
it admits a Hermitian right intertwiner, including rank-deficient matrices. -/
theorem commute_mul_conjTranspose_iff_exists_hermitian_intertwiner
    (F : Matrix m n ℂ) (L : Matrix m m ℂ) (hL : L.IsHermitian) :
    Commute L (F * Fᴴ) ↔
      ∃ K : Matrix n n ℂ, K.IsHermitian ∧ F * K = L * F := by
  constructor
  · intro h
    obtain ⟨K, hK, hFK, _⟩ :=
      exists_hermitian_intertwiner_of_commute_mul_conjTranspose F L hL h
    exact ⟨K, hK, hFK⟩
  · rintro ⟨K, hK, hFK⟩
    exact commute_mul_conjTranspose_of_hermitian_intertwiner F L K hL hK hFK

end Matrix
