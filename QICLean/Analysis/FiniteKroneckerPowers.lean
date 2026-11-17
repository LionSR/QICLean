/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.KroneckerFactorPositivity
import QICLean.Analysis.CfcKronecker

/-!
# Powers and traces of finite tensor products

Real powers factor over finite tensor products of positive semidefinite matrices.
Together with multiplication and trace factorization, this gives the product law
for the overlaps used in finite-copy quantum hypothesis testing.
The factors may have different finite index types, and the empty product is included.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace Matrix

variable {N : ℕ} {I : Fin N → Type*} [∀ i, Fintype (I i)]

/-- Multiplication of finite tensor products is componentwise. -/
theorem finKronecker_mul (A B : (i : Fin N) → Matrix (I i) (I i) ℂ) :
    finKronecker (fun i ↦ A i * B i) = finKronecker A * finKronecker B := by
  ext x y
  simp only [finKronecker_apply, mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

/-- The trace of a finite tensor product is the product of the traces. -/
theorem trace_finKronecker (A : (i : Fin N) → Matrix (I i) (I i) ℂ) :
    (finKronecker A).trace = ∏ i, (A i).trace := by
  simp only [trace, diag, finKronecker_apply]
  exact (Fintype.prod_sum (fun i x ↦ A i x x)).symm

/-- Real powers commute with a bijective change of matrix coordinates. -/
theorem PosSemidef.rpow_submatrix_equiv {m n : Type*}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℂ} (hA : A.PosSemidef) (e : n ≃ m) (s : ℝ) :
    (A.submatrix e e) ^ s = (A ^ s).submatrix e e := by
  rw [CFC.rpow_eq_cfc_real (hA.submatrix e).nonneg, CFC.rpow_eq_cfc_real hA.nonneg]
  exact cfc_submatrix_equiv hA.isHermitian _ e.symm

/-- Real powers factor over finite tensor products of positive semidefinite matrices,
including singular factors, arbitrary real exponents, and the empty product. -/
theorem rpow_finKronecker [∀ i, DecidableEq (I i)]
    (A : (i : Fin N) → Matrix (I i) (I i) ℂ) (hA : ∀ i, (A i).PosSemidef) (s : ℝ) :
    (finKronecker A) ^ s = finKronecker (fun i ↦ (A i) ^ s) := by
  induction N with
  | zero =>
    have hzero (B : (i : Fin 0) → Matrix (I i) (I i) ℂ) : finKronecker B = 1 := by
      ext x y
      have hxy : x = y := Subsingleton.elim x y
      subst y
      simp
    rw [hzero, CFC.one_rpow, hzero]
  | succ N ih =>
    apply (submatrix_injective (Fin.consEquiv I).surjective (Fin.consEquiv I).surjective)
    dsimp only
    rw [← (finKronecker_posSemidef A hA).rpow_submatrix_equiv (Fin.consEquiv I),
      finKronecker_submatrix_cons, finKronecker_submatrix_cons,
      (hA 0).rpow_kronecker (finKronecker_posSemidef (Fin.tail A) (fun i ↦ hA i.succ)),
      ih (Fin.tail A) (fun i ↦ hA i.succ)]
    rfl

/-- Scalar homogeneity of real powers also holds for singular positive matrices
and nonnegative scalars, using the convention `0 ^ (0 : ℝ) = 1`. -/
theorem PosSemidef.smul_rpow {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) :
    (c • A) ^ s = c ^ s • A ^ s := by
  rw [CFC.rpow_eq_cfc_real (hA.smul hc).nonneg, CFC.rpow_eq_cfc_real hA.nonneg]
  rw [← cfc_comp_smul c (fun x : ℝ ↦ x ^ s) A
    ((A.finite_real_spectrum.image _).continuousOn _),
    ← cfc_smul (c ^ s) (fun x : ℝ ↦ x ^ s) A (A.finite_real_spectrum.continuousOn _)]
  exact cfc_congr fun x hx ↦ Real.mul_rpow hc (spectrum_nonneg_of_nonneg hA.nonneg hx)

end Matrix
