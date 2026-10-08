/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CfcKronecker
import QICLean.Algebra.KroneckerFactorPositivity

/-!
# Multiplicative functional calculus on finite tensor powers

A function multiplicative on nonnegative numbers passes through a tensor power
of a positive matrix. The condition at one includes the zero-copy tensor power.
This includes the kernel-preserving function used for the surprisal moment in
OpenAI's area-law manuscript, `07-comparators.tex`, lines 75–85 and 227–238.
-/

noncomputable section
open scoped ComplexOrder Kronecker Matrix.Norms.L2Operator
namespace Matrix
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-
Provenance-ID: 8753-qic-schur-iid-02
Original formalization, no upstream Lean proof text reused.
Declaration: Matrix.cfc_finKronecker_const
Manuscript: September 24, 2026, comparator:mgf-data and comparator:signed-label-moments.
-/

/-- Multiplicative functional calculus on a positive tensor power, including
zero copies. Only the values on the nonnegative axis are relevant. -/
theorem cfc_finKronecker_const {σ : Matrix Ω Ω ℂ} (hσ : σ.PosSemidef)
    (f : ℝ → ℝ) (h1 : f 1 = 1)
    (hmul : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → f (x * y) = f x * f y) (k : ℕ) :
    cfc f (finKronecker (fun _ : Fin k ↦ σ)) =
      finKronecker (fun _ : Fin k ↦ cfc f σ) := by
  induction k with
  | zero =>
    have hzero (A : Matrix Ω Ω ℂ) : finKronecker (fun _ : Fin 0 ↦ A) = 1 := by
      ext x y
      have hxy : x = y := Subsingleton.elim x y
      subst y
      simp
    rw [hzero, hzero, cfc_apply_one, h1, map_one]
  | succ k ih =>
    let e := Fin.consEquiv (fun _ : Fin (k + 1) ↦ Ω)
    have he : (cfc f (finKronecker (fun _ : Fin (k + 1) ↦ σ))).submatrix e e =
        (finKronecker (fun _ : Fin (k + 1) ↦ cfc f σ)).submatrix e e := by
      have hc := cfc_submatrix_equiv
        (finKronecker_posSemidef (fun _ : Fin (k + 1) ↦ σ) (fun _ ↦ hσ)).isHermitian
        f e.symm
      simp only [Equiv.symm_symm] at hc
      rw [← hc]
      rw [finKronecker_cons, finKronecker_cons]
      change cfc f (σ ⊗ₖ finKronecker (fun _ : Fin k ↦ σ)) =
        cfc f σ ⊗ₖ finKronecker (fun _ : Fin k ↦ cfc f σ)
      rw [cfc_kronecker_of_mul_posSemidef hσ
        (finKronecker_posSemidef (fun _ : Fin k ↦ σ) (fun _ ↦ hσ)) f hmul]
      exact congrArg (fun B ↦ cfc f σ ⊗ₖ B) ih
    ext x y
    simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply] using
      congrFun (congrFun he (e.symm x)) (e.symm y)

end Matrix
