/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SupportPower
import QICLean.Analysis.CfcConjugation
import QICLean.Analysis.CfcKronecker
import QICLean.Entropy.ConditionalMovement.LogCompression

/-!
# Complex functions of Hermitian matrices

For a Hermitian matrix `A` and a complex function `g` on `ℝ`, put
`cfcC A g = cfc (Re ∘ g) A + i cfc (Im ∘ g) A`.  In an eigenbasis this is
`U diag(g ∘ λ) U*`, so it inherits the algebra of spectral functions, and through the
real continuous functional calculus it commutes with transposition, tensoring with the
identity, reindexing and intertwiners.

## Main definitions

* `Matrix.cfcC`.

## Main results

* `Matrix.cfcC_eq_spectralFun`, `Matrix.cfcC_mul`, `Matrix.conjTranspose_cfcC`.
* `Matrix.cfcC_transpose`, `Matrix.cfcC_kronecker_one`, `Matrix.cfcC_one_kronecker`,
  `Matrix.cfcC_submatrix_equiv`, `Matrix.cfcC_mul_intertwine`.
-/

open scoped Matrix Kronecker ComplexOrder

noncomputable section

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The complex function `g` of a matrix through the real functional calculus of its real
and imaginary parts. -/
def cfcC (A : Matrix n n ℂ) (g : ℝ → ℂ) : Matrix n n ℂ :=
  cfc (fun t => (g t).re) A + Complex.I • cfc (fun t => (g t).im) A

theorem cfcC_eq_spectralFun {A : Matrix n n ℂ} (hA : A.IsHermitian) (g : ℝ → ℂ) :
    cfcC A g = spectralFun hA.eigenvectorUnitary (fun k => g (hA.eigenvalues k)) :=
  (hA.spectralFun_eq_cfc_re_add_im g).symm

theorem cfcC_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) (g₁ g₂ : ℝ → ℂ) :
    cfcC A g₁ * cfcC A g₂ = cfcC A (fun t => g₁ t * g₂ t) := by
  rw [cfcC_eq_spectralFun hA, cfcC_eq_spectralFun hA, cfcC_eq_spectralFun hA, spectralFun_mul]
  rfl

theorem conjTranspose_cfcC {A : Matrix n n ℂ} (hA : A.IsHermitian) (g : ℝ → ℂ) :
    (cfcC A g)ᴴ = cfcC A (fun t => starRingEnd ℂ (g t)) := by
  rw [cfcC_eq_spectralFun hA, cfcC_eq_spectralFun hA, conjTranspose_spectralFun]
  rfl

theorem cfcC_transpose {A : Matrix n n ℂ} (hA : A.IsHermitian) (g : ℝ → ℂ) :
    (cfcC A g)ᵀ = cfcC Aᵀ g := by
  rw [cfcC, cfcC, transpose_add, transpose_smul, cfc_transpose hA, cfc_transpose hA]

theorem cfcC_kronecker_one {A : Matrix n n ℂ} (hA : A.IsHermitian) (g : ℝ → ℂ) :
    cfcC (A ⊗ₖ (1 : Matrix m m ℂ)) g = cfcC A g ⊗ₖ (1 : Matrix m m ℂ) := by
  rw [cfcC, cfcC, cfc_kronecker_one hA, cfc_kronecker_one hA, add_kronecker, smul_kronecker]

theorem cfcC_one_kronecker {B : Matrix m m ℂ} (hB : B.IsHermitian) (g : ℝ → ℂ) :
    cfcC ((1 : Matrix n n ℂ) ⊗ₖ B) g = (1 : Matrix n n ℂ) ⊗ₖ cfcC B g := by
  rw [cfcC, cfcC, cfc_one_kronecker hB, cfc_one_kronecker hB, kronecker_add, kronecker_smul]

theorem cfcC_submatrix_equiv {A : Matrix m m ℂ} (hA : A.IsHermitian) (g : ℝ → ℂ) (e : m ≃ n) :
    cfcC (A.submatrix e.symm e.symm) g = (cfcC A g).submatrix e.symm e.symm := by
  rw [cfcC, cfcC, cfc_submatrix_equiv hA, cfc_submatrix_equiv hA]
  rfl

theorem cfcC_mul_intertwine {A : Matrix n n ℂ} {B : Matrix m m ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (V : Matrix n m ℂ) (hV : A * V = V * B) (g : ℝ → ℂ) :
    cfcC A g * V = V * cfcC B g := by
  rw [cfcC, cfcC, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    ConditionalMovement.QuantumSSA.cfc_intertwine hA hB V hV,
    ConditionalMovement.QuantumSSA.cfc_intertwine hA hB V hV]

/-- The power `A^{[z]}` vanishing on the kernel equals the complex function
`t ↦ if t = 0 then 0 else t^z`. -/
theorem supportCPow_eq_cfcC {A : Matrix n n ℂ} (hA : A.IsHermitian) (z : ℂ) :
    supportCPow hA z = cfcC A (fun t => if t = 0 then 0 else ((t : ℝ) : ℂ) ^ z) := by
  rw [cfcC_eq_spectralFun hA]
  rfl

theorem cfcC_add {A : Matrix n n ℂ} (hA : A.IsHermitian) (g₁ g₂ : ℝ → ℂ) :
    cfcC A g₁ + cfcC A g₂ = cfcC A (fun t => g₁ t + g₂ t) := by
  rw [cfcC_eq_spectralFun hA, cfcC_eq_spectralFun hA, cfcC_eq_spectralFun hA, ← spectralFun_add]
  rfl

theorem cfcC_one {A : Matrix n n ℂ} (hA : A.IsHermitian) : cfcC A (fun _ => 1) = 1 := by
  rw [cfcC_eq_spectralFun hA]; exact spectralFun_one _

theorem cfcC_id {A : Matrix n n ℂ} (hA : A.IsHermitian) : cfcC A (fun t => (t : ℂ)) = A := by
  rw [cfcC_eq_spectralFun hA]; exact hA.spectralFun_eigenvectorUnitary

theorem cfcC_congr_of_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) {g₁ g₂ : ℝ → ℂ}
    (h : ∀ t, 0 ≤ t → g₁ t = g₂ t) : cfcC A g₁ = cfcC A g₂ := by
  rw [cfcC_eq_spectralFun hA.1, cfcC_eq_spectralFun hA.1]
  congr 1; funext k; exact h _ (hA.eigenvalues_nonneg k)

end Matrix

end
