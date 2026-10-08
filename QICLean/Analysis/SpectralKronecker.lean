/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ResolventDefect
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Spectral functions on Hilbert--Schmidt spaces

This file collects the algebra of spectral functions `spectralFun U f = U diag(f) U*`
needed to realize left and right multiplications on the Hilbert--Schmidt space of
matrices.  With Mathlib's column-stacking `Matrix.vec`, `vec (A X B) = (Bᵀ ⊗ A) vec X`;
for `A = U diag(a) U*` and `B = W diag(b) W*` the operator `Bᵀ ⊗ A` is the spectral
function of `conj W ⊗ U` with eigenvalues `b_j a_i`.

## Main results

* `Matrix.spectralFun_kronecker` — Kronecker products of spectral functions.
* `Matrix.transpose_spectralFun` — transposes of spectral functions.
* `Matrix.IsHermitian.spectralFun_eigenvectorUnitary` — the spectral theorem in the form
  `A = spectralFun U λ`.
* `Matrix.linMatrix` — the matrix of a linear map on matrices, with
  `linMatrix Φ *ᵥ vec Y = vec (Φ Y)`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 5.2,
  `04-conditional.tex`, lines 352–366.
-/

open scoped Matrix Kronecker ComplexOrder

noncomputable section

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Kronecker product of two unitaries. -/
def kroneckerUnitary (U : unitary (Matrix n n ℂ)) (W : unitary (Matrix m m ℂ)) :
    unitary (Matrix (n × m) (n × m) ℂ) :=
  ⟨(U : Matrix n n ℂ) ⊗ₖ (W : Matrix m m ℂ), kronecker_mem_unitary U.2 W.2⟩

/-- The entrywise complex conjugate of a unitary. -/
def conjUnitary (U : unitary (Matrix n n ℂ)) : unitary (Matrix n n ℂ) :=
  ⟨(U : Matrix n n ℂ).map (starRingEnd ℂ), by
    have e : ((U : Matrix n n ℂ).map (starRingEnd ℂ))ᴴ =
        ((U : Matrix n n ℂ)ᴴ).map (starRingEnd ℂ) := by
      ext i j; simp [conjTranspose_apply]
    rw [Unitary.mem_iff, star_eq_conjTranspose, e, ← Matrix.map_mul, ← Matrix.map_mul,
      ← star_eq_conjTranspose, Unitary.star_mul_self_of_mem U.2, Unitary.mul_star_self_of_mem U.2,
      Matrix.map_one _ (map_zero _) (map_one _)]
    exact ⟨rfl, rfl⟩⟩

theorem coe_kroneckerUnitary (U : unitary (Matrix n n ℂ)) (W : unitary (Matrix m m ℂ)) :
    (kroneckerUnitary U W : Matrix (n × m) (n × m) ℂ) = (U : Matrix n n ℂ) ⊗ₖ (W : Matrix m m ℂ) :=
  rfl

theorem spectralFun_kronecker (U : unitary (Matrix n n ℂ)) (W : unitary (Matrix m m ℂ))
    (f : n → ℂ) (g : m → ℂ) :
    spectralFun U f ⊗ₖ spectralFun W g =
      spectralFun (kroneckerUnitary U W) (fun p => f p.1 * g p.2) := by
  simp only [spectralFun, coe_kroneckerUnitary, mul_kronecker_mul, diagonal_kronecker_diagonal,
    star_eq_conjTranspose, conjTranspose_kronecker]

theorem transpose_spectralFun (U : unitary (Matrix n n ℂ)) (f : n → ℂ) :
    (spectralFun U f)ᵀ = spectralFun (conjUnitary U) f := by
  simp only [spectralFun, transpose_mul, diagonal_transpose, conjUnitary, star_eq_conjTranspose]
  rw [Matrix.mul_assoc]
  congr 1
  · ext i j; simp [conjTranspose_apply, transpose_apply]

theorem trace_spectralFun (U : unitary (Matrix n n ℂ)) (f : n → ℂ) :
    (spectralFun U f).trace = ∑ k, f k := by
  rw [spectralFun, trace_mul_cycle, Unitary.star_mul_self_of_mem U.2, Matrix.one_mul,
    trace_diagonal]

theorem spectralFun_congr (U : unitary (Matrix n n ℂ)) {f g : n → ℂ} (h : ∀ k, f k = g k) :
    spectralFun U f = spectralFun U g := by
  rw [funext h]

theorem spectralFun_smul (U : unitary (Matrix n n ℂ)) (c : ℂ) (f : n → ℂ) :
    spectralFun U (c • f) = c • spectralFun U f := by
  simp only [spectralFun, diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- The spectral theorem in the form `A = U diag(λ) U*` with the eigenvector unitary. -/
theorem IsHermitian.spectralFun_eigenvectorUnitary {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    spectralFun hA.eigenvectorUnitary (fun k => (hA.eigenvalues k : ℂ)) = A := by
  conv_rhs => rw [hA.spectral_theorem]
  rfl

/-- The matrix of a linear map on matrices, in the column-stacking coordinates `vec`. -/
def linMatrix (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) : Matrix (n × n) (m × m) ℂ :=
  Matrix.of fun p q => vec (Φ (single q.2 q.1 1)) p

omit [Fintype n] [DecidableEq n] in
theorem linMatrix_mulVec_vec (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ) (Y : Matrix m m ℂ) :
    linMatrix Φ *ᵥ vec Y = vec (Φ Y) := by
  have hY : Y = ∑ i, ∑ j, Y i j • single i j (1 : ℂ) := by
    conv_lhs => rw [matrix_eq_sum_single Y]
    simp only [smul_single, smul_eq_mul, mul_one]
  ext p
  conv_rhs => rw [hY]
  simp only [map_sum, map_smul, vec_sum, vec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [linMatrix, mulVec, dotProduct, of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [vec, mul_comm]

/-- Two matrices with the same sesquilinear form are equal. -/
theorem ext_star_dotProduct_mulVec {M N : Matrix n m ℂ}
    (h : ∀ x y, star x ⬝ᵥ (M *ᵥ y) = star x ⬝ᵥ (N *ᵥ y)) : M = N := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [mulVec_single, dotProduct, Pi.single_apply] using this

/-- Two matrices on Hilbert--Schmidt spaces agree when their forms agree on all `vec`s. -/
theorem ext_star_vec_dotProduct_mulVec_vec {l k : Type*} [Fintype l] [DecidableEq l]
    [Fintype k] [DecidableEq k] {M N : Matrix (l × l) (k × k) ℂ}
    (h : ∀ (Z : Matrix l l ℂ) (Y : Matrix k k ℂ),
      star (vec Z) ⬝ᵥ (M *ᵥ vec Y) = star (vec Z) ⬝ᵥ (N *ᵥ vec Y)) : M = N := by
  refine ext_star_dotProduct_mulVec fun x y => ?_
  obtain ⟨Z, rfl⟩ := vec_bijective.2 x
  obtain ⟨Y, rfl⟩ := vec_bijective.2 y
  exact h Z Y

/-- A multiplicative function of the eigenvalues `aⱼ⁻¹ bᵢ` of `Bᵀ ⊗ A`. -/
theorem spectralFun_leftRight_mul (U : unitary (Matrix n n ℂ)) (W : unitary (Matrix m m ℂ))
    (a : n → ℝ) (b : m → ℝ) (g : ℝ → ℂ) (φ ψ : ℝ → ℂ)
    (hg : ∀ k j, g (a k ^ (-1 : ℝ) * b j) = φ (a k) * ψ (b j)) :
    spectralFun (kroneckerUnitary (conjUnitary U) W) (fun p => g (a p.1 ^ (-1 : ℝ) * b p.2)) =
      (spectralFun U (fun k => φ (a k)))ᵀ ⊗ₖ spectralFun W (fun j => ψ (b j)) := by
  rw [transpose_spectralFun, spectralFun_kronecker]
  congr 1
  funext p
  exact hg p.1 p.2

/-- An additive function of the eigenvalues `aⱼ⁻¹ bᵢ` of `Bᵀ ⊗ A`. -/
theorem spectralFun_leftRight_add (U : unitary (Matrix n n ℂ)) (W : unitary (Matrix m m ℂ))
    (a : n → ℝ) (b : m → ℝ) (g : ℝ → ℂ) (φ ψ : ℝ → ℂ)
    (hg : ∀ k j, g (a k ^ (-1 : ℝ) * b j) = φ (a k) + ψ (b j)) :
    spectralFun (kroneckerUnitary (conjUnitary U) W) (fun p => g (a p.1 ^ (-1 : ℝ) * b p.2)) =
      (spectralFun U (fun k => φ (a k)))ᵀ ⊗ₖ 1 + 1 ⊗ₖ spectralFun W (fun j => ψ (b j)) := by
  have h1 : (1 : Matrix m m ℂ) = spectralFun W (fun _ => 1) := (spectralFun_one W).symm
  have h2 : (1 : Matrix n n ℂ) = (spectralFun U (fun _ => 1))ᵀ := by
    rw [spectralFun_one, transpose_one]
  rw [h1, h2, transpose_spectralFun, transpose_spectralFun, spectralFun_kronecker,
    spectralFun_kronecker, ← spectralFun_add]
  congr 1
  funext p
  simp only [Pi.add_apply, mul_one, one_mul]
  exact hg p.1 p.2

end Matrix

end
