/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorConvexity

/-!
# Powers of compressions have smaller trace

For a positive semidefinite matrix `A` on `ℂ^n`, an injection `j : m ↪ n` and `p ≥ 1`,

`Tr (A|_m)^p ≤ Tr A^p`,

where `A|_m = E† A E` is the compression to the coordinates in the range of `j`. Write
`A|_m = ∑_i β_i ψ_i ψ_i†`. Then `β_i = ⟨Eψ_i, A Eψ_i⟩`, and Jensen's inequality for the convex
function `x^p` gives `β_i^p ≤ ⟨Eψ_i, A^p Eψ_i⟩`; summing over `i` gives the trace of the
compression of `A^p`, which is at most `Tr A^p`.

The area-law paper (*A two-dimensional area law from a global spectral gap*, `05-replicas.tex`,
proof of Lemma 6.2, lines 380–388) uses this for `p = 1/t` to bound the trace of the
compressed samples `τ = (E† σ^t E)^{1/t}` by `Tr σ = 1`; it argues through the min–max
principle.

The proof is written from the standard theory; no Lean source was adapted.

## Main declarations

* `Matrix.embedMatrix j` — the isometry `E` of an injection.
* `Matrix.conjTranspose_mul_mul_embedMatrix` — `E† A E = A.submatrix j j`.
* `Matrix.re_trace_rpow_submatrix_le` — `Re Tr (A.submatrix j j)^p ≤ Re Tr A^p`.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Finset

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The isometry `E : ℂ^m → ℂ^n` of an injection `j : m ↪ n`. -/
def embedMatrix (j : m ↪ n) : Matrix n m ℂ := fun a c => if a = j c then 1 else 0

omit [Fintype m] [DecidableEq m] in
theorem conjTranspose_mul_mul_embedMatrix (j : m ↪ n) (A : Matrix n n ℂ) :
    (embedMatrix j)ᴴ * A * embedMatrix j = A.submatrix j j := by
  ext c c'
  simp only [mul_apply, conjTranspose_apply, embedMatrix, submatrix_apply]
  rw [sum_eq_single (j c')]
  · rw [sum_eq_single (j c)]
    · simp
    · intro a _ ha; simp [ha]
    · simp
  · intro b _ hb; simp [hb]
  · simp

omit [Fintype m] in
theorem conjTranspose_mul_embedMatrix (j : m ↪ n) :
    (embedMatrix j)ᴴ * embedMatrix j = 1 := by
  have h := conjTranspose_mul_mul_embedMatrix j 1
  rw [Matrix.mul_one] at h
  rw [h]
  ext c c'
  simp [submatrix_apply, one_apply, j.injective.eq_iff]

omit [DecidableEq m] in
/-- Quadratic forms of `A` at `E v` are quadratic forms of the compression at `v`. -/
theorem star_embedMatrix_mulVec_dotProduct (j : m ↪ n) (M : Matrix n n ℂ) (v : m → ℂ) :
    star (embedMatrix j *ᵥ v) ⬝ᵥ (M *ᵥ (embedMatrix j *ᵥ v)) =
      star v ⬝ᵥ (M.submatrix j j *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
    conjTranspose_mul_mul_embedMatrix]

theorem IsHermitian.star_eigenvectorBasis_dotProduct_self {A : Matrix m m ℂ} (hA : A.IsHermitian)
    (i : m) : star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ ⇑(hA.eigenvectorBasis i) = 1 := by
  have hnorm : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have h1 : inner ℂ (hA.eigenvectorBasis i) (hA.eigenvectorBasis i) = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]; simp
  rw [dotProduct_comm]
  exact (EuclideanSpace.inner_eq_star_dotProduct _ _).symm.trans h1

/-- **Powers of compressions have smaller trace**: for `A ≥ 0`, an injection `j` and `p ≥ 1`,
`Re Tr (A.submatrix j j)^p ≤ Re Tr A^p`. -/
theorem re_trace_rpow_submatrix_le {A : Matrix n n ℂ} (hA : A.PosSemidef) (j : m ↪ n)
    {p : ℝ} (hp : 1 ≤ p) : ((A.submatrix j j) ^ p).trace.re ≤ (A ^ p).trace.re := by
  set B := A.submatrix j j
  set E := embedMatrix j
  have hB : B.PosSemidef := hA.submatrix j
  have hf : ConvexOn ℝ (Set.Ici (0 : ℝ)) fun x : ℝ => x ^ p := convexOn_rpow hp
  set C := hA.isHermitian.cfc fun x : ℝ => x ^ p with hCdef
  have hC : C.PosSemidef := by
    rw [hCdef, ← hA.isHermitian.cfc_eq]
    exact Matrix.nonneg_iff_posSemidef.mp
      (cfc_nonneg fun x hx => Real.rpow_nonneg (spectrum_nonneg_of_nonneg hA.nonneg hx) p)
  rw [CFC.rpow_eq_cfc_real hB.nonneg, CFC.rpow_eq_cfc_real hA.nonneg, hB.isHermitian.cfc_eq,
    hA.isHermitian.cfc_eq]
  have h1 := hB.isHermitian.trace_cfc_eq_sum_re fun x : ℝ => x ^ p
  simp only [RCLike.re_to_complex] at h1
  rw [h1]
  set ψ := fun i => ⇑(hB.isHermitian.eigenvectorBasis i)
  -- each eigenvalue of the compression is a diagonal value of `A`
  have hstep : ∀ i, hB.isHermitian.eigenvalues i ^ p ≤
      (star (ψ i) ⬝ᵥ (C.submatrix j j *ᵥ ψ i)).re := by
    intro i
    have hunit : star (E *ᵥ ψ i) ⬝ᵥ (E *ᵥ ψ i) = 1 := by
      have := star_embedMatrix_mulVec_dotProduct j 1 (ψ i)
      rw [one_mulVec, submatrix_one_embedding, one_mulVec] at this
      rw [this]
      exact hB.isHermitian.star_eigenvectorBasis_dotProduct_self i
    have hj := diagonal_jensen_of_convexOn hf hA hunit
    rw [star_embedMatrix_mulVec_dotProduct, star_embedMatrix_mulVec_dotProduct] at hj
    rw [hB.isHermitian.eigenvalues_eq i]
    exact hj
  calc ∑ i, hB.isHermitian.eigenvalues i ^ p
      ≤ ∑ i, (star (ψ i) ⬝ᵥ (C.submatrix j j *ᵥ ψ i)).re := sum_le_sum fun i _ => hstep i
    _ = (C.submatrix j j).trace.re := by
        rw [← Complex.re_sum]
        congr 1
        exact hB.isHermitian.sum_dotProduct_eigenvectorBasis_eq_trace _
    _ ≤ C.trace.re := by
        simp only [trace, diag_apply, submatrix_apply, Complex.re_sum]
        rw [← sum_map univ j (fun a => (C a a).re)]
        refine sum_le_sum_of_subset_of_nonneg (subset_univ _) fun a _ _ => ?_
        exact Complex.nonneg_iff.mp hC.diag_nonneg |>.1

end Matrix
