/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.PartialTrace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.Order.Chebyshev

/-!
# A positive matrix is dominated by its marginal

For a positive semidefinite matrix `ρ` on `X ⊗ Y` with `d = dim X`,
$$\rho\le d\,(I_X\otimes\rho_Y),\qquad \rho_Y=\operatorname{tr}_X\rho.$$
Writing `ρ = Bᴴ B` and `v = ∑_b |b⟩ ⊗ v_b`, the Cauchy--Schwarz inequality over the `d`
blocks gives `⟨v, ρ v⟩ ≤ d ∑_b ⟨v_b, ρ_{bb} v_b⟩ ≤ d ∑_b ⟨v_b, ρ_Y v_b⟩`.

## Main results

* `Matrix.PosSemidef.le_card_smul_one_kronecker_partialTraceLeft`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), Section 5.1,
  `04-conditional.tex`, lines 56–63.
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker

namespace Matrix

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

omit [DecidableEq X] [DecidableEq Y] in
theorem dotProduct_self_eq_sum_normSq {K : Type*} [Fintype K] (v : K → ℂ) :
    star v ⬝ᵥ v = ((∑ k, Complex.normSq (v k) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

omit [DecidableEq Y] in
theorem dotProduct_one_kronecker_mulVec (M : Matrix Y Y ℂ) (x : X × Y → ℂ) :
    star x ⬝ᵥ (((1 : Matrix X X ℂ) ⊗ₖ M) *ᵥ x) =
      ∑ a, star (fun y => x (a, y)) ⬝ᵥ (M *ᵥ fun y => x (a, y)) := by
  simp only [dotProduct, mulVec, kroneckerMap_apply, one_apply, Fintype.sum_prod_type,
    Pi.star_apply, ite_mul, one_mul, zero_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => ?_
  congr 1
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

omit [DecidableEq X] [DecidableEq Y] [Fintype Y] in
theorem partialTraceLeft_conjTranspose_mul_self {K : Type*} [Fintype K]
    (B : Matrix K (X × Y) ℂ) :
    partialTraceLeft (Bᴴ * B) = ∑ b, (Matrix.of fun k y => B k (b, y))ᴴ *
      (Matrix.of fun k y => B k (b, y) : Matrix K Y ℂ) := by
  ext y y'
  simp only [partialTraceLeft_apply, mul_apply, conjTranspose_apply, Matrix.sum_apply, of_apply]

/-- **Domination by the marginal.** For positive semidefinite `ρ` on `X ⊗ Y`,
`ρ ≤ (dim X) (I_X ⊗ tr_X ρ)`.  Area-law manuscript, `04-conditional.tex`,
lines 56–63. -/
theorem PosSemidef.le_card_smul_one_kronecker_partialTraceLeft
    {ρ : Matrix (X × Y) (X × Y) ℂ} (hρ : ρ.PosSemidef) :
    ρ ≤ (Fintype.card X : ℂ) • ((1 : Matrix X X ℂ) ⊗ₖ Matrix.partialTraceLeft ρ) := by
  have hnn : 0 ≤ ρ := hρ.nonneg
  set B := CFC.sqrt ρ
  have hB : Bᴴ = B := (CFC.sqrt_nonneg ρ).isSelfAdjoint.star_eq
  have hρB : ρ = Bᴴ * B := by rw [hB]; exact (CFC.sqrt_mul_sqrt_self ρ hnn).symm
  have hherm : ((Fintype.card X : ℂ) •
      ((1 : Matrix X X ℂ) ⊗ₖ Matrix.partialTraceLeft ρ)).IsHermitian := by
    have h1 := (Matrix.partialTraceLeft_isHermitian hρ.isHermitian)
    rw [IsHermitian, conjTranspose_smul, conjTranspose_kronecker, conjTranspose_one, h1.eq]
    simp
  rw [le_iff, posSemidef_iff_dotProduct_mulVec]
  refine ⟨hherm.sub hρ.isHermitian, fun x => ?_⟩
  set Bb : X → Matrix (X × Y) Y ℂ := fun b => Matrix.of fun k y => B k (b, y)
  set xs : X → Y → ℂ := fun a y => x (a, y)
  -- the left quadratic form
  have hBx : ∀ k, (B *ᵥ x) k = ∑ a, (Bb a *ᵥ xs a) k := by
    intro k
    simp only [mulVec, dotProduct, Fintype.sum_prod_type, Bb, xs, of_apply]
  have hL : star x ⬝ᵥ (ρ *ᵥ x) =
      ((∑ k, Complex.normSq (∑ a, (Bb a *ᵥ xs a) k) : ℝ) : ℂ) := by
    rw [hρB, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, dotProduct_self_eq_sum_normSq]
    simp only [hBx]
  -- the right quadratic form
  have hR : star x ⬝ᵥ (((1 : Matrix X X ℂ) ⊗ₖ Matrix.partialTraceLeft ρ) *ᵥ x) =
      ((∑ a, ∑ b, ∑ k, Complex.normSq ((Bb b *ᵥ xs a) k) : ℝ) : ℂ) := by
    rw [dotProduct_one_kronecker_mulVec, hρB, partialTraceLeft_conjTranspose_mul_self]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, dotProduct_self_eq_sum_normSq]
    push_cast
    rfl
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, hL, hR, smul_eq_mul]
  rw [show ((Fintype.card X : ℂ)) = ((Fintype.card X : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.zero_le_real, sub_nonneg]
  -- Cauchy--Schwarz over the blocks
  have hcs : ∀ k, Complex.normSq (∑ a, (Bb a *ᵥ xs a) k) ≤
      Fintype.card X * ∑ a, Complex.normSq ((Bb a *ᵥ xs a) k) := by
    intro k
    simp only [Complex.normSq_eq_norm_sq]
    calc ‖∑ a, (Bb a *ᵥ xs a) k‖ ^ 2 ≤ (∑ a, ‖(Bb a *ᵥ xs a) k‖) ^ 2 := by
          gcongr; exact norm_sum_le _ _
      _ ≤ Fintype.card X * ∑ a, ‖(Bb a *ᵥ xs a) k‖ ^ 2 := by
          simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ)
            (f := fun a => ‖(Bb a *ᵥ xs a) k‖)
  calc ∑ k, Complex.normSq (∑ a, (Bb a *ᵥ xs a) k)
      ≤ ∑ k, Fintype.card X * ∑ a, Complex.normSq ((Bb a *ᵥ xs a) k) :=
        Finset.sum_le_sum fun k _ => hcs k
    _ = Fintype.card X * ∑ a, ∑ k, Complex.normSq ((Bb a *ᵥ xs a) k) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ Fintype.card X * ∑ a, ∑ b, ∑ k, Complex.normSq ((Bb b *ᵥ xs a) k) := by
        gcongr with a
        exact Finset.single_le_sum (f := fun b => ∑ k, Complex.normSq ((Bb b *ᵥ xs a) k))
          (fun b _ => Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ a)

end Matrix
