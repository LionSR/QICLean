/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.ConditionalSkewSetup

/-!
# The strip bound for the conditional skew function

For a unit vector `θ` and `0 ≤ h ≤ 1` on `P₀ x`, the function `f` of the conditional
skew estimate satisfies `|f(z)| ≤ (dim P₀ · dim x)²` on `|Re z| ≤ 1/4`.  Expanding `h` in
matrix units of `P₀ x`, each term is the inner product of
`ρ_Y^{[z̄]} d* ρ_Y^{[-z̄]} θ` and `ρ_P^{[z]} c ρ_P^{[-z]} θ` for matrix units `c` on `P₀`
and `d` on `x`, and each of these vectors has norm at most one by the sandwich bound.

## Main results

* `Entropy.ConditionalSkew.norm_skewFun_le_of_strip`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 5.3,
  `04-conditional.tex`, lines 511–532.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.ConditionalSkew

open _root_.Matrix

variable {P₀ P₁ X U F : Type*} [Fintype P₀] [DecidableEq P₀] [Fintype P₁] [DecidableEq P₁]
  [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F] [DecidableEq F]

theorem norm_toLp_sq_eq_re' {n : Type*} [Fintype n] (v : n → ℂ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 = (star v ⬝ᵥ v).re := by
  rw [@norm_sq_eq_re_inner ℂ, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rfl

theorem norm_star_dotProduct_le {n : Type*} [Fintype n] (u v : n → ℂ) :
    ‖star u ⬝ᵥ v‖ ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℂ n)‖ *
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ := by
  have := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 u : EuclideanSpace ℂ n)
    (WithLp.toLp 2 v)
  rwa [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at this

/-- A positive semidefinite form bounded by the identity is a contraction:
`‖⟨u, H v⟩‖ ≤ ‖u‖ ‖v‖`. -/
theorem norm_dotProduct_mulVec_le_of_nonneg_le_one {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (h0 : 0 ≤ H) (h1 : H ≤ 1) (u v : n → ℂ) :
    ‖star u ⬝ᵥ (H *ᵥ v)‖ ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℂ n)‖ *
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ := by
  set B := CFC.sqrt H
  have hB : Bᴴ = B := (CFC.sqrt_nonneg H).isSelfAdjoint.star_eq
  have hHB : H = Bᴴ * B := by rw [hB]; exact (CFC.sqrt_mul_sqrt_self H h0).symm
  have hBw : ∀ w : n → ℂ, ‖(WithLp.toLp 2 (B *ᵥ w) : EuclideanSpace ℂ n)‖ ≤
      ‖(WithLp.toLp 2 w : EuclideanSpace ℂ n)‖ := by
    intro w
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [norm_toLp_sq_eq_re', norm_toLp_sq_eq_re', star_mulVec_dotProduct, mulVec_mulVec, ← hHB]
    have := (le_iff.1 h1).dotProduct_mulVec_nonneg w
    rw [sub_mulVec, one_mulVec, dotProduct_sub, sub_nonneg, Complex.le_def] at this
    exact this.1
  rw [hHB, ← mulVec_mulVec, ← star_mulVec_dotProduct]
  exact (norm_star_dotProduct_le _ _).trans (mul_le_mul (hBw u) (hBw v) (norm_nonneg _)
    (norm_nonneg _))

end Entropy.ConditionalSkew

end
