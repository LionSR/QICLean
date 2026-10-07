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

theorem norm_apply_le_one_of_nonneg_le_one {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (h0 : 0 ≤ H) (h1 : H ≤ 1) (i j : n) : ‖H i j‖ ≤ 1 := by
  have h := norm_dotProduct_mulVec_le_of_nonneg_le_one h0 h1 (Pi.single i 1) (Pi.single j 1)
  have hn : ∀ k : n, ‖(WithLp.toLp 2 (Pi.single k (1 : ℂ)) : EuclideanSpace ℂ n)‖ = 1 := by
    intro k
    have h2 := norm_toLp_sq_eq_re' (Pi.single k (1 : ℂ))
    have h3 : star (Pi.single k (1 : ℂ)) ⬝ᵥ Pi.single k 1 = 1 := by
      simp [dotProduct, Pi.single_apply]
    rw [h3, Complex.one_re] at h2
    have := norm_nonneg (WithLp.toLp 2 (Pi.single k (1 : ℂ)) : EuclideanSpace ℂ n)
    nlinarith [sq_nonneg (‖(WithLp.toLp 2 (Pi.single k (1 : ℂ)) : EuclideanSpace ℂ n)‖ - 1)]
  have he : star (Pi.single i (1 : ℂ)) ⬝ᵥ (H *ᵥ Pi.single j 1) = H i j := by
    simp [mulVec_single, dotProduct, Pi.single_apply]
  rw [he, hn, hn, one_mul] at h
  exact h

/-- The matrix unit `|a⟩⟨b| ⊗ I_{P₁}` on `P`. -/
def unitP (a b : P₀) : Matrix (P₀ × P₁) (P₀ × P₁) ℂ := single a b 1 ⊗ₖ (1 : Matrix P₁ P₁ ℂ)

/-- The matrix unit `|x⟩⟨x'| ⊗ I_U` on `Y`. -/
def unitY (x x' : X) : Matrix (X × U) (X × U) ℂ := single x x' 1 ⊗ₖ (1 : Matrix U U ℂ)

/-- Expansion of `h ⊗ I` in matrix units of `P₀ x`. -/
theorem liftH_eq_sum (h : Matrix (P₀ × X) (P₀ × X) ℂ) :
    liftH (P₁ := P₁) (U := U) (F := F) h =
      ∑ i, ∑ j, h i j • (liftP (unitP (P₁ := P₁) i.1 j.1) * liftY (unitY (U := U) i.2 j.2)) := by
  ext q q'
  obtain ⟨⟨p₀, p₁⟩, ⟨⟨x, u⟩, f⟩⟩ := q
  obtain ⟨⟨p₀', p₁'⟩, ⟨⟨x', u'⟩, f'⟩⟩ := q'
  simp only [liftH, liftP, liftY, unitP, unitY, ← mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, submatrix_apply, regroup, kroneckerMap_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, single_apply, one_apply, Fintype.sum_prod_type]
  simp only [ite_and, mul_ite, ite_mul, one_mul, mul_one, zero_mul, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Prod.mk.injEq]
  by_cases h1 : p₁ = p₁' <;> by_cases h2 : u = u' <;> by_cases h3 : f = f' <;> simp [h1, h2, h3]

section Contraction

theorem single_mul_conjTranspose_le_one {n : Type*} [Fintype n] [DecidableEq n] (a b : n) :
    single a b (1 : ℂ) * (single a b 1)ᴴ ≤ 1 := by
  rw [conjTranspose_single, star_one, single_mul_single_same, mul_one, le_iff]
  have : (1 : Matrix n n ℂ) - single a a 1 = diagonal (fun k => if k = a then 0 else 1) := by
    ext i j; by_cases hij : i = j <;> by_cases hi : i = a <;> simp [hij, hi, single_apply, one_apply]
      <;> aesop
  rw [this]
  exact PosSemidef.diagonal fun k => by dsimp; split_ifs <;> norm_num

theorem kronecker_one_le_one {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] {A : Matrix n n ℂ} (hA : A ≤ 1) : A ⊗ₖ (1 : Matrix m m ℂ) ≤ 1 := by
  have h : (1 : Matrix (n × m) (n × m) ℂ) - A ⊗ₖ (1 : Matrix m m ℂ) =
      (1 - A) ⊗ₖ (1 : Matrix m m ℂ) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [one_apply, h1, h2, sub_mul]
  rw [le_iff, h]
  exact (le_iff.1 hA).kronecker PosSemidef.one

end Contraction

end Entropy.ConditionalSkew

end
