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

/-- The sandwich bound in the form `tr (Xᴴ X ρ) ≤ 1` for `X = ρ^{[z]} c ρ^{[-z]}`. -/
theorem re_trace_sandwich_mul_le {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (htr : A.trace.re ≤ 1) {c : Matrix n n ℂ} (hc1 : c * cᴴ ≤ 1)
    (hc2 : cᴴ * c ≤ 1) {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1 / 2) :
    ((cfcC A (suppPowFun z) * c * cfcC A (suppPowFun (-z)))ᴴ *
      (cfcC A (suppPowFun z) * c * cfcC A (suppPowFun (-z))) * A).trace.re ≤ 1 := by
  set X := cfcC A (suppPowFun z) * c * cfcC A (suppPowFun (-z))
  set R := cfcC A (suppPowFun (1 / 2))
  have hhalf : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := Complex.ext (by simp) (by simp)
  have hR : Rᴴ = R := by rw [conjTranspose_suppPow hA, hhalf]
  have hcfc : ∀ w : ℂ, supportCPow hA.1 w = cfcC A (suppPowFun w) := fun w =>
    (supportCPow_eq_cfcC hA.1 w).trans rfl
  have hRR : R * R = A := by
    rw [suppPow_mul hA.1]
    calc cfcC A (suppPowFun (1 / 2 + 1 / 2)) = cfcC A (fun t => (t : ℂ)) := by
          refine cfcC_congr_of_nonneg hA fun t ht => ?_
          unfold suppPowFun
          split_ifs with h
          · simp [h]
          · norm_num
      _ = A := cfcC_id hA.1
  have hXR : X * R = supportCPow hA.1 z * c * supportCPow hA.1 (1 / 2 - z) := by
    rw [hcfc, hcfc]
    simp only [X, R, Matrix.mul_assoc, suppPow_mul hA.1]
    congr 3; ring
  have h := re_trace_supportCPow_sandwich_le hA htr hc1 hc2 hz0 hz1
  rw [← hXR, conjTranspose_mul, hR] at h
  calc (Xᴴ * X * A).trace.re = (R * Xᴴ * (X * R)).trace.re := by
        rw [← hRR, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
          Matrix.mul_assoc (R * Xᴴ)]
    _ ≤ 1 := h

end Contraction

section Terms

variable (θ : (P₀ × P₁) × ((X × U) × F) → ℂ)

theorem trace_margP : (margP θ).trace = star θ ⬝ᵥ θ := by
  rw [margP, trace_partialTraceRight, trace_vecMulVec, dotProduct_comm]

theorem trace_margY : (margY θ).trace = star θ ⬝ᵥ θ := by
  rw [margY, margW, trace_partialTraceRight, trace_partialTraceLeft, trace_vecMulVec,
    dotProduct_comm]

theorem normSq_liftP_mulVec (A : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) :
    star (liftP (X := X) (U := U) (F := F) A *ᵥ θ) ⬝ᵥ (liftP A *ᵥ θ) =
      (Aᴴ * A * margP θ).trace := by
  rw [star_mulVec_dotProduct, mulVec_mulVec, conjTranspose_liftP, liftP_mul,
    dotProduct_mulVec_eq_trace', trace_mul_comm, liftP, ← trace_partialTraceRight_mul,
    trace_mul_comm]
  rfl

theorem normSq_liftY_mulVec (B : Matrix (X × U) (X × U) ℂ) :
    star (liftY (P₀ := P₀) (P₁ := P₁) (F := F) B *ᵥ θ) ⬝ᵥ (liftY B *ᵥ θ) =
      (Bᴴ * B * margY θ).trace := by
  rw [star_mulVec_dotProduct, mulVec_mulVec, conjTranspose_liftY, liftY_mul,
    dotProduct_mulVec_eq_trace', trace_mul_comm, liftY, ← trace_partialTraceLeft_mul,
    ← trace_partialTraceRight_mul, trace_mul_comm]
  rfl

theorem lift_mul_rearrange (a₁ c a₂ : Matrix (P₀ × P₁) (P₀ × P₁) ℂ)
    (b₁ d b₂ : Matrix (X × U) (X × U) ℂ) :
    liftP (F := F) a₁ * liftY b₁ * (liftP c * liftY d) * liftP a₂ * liftY b₂ =
      liftP (a₁ * c * a₂) * liftY (b₁ * d * b₂) := by
  have e1 := (liftP_liftY_comm (F := F) c b₁).symm
  have e2 := liftP_liftY_comm (F := F) a₂ d
  have e3 := (liftP_liftY_comm (F := F) a₂ b₁).symm
  rw [← liftP_mul, ← liftP_mul, ← liftY_mul, ← liftY_mul]
  calc liftP a₁ * liftY b₁ * (liftP c * liftY d) * liftP a₂ * liftY b₂
      = liftP a₁ * ((liftY b₁ * liftP c) * ((liftY d * liftP a₂) * liftY b₂)) := by
        simp only [Matrix.mul_assoc]
    _ = liftP a₁ * ((liftP c * liftY b₁) * ((liftP a₂ * liftY d) * liftY b₂)) := by
        rw [e1, ← e2]
    _ = liftP a₁ * (liftP c * ((liftY b₁ * liftP a₂) * (liftY d * liftY b₂))) := by
        simp only [Matrix.mul_assoc]
    _ = liftP a₁ * (liftP c * ((liftP a₂ * liftY b₁) * (liftY d * liftY b₂))) := by rw [e3]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem norm_toLp_le_one_of_re_le {n : Type*} [Fintype n] {v : n → ℂ}
    (h : (star v ⬝ᵥ v).re ≤ 1) : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ ≤ 1 := by
  have h2 := norm_toLp_sq_eq_re' v
  have := norm_nonneg (WithLp.toLp 2 v : EuclideanSpace ℂ n)
  nlinarith

/-- One term of the matrix-unit expansion has modulus at most one. -/
theorem norm_skew_term_le (hθ : star θ ⬝ᵥ θ = 1) {c : Matrix (P₀ × P₁) (P₀ × P₁) ℂ}
    (hc₁ : c * cᴴ ≤ 1) (hc₂ : cᴴ * c ≤ 1) {d : Matrix (X × U) (X × U) ℂ} (hd₁ : d * dᴴ ≤ 1)
    (hd₂ : dᴴ * d ≤ 1) {z : ℂ} (hz₀ : 0 ≤ z.re) (hz₁ : z.re ≤ 1 / 2) :
    ‖star θ ⬝ᵥ ((liftP (cfcC (margP θ) (suppPowFun z) * c * cfcC (margP θ) (suppPowFun (-z))) *
      liftY (cfcC (margY θ) (suppPowFun (-z)) * d * cfcC (margY θ) (suppPowFun z))) *ᵥ θ)‖ ≤ 1 := by
  have hP := posSemidef_margP θ
  have hY := posSemidef_margY θ
  have htrP : (margP θ).trace.re ≤ 1 := by rw [trace_margP, hθ, Complex.one_re]
  have htrY : (margY θ).trace.re ≤ 1 := by rw [trace_margY, hθ, Complex.one_re]
  rw [liftP_liftY_comm, ← mulVec_mulVec, star_dotProduct_mulVec_eq, conjTranspose_liftY]
  refine (norm_star_dotProduct_le _ _).trans ?_
  rw [← one_mul (1 : ℝ)]
  refine mul_le_mul (norm_toLp_le_one_of_re_le ?_) (norm_toLp_le_one_of_re_le ?_) (norm_nonneg _)
    zero_le_one
  · have hB : (cfcC (margY θ) (suppPowFun (-z)) * d * cfcC (margY θ) (suppPowFun z))ᴴ =
        cfcC (margY θ) (suppPowFun (starRingEnd ℂ z)) * dᴴ *
          cfcC (margY θ) (suppPowFun (-(starRingEnd ℂ z))) := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_suppPow hY,
        conjTranspose_suppPow hY, map_neg, Matrix.mul_assoc]
    rw [normSq_liftY_mulVec, hB]
    have hd₁' : dᴴ * dᴴᴴ ≤ 1 := by rwa [conjTranspose_conjTranspose]
    have hd₂' : dᴴᴴ * dᴴ ≤ 1 := by rwa [conjTranspose_conjTranspose]
    have := re_trace_sandwich_mul_le hY htrY hd₁' hd₂' (z := starRingEnd ℂ z)
      (by simpa using hz₀) (by simpa using hz₁)
    simpa [Matrix.mul_assoc] using this
  · rw [normSq_liftP_mulVec]
    exact re_trace_sandwich_mul_le hP htrP hc₁ hc₂ hz₀ hz₁

end Terms

end Entropy.ConditionalSkew

end
