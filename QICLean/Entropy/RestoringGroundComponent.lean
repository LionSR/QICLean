/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RestoringVectors
import QICLean.Entropy.RestoringNorm
import QICLean.Entropy.RestoringMarginal
import QICLean.Analysis.RestoringCoefficientBound

/-!
# The physical ground component of the restoring operator

The physical ground projection is the rank-one matrix of the actual physical
vector, lifted through the ancillary identities. The reduced density is its
partial trace over the remote system. No coefficients of the projected vector
or order bounds on its reduced matrix are supplied as hypotheses.

## References

* Two-dimensional area-law manuscript (September 24, 2026),
  `09-amplification.tex`, lines 417–446,
  `eq:amplification-ground-component`, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently written from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix Finset
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Entropy

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [Fintype Z]

/-- The actual reduced physical density on `X ⊗ Y`.
Source: `09-amplification.tex`, lines 417–424. -/
noncomputable def restoringReducedDensity (Ω : EuclideanSpace ℂ ((X × Y) × Z)) :
    Matrix (X × Y) (X × Y) ℂ :=
  partialTraceRight (vecMulVec Ω.ofLp (star Ω.ofLp))

/-- The physical outer-product matrix, extended by the identities on both ancillas.
For unit `Ω`, this is the orthogonal projection onto the physical ground vector.
Source: `09-amplification.tex`, lines 417–446. -/
noncomputable def restoringGroundOuterProduct (Ω : EuclideanSpace ℂ ((X × Y) × Z)) :
    Matrix (((X × X) × (X × Y)) × Z) (((X × X) × (X × Y)) × Z) ℂ :=
  restoringPhysicalLift (vecMulVec Ω.ofLp (star Ω.ofLp))

/-- The physical ground component of the actual restored copied vector.
Source: `eq:amplification-ground-component`, lines 438–446. -/
noncomputable def restoringGroundComponent [DecidableEq Z]
    (E : Finset X) (p : X → ℝ) (sBlank xBlank : X → ℂ)
    (Q : Matrix (X × Y) (X × Y) ℂ) (T : Matrix Y Y ℂ)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) :
    EuclideanSpace ℂ (((X × X) × (X × Y)) × Z) :=
  WithLp.toLp 2 (restoringGroundOuterProduct Ω *ᵥ
    (restoringGlobal E p sBlank xBlank Q T *ᵥ (restoringCopy sBlank xBlank Ω).ofLp))

/-- Applying the actual restoring operator to the copied vector contracts its
two unit blanks. No projection or spectral assumptions are needed here.
Source: `09-amplification.tex`, lines 334–358 and 438–441. -/
theorem restoringGlobal_copy_apply [DecidableEq Z]
    (E : Finset X) (p : X → ℝ) (sBlank xBlank : X → ℂ)
    (hs : ‖WithLp.toLp 2 sBlank‖ = 1) (hx : ‖WithLp.toLp 2 xBlank‖ = 1)
    (Q : Matrix (X × Y) (X × Y) ℂ) (T : Matrix Y Y ℂ)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) (s e : X) (a : X × Y) (z : Z) :
    (restoringGlobal E p sBlank xBlank Q T *ᵥ (restoringCopy sBlank xBlank Ω).ofLp)
        (((s, e), a), z) =
      (if s ∈ E then restoringWeight (p s) else 0) *
        ∑ j : Y, ∑ k : Y, Q a (s, k) * T k j * Ω ((e, j), z) := by
  have hs' := restoringBlank_sum_eq_one sBlank hs
  have hx' := restoringBlank_sum_eq_one xBlank hx
  simp only [restoringGlobal, mulVec, dotProduct, kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, restoringOperatorWithAncilla_apply,
    restoringCopy, WithLp.ofLp_toLp]
  simp only [mul_ite, ite_mul, zero_mul, mul_zero, mul_one,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  by_cases hse : s ∈ E
  · simp only [hse, ite_true]
    calc
      _ = (∑ s', star (sBlank s') * sBlank s') *
          ((∑ x', star (xBlank x') * xBlank x') *
          (restoringWeight (p s) *
            ∑ j : Y, ∑ k : Y, Q a (s, k) * T k j * Ω ((e, j), z))) := by
        conv_rhs => rw [Finset.sum_mul]
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro s' _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x' _
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [hs', hx']; simp
  · simp [hse]

omit [DecidableEq X] [Fintype X] [Fintype Y] in
/-- The reduced density of the physical vector is positive.
Source: `09-amplification.tex`, lines 417–424. -/
theorem restoringReducedDensity_posSemidef [Finite X] [Finite Y]
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) :
    (restoringReducedDensity Ω).PosSemidef :=
  (posSemidef_vecMulVec_self_star Ω.ofLp).partialTraceRight

omit [DecidableEq X] in
/-- The reduced density of a unit physical vector has trace one.
Source: `eq:amplification-ground-component`, lines 443–446. -/
theorem restoringReducedDensity_trace (Ω : EuclideanSpace ℂ ((X × Y) × Z))
    (hΩ : ‖Ω‖ = 1) : (restoringReducedDensity Ω).trace = 1 := by
  rw [restoringReducedDensity, trace_partialTraceRight, trace_vecMulVec,
    ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, hΩ]
  simp

/-- For a unit physical vector, the lifted ground matrix is an orthogonal projection.
Source: `09-amplification.tex`, lines 417–446. -/
theorem restoringGroundOuterProduct_isStarProjection
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) (hΩ : ‖Ω‖ = 1) :
    IsStarProjection (restoringGroundOuterProduct Ω) := by
  classical
  have hP : IsStarProjection (vecMulVec Ω.ofLp (star Ω.ofLp)) :=
    blankOuterProduct_isStarProjection Ω.ofLp (by simpa using hΩ)
  constructor
  · change ((1 ⊗ₖ vecMulVec Ω.ofLp (star Ω.ofLp)).submatrix
        restoringPhysicalGrouping restoringPhysicalGrouping) *
      ((1 ⊗ₖ vecMulVec Ω.ofLp (star Ω.ofLp)).submatrix
        restoringPhysicalGrouping restoringPhysicalGrouping) = _
    rw [submatrix_mul_equiv, ← mul_kronecker_mul, one_mul, hP.isIdempotentElem.eq]
    rfl
  · change (restoringGroundOuterProduct Ω)ᴴ = restoringGroundOuterProduct Ω
    have hpstar : (vecMulVec Ω.ofLp (star Ω.ofLp))ᴴ =
        vecMulVec Ω.ofLp (star Ω.ofLp) := hP.isSelfAdjoint
    simp only [restoringGroundOuterProduct, restoringPhysicalLift, conjTranspose_submatrix,
      conjTranspose_kronecker, conjTranspose_one, hpstar]

/-- The physical rank-one projection contracts the physical coordinates alone.
Source: `09-amplification.tex`, lines 438–441. -/
theorem restoringGroundOuterProduct_mulVec_apply
    (Ω : EuclideanSpace ℂ ((X × Y) × Z))
    (v : (((X × X) × (X × Y)) × Z) → ℂ) (s e : X) (a : X × Y) (z : Z) :
    (restoringGroundOuterProduct Ω *ᵥ v) (((s, e), a), z) =
      Ω (a, z) * ∑ b : X × Y, ∑ w : Z, star (Ω (b, w)) * v (((s, e), b), w) := by
  classical
  simp only [restoringGroundOuterProduct, restoringPhysicalLift, Matrix.submatrix_apply,
    restoringPhysicalGrouping, Equiv.prodAssoc, Equiv.coe_fn_mk, kroneckerMap_apply,
    mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, vecMulVec_apply,
    Pi.star_apply, Prod.mk.injEq, ite_and]
  simp only [ite_mul, zero_mul, one_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.mul_sum, mul_assoc]

private theorem partialTraceRight_one_kronecker_mul_apply
    (A : Matrix (X × Y) (X × Y) ℂ) (T : Matrix Y Y ℂ) (e s : X) :
    partialTraceRight (((1 : Matrix X X ℂ) ⊗ₖ T) * A) e s =
      ∑ k : Y, ∑ j : Y, T k j * A (e, j) (s, k) := by
  simp only [partialTraceRight_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- The actual reduced matrix has the ground-overlap coefficients, with every
coordinate of the copied ancillary system included.
Source: `09-amplification.tex`, lines 419–421 and 438–441. -/
theorem restoringMarginal_reducedDensity_apply
    (Ω : EuclideanSpace ℂ ((X × Y) × Z))
    (Q : Matrix (X × Y) (X × Y) ℂ) (T : Matrix Y Y ℂ) (e s : X) :
    restoringMarginal (restoringReducedDensity Ω) Q T e s =
      ∑ a : X × Y, ∑ z : Z, ∑ j : Y, ∑ k : Y,
        star (Ω (a, z)) * Q a (s, k) * T k j * Ω ((e, j), z) := by
  classical
  rw [restoringMarginal, Matrix.mul_assoc, partialTraceRight_one_kronecker_mul_apply]
  simp only [Matrix.mul_apply,
    restoringReducedDensity, partialTraceRight_apply, vecMulVec_apply,
    Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, j]
    rw [Finset.sum_comm]
    enter [2, a]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The ancillary ground coefficient is the actual reduced-matrix entry divided
by the selected square root. The second ancillary coordinate is unrestricted.
Source: `09-amplification.tex`, lines 438–441. -/
theorem restoringGroundComponent_apply [DecidableEq Z]
    (E : Finset X) (p : X → ℝ) (sBlank xBlank : X → ℂ)
    (hs : ‖WithLp.toLp 2 sBlank‖ = 1) (hx : ‖WithLp.toLp 2 xBlank‖ = 1)
    (Q : Matrix (X × Y) (X × Y) ℂ) (T : Matrix Y Y ℂ)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) (s e : X) (a : X × Y) (z : Z) :
    restoringGroundComponent E p sBlank xBlank Q T Ω (((s, e), a), z) =
      (if s ∈ E then restoringWeight (p s) else 0) *
        restoringMarginal (restoringReducedDensity Ω) Q T e s * Ω (a, z) := by
  change (restoringGroundOuterProduct Ω *ᵥ
    (restoringGlobal E p sBlank xBlank Q T *ᵥ (restoringCopy sBlank xBlank Ω).ofLp))
      (((s, e), a), z) = _
  rw [restoringGroundOuterProduct_mulVec_apply]
  simp_rw [restoringGlobal_copy_apply E p sBlank xBlank hs hx,
    restoringMarginal_reducedDensity_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The squared norm of the actual physical ground projection is exactly the
selected weighted coefficient sum, with the row index running over all of `X`.
Source: `eq:amplification-ground-component`, lines 443–446. -/
theorem restoringGroundComponent_norm_sq [DecidableEq Z]
    (E : Finset X) (p : X → ℝ) (hp : ∀ x ∈ E, 0 < p x)
    (sBlank xBlank : X → ℂ)
    (hs : ‖WithLp.toLp 2 sBlank‖ = 1) (hx : ‖WithLp.toLp 2 xBlank‖ = 1)
    (Q : Matrix (X × Y) (X × Y) ℂ) (T : Matrix Y Y ℂ)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) (hΩ : ‖Ω‖ = 1) :
    ‖restoringGroundComponent E p sBlank xBlank Q T Ω‖ ^ 2 =
      ∑ x ∈ E, ∑ y : X, ‖restoringMarginal (restoringReducedDensity Ω) Q T y x‖ ^ 2 /
        p x := by
  have hΩsum : (∑ x : X, ∑ y : Y, ∑ z : Z, ‖Ω ((x, y), z)‖ ^ 2) = 1 := by
    simpa only [Fintype.sum_prod_type, hΩ, one_pow] using
      (EuclideanSpace.norm_sq_eq Ω).symm
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type]
  simp_rw [restoringGroundComponent_apply E p sBlank xBlank hs hx, norm_mul, mul_pow]
  simp_rw [← Finset.mul_sum]
  simp only [hΩsum, mul_one]
  calc
    _ = ∑ x : X, if x ∈ E then
        ∑ y : X, ‖restoringMarginal (restoringReducedDensity Ω) Q T y x‖ ^ 2 / p x
        else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxE : x ∈ E
      · simp only [hxE, ite_true]
        have hw : ‖restoringWeight (p x)‖ ^ 2 = (p x)⁻¹ := by
          simp [restoringWeight, abs_of_nonneg (Real.sqrt_nonneg (p x)), inv_pow,
            Real.sq_sqrt (le_of_lt (hp x hxE))]
        rw [hw]
        apply Finset.sum_congr rfl
        intro y _
        rw [div_eq_mul_inv, mul_comm]
      · simp [hxE]
    _ = _ := by simp

/-- The same ground component is obtained from the actual column operator acting
on the initial physical vector and ancillary blanks.
Source: `eq:amplification-column-identity` and `eq:amplification-ground-component`. -/
theorem restoringGroundComponent_column_eq [DecidableEq Z]
    (E : Finset X) (p : X → ℝ) (sBlank xBlank eBlank : X → ℂ)
    (hx : ‖WithLp.toLp 2 xBlank‖ = 1) (he : ‖WithLp.toLp 2 eBlank‖ = 1)
    (Q : Matrix (X × Y) (X × Y) ℂ) (T : Matrix Y Y ℂ)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) :
    restoringGroundComponent E p sBlank xBlank Q T Ω =
      WithLp.toLp 2 (restoringGroundOuterProduct Ω *ᵥ
        (restoringColumnGlobal E p sBlank eBlank Q T *ᵥ
          (restoringInitial sBlank eBlank Ω).ofLp)) := by
  rw [restoringGroundComponent, restoringGlobal_mulVec_copy E p sBlank xBlank eBlank hx he]

/-- The actual ground component obeys the singular support-inverse trace chain.
Only the reduced density and `Q` commute; no commutation with `T` and no
full-rank assumption are used. The density, reduced matrix, and ground
projection are all those constructed from the physical vector.
Source: `eq:amplification-ground-component`, lines 417–446. -/
theorem restoringGroundComponent_trace_chain [DecidableEq Z]
    (E : Finset X) (p : X → ℝ) (hp : ∀ x ∈ E, 0 < p x)
    (sBlank xBlank : X → ℂ)
    (hs : ‖WithLp.toLp 2 sBlank‖ = 1) (hx : ‖WithLp.toLp 2 xBlank‖ = 1)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) (hΩ : ‖Ω‖ = 1)
    {Q : Matrix (X × Y) (X × Y) ℂ} (hQ : IsStarProjection Q)
    (hρQ : Commute (restoringReducedDensity Ω) Q)
    {T : Matrix Y Y ℂ} (hT : IsStarProjection T)
    (hdiag : partialTraceRight (restoringReducedDensity Ω) =
      diagonal (fun x ↦ (p x : ℂ))) :
    let M := restoringMarginal (restoringReducedDensity Ω) Q T
    let hρX := (restoringReducedDensity_posSemidef Ω).partialTraceRight
    ‖restoringGroundComponent E p sBlank xBlank Q T Ω‖ ^ 2 ≤
        (M * hρX.supportInv * M).trace.re ∧
      (M * hρX.supportInv * M).trace.re ≤ M.trace.re ∧ M.trace.re ≤ 1 := by
  dsimp only
  have hρ := restoringReducedDensity_posSemidef Ω
  have hM := (restoringMarginal_nonneg hρ hQ hρQ hT).posSemidef
  have hMρ := restoringMarginal_le hρ hQ hρQ hT
  have hchain := hM.selected_sum_sq_div_le_trace hρ.partialTraceRight hdiag hMρ E
  refine ⟨?_, hchain.2, ?_⟩
  · rw [restoringGroundComponent_norm_sq E p hp sBlank xBlank hs hx Q T Ω hΩ]
    exact hchain.1
  · have htr := (Complex.nonneg_iff.mp (Matrix.le_iff.mp hMρ).trace_nonneg).1
    rw [trace_sub, trace_partialTraceRight, restoringReducedDensity_trace Ω hΩ,
      Complex.sub_re, Complex.one_re] at htr
    exact sub_nonneg.mp htr

/-- The physical ground component of the actual restoring operator has norm at
most one, including for singular physical marginals.
Source: `eq:amplification-ground-component`, lines 417–446. -/
theorem restoringGroundComponent_norm_le_one [DecidableEq Z]
    (E : Finset X) (p : X → ℝ) (hp : ∀ x ∈ E, 0 < p x)
    (sBlank xBlank : X → ℂ)
    (hs : ‖WithLp.toLp 2 sBlank‖ = 1) (hx : ‖WithLp.toLp 2 xBlank‖ = 1)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) (hΩ : ‖Ω‖ = 1)
    {Q : Matrix (X × Y) (X × Y) ℂ} (hQ : IsStarProjection Q)
    (hρQ : Commute (restoringReducedDensity Ω) Q)
    {T : Matrix Y Y ℂ} (hT : IsStarProjection T)
    (hdiag : partialTraceRight (restoringReducedDensity Ω) =
      diagonal (fun x ↦ (p x : ℂ))) :
    ‖restoringGroundComponent E p sBlank xBlank Q T Ω‖ ≤ 1 := by
  have h := restoringGroundComponent_trace_chain E p hp sBlank xBlank hs hx Ω hΩ
    hQ hρQ hT hdiag
  have hsq := h.1.trans (h.2.1.trans h.2.2)
  nlinarith [norm_nonneg (restoringGroundComponent E p sBlank xBlank Q T Ω)]

end Entropy
