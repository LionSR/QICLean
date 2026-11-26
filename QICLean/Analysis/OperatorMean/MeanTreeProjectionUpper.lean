/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.FiniteTree
import QICLean.Analysis.Logarithm.InversePowerLogJensen
import QICLean.Analysis.FunctionalCalculus.MatrixPowers

/-!
# A terminal-weighted upper bound in a supplied projection sector

The projection and vector are supplied, rather than selected by this theorem.
If the projection commutes with every positive definite leaf, conditioning on
its nonzero component costs exactly the negative logarithm of its squared norm.
The remaining bound is the terminal-weighted average of the original leaf
logarithms. No normalization of the original vector, mutual commutation of the
leaves, or relaxation to a largest leaf is used.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 383–404,
`comparator:sharp-jensen`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is the single-band conditioning interface, not a construction of the
auxiliary sector or an assembly of the sharp comparator.

It also contains the following results.

* `Matrix.MeanTree.re_inner_log_eval_prod_le_of_projection`,
  `Matrix.MeanTree.mass_rpow_mul_exp_le_norm_rpow_neg_eval_prod_projection_sq`: one supplied
  projection sector across commuting mean-tree bands.
-/

section MeanTreeProjectionUpper

noncomputable section

open scoped BigOperators Matrix ComplexOrder MatrixOrder InnerProductSpace
  Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A commuting orthogonal projection can only decrease the quadratic form of
a positive semidefinite matrix. The projection and the vector remain fixed.
Source: `07-comparators.tex`, lines 391–404. -/
theorem PosSemidef.re_dotProduct_projection_mulVec_le
    {A P : Matrix n n ℂ} (hA : A.PosSemidef) (hP : IsStarProjection P)
    (hPA : Commute P A) (p : n → ℂ) :
    (star (P *ᵥ p) ⬝ᵥ (A *ᵥ (P *ᵥ p))).re ≤ (star p ⬝ᵥ (A *ᵥ p)).re := by
  classical
  have hPAP : P * A * P = P * A := by
    rw [hPA.eq, Matrix.mul_assoc, hP.isIdempotentElem.eq, ← hPA.eq]
  have hcomplement : (1 - P)ᴴ * A * (1 - P) = A - P * A * P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.isSelfAdjoint.isHermitian.eq]
    calc
      (1 - P) * A * (1 - P) = A - A * P - P * A + P * A * P := by
        noncomm_ring
      _ = A - P * A * P := by
        rw [hPAP, hPA.eq]
        abel
  have hpositive := hA.conjTranspose_mul_mul_same (1 - P)
  rw [hcomplement] at hpositive
  have hreal : 0 ≤ (star p ⬝ᵥ ((A - P * A * P) *ᵥ p)).re :=
    hpositive.re_dotProduct_nonneg p
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at hreal
  rw [hP.isSelfAdjoint.isHermitian.star_mulVec_dotProduct,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact sub_nonneg.mp hreal

private theorem re_inner_toEuclideanLin_eq_dotProduct (A : Matrix n n ℂ)
    (p : EuclideanSpace ℂ n) :
    (inner ℂ p (toEuclideanLin A p)).re =
      (star (WithLp.ofLp p) ⬝ᵥ (A *ᵥ WithLp.ofLp p)).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, dotProduct_comm]

private theorem re_inner_normalized (A : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    (inner ℂ ((‖v‖⁻¹ : ℂ) • v) (toEuclideanLin A ((‖v‖⁻¹ : ℂ) • v))).re =
      (‖v‖ ^ 2)⁻¹ * (inner ℂ v (toEuclideanLin A v)).re := by
  rw [map_smul, inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal,
    ← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.re_ofReal_mul,
    ← inv_pow, sq]

namespace MeanTree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The normalized component in the supplied commuting projection sector has
an upper logarithmic expectation with one exact conditioning cost. All
terminal weights, including repeated labels and zero weights, are retained.
Source: `07-comparators.tex`, lines 391–404, `comparator:sharp-jensen`. -/
theorem re_inner_log_eval_le_of_projection
    {A : ι → Matrix n n ℂ} (hA : ∀ j, (A j).PosDef)
    {P : Matrix n n ℂ} (hP : IsStarProjection P)
    (hcomm : ∀ j, Commute P (A j)) (T : MeanTree ι)
    (p : EuclideanSpace ℂ n) (hq : 0 < ‖toEuclideanLin P p‖ ^ 2) :
    let v := toEuclideanLin P p
    let q := ‖v‖ ^ 2
    let φ := (‖v‖⁻¹ : ℂ) • v
    (inner ℂ φ (toEuclideanLin (CFC.log (T.eval A)) φ)).re ≤
      -Real.log q + ∑ j, T.weight j * Real.log (inner ℂ p (toEuclideanLin (A j) p)).re := by
  intro v q φ
  let M := T.eval A
  let e : ι → ℝ := fun j ↦ (inner ℂ p (toEuclideanLin (A j) p)).re
  have hM : M.PosDef := T.posDef_eval hA
  have hn : ‖v‖ ≠ 0 := by
    intro h
    change 0 < ‖v‖ ^ 2 at hq
    simp only [h, zero_pow (by decide : 2 ≠ 0), lt_self_iff_false] at hq
  have hvne : v ≠ 0 := norm_ne_zero_iff.mp hn
  have hpne : WithLp.ofLp p ≠ 0 := by
    intro h
    apply hvne
    ext i
    change (P *ᵥ WithLp.ofLp p) i = 0
    rw [h, Matrix.mulVec_zero, Pi.zero_apply]
  have hφ : ‖φ‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) hvne
  have hφdot : star (WithLp.ofLp φ) ⬝ᵥ WithLp.ofLp φ = (1 : ℂ) := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) φ
    rw [hφ, RCLike.ofReal_one, one_pow,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
    exact h
  have hφne : WithLp.ofLp φ ≠ 0 := by
    intro h
    simp [h] at hφdot
  have he : ∀ j, 0 < e j := fun j ↦ by
    dsimp only [e]
    rw [re_inner_toEuclideanLin_eq_dotProduct]
    exact (hA j).re_dotProduct_pos hpne
  have hrootpos : 0 < (inner ℂ φ (toEuclideanLin M φ)).re := by
    rw [re_inner_toEuclideanLin_eq_dotProduct]
    exact hM.re_dotProduct_pos hφne
  have hprojection : (inner ℂ v (toEuclideanLin M v)).re ≤
      (inner ℂ p (toEuclideanLin M p)).re := by
    rw [re_inner_toEuclideanLin_eq_dotProduct, re_inner_toEuclideanLin_eq_dotProduct]
    exact hM.posSemidef.re_dotProduct_projection_mulVec_le hP
      (T.commute_eval_right hA hcomm) (WithLp.ofLp p)
  have htree : (inner ℂ p (toEuclideanLin M p)).re ≤ ∏ j, e j ^ T.weight j := by
    simpa only [e, re_inner_toEuclideanLin_eq_dotProduct] using
      T.re_dotProduct_eval_le hA (WithLp.ofLp p)
  have hnormalized : (inner ℂ φ (toEuclideanLin M φ)).re ≤
      q⁻¹ * ∏ j, e j ^ T.weight j := by
    rw [re_inner_normalized]
    exact mul_le_mul_of_nonneg_left (hprojection.trans htree) (inv_nonneg.mpr hq.le)
  have hprod : 0 < ∏ j, e j ^ T.weight j :=
    Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (he j) _
  have hlogprod : Real.log (∏ j, e j ^ T.weight j) =
      ∑ j, T.weight j * Real.log (e j) := by
    rw [Real.log_prod (fun j _ ↦ (Real.rpow_pos_of_pos (he j) _).ne')]
    exact Finset.sum_congr rfl fun j _ ↦ Real.log_rpow (he j) _
  have hJ := hM.posSemidef.re_dotProduct_cfc_log_mulVec_le_log hφdot
    (by rw [hM.supportProj_eq_one, Matrix.one_mulVec])
  calc
    _ ≤ Real.log (inner ℂ φ (toEuclideanLin M φ)).re := by
      simpa only [re_inner_toEuclideanLin_eq_dotProduct] using hJ
    _ ≤ Real.log (q⁻¹ * ∏ j, e j ^ T.weight j) :=
      Real.log_le_log hrootpos hnormalized
    _ = _ := by
      rw [Real.log_mul (inv_ne_zero hq.ne') hprod.ne', Real.log_inv, hlogprod]

/-- Undoing normalization retains the exact supplied-sector mass to the
power `1 + 2s` for every real `s ≥ 0`. This is a single-band estimate and
does not choose or lower-bound that mass.
Source: `07-comparators.tex`, lines 383–404. -/
theorem mass_rpow_mul_exp_le_norm_rpow_neg_eval_projection_sq
    {A : ι → Matrix n n ℂ} (hA : ∀ j, (A j).PosDef)
    {P : Matrix n n ℂ} (hP : IsStarProjection P)
    (hcomm : ∀ j, Commute P (A j)) (T : MeanTree ι)
    (p : EuclideanSpace ℂ n) (hq : 0 < ‖toEuclideanLin P p‖ ^ 2)
    {s : ℝ} (hs : 0 ≤ s) :
    let q := ‖toEuclideanLin P p‖ ^ 2
    q ^ (1 + 2 * s) *
        Real.exp (-2 * s * ∑ j, T.weight j *
          Real.log (inner ℂ p (toEuclideanLin (A j) p)).re) ≤
      ‖toEuclideanLin (T.eval A ^ (-s)) (toEuclideanLin P p)‖ ^ 2 := by
  intro q
  let L := ∑ j, T.weight j * Real.log (inner ℂ p (toEuclideanLin (A j) p)).re
  have hlog := re_inner_log_eval_le_of_projection hA hP hcomm T p hq
  have hnorm := (T.posDef_eval hA).norm_sq_mul_exp_le_norm_rpow_neg_sq_of_normalized_log_le
    (toEuclideanLin P p) hq hlog hs
  calc
    _ = Real.exp (Real.log q * (1 + 2 * s)) * Real.exp (-2 * s * L) := by
      rw [Real.rpow_def_of_pos hq]
    _ = Real.exp (Real.log q) * Real.exp (-2 * s * (-Real.log q + L)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ = q * Real.exp (-2 * s * (-Real.log q + L)) := by rw [Real.exp_log hq]
    _ ≤ _ := hnorm

end MeanTree

end Matrix

end

end MeanTreeProjectionUpper

section MeanTreeProjectionMultibandUpper

/-!
## One supplied projection sector across commuting mean-tree bands

The same projection and the same original vector are retained in every band.
Splitting the logarithm of the ordered product incurs one conditioning cost
per band and preserves every terminal weight. Undoing normalization gives
the exact mass power `1 + 2sG` for every nonnegative real exponent.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 383–404,
`comparator:sharp-jensen`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This analytic result does not choose or lower-bound the supplied sector mass.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder MatrixOrder InnerProductSpace
  Matrix.Norms.L2Operator

namespace Matrix.MeanTree

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

private theorem re_inner_matrix_eq_dotProduct (A : Matrix n n ℂ)
    (p : EuclideanSpace ℂ n) :
    (inner ℂ p (toEuclideanLin A p)).re =
      (star (WithLp.ofLp p) ⬝ᵥ (A *ᵥ WithLp.ofLp p)).re := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, dotProduct_comm]

/-- The logarithmic expectation of an ordered product of commuting band
roots costs exactly one negative log mass per band. The projection and
normalized projected vector are common to all bands.
Source: `07-comparators.tex`, lines 383–404. -/
theorem re_inner_log_eval_prod_le_of_projection
    {G : ℕ} (T : Fin G → MeanTree ι) {A : ι → Fin G → Matrix n n ℂ}
    (hA : ∀ j g, (A j g).PosDef)
    (hroots : ∀ g h, g ≠ h → Commute ((T g).eval (A · g)) ((T h).eval (A · h)))
    {P : Matrix n n ℂ} (hP : IsStarProjection P)
    (hPA : ∀ j g, Commute P (A j g))
    (p : EuclideanSpace ℂ n) (hq : 0 < ‖toEuclideanLin P p‖ ^ 2) :
    let M := (List.ofFn fun g ↦ (T g).eval (A · g)).prod
    let v := toEuclideanLin P p
    let q := ‖v‖ ^ 2
    let φ := (‖v‖⁻¹ : ℂ) • v
    (inner ℂ φ (toEuclideanLin (CFC.log M) φ)).re ≤
      -(G : ℝ) * Real.log q + ∑ g, ∑ j, (T g).weight j *
        Real.log (inner ℂ p (toEuclideanLin (A j g) p)).re := by
  intro M v q φ
  have hpos : ∀ g, ((T g).eval (A · g)).PosDef :=
    fun g ↦ (T g).posDef_eval (fun j ↦ hA j g)
  have hsplit : (inner ℂ φ (toEuclideanLin (CFC.log M) φ)).re =
      ∑ g, (inner ℂ φ (toEuclideanLin (CFC.log ((T g).eval (A · g))) φ)).re := by
    simp only [re_inner_matrix_eq_dotProduct]
    rw [cfc_log_listProd_ofFn hpos hroots, sum_mulVec, dotProduct_sum, Complex.re_sum]
  rw [hsplit]
  calc
    _ ≤ ∑ g, (-Real.log q + ∑ j, (T g).weight j *
        Real.log (inner ℂ p (toEuclideanLin (A j g) p)).re) := by
      exact Finset.sum_le_sum fun g _ ↦
        re_inner_log_eval_le_of_projection (fun j ↦ hA j g) hP
          (fun j ↦ hPA j g) (T g) p hq
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The same supplied sector mass is restored with exponent `1 + 2sG`
after conditioning on `G` bands. No normalization of the original vector
or upper bound on its sector mass is needed, including for zero bands.
Source: `07-comparators.tex`, lines 383–404. -/
theorem mass_rpow_mul_exp_le_norm_rpow_neg_eval_prod_projection_sq
    {G : ℕ} (T : Fin G → MeanTree ι) {A : ι → Fin G → Matrix n n ℂ}
    (hA : ∀ j g, (A j g).PosDef)
    (hroots : ∀ g h, g ≠ h → Commute ((T g).eval (A · g)) ((T h).eval (A · h)))
    {P : Matrix n n ℂ} (hP : IsStarProjection P)
    (hPA : ∀ j g, Commute P (A j g))
    (p : EuclideanSpace ℂ n) (hq : 0 < ‖toEuclideanLin P p‖ ^ 2)
    {s : ℝ} (hs : 0 ≤ s) :
    let M := (List.ofFn fun g ↦ (T g).eval (A · g)).prod
    let q := ‖toEuclideanLin P p‖ ^ 2
    q ^ (1 + 2 * s * G) * Real.exp (-2 * s * ∑ g, ∑ j,
        (T g).weight j * Real.log (inner ℂ p (toEuclideanLin (A j g) p)).re) ≤
      ‖toEuclideanLin (M ^ (-s)) (toEuclideanLin P p)‖ ^ 2 := by
  intro M q
  let L := ∑ g, ∑ j, (T g).weight j *
    Real.log (inner ℂ p (toEuclideanLin (A j g) p)).re
  have hM : M.PosDef := posDef_listProd_ofFn
    (fun g ↦ (T g).posDef_eval (fun j ↦ hA j g)) hroots
  have hlog := re_inner_log_eval_prod_le_of_projection T hA hroots hP hPA p hq
  have hnorm := hM.norm_sq_mul_exp_le_norm_rpow_neg_sq_of_normalized_log_le
    (toEuclideanLin P p) hq hlog hs
  calc
    _ = Real.exp (Real.log q * (1 + 2 * s * G)) * Real.exp (-2 * s * L) := by
      rw [Real.rpow_def_of_pos hq]
    _ = Real.exp (Real.log q) * Real.exp (-2 * s * (-(G : ℝ) * Real.log q + L)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ = q * Real.exp (-2 * s * (-(G : ℝ) * Real.log q + L)) := by
      rw [Real.exp_log hq]
    _ ≤ _ := hnorm

end Matrix.MeanTree

end

end MeanTreeProjectionMultibandUpper
