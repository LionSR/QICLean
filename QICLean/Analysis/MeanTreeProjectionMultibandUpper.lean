/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MeanTreeProjectionUpper
import QICLean.Analysis.CfcLogListProduct

/-!
# One supplied projection sector across commuting mean-tree bands

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
