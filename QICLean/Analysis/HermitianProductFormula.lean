/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProductFormula
import QICLean.Analysis.SpectralFilter.MatrixFilter

/-!
# Product formulas for Hermitian matrices

For Hermitian matrices `H_k` listed in an order `order`, the first-order product formula
`lieEvolution H order t n = (∏_{k ∈ order} e^{-i (t/n) H_k})^n` (the head of `order` applied
first) and its second-order analogue `strangEvolution H order t n` approximate the evolution
`e^{-itH} = Matrix.hermitianUnitaryPath H (-t)` of the sum `H = ∑_{k ∈ order} H_k`. They are the
product formulas of `ProductFormula` for the elements `i H_k` at `z = -t`. The exponentials are
unitary, so the errors hold with `M = 1`:

* `‖lieEvolution H order t n - e^{-itH}‖ ≤ t²/(2n) ∑_{i<j} ‖[H_i, H_j]‖`;
* `‖strangEvolution H order t n - e^{-itH}‖ ≤ |t|³/(2n²) ∑_{i<j} ‖[H_i, H_j]‖ ∑_k ‖H_k‖`,

and conjugating an operator `A` at most doubles the error, times `‖A‖`.

## Main definitions

* `ProductFormula.lieEvolution`, `ProductFormula.strangEvolution`.

## Main results

* `ProductFormula.lieEvolution_eq` — the first-order formula as a product of unitary paths.
* `ProductFormula.lieEvolution_mem_unitary`, `ProductFormula.strangEvolution_mem_unitary`.
* `ProductFormula.norm_lieEvolution_sub_le`, `ProductFormula.norm_strangEvolution_sub_le`.
* `ProductFormula.norm_lieEvolution_conj_sub_le`, `ProductFormula.norm_strangEvolution_conj_sub_le`.
-/

open Matrix SpectralFilter
open scoped Matrix.Norms.L2Operator

namespace ProductFormula

variable {n κ : Type*} [Fintype n] [DecidableEq n] (H : κ → Matrix n n ℂ)

/-- The first-order product formula `(∏_{k ∈ order} e^{-i (t/n) H_k})^n` for the evolution under
`∑_{k ∈ order} H_k` at time `t`, the head of `order` applied first. -/
noncomputable def lieEvolution (order : List κ) (t : ℝ) (m : ℕ) : Matrix n n ℂ :=
  lie (fun k ↦ Complex.I • H k) order ((-t : ℝ) : ℂ) m

/-- The second-order product formula: `m` symmetric steps, each forward through `order` for the
time `t/(2m)` and back. -/
noncomputable def strangEvolution (order : List κ) (t : ℝ) (m : ℕ) : Matrix n n ℂ :=
  strang (fun k ↦ Complex.I • H k) order ((-t : ℝ) : ℂ) m

private theorem cast_neg_div (t : ℝ) (m : ℕ) : ((-t : ℝ) : ℂ) / m = ((-t / m : ℝ) : ℂ) := by
  push_cast
  ring

/-- The first-order formula is a power of an ordered product of unitary paths. -/
theorem lieEvolution_eq (order : List κ) (t : ℝ) (m : ℕ) :
    lieEvolution H order t m =
      (order.map fun k ↦ hermitianUnitaryPath (H k) (-t / m)).reverse.prod ^ m := by
  simp only [lieEvolution, lie, step, cast_neg_div]
  rfl

variable {H}

theorem isHermitian_gen (hH : ∀ k, (H k).IsHermitian) : ∀ l : List κ, (gen H l).IsHermitian
  | [] => isHermitian_zero
  | a :: l => by
    rw [gen_cons]
    exact (hH a).add (isHermitian_gen hH l)

/-- For Hermitian `H_k` and real `r`, one step `∏_{k ∈ l} e^{i r H_k}` is unitary. -/
theorem step_smul_I_mem_unitary (hH : ∀ k, (H k).IsHermitian) (l : List κ) (r : ℝ) :
    step (fun k ↦ Complex.I • H k) l (r : ℂ) ∈ unitary (Matrix n n ℂ) := by
  induction l with
  | nil => exact one_mem _
  | cons a l ih =>
    rw [step_cons]
    exact mul_mem ih (hermitianUnitaryPath_mem_unitary (hH a) r)

theorem lieEvolution_mem_unitary (hH : ∀ k, (H k).IsHermitian) (order : List κ) (t : ℝ)
    (m : ℕ) : lieEvolution H order t m ∈ unitary (Matrix n n ℂ) := by
  rw [lieEvolution, lie, cast_neg_div]
  exact pow_mem (step_smul_I_mem_unitary hH order _) m

theorem strangEvolution_mem_unitary (hH : ∀ k, (H k).IsHermitian) (order : List κ) (t : ℝ)
    (m : ℕ) : strangEvolution H order t m ∈ unitary (Matrix n n ℂ) := by
  have hz : ((-t : ℝ) : ℂ) / m / 2 = ((-t / m / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [strangEvolution, strang, symmStep, hz]
  exact pow_mem (mul_mem (step_smul_I_mem_unitary hH _ _) (step_smul_I_mem_unitary hH _ _)) m

/-- For Hermitian `H_k` and real `r` the exponentials of the partial sums are unitary, so the
bound hypothesis of the product formulas holds with `M = 1`. -/
theorem expBound_smul_I_one (hH : ∀ k, (H k).IsHermitian) (order : List κ) (r : ℝ) :
    ExpBound (fun k ↦ Complex.I • H k) order (r : ℂ) 1 := by
  intro l _ s _
  have e : s • ((r : ℂ) • (Complex.I • gen H l)) = ((s * r : ℝ) : ℂ) • (Complex.I • gen H l) := by
    rw [← Complex.coe_smul s, smul_smul, Complex.ofReal_mul]
  rw [gen_smul, e]
  exact CStarRing.norm_le_one_of_mem_unitary
    (hermitianUnitaryPath_mem_unitary (isHermitian_gen hH l) _)

/-- **First-order error.** `‖lieEvolution H order t m - e^{-itH}‖ ≤ t²/(2m) ∑_{i<j} ‖[H_i, H_j]‖`
for `H = ∑_{k ∈ order} H_k`. -/
theorem norm_lieEvolution_sub_le (hH : ∀ k, (H k).IsHermitian) (order : List κ) (t : ℝ) {m : ℕ}
    (hm : 0 < m) :
    ‖lieEvolution H order t m - hermitianUnitaryPath (gen H order) (-t)‖ ≤
      t ^ 2 / (2 * m) * commSum H order := by
  have hM := expBound_smul_I_one hH order (-t / m)
  rw [← cast_neg_div] at hM
  have h := norm_lie_sub_exp_le _ hm hM le_rfl
  simp only [one_pow, commSum_smul, Complex.norm_I, one_mul, gen_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_neg, sq_abs] at h
  exact h.trans_eq (by ring)

/-- **Second-order error.** `‖strangEvolution H order t m - e^{-itH}‖ ≤
|t|³/(2m²) ∑_{i<j} ‖[H_i, H_j]‖ ∑_k ‖H_k‖` for `H = ∑_{k ∈ order} H_k`. -/
theorem norm_strangEvolution_sub_le (hH : ∀ k, (H k).IsHermitian) (order : List κ) (t : ℝ)
    {m : ℕ} (hm : 0 < m) :
    ‖strangEvolution H order t m - hermitianUnitaryPath (gen H order) (-t)‖ ≤
      |t| ^ 3 / (2 * m ^ 2) * commSum H order * normSum H order := by
  have hM := expBound_smul_I_one hH order (-t / m)
  rw [← cast_neg_div] at hM
  have h := norm_strang_sub_exp_le _ hm hM le_rfl
  simp only [one_pow, commSum_smul, normSum_smul, Complex.norm_I, one_mul, gen_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_neg] at h
  exact h.trans_eq (by ring)

/-- Conjugating by an approximation `U` of `e^{-itH}`: the error of `U† A U` against
`e^{itH} A e^{-itH}` is at most `2 ‖A‖ ‖U - e^{-itH}‖`. -/
private theorem norm_conj_sub_le_of_mem_unitary {G U : Matrix n n ℂ} (hG : G.IsHermitian)
    (hU : U ∈ unitary (Matrix n n ℂ)) (t : ℝ) (A : Matrix n n ℂ) :
    ‖Uᴴ * A * U - hermitianUnitaryPath G t * A * hermitianUnitaryPath G (-t)‖ ≤
      2 * ‖A‖ * ‖U - hermitianUnitaryPath G (-t)‖ := by
  have e : hermitianUnitaryPath G t = (hermitianUnitaryPath G (-t))ᴴ := by
    rw [hermitianUnitaryPath_conjTranspose hG, neg_neg]
  rw [e]
  exact CStarRing.norm_star_mul_mul_sub_star_mul_mul_le hU
    (hermitianUnitaryPath_mem_unitary hG (-t)) A

/-- **First-order error, conjugation.** `‖U_1† A U_1 - e^{itH} A e^{-itH}‖ ≤
2 ‖A‖ t²/(2m) ∑_{i<j} ‖[H_i, H_j]‖`. -/
theorem norm_lieEvolution_conj_sub_le (hH : ∀ k, (H k).IsHermitian) (order : List κ) (t : ℝ)
    {m : ℕ} (hm : 0 < m) (A : Matrix n n ℂ) :
    ‖(lieEvolution H order t m)ᴴ * A * lieEvolution H order t m -
        hermitianUnitaryPath (gen H order) t * A * hermitianUnitaryPath (gen H order) (-t)‖ ≤
      2 * ‖A‖ * (t ^ 2 / (2 * m) * commSum H order) :=
  (norm_conj_sub_le_of_mem_unitary (isHermitian_gen hH order)
    (lieEvolution_mem_unitary hH order t m) t A).trans
    (mul_le_mul_of_nonneg_left (norm_lieEvolution_sub_le hH order t hm) (by positivity))

/-- **Second-order error, conjugation.** `‖U_2† A U_2 - e^{itH} A e^{-itH}‖ ≤
2 ‖A‖ |t|³/(2m²) ∑_{i<j} ‖[H_i, H_j]‖ ∑_k ‖H_k‖`. -/
theorem norm_strangEvolution_conj_sub_le (hH : ∀ k, (H k).IsHermitian) (order : List κ)
    (t : ℝ) {m : ℕ} (hm : 0 < m) (A : Matrix n n ℂ) :
    ‖(strangEvolution H order t m)ᴴ * A * strangEvolution H order t m -
        hermitianUnitaryPath (gen H order) t * A * hermitianUnitaryPath (gen H order) (-t)‖ ≤
      2 * ‖A‖ * (|t| ^ 3 / (2 * m ^ 2) * commSum H order * normSum H order) :=
  (norm_conj_sub_le_of_mem_unitary (isHermitian_gen hH order)
    (strangEvolution_mem_unitary hH order t m) t A).trans
    (mul_le_mul_of_nonneg_left (norm_strangEvolution_sub_le hH order t hm) (by positivity))

end ProductFormula
