/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.MatrixIntegral
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Finite complex regressions for the two-Hamiltonian Gaussian integral. -/

open Matrix Complex GaussianFilter
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace NNReal

namespace GaussianMatrixIntegralTest

private noncomputable def diagonalReal (a : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal fun i => (a i : ℂ)

private theorem diagonalReal_hermitian (a : Fin 2 → ℝ) : (diagonalReal a).IsHermitian := by
  apply isHermitian_diagonal_of_self_adjoint
  ext i
  simp

private theorem diagonalReal_eigen (a : Fin 2 → ℝ) (i : Fin 2) :
    diagonalReal a *ᵥ Pi.single i 1 = (a i : ℂ) • Pi.single i 1 := by
  rw [diagonalReal, diagonal_mulVec_single, mul_one]
  simpa only [smul_eq_mul, mul_one] using (Pi.single_smul' i (a i : ℂ) (1 : ℂ))

private theorem diagonal_entry (h : ℝ≥0) (a b : Fin 2 → ℝ)
    (W : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    gaussianIntertwiner h (diagonalReal a) (diagonalReal b) W i j =
      Complex.exp (-(h : ℂ) * ((a i - b j : ℝ) : ℂ) ^ 2 / 2) * W i j := by
  simpa only [Pi.star_single, star_one, single_one_dotProduct, mulVec_single_one,
    Matrix.col_apply] using
    dotProduct_gaussianIntertwiner_mulVec h (diagonalReal_hermitian a)
      (diagonalReal_hermitian b) W (diagonalReal_eigen a i) (diagonalReal_eigen b j)

private def W : Matrix (Fin 2) (Fin 2) ℂ := !![0, I; -I, 0]

private theorem W_hermitian : W.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [W, Matrix.conjTranspose_apply]

-- A non-real Hermitian input need not yield a Hermitian two-generator filter.
-- Its two off-diagonal entries receive different real attenuation factors.
example :
    ¬ (gaussianIntertwiner 1 (diagonalReal ![0, 1]) (diagonalReal ![0, 2]) W).IsHermitian := by
  let M := gaussianIntertwiner 1 (diagonalReal ![0, 1]) (diagonalReal ![0, 2]) W
  have h01 : M 0 1 = (Real.exp (-2) : ℂ) * I := by
    change gaussianIntertwiner 1 _ _ W 0 1 = _
    rw [diagonal_entry]
    norm_num [W, Complex.ofReal_exp]
  have h10 : M 1 0 = (Real.exp (-(1 / 2 : ℝ)) : ℂ) * (-I) := by
    change gaussianIntertwiner 1 _ _ W 1 0 = _
    rw [diagonal_entry]
    norm_num [W, Complex.ofReal_exp]
  intro hM
  have heq := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) hM.eq
  change star (M 1 0) = M 0 1 at heq
  rw [h01, h10] at heq
  have hexp : Real.exp (-(1 / 2 : ℝ)) = Real.exp (-2) := by
    apply Complex.ofReal_injective
    apply mul_right_cancel₀ I_ne_zero
    simpa only [star_mul', star_neg, Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
      neg_neg] using heq
  have := Real.exp_injective hexp
  norm_num at this

-- The adjoint theorem still applies to that non-real input by exchanging H and H'.
example (h : ℝ≥0) :
    (gaussianIntertwiner h (diagonalReal ![0, 1]) (diagonalReal ![0, 2]) W)ᴴ =
      gaussianIntertwiner h (diagonalReal ![0, 2]) (diagonalReal ![0, 1]) W := by
  rw [gaussianIntertwiner_conjTranspose h (diagonalReal_hermitian _)
    (diagonalReal_hermitian _), W_hermitian.eq]

-- Non-real eigenvector phases test conjugate-linearity in the first inner-product slot.
example (t : ℝ) :
    star (![I, 0] : Fin 2 → ℂ) ⬝ᵥ
      ((hermitianUnitaryPath (diagonalReal ![1, 3]) t * W *
        hermitianUnitaryPath (diagonalReal ![0, 2]) (-t)) *ᵥ ![0, 1]) =
      Complex.exp (-(t : ℂ) * I) := by
  have hv : diagonalReal ![1, 3] *ᵥ ![I, 0] = (1 : ℂ) • ![I, 0] := by
    ext i
    fin_cases i <;> norm_num [diagonalReal, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hw : diagonalReal ![0, 2] *ᵥ ![0, 1] = (2 : ℂ) • ![0, 1] := by
    ext i
    fin_cases i <;> norm_num [diagonalReal, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [dotProduct_intertwinerIntegrand_mulVec (diagonalReal_hermitian _) W hv hw]
  norm_num [W, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

-- Zero variance is supported without a positive-variance side condition.
example : gaussianIntertwiner 0 (diagonalReal ![1, 3]) (diagonalReal ![0, 2]) W = W := by
  simp

-- A negative cutoff yields the empty, unrenormalized integral.
example (h : ℝ≥0) :
    gaussianIntertwinerTruncated h (-1) (diagonalReal ![1, 3]) (diagonalReal ![0, 2]) W = 0 := by
  simp [gaussianIntertwinerTruncated]

-- The empty finite-dimensional case needs no nonempty-index assumption.
example (h : ℝ≥0) (H' H W : Matrix (Fin 0) (Fin 0) ℂ) :
    gaussianIntertwiner h H' H W = W := Subsingleton.elim _ _

end GaussianMatrixIntegralTest

/--
info: 'GaussianFilter.integrable_intertwinerIntegrand' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.integrable_intertwinerIntegrand

/--
info: 'GaussianFilter.norm_gaussianIntertwiner_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.norm_gaussianIntertwiner_le

/--
info: 'GaussianFilter.norm_gaussianIntertwinerTruncated_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.norm_gaussianIntertwinerTruncated_le

/--
info: 'GaussianFilter.gaussianIntertwiner_conjTranspose' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.gaussianIntertwiner_conjTranspose

/--
info: 'GaussianFilter.inner_gaussianIntertwiner' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.inner_gaussianIntertwiner
