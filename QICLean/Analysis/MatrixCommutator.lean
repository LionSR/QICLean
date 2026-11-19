/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The commutator map of a matrix

For a square matrix `H`, `ad_H(X) = HX - XH` is a continuous linear map on matrices, and its
powers are the iterated commutators. Left and right multiplication by `H` commute, so the
exponential of `s ad_H` is conjugation by `e^{sH}`:
`exp(s ad_H)(O) = e^{sH} O e^{-sH}` (the Hadamard formula).

`GaussianFilter.commutatorCLM` and `GaussianFilter.commutatorCLM_apply` are moved unchanged
from `QICLean/Analysis/GaussianFilter/CommutatorSeries.lean`; the Hadamard formula is moved
from TNLean, `TNLean/Algebra/ExpConjugation.lean` at commit `e41c3b63`, where it was private.

## Main definitions

* `GaussianFilter.commutatorCLM` — the map `X ↦ HX - XH`.

## Main results

* `GaussianFilter.exp_smul_commutatorCLM_apply` — the Hadamard formula.

## References

* Arad, Kuwahara and Landau, arXiv:1406.3898, proof of Lemma `lem:Hadamard-bound`,
  `low70.tex`, lines 804–811.
* Hastings, arXiv:cond-mat/0508554v3, lines 856–877 and 1005–1009.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace GaussianFilter

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Commutation with `H`, as a continuous linear map on matrices.
Hastings, arXiv:cond-mat/0508554v3, lines 856–877 and 1005–1009. -/
noncomputable def commutatorCLM (H : Matrix n n ℂ) :
    Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  ContinuousLinearMap.mul ℂ _ H - (ContinuousLinearMap.mul ℂ _).flip H

@[simp] theorem commutatorCLM_apply (H W : Matrix n n ℂ) :
    commutatorCLM H W = H * W - W * H := rfl

/-- Exponentiating left multiplication gives left multiplication by the
exponential. -/
private theorem exp_left_multiplication_apply (H O : Matrix n n ℂ) :
    NormedSpace.exp (ContinuousLinearMap.mul ℂ (Matrix n n ℂ) H) O =
      NormedSpace.exp H * O := by
  let L : Matrix n n ℂ →+* (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :=
    { toFun := ContinuousLinearMap.mul ℂ (Matrix n n ℂ)
      map_zero' := ContinuousLinearMap.ext fun X ↦ zero_mul X
      map_one' := ContinuousLinearMap.ext fun X ↦ one_mul X
      map_add' := fun X Y ↦ ContinuousLinearMap.ext fun Z ↦ add_mul X Y Z
      map_mul' := fun X Y ↦ ContinuousLinearMap.ext fun Z ↦ mul_assoc X Y Z }
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let _ : NormedAlgebra ℚ (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have h := NormedSpace.map_exp L (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).continuous H
  exact (congrArg (fun f : Matrix n n ℂ →L[ℂ] Matrix n n ℂ ↦ f O) h).symm

/-- The opposite regular representation gives the corresponding right
multiplication identity. -/
private theorem exp_right_multiplication_apply (H O : Matrix n n ℂ) :
    NormedSpace.exp ((ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip H) O =
      O * NormedSpace.exp H := by
  let R : (Matrix n n ℂ)ᵐᵒᵖ →+* (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :=
    { toFun := fun a ↦ (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip a.unop
      map_zero' := ContinuousLinearMap.ext fun X ↦ mul_zero X
      map_one' := ContinuousLinearMap.ext fun X ↦ mul_one X
      map_add' := fun X Y ↦ ContinuousLinearMap.ext fun Z ↦ mul_add Z X.unop Y.unop
      map_mul' := by
        intro X Y
        apply ContinuousLinearMap.ext
        intro Z
        change Z * (Y.unop * X.unop) = (Z * Y.unop) * X.unop
        exact (mul_assoc Z Y.unop X.unop).symm }
  have hR : Continuous R :=
    (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip.continuous.comp
      MulOpposite.continuous_unop
  let _ : NormedAlgebra ℚ (Matrix n n ℂ)ᵐᵒᵖ := NormedAlgebra.restrictScalars ℚ ℂ _
  let _ : NormedAlgebra ℚ (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  have h := NormedSpace.map_exp R hR (MulOpposite.op H)
  have hO := congrArg (fun f : Matrix n n ℂ →L[ℂ] Matrix n n ℂ ↦ f O) h
  change O * (NormedSpace.exp (MulOpposite.op H)).unop =
    NormedSpace.exp ((ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip H) O at hO
  simpa only [NormedSpace.exp_op, MulOpposite.unop_op,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] using hO.symm

/-- Left and right multiplication commute, so the exponential of their
commutator splits into two regular exponentials. -/
private theorem exp_commutatorCLM_eq (H : Matrix n n ℂ) :
    NormedSpace.exp (commutatorCLM H) =
    NormedSpace.exp (ContinuousLinearMap.mul ℂ (Matrix n n ℂ) H) *
      NormedSpace.exp (-((ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip H)) := by
  let L := ContinuousLinearMap.mul ℂ (Matrix n n ℂ) H
  let R := (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip H
  have hcomm : Commute L R := by
    apply ContinuousLinearMap.ext
    intro X
    change H * (X * H) = (H * X) * H
    exact (mul_assoc H X H).symm
  let _ : NormedAlgebra ℚ (Matrix n n ℂ →L[ℂ] Matrix n n ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ _
  simpa only [commutatorCLM, sub_eq_add_neg] using NormedSpace.exp_add_of_commute hcomm.neg_right

/-- **The Hadamard formula.** `exp(s ad_H)(O) = e^{sH} O e^{-sH}` for every `s ∈ ℂ`.
AKL14, arXiv:1406.3898, eq. `expansion`, `low70.tex`, lines 804–811. -/
theorem exp_smul_commutatorCLM_apply (H O : Matrix n n ℂ) (s : ℂ) :
    NormedSpace.exp (s • commutatorCLM H) O =
      NormedSpace.exp (s • H) * O * NormedSpace.exp (-(s • H)) := by
  have hs : s • commutatorCLM H = commutatorCLM (s • H) := by
    ext X
    simp only [_root_.smul_apply, commutatorCLM_apply, smul_sub, smul_mul_assoc,
      mul_smul_comm]
  have hneg : -((ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip (s • H)) =
      (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip (-(s • H)) :=
    (map_neg (ContinuousLinearMap.mul ℂ (Matrix n n ℂ)).flip (s • H)).symm
  rw [hs, exp_commutatorCLM_eq, hneg, mul_apply_eq_comp,
    exp_right_multiplication_apply, exp_left_multiplication_apply, mul_assoc]

end GaussianFilter
