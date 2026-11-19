/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import QICLean.Analysis.MatrixCommutator
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Algebra.Group.IsApply
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Conjugation by a matrix exponential

Write `ad_H(X) = HX - XH`. If `‖ad_H^m O‖ ≤ a^m m! ‖O‖` for every `m`, then the Hadamard
series `e^{sH} O e^{-sH} = ∑ₘ sᵐ/m! · ad_H^m O` has the geometric majorant
`∑ₘ (as)ᵐ ‖O‖`, so `‖e^{sH} O e^{-sH}‖ ≤ 2‖O‖` for `0 ≤ s` with `as ≤ 1/2`. No locality or
Hermiticity is assumed; locality enters only through the growth bound. A positive contraction
`0 ≤ h ≤ 1` satisfies `‖hO - Oh‖ ≤ ‖O‖`, since `h - 1/2` has norm at most `1/2`.

Moved from TNLean, `TNLean/Algebra/ExpConjugation.lean` at commit
`e41c3b63`; the growth rate is no longer assumed nonnegative, since the growth bound at
`m = 1` forces it unless `O = 0`.

## Main results

* `Matrix.norm_exp_conjugation_le_two_of_growth` — the conjugation bound from factorial growth.
* `Matrix.norm_commutator_le_of_nonneg_le_one` — commutators with a positive contraction.

## References

* Arad, Kuwahara and Landau, arXiv:1406.3898, proof of Lemma `lem:Hadamard-bound`,
  `low70.tex`, lines 804–877 (the Hadamard expansion and the commutator estimate for a
  positive term).
-/

open scoped Matrix.Norms.L2Operator BigOperators

namespace ContinuousLinearMap

/-- The exponential series of `s T`, evaluated at a vector. -/
private theorem hasSum_exp_smul_apply_pow {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (s : ℂ) (O : E) :
    HasSum (fun m : ℕ ↦ (s ^ m / (m.factorial : ℂ)) • (T ^ m) O)
      ((NormedSpace.exp (s • T)) O) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (s • T)).mapL
    (ContinuousLinearMap.apply ℂ E O)
  simpa only [ContinuousLinearMap.apply_apply, smul_pow, smul_apply, smul_smul, div_eq_mul_inv,
    mul_comm] using h

end ContinuousLinearMap

namespace NormedSpace

/-- A factorial growth estimate gives a geometric majorant for the scaled
series. Supporting the Hadamard-series argument of AKL14, arXiv:1406.3898,
low70.tex, lines 795–810. -/
private theorem summable_factorial_smul_and_norm_tsum_le_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (v : ℕ → E) (C a s : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hs0 : 0 ≤ s) (hs : a * s ≤ 1 / 2)
    (hv : ∀ m, ‖v m‖ ≤ a ^ m * (m.factorial : ℝ) * C) :
    Summable (fun m : ℕ ↦ ((s : ℂ) ^ m / (m.factorial : ℂ)) • v m) ∧
      ‖∑' m : ℕ, ((s : ℂ) ^ m / (m.factorial : ℂ)) • v m‖ ≤ 2 * C := by
  have hbound (m : ℕ) :
      ‖((s : ℂ) ^ m / (m.factorial : ℂ)) • v m‖ ≤ (1 / 2 : ℝ) ^ m * C := by
    have hfac : 0 < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    calc
      ‖((s : ℂ) ^ m / (m.factorial : ℂ)) • v m‖ =
          (s ^ m / (m.factorial : ℝ)) * ‖v m‖ := by
        rw [norm_smul, norm_div, norm_pow, Complex.norm_of_nonneg hs0,
          Complex.norm_natCast]
      _ ≤ (s ^ m / (m.factorial : ℝ)) *
          (a ^ m * (m.factorial : ℝ) * C) :=
        mul_le_mul_of_nonneg_left (hv m) (div_nonneg (pow_nonneg hs0 _) hfac.le)
      _ = ((s ^ m / (m.factorial : ℝ)) * (m.factorial : ℝ)) *
          (a ^ m * C) := by ring
      _ = (a * s) ^ m * C := by
        rw [div_mul_cancel₀ _ hfac.ne', mul_pow]
        ring
      _ ≤ (1 / 2 : ℝ) ^ m * C :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (mul_nonneg ha hs0) hs m) hC
  have hgeom : HasSum (fun m : ℕ ↦ (1 / 2 : ℝ) ^ m * C) (2 * C) :=
    hasSum_geometric_two.mul_right C
  exact ⟨hgeom.summable.of_norm_bounded hbound, tsum_of_norm_bounded hgeom hbound⟩

end NormedSpace

namespace Matrix

/-- **Conjugation from factorial commutator growth.** If `‖ad_H^m O‖ ≤ a^m m! ‖O‖` for every
`m`, then `‖e^{sH} O e^{-sH}‖ ≤ 2‖O‖` for `0 ≤ s` with `as ≤ 1/2`.
AKL14, arXiv:1406.3898, proof of `lem:Hadamard-bound`, `low70.tex`, lines 804–877. -/
theorem norm_exp_conjugation_le_two_of_growth {n : Type*} [Fintype n] [DecidableEq n]
    (H O : Matrix n n ℂ) (a s : ℝ)
    (hs0 : 0 ≤ s) (hs : a * s ≤ 1 / 2)
    (hgrowth : ∀ m : ℕ,
      ‖(GaussianFilter.commutatorCLM H ^ m) O‖ ≤ a ^ m * (m.factorial : ℝ) * ‖O‖) :
    ‖NormedSpace.exp ((s : ℂ) • H) * O *
      NormedSpace.exp (-((s : ℂ) • H))‖ ≤ 2 * ‖O‖ := by
  rcases eq_or_ne O 0 with rfl | hO
  · simp
  have ha : 0 ≤ a := by
    have h1 := hgrowth 1
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at h1
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h1) (norm_pos_iff.mpr hO)
  have hsum := ContinuousLinearMap.hasSum_exp_smul_apply_pow
    (GaussianFilter.commutatorCLM H) (s : ℂ) O
  obtain ⟨-, hbound⟩ := NormedSpace.summable_factorial_smul_and_norm_tsum_le_two
    (fun m : ℕ ↦ (GaussianFilter.commutatorCLM H ^ m) O) ‖O‖ a s (norm_nonneg O) ha hs0 hs
    hgrowth
  rwa [hsum.tsum_eq, GaussianFilter.exp_smul_commutatorCLM_apply] at hbound

open scoped ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If `0 ≤ h ≤ 1`, then `‖hO - Oh‖ ≤ ‖O‖` for every `O`.
AKL14, arXiv:1406.3898, proof of `lem:Hadamard-bound`, `low70.tex`, lines 831–837. -/
theorem norm_commutator_le_of_nonneg_le_one (h O : Matrix n n ℂ)
    (h0 : 0 ≤ h) (h1 : h ≤ 1) : ‖h * O - O * h‖ ≤ ‖O‖ := by
  let c : Matrix n n ℂ := (1 / 2 : ℝ) • 1
  have hsplit : (1 : Matrix n n ℂ) = c + c := by
    dsimp [c]
    rw [← add_smul]
    norm_num
  have hlo : -c ≤ h - c := by
    simpa only [zero_sub] using sub_le_sub_right h0 c
  have hhi : h - c ≤ c := by
    apply (sub_le_iff_le_add).2
    rw [← hsplit]
    exact h1
  have hcself : IsSelfAdjoint c :=
    IsSelfAdjoint.smul (IsSelfAdjoint.all (1 / 2 : ℝ)) (IsSelfAdjoint.one (Matrix n n ℂ))
  have hcenterself : IsSelfAdjoint (h - c) := (IsSelfAdjoint.of_nonneg h0).sub hcself
  have hnorm1 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 :=
    IsStarProjection.norm_le _ (IsStarProjection.one (Matrix n n ℂ))
  have hcnorm : ‖c‖ ≤ (1 / 2 : ℝ) := by
    calc
      ‖c‖ = (1 / 2 : ℝ) * ‖(1 : Matrix n n ℂ)‖ := by
        dsimp [c]
        rw [norm_smul]
        norm_num
      _ ≤ (1 / 2 : ℝ) * 1 := mul_le_mul_of_nonneg_left hnorm1 (by norm_num)
      _ = 1 / 2 := by ring
  have hcenternorm0 : ‖h - c‖ ≤ ‖c‖ := by
    simpa only [norm_neg, max_self] using
      (IsSelfAdjoint.norm_le_max_of_le_of_le hlo hhi hcenterself)
  have hcenternorm : ‖h - c‖ ≤ (1 / 2 : ℝ) := hcenternorm0.trans hcnorm
  have hcomm : h * O - O * h = (h - c) * O - O * (h - c) := by
    dsimp [c]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    abel
  calc
    ‖h * O - O * h‖ = ‖(h - c) * O - O * (h - c)‖ := congrArg (‖·‖) hcomm
    _ ≤ ‖(h - c) * O‖ + ‖O * (h - c)‖ := norm_sub_le _ _
    _ ≤ ‖h - c‖ * ‖O‖ + ‖O‖ * ‖h - c‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ (1 / 2 : ℝ) * ‖O‖ + ‖O‖ * (1 / 2 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_right hcenternorm (norm_nonneg O))
        (mul_le_mul_of_nonneg_left hcenternorm (norm_nonneg O))
    _ = ‖O‖ := by ring

end Matrix
