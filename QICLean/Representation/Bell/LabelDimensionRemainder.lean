/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Real.SublinearRemainder
import QICLean.Representation.Permutation.IrrepLabels
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Remainders of the lower norm comparisons for a sequence of labels

Let `λ_k` be a label of the symmetric group on `k` letters for every `k`, and let `S` be a
real number with `log dim λ_k = k S + o(k)`. The label defect
`ε_k = 2 |log dim λ_k - k S|` is nonnegative, satisfies `2 k S - ε_k ≤ 2 log dim λ_k`, and
is `o(k)`. It enters the finite-copy lower norm comparisons through the explicit remainders

* `roughLowerRemainderAtWeight K a c C_f`, equal to
  `(K/2) (2 |log (k+1) + c log (k+2) + a ε_k| + C_f log (k+2) + 2 log 2 + log (3/2)) / k`,
  for `K` bands of weight `a`, and `roughLowerRemainder`, its value at total weight `a K = 4`;
* `sharpLowerRemainder a c C_f`, equal to
  `(2 |log (k+1) + c log (k+2) + a ε_k| + |log ((k+2)^{-C_f} / 2)| + log 2 + log (3/2)) / (a k)`.

All of them tend to zero as `k → ∞`, for all real values of the fixed constants: these are
explicit forms of the remainders `o_k(1)` of the lower comparisons. Real division by zero is
zero, so the remainders vanish at `k = 0`, and the sharp remainder vanishes identically at
`a = 0`; the comparisons use them for `k > 0` and `a > 0` only.

## Main definitions

* `TensorPower.labelDimensionDefect`: the label defect `ε_k`.
* `TensorPower.roughLowerRemainderAtWeight`, `TensorPower.roughLowerRemainder`,
  `TensorPower.sharpLowerRemainder`: the remainders.

## Main statements

* `TensorPower.tendsto_roughLowerRemainderAtWeight_of_label_dimension`,
  `TensorPower.tendsto_roughLowerRemainder_of_label_dimension`,
  `TensorPower.tendsto_sharpLowerRemainder_of_label_dimension`: the remainders tend to zero.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `07-comparators.tex`, lines 130–169, 255–281 and 585–651; `08-scanner.tex`, lines 755–769,
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

open Filter PermutationRepresentation
open scoped Topology

namespace TensorPower

/-- The label defect `ε_k = 2 |log dim λ_k - k S|` of a sequence of labels against an entropy
`S` (`07-comparators.tex`, lines 255–281 and 585–651). -/
def labelDimensionDefect
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (k : ℕ) : ℝ :=
  2 * |Real.log (ell k).dim - (k : ℝ) * Sent|

/-- The label defect is nonnegative, and with it the label `λ_k`, taken twice, obeys the
lower entropy condition `2 k S - ε_k ≤ log dim λ_k + log dim λ_k`
(`07-comparators.tex`, lines 255–281 and 585–651). -/
theorem labelDimensionDefect_label_bound
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (k : ℕ) :
    0 ≤ labelDimensionDefect ell Sent k ∧
      2 * (k : ℝ) * Sent - labelDimensionDefect ell Sent k ≤
        Real.log (ell k).dim + Real.log (ell k).dim := by
  refine ⟨mul_nonneg (by norm_num) (abs_nonneg _), ?_⟩
  have h := le_abs_self ((k : ℝ) * Sent - Real.log (ell k).dim)
  rw [abs_sub_comm] at h
  dsimp only [labelDimensionDefect]
  linarith only [h]

/-- If `log dim λ_k = k S + o(k)`, the label defect is `o(k)`. -/
private theorem tendsto_labelDimensionDefect_div
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ ↦ Real.log (ell k).dim - (k : ℝ) * Sent) (fun k : ℕ ↦ (k : ℝ))) :
    Tendsto (fun k : ℕ ↦ labelDimensionDefect ell Sent k / (k : ℝ)) atTop (𝓝 0) := by
  have habs := hdim.tendsto_div_nhds_zero.abs
  simp only [abs_zero] at habs
  have h2 := habs.const_mul 2
  rw [mul_zero] at h2
  refine h2.congr fun k ↦ ?_
  rw [labelDimensionDefect, abs_div, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ)),
    mul_div_assoc]

/-- The remainder of the rough lower comparison for `K` bands of weight `a` each:
`(K/2) (2 |log (k+1) + c log (k+2) + a ε_k| + C_f log (k+2) + 2 log 2 + log (3/2)) / k`
(`07-comparators.tex`, lines 97–169 and 585–651). -/
def roughLowerRemainderAtWeight (Kband : ℕ) (a c Cf : ℝ)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (k : ℕ) : ℝ :=
  ((Kband : ℝ) / 2 *
    (2 * |Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
      a * labelDimensionDefect ell Sent k| +
      Cf * Real.log ((k : ℝ) + 2) + 2 * Real.log 2 + Real.log (3 / 2))) /
        (k : ℝ)

/-- If `log dim λ_k = k S + o(k)`, the rough lower remainder at a fixed weight tends to zero
(`07-comparators.tex`, lines 255–281 and 585–651). -/
theorem tendsto_roughLowerRemainderAtWeight_of_label_dimension
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) * Sent)
      (fun k : ℕ => (k : ℝ))) (Kband : ℕ) (a c Cf : ℝ) :
    Tendsto (roughLowerRemainderAtWeight Kband a c Cf ell Sent) atTop (𝓝 0) := by
  refine (Matrix.MeanTree.tendsto_rough_lower_remainder_div_nat (1 / 4) Kband (a / 2) c Cf
    (tendsto_labelDimensionDefect_div ell Sent hdim)).congr fun k ↦ ?_
  rw [roughLowerRemainderAtWeight, show 2 * (a / 2) = a by ring,
    show 2 * (1 / 4 : ℝ) * Kband = Kband / 2 by ring]

/-- The remainder of the rough lower comparison at total band weight four, that is, at
weight `4 / K` in each of the `K` bands (`07-comparators.tex`, lines 585–651;
`08-scanner.tex`, lines 755–769). -/
def roughLowerRemainder (Kband : ℕ) (c Cf : ℝ)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (k : ℕ) : ℝ :=
  roughLowerRemainderAtWeight Kband (4 / (Kband : ℝ)) c Cf ell Sent k

/-- If `log dim λ_k = k S + o(k)`, the rough lower remainder at total weight four tends to
zero (`07-comparators.tex`, lines 255–281 and 585–651). -/
theorem tendsto_roughLowerRemainder_of_label_dimension
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) * Sent)
      (fun k : ℕ => (k : ℝ))) (Kband : ℕ) (c Cf : ℝ) :
    Tendsto (roughLowerRemainder Kband c Cf ell Sent) atTop (𝓝 0) :=
  tendsto_roughLowerRemainderAtWeight_of_label_dimension
    ell Sent hdim Kband (4 / (Kband : ℝ)) c Cf

/-- If `log dim λ_k = k S + o(k)`, then for every `ε > 0` the rough lower remainder at total
weight four is below `ε` for all sufficiently large numbers of copies (`08-scanner.tex`,
lines 755–769). -/
theorem exists_roughLowerRemainder_threshold
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) * Sent)
      (fun k : ℕ => (k : ℝ))) (Kband : ℕ) (c Cf εrep : ℝ) (hεrep : 0 < εrep) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → roughLowerRemainder Kband c Cf ell Sent k < εrep := by
  have hlim := tendsto_roughLowerRemainder_of_label_dimension ell Sent hdim Kband c Cf
  exact eventually_atTop.1 (hlim.eventually (gt_mem_nhds hεrep))

/-- The remainder of the sharp lower comparison at weight `a`, divided by `a k`:
`(2 |log (k+1) + c log (k+2) + a ε_k| + |log ((k+2)^{-C_f} / 2)| + log 2 + log (3/2)) / (a k)`
(`07-comparators.tex`, lines 585–651). By the convention for real division it is zero at
`a = 0` and at `k = 0`. -/
def sharpLowerRemainder (a c Cf : ℝ)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ) (k : ℕ) : ℝ :=
  (2 * |Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
      a * labelDimensionDefect ell Sent k| +
    |Real.log (((k : ℝ) + 2) ^ (-Cf) / 2)| + Real.log 2 + Real.log (3 / 2)) /
      (a * (k : ℝ))

/-- If `log dim λ_k = k S + o(k)`, the sharp lower remainder tends to zero, for all real
`a`, `c` and `C_f` (`07-comparators.tex`, lines 255–281 and 585–651). At `a = 0` it is
identically zero. -/
theorem tendsto_sharpLowerRemainder_of_label_dimension
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (Sent : ℝ)
    (hdim : Asymptotics.IsLittleO atTop
      (fun k : ℕ => Real.log (ell k).dim - (k : ℝ) * Sent)
      (fun k : ℕ => (k : ℝ))) (a c Cf : ℝ) :
    Tendsto (sharpLowerRemainder a c Cf ell Sent) atTop (𝓝 0) := by
  have hlog (b : ℝ) :
      Tendsto (fun k : ℕ => Real.log ((k : ℝ) + b) / (k : ℝ)) atTop (𝓝 0) := by
    have hshift : Tendsto (fun k : ℕ => (k : ℝ) + b) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-b) 1 one_ne_zero).comp hshift
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using hh
  have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hconst (b : ℝ) : Tendsto (fun k : ℕ => b / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul b
  have habs (f : ℕ → ℝ)
      (hf : Tendsto (fun k : ℕ => f k / (k : ℝ)) atTop (𝓝 0)) :
      Tendsto (fun k : ℕ => |f k| / (k : ℝ)) atTop (𝓝 0) := by
    have heq (k : ℕ) : |f k / (k : ℝ)| = |f k| / (k : ℝ) := by
      rw [abs_div, abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    simpa only [heq, abs_zero] using hf.abs
  have hdefect := tendsto_labelDimensionDefect_div ell Sent hdim
  let r := fun k : ℕ => Real.log ((k : ℝ) + 1) + c * Real.log ((k : ℝ) + 2) +
    a * labelDimensionDefect ell Sent k
  have hr : Tendsto (fun k : ℕ => r k / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [r, add_div, mul_div_assoc, mul_zero, add_zero] using
      ((hlog 1).add ((hlog 2).const_mul c)).add (hdefect.const_mul a)
  let b := fun k : ℕ => Real.log (((k : ℝ) + 2) ^ (-Cf) / 2)
  have hb_eq (k : ℕ) : b k = -Cf * Real.log ((k : ℝ) + 2) - Real.log 2 := by
    simp (disch := positivity) only [b, Real.log_div, Real.log_rpow]
  have hb : Tendsto (fun k : ℕ => b k / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [hb_eq, sub_div, mul_div_assoc, mul_zero, sub_zero] using
      ((hlog 2).const_mul (-Cf)).sub (hconst (Real.log 2))
  have herr : Tendsto (fun k : ℕ =>
      (2 * |r k| + |b k| + Real.log 2 + Real.log (3 / 2)) / (k : ℝ))
      atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using
      ((((habs r hr).const_mul 2).add (habs b hb)).add
        (hconst (Real.log 2))).add (hconst (Real.log (3 / 2)))
  change Tendsto (fun k : ℕ =>
    (2 * |r k| + |b k| + Real.log 2 + Real.log (3 / 2)) / (a * (k : ℝ)))
    atTop (𝓝 0)
  simpa only [div_div, mul_comm, zero_div] using herr.div_const a

end TensorPower
