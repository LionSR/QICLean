/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.BlockDiagonalNorm
import QICLean.Analysis.JordanBlockComparison

/-!
# Finite sums of genuine Jordan blocks

For a nonempty finite family, choose a block of maximal eigenvalue modulus
and maximal dimension among ties. Its power norm eventually equals the
power norm of the whole sum. The explicit bounds of
`Matrix.l2_opNorm_jordanBlock_pow_polynomial_bounds` therefore apply to the
sum when that modulus is positive. All-zero eigenvalues are treated by
nilpotence, and the generic maximum formula includes the empty family.

These are the finite direct-sum steps of Wolf, Chapter 8, lines 1252--1267
of `Notes/WolfNoteTexSource/ch08_distance_measures.tex`. No Jordan
decomposition for an arbitrary matrix or minimizing similarity is assumed
or constructed here.
-/

open scoped Matrix.Norms.L2Operator
open Filter

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite dependent direct sum of explicit Jordan blocks. -/
def jordanBlockDirectSum (D : ι → ℕ) (a : ι → ℂ) :
    Matrix (Σ i, Fin (D i)) (Σ i, Fin (D i)) ℂ :=
  blockDiagonal' (fun i ↦ jordanBlock (D i) (a i))

/-- Exact maximum of all Jordan-block power norms; the empty maximum is zero. -/
theorem l2_opNNNorm_jordanBlockDirectSum_pow (D : ι → ℕ) (a : ι → ℂ) (n : ℕ) :
    ‖jordanBlockDirectSum D a ^ n‖₊ =
      Finset.univ.sup (fun i ↦ ‖jordanBlock (D i) (a i) ^ n‖₊) := by
  rw [jordanBlockDirectSum, ← blockDiagonal'_pow, l2_opNNNorm_blockDiagonal']
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Finite nonempty families have the lexicographic choice used by Wolf:
maximal modulus, then maximal dimension among equal moduli. -/
theorem exists_jordanBlock_maximal [Finite ι] [Nonempty ι] (D : ι → ℕ) (a : ι → ℂ) :
    ∃ k, (∀ i, ‖a i‖ ≤ ‖a k‖) ∧ (∀ i, ‖a i‖ = ‖a k‖ → D i ≤ D k) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun i ↦ ‖a i‖)
    Finset.univ_nonempty
  let s := Finset.univ.filter (fun i ↦ ‖a i‖ = ‖a j‖)
  have hs : s.Nonempty := ⟨j, by simp [s]⟩
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image s D hs
  have hkj : ‖a k‖ = ‖a j‖ := (Finset.mem_filter.mp hk).2
  refine ⟨k, fun i ↦ ?_, fun i hi ↦ ?_⟩
  · rw [hkj]
    exact hj i (Finset.mem_univ i)
  · exact hmax i (by simp [s, hi, hkj])

/-- The selected maximal-modulus, maximal-dimension block eventually realizes
the norm of the direct sum. Equal-modulus ties require no strict comparison.
Source: Wolf Chapter 8, lines 1255--1263. -/
theorem eventually_l2_opNorm_jordanBlockDirectSum_pow_eq
    (D : ι → ℕ) [∀ i, NeZero (D i)] (a : ι → ℂ) (k : ι)
    (hmod : ∀ i, ‖a i‖ ≤ ‖a k‖)
    (hdim : ∀ i, ‖a i‖ = ‖a k‖ → D i ≤ D k) :
    ∀ᶠ n : ℕ in atTop,
      ‖jordanBlockDirectSum D a ^ n‖ = ‖jordanBlock (D k) (a k) ^ n‖ := by
  have hblocks : ∀ i, ∀ᶠ n : ℕ in atTop,
      ‖jordanBlock (D i) (a i) ^ n‖ ≤ ‖jordanBlock (D k) (a k) ^ n‖ := by
    intro i
    rcases (hmod i).eq_or_lt with hi | hi
    · exact Eventually.of_forall (l2_opNorm_jordanBlock_pow_le_of_norm_eq (hdim i hi) _ _ hi)
    · exact (eventually_l2_opNorm_jordanBlock_pow_lt_of_norm_lt
        (D i) (D k) (a i) (a k) hi).mono (fun _ hn ↦ hn.le)
  filter_upwards [eventually_all.mpr hblocks] with n hn
  rw [jordanBlockDirectSum, ← blockDiagonal'_pow]
  exact l2_opNorm_blockDiagonal'_eq_of_max _ k hn

/-- A finite direct sum with all eigenvalues zero vanishes at and after the
largest block dimension. This also covers an empty family. -/
theorem jordanBlockDirectSum_zero_pow_eq_zero
    (D : ι → ℕ) [∀ i, NeZero (D i)] (n : ℕ) (hn : Finset.univ.sup D ≤ n) :
    jordanBlockDirectSum D (fun _ ↦ 0) ^ n = 0 := by
  rw [jordanBlockDirectSum, ← blockDiagonal'_pow]
  have hzero : (fun i ↦ jordanBlock (D i) 0) ^ n = 0 := by
    funext i
    exact jordanBlock_zero_pow_eq_zero (D i) n
      ((Finset.le_sup (f := D) (Finset.mem_univ i)).trans hn)
  rw [hzero, blockDiagonal'_zero]

/-- If the selected maximal modulus is zero, the whole sum vanishes from
the selected maximal block dimension onward, rather than at every positive power. -/
theorem jordanBlockDirectSum_pow_eq_zero_of_maximal_zero
    (D : ι → ℕ) [∀ i, NeZero (D i)] (a : ι → ℂ) (k : ι)
    (hmod : ∀ i, ‖a i‖ ≤ ‖a k‖)
    (hdim : ∀ i, ‖a i‖ = ‖a k‖ → D i ≤ D k)
    (hk0 : ‖a k‖ = 0) (n : ℕ) (hn : D k ≤ n) :
    jordanBlockDirectSum D a ^ n = 0 := by
  have hz (i : ι) : ‖a i‖ = 0 := le_antisymm (by simpa [hk0] using hmod i) (norm_nonneg _)
  have ha : a = fun _ ↦ 0 := funext (fun i ↦ norm_eq_zero.mp (hz i))
  rw [ha]
  exact jordanBlockDirectSum_zero_pow_eq_zero D n
    ((Finset.sup_le (fun i _ ↦ hdim i ((hz i).trans hk0.symm))).trans hn)

/-- The selected-block lower bound holds throughout the fixed-block range,
without waiting for eventual dominance. -/
theorem le_l2_opNorm_jordanBlockDirectSum_pow_polynomial
    (D : ι → ℕ) [∀ i, NeZero (D i)] (a : ι → ℂ) (k : ι)
    (hk0 : 0 < ‖a k‖) (n : ℕ) (hn : D k - 1 ≤ n) :
    ((‖a k‖ * (D k - 1 : ℕ))⁻¹) ^ (D k - 1) * ‖a k‖ ^ n *
      (n : ℝ) ^ (D k - 1) ≤ ‖jordanBlockDirectSum D a ^ n‖ := by
  refine (le_l2_opNorm_jordanBlock_pow_polynomial (D k) (a k) n hk0 hn).trans ?_
  rw [jordanBlockDirectSum, ← blockDiagonal'_pow]
  exact l2_opNorm_block_le_blockDiagonal' (fun i ↦ jordanBlock (D i) (a i) ^ n) k

/-- Two-sided polynomial-exponential bounds for a finite sum, with the exact
constants of the landed fixed-block theorem. The maximal modulus is positive;
zero-modulus sums instead use `jordanBlockDirectSum_zero_pow_eq_zero`.
Source: Wolf Chapter 8, lines 1261--1267 and Equations (8.106)--(8.107). -/
theorem eventually_l2_opNorm_jordanBlockDirectSum_pow_polynomial_bounds
    (D : ι → ℕ) [∀ i, NeZero (D i)] (a : ι → ℂ) (k : ι)
    (hmod : ∀ i, ‖a i‖ ≤ ‖a k‖)
    (hdim : ∀ i, ‖a i‖ = ‖a k‖ → D i ≤ D k)
    (hk0 : 0 < ‖a k‖) (hk1 : ‖a k‖ ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      ((‖a k‖ * (D k - 1 : ℕ))⁻¹) ^ (D k - 1) * ‖a k‖ ^ n *
          (n : ℝ) ^ (D k - 1) ≤ ‖jordanBlockDirectSum D a ^ n‖ ∧
      ‖jordanBlockDirectSum D a ^ n‖ ≤
        (D k : ℝ) * (‖a k‖⁻¹) ^ (D k - 1) * ‖a k‖ ^ n *
          (n : ℝ) ^ (D k - 1) := by
  filter_upwards [eventually_l2_opNorm_jordanBlockDirectSum_pow_eq D a k hmod hdim,
    eventually_ge_atTop (D k - 1)] with n heq hn
  rw [heq]
  exact l2_opNorm_jordanBlock_pow_polynomial_bounds (D k) (a k) n hk0 hk1 hn

/-- Positive constants for the two-sided asymptotic scale, with the printed
`D = 1` lower constant interpreted as one. -/
theorem exists_pos_eventually_jordanBlockDirectSum_pow_bounds
    (D : ι → ℕ) [∀ i, NeZero (D i)] (a : ι → ℂ) (k : ι)
    (hmod : ∀ i, ‖a i‖ ≤ ‖a k‖)
    (hdim : ∀ i, ‖a i‖ = ‖a k‖ → D i ≤ D k)
    (hk0 : 0 < ‖a k‖) (hk1 : ‖a k‖ ≤ 1) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ n : ℕ in atTop,
      C₁ * ‖a k‖ ^ n * (n : ℝ) ^ (D k - 1) ≤ ‖jordanBlockDirectSum D a ^ n‖ ∧
      ‖jordanBlockDirectSum D a ^ n‖ ≤ C₂ * ‖a k‖ ^ n * (n : ℝ) ^ (D k - 1) := by
  refine ⟨((‖a k‖ * (D k - 1 : ℕ))⁻¹) ^ (D k - 1),
    (D k : ℝ) * (‖a k‖⁻¹) ^ (D k - 1), ?_, ?_,
    eventually_l2_opNorm_jordanBlockDirectSum_pow_polynomial_bounds D a k hmod hdim hk0 hk1⟩
  · by_cases hD : D k = 1
    · simp [hD]
    · apply pow_pos
      apply inv_pos.mpr
      exact mul_pos hk0 (by exact_mod_cast (by have := NeZero.pos (D k); omega : 0 < D k - 1))
  · exact mul_pos (by exact_mod_cast NeZero.pos (D k)) (pow_pos (inv_pos.mpr hk0) _)

/-- Rescaling the upper constant covers every positive exponent when the
maximal modulus is positive. The polynomial scale at `n = 0` is deliberately
excluded, as in Wolf's positive-exponent argument at lines 1263--1264. -/
theorem exists_pos_jordanBlockDirectSum_pow_le_polynomial
    (D : ι → ℕ) [∀ i, NeZero (D i)] (a : ι → ℂ) (k : ι)
    (hmod : ∀ i, ‖a i‖ ≤ ‖a k‖)
    (hdim : ∀ i, ‖a i‖ = ‖a k‖ → D i ≤ D k)
    (hk0 : 0 < ‖a k‖) (hk1 : ‖a k‖ ≤ 1) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ n : ℕ, 0 < n →
      ‖jordanBlockDirectSum D a ^ n‖ ≤ C₂ * ‖a k‖ ^ n * (n : ℝ) ^ (D k - 1) := by
  let C : ℝ := (D k : ℝ) * (‖a k‖⁻¹) ^ (D k - 1)
  have hC : 0 < C :=
    mul_pos (by exact_mod_cast NeZero.pos (D k)) (pow_pos (inv_pos.mpr hk0) _)
  have hevent : ∀ᶠ n : ℕ in atTop, ‖jordanBlockDirectSum D a ^ n‖ ≤
      C * ‖a k‖ ^ n * (n : ℝ) ^ (D k - 1) :=
    (eventually_l2_opNorm_jordanBlockDirectSum_pow_polynomial_bounds D a k hmod hdim hk0 hk1).mono
      (fun _ h ↦ h.2)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let scale (n : ℕ) : ℝ := ‖a k‖ ^ n * (n : ℝ) ^ (D k - 1)
  let R : ℝ := ∑ n ∈ Finset.range N, ‖jordanBlockDirectSum D a ^ n‖ / scale n
  refine ⟨max C R, hC.trans_le (le_max_left _ _), fun n hn ↦ ?_⟩
  rw [mul_assoc]
  change ‖jordanBlockDirectSum D a ^ n‖ ≤ max C R * scale n
  have hs : 0 < scale n := mul_pos (pow_pos hk0 n) (pow_pos (by exact_mod_cast hn) _)
  by_cases hnN : n < N
  · have hr : ‖jordanBlockDirectSum D a ^ n‖ / scale n ≤ R :=
      Finset.single_le_sum (fun m _ ↦ div_nonneg (norm_nonneg _) (by dsimp [scale]; positivity))
        (Finset.mem_range.mpr hnN)
    exact (div_le_iff₀ hs).mp (hr.trans (le_max_right C R))
  · have hf : ‖jordanBlockDirectSum D a ^ n‖ ≤ C * scale n := by
      simpa [scale, mul_assoc] using hN n (by omega)
    exact hf.trans (mul_le_mul_of_nonneg_right (le_max_left C R) hs.le)

end Matrix
