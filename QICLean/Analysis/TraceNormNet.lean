/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorNormFrobenius
import QICLean.Analysis.RectangularTraceNormAlgebra

/-!
# A finite net for the trace-norm unit ball

For a square complex matrix of size `c`, the entries have modulus at most the trace norm, and
the trace norm is at most the sum of the moduli of the entries. Rounding the real and imaginary
part of every entry of a matrix in the trace-norm unit ball to a grid of step `1/M` on
`[-1, 1]`, with `M = ⌈c²/η⌉`, therefore moves it by at most `η` in trace norm. The rounded
matrices form a set of at most `(2M + 1)^(2c²)` elements.

## Main results

* `Matrix.norm_apply_le_rectangularTraceNorm`: `|Y i j| ≤ ‖Y‖₁`.
* `Matrix.rectangularTraceNorm_le_sum_norm_apply`: `‖Z‖₁ ≤ ∑ i j, |Z i j|`.
* `Matrix.exists_finset_rectangularTraceNorm_net`: a finite `η`-net for the trace-norm unit
  ball with at most `(2 ⌈c²/η⌉ + 1)^(2c²)` elements.

This is Lemma `l:constantbondapprox` of Landau, Vazirani and Vidick, for matrices on
`ℂ^B ⊗ ℂ^d`, where `c = Bd`.

**Local fix (Lemma `l:constantbondapprox`):** the printed grid step `⌊η/(Bd)²⌋` is read as
`η/(Bd)²` (here `1/M ≤ η/(Bd)²`), the net is written `N_δ` for `N_η`, the printed product
`I^B × I^d` is read as a grid for the real and imaginary parts of every entry, and the printed
size `(2⌈Bd/η⌉ + 1)^(2Bd)` is corrected to `(2⌈(Bd)²/η⌉ + 1)^(2(Bd)²)`. Both sizes are
polynomial in `1/η` for fixed `B` and `d`. Documented in
`docs/paper-gaps/lvv13_trace_norm_net.tex`.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of
  1D gapped local Hamiltonians*, arXiv:1307.5143v1, `algo53.tex`, Lemma
  `l:constantbondapprox`, lines 451–460.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An entry of a complex square matrix has modulus at most its L² operator norm. -/
theorem norm_apply_le_l2_opNorm (U : Matrix n n ℂ) (i j : n) : ‖U i j‖ ≤ ‖U‖ := by
  have h := sum_column_norm_sq_le_norm_sq U j
  have hi : ‖U i j‖ ^ 2 ≤ ∑ k, ‖U k j‖ ^ 2 :=
    Finset.single_le_sum (f := fun k ↦ ‖U k j‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
      (Finset.mem_univ i)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (hi.trans h)

/-- An entry of a complex square matrix has modulus at most its trace norm. -/
theorem norm_apply_le_rectangularTraceNorm (Y : Matrix n n ℂ) (i j : n) :
    ‖Y i j‖ ≤ rectangularTraceNorm Y := by
  have h := norm_trace_conjTranspose_mul_le_rectangularTraceNorm Y (single i j 1)
    (l2_opNorm_single_one i j).le
  have htr : (Yᴴ * single i j 1).trace = star (Y i j) := by
    simp [trace_mul_single, conjTranspose_apply]
  rwa [htr, norm_star] at h

/-- A matrix unit has trace norm at most one. -/
theorem rectangularTraceNorm_single_one_le (i j : n) :
    rectangularTraceNorm (single i j (1 : ℂ)) ≤ 1 := by
  refine rectangularTraceNorm_le_of_forall_contraction _ 1 fun U hU ↦ ?_
  have htr : ((single i j (1 : ℂ))ᴴ * U).trace = U i j := by
    simp [conjTranspose_single, trace_single_mul]
  rw [htr]
  exact (norm_apply_le_l2_opNorm U i j).trans hU

/-- The trace norm of a complex square matrix is at most the sum of the moduli of its
entries. -/
theorem rectangularTraceNorm_le_sum_norm_apply (Z : Matrix n n ℂ) :
    rectangularTraceNorm Z ≤ ∑ i, ∑ j, ‖Z i j‖ := by
  conv_lhs => rw [matrix_eq_sum_single Z]
  refine (rectangularTraceNorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  refine (rectangularTraceNorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  have h : single i j (Z i j) = Z i j • single i j (1 : ℂ) := by
    rw [smul_single, smul_eq_mul, mul_one]
  rw [h, rectangularTraceNorm_smul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (rectangularTraceNorm_single_one_le i j))

/-- Rounding `t ∈ [-1, 1]` to the grid `{-1 + k/M : 0 ≤ k ≤ 2M}` moves it by at most
`1/(2M)`. -/
private theorem exists_grid_le {M : ℕ} (hM : 0 < M) {t : ℝ} (ht : |t| ≤ 1) :
    ∃ k ∈ Finset.range (2 * M + 1), |t - (-1 + (k : ℝ) / M)| ≤ 1 / (2 * M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨ht1, ht2⟩ := abs_le.mp ht
  set y := (t + 1) * M + 1 / 2 with hy
  have hy0 : 0 ≤ y := by rw [hy]; nlinarith
  refine ⟨⌊y⌋₊, ?_, ?_⟩
  · rw [Finset.mem_range, Nat.lt_succ_iff]
    have : y < 2 * M + 1 := by rw [hy]; nlinarith
    have h := Nat.floor_lt hy0 |>.mpr (by exact_mod_cast this)
    omega
  · have hfl := Nat.floor_le hy0
    have hlt := Nat.lt_floor_add_one y
    rw [abs_le]
    constructor
    · rw [show t - (-1 + (⌊y⌋₊ : ℝ) / M) = ((t + 1) * M - ⌊y⌋₊) / M by field_simp; ring,
        le_div_iff₀ hM']
      field_simp
      nlinarith
    · rw [show t - (-1 + (⌊y⌋₊ : ℝ) / M) = ((t + 1) * M - ⌊y⌋₊) / M by field_simp; ring,
        div_le_iff₀ hM']
      field_simp
      nlinarith

/-- **A finite net for the trace-norm unit ball** (Lemma `l:constantbondapprox` of
arXiv:1307.5143v1, `algo53.tex`, lines 451–460, with the corrections of the module
docstring). For `η > 0` there is a finite set `N` of `c × c` complex matrices, `c` the size of
the index type, with at most `(2 ⌈c²/η⌉ + 1)^(2c²)` elements, such that every matrix of trace
norm at most `1` is within trace-norm distance `η` of an element of `N`. -/
theorem exists_finset_rectangularTraceNorm_net {η : ℝ} (hη : 0 < η) :
    ∃ N : Finset (Matrix n n ℂ),
      N.card ≤ (2 * ⌈(Fintype.card n : ℝ) ^ 2 / η⌉₊ + 1) ^ (2 * Fintype.card n ^ 2) ∧
      ∀ Y : Matrix n n ℂ, rectangularTraceNorm Y ≤ 1 →
        ∃ X ∈ N, rectangularTraceNorm (Y - X) ≤ η := by
  classical
  set c := Fintype.card n
  set M := ⌈(c : ℝ) ^ 2 / η⌉₊ with hMdef
  rcases Nat.eq_zero_or_pos c with hc | hc
  · -- No entries: every matrix is `0`.
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hc
    refine ⟨{0}, by simp [hc], fun Y _ ↦ ⟨0, Finset.mem_singleton_self _, ?_⟩⟩
    rw [Subsingleton.elim (Y - 0) 0, rectangularTraceNorm_zero]
    exact hη.le
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hMpos : 0 < M := Nat.ceil_pos.mpr (by positivity)
  have hM' : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hMge : (c : ℝ) ^ 2 / η ≤ M := Nat.le_ceil _
  set p : ℕ → ℝ := fun k ↦ -1 + (k : ℝ) / M
  set G : Finset ℝ := (Finset.range (2 * M + 1)).image p
  have hG : G.card ≤ 2 * M + 1 := Finset.card_image_le.trans (Finset.card_range _).le
  set toMat : (n × n → ℝ × ℝ) → Matrix n n ℂ := fun f ↦ of fun i j ↦ ⟨(f (i, j)).1, (f (i, j)).2⟩
  refine ⟨(Fintype.piFinset fun _ : n × n ↦ G ×ˢ G).image toMat, ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Finset.card_product]
    calc (G.card * G.card) ^ (c * c) ≤ ((2 * M + 1) * (2 * M + 1)) ^ (c * c) :=
          Nat.pow_le_pow_left (Nat.mul_le_mul hG hG) _
      _ = (2 * M + 1) ^ (2 * c ^ 2) := by rw [← sq, ← pow_mul, sq c]
  · intro Y hY
    have hentry (i j : n) : ‖Y i j‖ ≤ 1 := (norm_apply_le_rectangularTraceNorm Y i j).trans hY
    have hround (t : ℝ) (ht : |t| ≤ 1) : ∃ g ∈ G, |t - g| ≤ 1 / (2 * M) := by
      obtain ⟨k, hk, hb⟩ := exists_grid_le hMpos ht
      exact ⟨p k, Finset.mem_image_of_mem p hk, hb⟩
    choose! rnd hrndG hrnd using hround
    set f : n × n → ℝ × ℝ := fun ij ↦ (rnd (Y ij.1 ij.2).re, rnd (Y ij.1 ij.2).im)
    have hre (i j : n) : |(Y i j).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (hentry i j)
    have him (i j : n) : |(Y i j).im| ≤ 1 := (Complex.abs_im_le_norm _).trans (hentry i j)
    refine ⟨toMat f, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.mpr fun ij ↦
      Finset.mem_product.mpr ⟨hrndG _ (hre ij.1 ij.2), hrndG _ (him ij.1 ij.2)⟩), ?_⟩
    have herr (i j : n) : ‖(Y - toMat f) i j‖ ≤ 1 / M := by
      have h1 := hrnd _ (hre i j)
      have h2 := hrnd _ (him i j)
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [sub_apply, Complex.sub_re, Complex.sub_im, toMat, f, of_apply]
      calc |(Y i j).re - rnd (Y i j).re| + |(Y i j).im - rnd (Y i j).im|
          ≤ 1 / (2 * M) + 1 / (2 * M) := add_le_add h1 h2
        _ = 1 / M := by field_simp; ring
    calc rectangularTraceNorm (Y - toMat f) ≤ ∑ i, ∑ j, ‖(Y - toMat f) i j‖ :=
          rectangularTraceNorm_le_sum_norm_apply _
      _ ≤ ∑ _i : n, ∑ _j : n, 1 / (M : ℝ) :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ herr i j
      _ = (c : ℝ) ^ 2 / M := by simp [Finset.sum_const, c]; ring
      _ ≤ η := by
          rw [div_le_iff₀ hM']
          rw [div_le_iff₀ hη] at hMge
          linarith

end Matrix
