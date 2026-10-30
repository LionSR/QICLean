/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.JordanBlockAsymptotics
import QICLean.Analysis.MatrixFramePerturbation
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Comparing genuine Jordan blocks

Phase invariance, dimension monotonicity, and eventual strict dominance at
different moduli for the explicit matrices `Matrix.jordanBlock`.
Source: Wolf, Chapter 8, lines 1255--1267 of
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`.
-/

open scoped Matrix.Norms.L2Operator
open Filter

namespace Matrix

/-- Entry formula independent of the ambient Jordan-block dimension. -/
theorem jordanBlock_pow_apply (D : ℕ) (a : ℂ) (n : ℕ) (i j : Fin D) :
    (jordanBlock D a ^ n) i j =
      if (i : ℕ) ≤ j ∧ (j : ℕ) - i ≤ n then
        (n.choose ((j : ℕ) - i) : ℂ) * a ^ (n - ((j : ℕ) - i)) else 0 := by
  have : NeZero D := ⟨by have := i.isLt; omega⟩
  rw [jordanBlock_pow]
  simp only [sum_apply, smul_apply, smul_eq_mul, nilpotentShift_pow_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ((j : ℕ) - i)]
    · simp [Nat.add_sub_of_le h.1]
    · intro k _ hk
      rw [ite_eq_right (by omega), mul_zero]
    · intro hk
      exact (hk (Finset.mem_range.mpr (by have := j.isLt; omega))).elim
  · apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    rw [ite_eq_right (by omega), mul_zero]

/-- Leading principal blocks commute with powers of a Jordan block. -/
theorem jordanBlock_pow_submatrix_castLE {D E : ℕ} (h : D ≤ E) (a : ℂ) (n : ℕ) :
    (jordanBlock E a ^ n).submatrix (Fin.castLE h) (Fin.castLE h) =
      jordanBlock D a ^ n := by
  ext i j
  simp [jordanBlock_pow_apply]

/-- Restriction to an injectively indexed principal submatrix is contractive. -/
theorem l2_opNorm_principal_submatrix_le {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix n n ℂ) (e : m → n) (he : Function.Injective e) :
    ‖A.submatrix e e‖ ≤ ‖A‖ := by
  let V : Matrix n m ℂ := (1 : Matrix n n ℂ).submatrix id e
  have hV : Vᴴ * V = 1 := by
    calc
      Vᴴ * V = V.submatrix e id := by
        simpa [V, conjTranspose_submatrix] using one_submatrix_mul e (Equiv.refl n) V
      _ = 1 := by simpa [V, submatrix_submatrix] using submatrix_one (α := ℂ) e he
  have hn : ‖V‖ ≤ 1 := l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one hV
  have hcompress : Vᴴ * A * V = A.submatrix e e := by
    calc
      Vᴴ * A * V = A.submatrix e id * V := by
        congr 1
        simpa [V, conjTranspose_submatrix] using one_submatrix_mul e (Equiv.refl n) A
      _ = A.submatrix e e := by
        simpa [V, submatrix_submatrix] using
          mul_submatrix_one (Equiv.refl n) e (A.submatrix e id)
  rw [← hcompress]
  calc
    ‖Vᴴ * A * V‖ ≤ ‖Vᴴ‖ * ‖A‖ * ‖V‖ :=
      (l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * ‖A‖ * 1 := by rw [l2_opNorm_conjTranspose]; gcongr
    _ = ‖A‖ := by ring

/-- Increasing the dimension of a Jordan block cannot decrease a power norm. -/
theorem l2_opNorm_jordanBlock_pow_mono_dim {D E : ℕ} (h : D ≤ E)
    (a : ℂ) (n : ℕ) : ‖jordanBlock D a ^ n‖ ≤ ‖jordanBlock E a ^ n‖ := by
  rw [← jordanBlock_pow_submatrix_castLE h a n]
  exact l2_opNorm_principal_submatrix_le _ _ (Fin.castLE_injective h)

private theorem jordanBlock_phase_intertwine (D : ℕ) (u r : ℂ) :
    jordanBlock D (u * r) * diagonal (fun i : Fin D ↦ u ^ (i : ℕ)) =
      diagonal (fun i : Fin D ↦ u ^ (i : ℕ)) * (u • jordanBlock D r) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [jordanBlock, nilpotentShift, mul_diagonal, diagonal_mul]
    ring
  · by_cases hs : (j : ℕ) = (i : ℕ) + 1
    · simp [jordanBlock, nilpotentShift, mul_diagonal, diagonal_mul,
        hij, hs, pow_succ]
    · simp [jordanBlock, nilpotentShift, mul_diagonal, diagonal_mul,
        hij, hs]

/-- Rotating the eigenvalue by a scalar of norm one preserves every power norm. -/
theorem l2_opNorm_jordanBlock_pow_phase (D : ℕ) (u r : ℂ) (hu : ‖u‖ = 1) (n : ℕ) :
    ‖jordanBlock D (u * r) ^ n‖ = ‖jordanBlock D r ^ n‖ := by
  let U := diagonal (fun i : Fin D ↦ u ^ (i : ℕ))
  have hU : U ∈ unitary (Matrix (Fin D) (Fin D) ℂ) := by
    apply mem_unitaryGroup_iff'.mpr
    change Uᴴ * U = 1
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    apply congrArg diagonal
    ext i
    simp only [Pi.star_apply, star_pow]
    rw [← mul_pow]
    simp [Complex.conj_mul', hu]
  have h : SemiconjBy U (u • jordanBlock D r) (jordanBlock D (u * r)) :=
    (jordanBlock_phase_intertwine D u r).symm
  have hp := h.pow_right n
  change U * (u • jordanBlock D r) ^ n = jordanBlock D (u * r) ^ n * U at hp
  calc
    ‖jordanBlock D (u * r) ^ n‖ = ‖jordanBlock D (u * r) ^ n * U‖ :=
      (CStarRing.norm_mul_mem_unitary _ hU).symm
    _ = ‖U * (u • jordanBlock D r) ^ n‖ := congrArg norm hp.symm
    _ = ‖jordanBlock D r ^ n‖ := by
      rw [CStarRing.norm_mem_unitary_mul _ hU, smul_pow, norm_smul, norm_pow, hu]
      simp

/-- A Jordan-block power norm depends only on the modulus of its eigenvalue. -/
theorem l2_opNorm_jordanBlock_pow_norm (D : ℕ) (a : ℂ) (n : ℕ) :
    ‖jordanBlock D a ^ n‖ = ‖jordanBlock D (‖a‖ : ℂ) ^ n‖ := by
  by_cases ha : a = 0
  · simp [ha]
  · have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hn : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hu : ‖a / (‖a‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        div_self hpos.ne']
    simpa [div_mul_cancel₀ _ hn] using
      l2_opNorm_jordanBlock_pow_phase D (a / (‖a‖ : ℂ)) (‖a‖ : ℂ) hu n

/-- Equal moduli and ordered dimensions give ordered power norms, including zero. -/
theorem l2_opNorm_jordanBlock_pow_le_of_norm_eq {D E : ℕ} (hDE : D ≤ E)
    (a b : ℂ) (hab : ‖a‖ = ‖b‖) (n : ℕ) :
    ‖jordanBlock D a ^ n‖ ≤ ‖jordanBlock E b ^ n‖ := by
  rw [l2_opNorm_jordanBlock_pow_norm D a, l2_opNorm_jordanBlock_pow_norm E b, hab]
  exact l2_opNorm_jordanBlock_pow_mono_dim hDE _ n

/-- A zero-eigenvalue block vanishes from its nilpotence index onward. -/
theorem jordanBlock_zero_pow_eq_zero (D : ℕ) [NeZero D] (n : ℕ) (hn : D ≤ n) :
    jordanBlock D 0 ^ n = 0 := by
  simpa [jordanBlock] using nilpotentShift_pow_eq_zero_of_ge_D D hn

private theorem jordanBlock_pow_le_polynomial_of_one_le_norm
    (D : ℕ) [NeZero D] (a : ℂ) (ha : 1 ≤ ‖a‖) (n : ℕ) (hn : D - 1 ≤ n) :
    ‖jordanBlock D a ^ n‖ ≤ (D : ℝ) * ‖a‖ ^ n * (n : ℝ) ^ (D - 1) := by
  have hterm : ∀ k ∈ Finset.range D,
      ‖a‖ ^ (n - k) * (n.choose k : ℝ) ≤ ‖a‖ ^ n * (n : ℝ) ^ (D - 1) := by
    intro k hk
    have hkD : k ≤ D - 1 := by rw [Finset.mem_range] at hk; omega
    have hp : (n : ℝ) ^ k ≤ (n : ℝ) ^ (D - 1) := by
      by_cases hD : D = 1
      · have hk0 : k = 0 := by omega
        simp [hD, hk0]
      · exact pow_right_mono₀ (by exact_mod_cast (by have := NeZero.pos D; omega : 1 ≤ n)) hkD
    have hc : (n.choose k : ℝ) ≤ (n : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow n k
    exact mul_le_mul (pow_right_mono₀ ha (Nat.sub_le n k)) (hc.trans hp)
      (by positivity) (by positivity)
  calc
    ‖jordanBlock D a ^ n‖ ≤ ∑ k ∈ Finset.range D,
        ‖a‖ ^ (n - k) * (n.choose k : ℝ) := by
      simpa [min_eq_right hn, Nat.sub_add_cancel (NeZero.pos D)] using
        l2_opNorm_jordanBlock_pow_le D a n
    _ ≤ ∑ _k ∈ Finset.range D, ‖a‖ ^ n * (n : ℝ) ^ (D - 1) :=
      Finset.sum_le_sum hterm
    _ = (D : ℝ) * ‖a‖ ^ n * (n : ℝ) ^ (D - 1) := by simp [mul_assoc]

/-- A block of smaller modulus is eventually strictly smaller
in norm, regardless of the two positive block dimensions. This is the
comparison used at Wolf Chapter 8, lines 1255--1256. It also holds outside
the unit disc. The smaller eigenvalue may be zero. -/
theorem eventually_l2_opNorm_jordanBlock_pow_lt_of_norm_lt
    (D E : ℕ) [NeZero D] [NeZero E] (a b : ℂ)
    (hab : ‖a‖ < ‖b‖) :
    ∀ᶠ n : ℕ in atTop, ‖jordanBlock D a ^ n‖ < ‖jordanBlock E b ^ n‖ := by
  have hb : 0 < ‖b‖ := (norm_nonneg a).trans_lt hab
  have hlower (n : ℕ) : ‖b‖ ^ n ≤ ‖jordanBlock E b ^ n‖ := by
    simpa using le_l2_opNorm_jordanBlock_pow E b n 0 (by omega)
  by_cases ha : a = 0
  · filter_upwards [eventually_ge_atTop D] with n hn
    rw [ha, jordanBlock_zero_pow_eq_zero D n hn, norm_zero]
    exact (pow_pos hb n).trans_le (hlower n)
  · have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr ha
    obtain ⟨C, hC, hupper⟩ : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, D - 1 ≤ n →
        ‖jordanBlock D a ^ n‖ ≤ C * ‖a‖ ^ n * (n : ℝ) ^ (D - 1) := by
      by_cases ha1 : ‖a‖ ≤ 1
      · exact ⟨(D : ℝ) * (‖a‖⁻¹) ^ (D - 1),
          mul_pos (by exact_mod_cast NeZero.pos D) (pow_pos (inv_pos.mpr ha0) _),
          fun n hn ↦ l2_opNorm_jordanBlock_pow_le_polynomial D a n ha0 ha1 hn⟩
      · exact ⟨(D : ℝ), by exact_mod_cast NeZero.pos D,
          fun n hn ↦ jordanBlock_pow_le_polynomial_of_one_le_norm D a (le_of_not_ge ha1) n hn⟩
    have hsmall : (fun n : ℕ ↦ (n : ℝ) ^ (D - 1) * ‖a‖ ^ n) =o[atTop]
        (fun n : ℕ ↦ ‖b‖ ^ n) :=
      isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt (D - 1)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)] using hab)
    have heps : 0 < C⁻¹ / 2 := by positivity
    filter_upwards [hsmall.bound heps, eventually_ge_atTop (D - 1)] with n hsmall hn
    have hs : (n : ℝ) ^ (D - 1) * ‖a‖ ^ n ≤ C⁻¹ / 2 * ‖b‖ ^ n := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ (n : ℝ) ^ (D - 1) * ‖a‖ ^ n),
        abs_of_nonneg (pow_nonneg (norm_nonneg b) n)] using hsmall
    have hu : ‖jordanBlock D a ^ n‖ ≤ C * ((n : ℝ) ^ (D - 1) * ‖a‖ ^ n) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hupper n hn
    have heq : C * (C⁻¹ / 2 * ‖b‖ ^ n) = ‖b‖ ^ n / 2 := by
      field_simp
    calc
      ‖jordanBlock D a ^ n‖ ≤ C * ((n : ℝ) ^ (D - 1) * ‖a‖ ^ n) := hu
      _ ≤ C * (C⁻¹ / 2 * ‖b‖ ^ n) := mul_le_mul_of_nonneg_left hs hC.le
      _ = ‖b‖ ^ n / 2 := heq
      _ < ‖b‖ ^ n := by linarith [pow_pos hb n]
      _ ≤ ‖jordanBlock E b ^ n‖ := hlower n

end Matrix
