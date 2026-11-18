/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Algorithm.QFT
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The amplitudes of phase estimation

The outcome `k` of phase estimation on `t` qubits with the phase `φ` has the amplitude
`αₖ = 2^{-t} ∑_{j < 2^t} e^{2πi j (φ - k/2^t)}` (Nielsen–Chuang, eq. (5.24)): it is the inverse
Fourier transform of `2^{-t/2} e^{2πiφ⟨x⟩}`, so the `|αₖ|²` sum to `1`. The outcomes farther than
`2^{-n}` from `φ` modulo `1` have total probability at most `1/(2(2^{t-n} - 1))`
(Nielsen–Chuang, eqs. (5.26)–(5.34)). This uses `|e^{2πix} - 1| ≥ 4|x - r|` for `|x - r| ≤ 1/2`,
which bounds `|αₖ|` by `1/(2|ℓ - δ|)` when `2^t φ - k ≡ δ - ℓ` with `0 ≤ δ < 1`, and
`∑_{a ≥ M} 1/a² ≤ 1/(M - 1)` on each side.

## Main definitions

* `QuantumCircuit.PhaseEstimation.amplitude` — the amplitude of an outcome.

## Main results

* `QuantumCircuit.PhaseEstimation.dft_conjTranspose_mulVec` — the amplitudes are an inverse
  Fourier transform.
* `QuantumCircuit.PhaseEstimation.sum_norm_sq_amplitude` — the probabilities sum to `1`.
* `QuantumCircuit.PhaseEstimation.one_sub_le_sum_norm_sq_amplitude` — the outcomes within `2^{-n}`
  of `φ` have total probability at least `1 - ε` for `t = n + ⌈log₂(2 + 1/(2ε))⌉`.
-/

open Matrix ManyBody Complex
open QuantumCircuit.Qubit (Q encode dft)

namespace QuantumCircuit

namespace PhaseEstimation

variable {t : ℕ}

/-- The amplitude `2^{-t} ∑_{j < 2^t} e^{2πi j (φ - k/2^t)}` of the outcome `k` (Nielsen–Chuang,
eq. (5.24)). -/
noncomputable def amplitude (t : ℕ) (φ : ℝ) (k : Fin (2 ^ t)) : ℂ :=
  (2 ^ t : ℂ)⁻¹ * ∑ j : Fin (2 ^ t), exp (2 * Real.pi * I * j * (φ - k / 2 ^ t))

/-- The inverse Fourier transform of `2^{-t/2} e^{2πiφ⟨x⟩}` has the amplitudes `αₖ`. -/
theorem dft_conjTranspose_mulVec (φ : ℝ) (y : Config (Q t)) :
    ((dft t)ᴴ *ᵥ fun x ↦ invSqrtTwo ^ t * exp (2 * Real.pi * I * φ) ^ (encode t x : ℕ)) y =
      amplitude t φ (encode t y) := by
  rw [mulVec, dotProduct, amplitude, ← (encode t).symm.sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hstar : star (invSqrtTwo ^ t) = invSqrtTwo ^ t := by simp
  simp only [conjTranspose_apply, dft, of_apply, star_mul', hstar, Equiv.apply_symm_apply,
    Complex.star_def, ← Complex.exp_conj, ← Complex.exp_nat_mul]
  rw [mul_mul_mul_comm, ← Complex.exp_add, ← mul_pow, invSqrtTwo_mul_self, inv_pow]
  congr 2
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_pow,
    map_natCast]
  ring

/-- The squared norm of a vector as the dot product with its conjugate. -/
theorem ofReal_sum_norm_sq {n : Type} [Fintype n] (w : n → ℂ) :
    ((∑ y, ‖w y‖ ^ 2 : ℝ) : ℂ) = star w ⬝ᵥ w := by
  rw [dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem sum_norm_sq_mulVec {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : Mᴴ * M = 1) (v : n → ℂ) : ∑ y, ‖(M *ᵥ v) y‖ ^ 2 = ∑ x, ‖v x‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [ofReal_sum_norm_sq, ofReal_sum_norm_sq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    hM, one_mulVec]

private theorem norm_invSqrtTwo_sq : ‖invSqrtTwo‖ ^ 2 = 2⁻¹ := by
  rw [invSqrtTwo, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num)]

/-- The probabilities of the outcomes sum to `1`. -/
theorem sum_norm_sq_amplitude (φ : ℝ) : ∑ k, ‖amplitude t φ k‖ ^ 2 = 1 := by
  have hU : ((dft t)ᴴ)ᴴ * (dft t)ᴴ = 1 := by
    rw [conjTranspose_conjTranspose]
    exact mem_unitaryGroup_iff.mp (Qubit.dft_mem_unitaryGroup t)
  rw [← (encode t).sum_comp]
  simp only [← dft_conjTranspose_mulVec]
  rw [sum_norm_sq_mulVec hU]
  have h : ∀ x : Config (Q t), ‖invSqrtTwo ^ t * exp (2 * Real.pi * I * φ) ^ (encode t x : ℕ)‖ ^ 2
      = (2 ^ t : ℝ)⁻¹ := fun x ↦ by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    rw [show ((2 * Real.pi - 0 * 0) * 0 - (2 * 0 + 0 * Real.pi) * 1) * φ -
      ((2 * Real.pi - 0 * 0) * 1 + (2 * 0 + 0 * Real.pi) * 0) * 0 = 0 by ring, Real.exp_zero,
      one_pow, mul_one, ← pow_mul, mul_comm t 2, pow_mul, norm_invSqrtTwo_sq,
      inv_pow]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ]
  push_cast
  exact mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero)
/-- Jordan's inequality on the circle: `|e^{2πix} - 1| ≥ 4|x - r|` when `|x - r| ≤ 1/2`. -/
private theorem four_mul_le_norm (x : ℝ) (r : ℤ) (hr : |x - r| ≤ 1 / 2) :
    4 * |x - r| ≤ ‖exp (2 * Real.pi * I * x) - 1‖ := by
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * x)
  rw [show I * ((2 * Real.pi * x : ℝ) : ℂ) = 2 * Real.pi * I * x by push_cast; ring] at h
  rw [h, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two,
    show 2 * Real.pi * x / 2 = Real.pi * (x - r) + r * Real.pi by ring, Real.sin_add_int_mul_pi,
    abs_mul, abs_neg_one_zpow, one_mul]
  have hy : |Real.sin (Real.pi * (x - r))| = Real.sin (Real.pi * |x - r|) := by
    rcases le_total 0 (x - r) with h0 | h0
    · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
        (by positivity) (by nlinarith [Real.pi_pos, abs_of_nonneg h0 ▸ hr]))]
    · rw [abs_of_nonpos h0, show Real.pi * (x - r) = -(Real.pi * -(x - r)) by ring,
        Real.sin_neg, abs_neg, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos, abs_of_nonpos h0 ▸ hr]))]
  rw [hy]
  have := Real.mul_le_sin (x := Real.pi * |x - r|) (by positivity)
    (by nlinarith [Real.pi_pos])
  rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ Real.pi_ne_zero] at this
  linarith

/-- The geometric series bound `|αₖ| ≤ 1/(2^{t+1} |φ - k/2^t - r|)` (Nielsen–Chuang, eq. (5.29)). -/
private theorem norm_amplitude_le (t : ℕ) (φ : ℝ) (k : Fin (2 ^ t)) (r : ℤ)
    (hr : |φ - k / 2 ^ t - r| ≤ 1 / 2) (hpos : 0 < |φ - k / 2 ^ t - r|) :
    ‖amplitude t φ k‖ ≤ 1 / (2 * 2 ^ t * |φ - k / 2 ^ t - r|) := by
  set x : ℝ := φ - k / 2 ^ t
  set z := exp (2 * Real.pi * I * x)
  have hz : 4 * |x - r| ≤ ‖z - 1‖ := four_mul_le_norm x r hr
  have hz1 : z ≠ 1 := fun h ↦ by
    rw [h, sub_self, norm_zero] at hz; linarith
  have hnorm : ‖z‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hsum : ∑ j : Fin (2 ^ t), exp (2 * Real.pi * I * j * (φ - k / 2 ^ t)) =
      ∑ j ∈ Finset.range (2 ^ t), z ^ j := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ exp (2 * Real.pi * I * j * (φ - k / 2 ^ t)))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Complex.exp_nat_mul]
    congr 1
    simp only [x]
    push_cast
    ring
  rw [amplitude, hsum, geom_sum_eq hz1, norm_mul, norm_div, norm_inv, norm_pow, Complex.norm_two]
  have hnum : ‖z ^ 2 ^ t - 1‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by rw [norm_pow, hnorm]; simp; norm_num)
  have hden : 0 < ‖z - 1‖ := by linarith
  calc (2 ^ t)⁻¹ * (‖z ^ 2 ^ t - 1‖ / ‖z - 1‖) ≤ (2 ^ t)⁻¹ * (2 / (4 * |x - r|)) := by
        gcongr
    _ = 1 / (2 * 2 ^ t * |x - r|) := by field_simp; ring

/-- `∑ 1/a² ≤ 1/(M-1)` over finitely many integers `a ≥ M`. -/
private theorem sum_inv_sq_le {M : ℤ} (hM : 2 ≤ M) (S : Finset ℤ) (hS : ∀ a ∈ S, M ≤ a) :
    ∑ a ∈ S, 1 / (a : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) := by
  have hM' : (1 : ℝ) ≤ M - 1 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  suffices h : ∀ c : ℤ, M - 1 ≤ c → (∀ a ∈ S, a ≤ c) →
      ∑ a ∈ S, 1 / (a : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) - 1 / c by
    have hc : M - 1 ≤ M - 1 + ∑ a ∈ S, |a| :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    have hpos : (0 : ℝ) < ((M - 1 + ∑ a ∈ S, |a| : ℤ) : ℝ) := by
      have : ((M - 1 : ℤ) : ℝ) ≤ ((M - 1 + ∑ a ∈ S, |a| : ℤ) : ℝ) := by exact_mod_cast hc
      push_cast at this ⊢
      linarith
    refine (h _ hc fun a ha ↦ ?_).trans (sub_le_self _ (by positivity))
    have h1 : a ≤ ∑ a ∈ S, |a| :=
      (le_abs_self a).trans (Finset.single_le_sum (f := fun a ↦ |a|)
        (fun _ _ ↦ abs_nonneg _) ha)
    linarith
  induction S using Finset.induction_on_max with
  | empty =>
    intro c hc _
    have : ((M : ℝ) - 1) ≤ c := by exact_mod_cast hc
    rw [Finset.sum_empty, sub_nonneg]
    exact one_div_le_one_div_of_le (by linarith) this
  | insert a S ha ih =>
    intro c hc hle
    have haM : M ≤ a := hS a (Finset.mem_insert_self a S)
    have hac : a ≤ c := hle a (Finset.mem_insert_self a S)
    have ih' := ih (fun x hx ↦ hS x (Finset.mem_insert_of_mem hx)) (a - 1) (by omega)
      fun x hx ↦ by have := ha x hx; omega
    rw [Finset.sum_insert fun h ↦ lt_irrefl a (ha a h)]
    have ha1 : (1 : ℝ) ≤ (a : ℝ) - 1 := by
      have : (M : ℝ) ≤ a := by exact_mod_cast haM
      linarith
    have hac' : (a : ℝ) ≤ c := by exact_mod_cast hac
    push_cast at ih'
    have key : 1 / (a : ℝ) ^ 2 ≤ 1 / ((a : ℝ) - 1) - 1 / a := by
      rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by nlinarith)
        (by nlinarith)]
      nlinarith
    have : 1 / (c : ℝ) ≤ 1 / a := one_div_le_one_div_of_le (by linarith) hac'
    linarith

/-- The outcomes farther than `2^{-n}` from `φ` modulo `1` have total probability at most
`1/(2(2^{t-n} - 1))` (Nielsen–Chuang, eqs. (5.30)–(5.34)). -/
private theorem sum_norm_sq_amplitude_far_le (t n : ℕ) (hn : n ≤ t) (hM : 2 ≤ 2 ^ (t - n)) (φ : ℝ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin (2 ^ t) ↦
        ¬ |(k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)| ≤ 1 / 2 ^ n),
      ‖amplitude t φ k‖ ^ 2 ≤ 1 / (2 * ((2 : ℝ) ^ (t - n) - 1)) := by
  set bad := Finset.univ.filter (fun k : Fin (2 ^ t) ↦
    ¬ |(k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)| ≤ 1 / 2 ^ n)
  have hN : (0 : ℝ) < 2 ^ t := by positivity
  set δ := Int.fract ((2 : ℝ) ^ t * φ)
  have hδ0 : 0 ≤ δ := Int.fract_nonneg _
  have hδ1 : δ < 1 := Int.fract_lt_one _
  set R : Fin (2 ^ t) → ℤ := fun k ↦ round ((k : ℝ) / 2 ^ t - φ)
  set m : Fin (2 ^ t) → ℤ := fun k ↦ (k : ℤ) - ⌊(2 : ℝ) ^ t * φ⌋ - 2 ^ t * R k
  have hm : ∀ k : Fin (2 ^ t), (2 : ℝ) ^ t * ((k : ℝ) / 2 ^ t - φ - R k) = m k - δ := by
    intro k
    simp only [m, δ, Int.fract]
    push_cast
    field_simp
    ring
  set M : ℝ := (2 : ℝ) ^ (t - n)
  have hMN : (2 : ℝ) ^ t / 2 ^ n = M := by
    rw [div_eq_iff (by positivity), ← pow_add, Nat.sub_add_cancel hn]
  have hbad : ∀ k ∈ bad, M < |(m k : ℝ) - δ| := by
    intro k hk
    have hk := (Finset.mem_filter.mp hk).2
    push Not at hk
    rw [← hm, abs_mul, abs_of_pos hN, ← hMN]
    rw [div_eq_mul_one_div]
    exact mul_lt_mul_of_pos_left hk hN
  have hamp : ∀ k ∈ bad, ‖amplitude t φ k‖ ^ 2 ≤ 1 / (4 * ((m k : ℝ) - δ) ^ 2) := by
    intro k hk
    have hd : |φ - k / 2 ^ t - ((-R k : ℤ) : ℝ)| = |(k : ℝ) / 2 ^ t - φ - R k| := by
      rw [← abs_neg]; push_cast; ring_nf
    have hd2 : |(k : ℝ) / 2 ^ t - φ - R k| ≤ 1 / 2 := abs_sub_round _
    have hMpos : 0 < M := by positivity
    have hdpos : 0 < |(k : ℝ) / 2 ^ t - φ - R k| := by
      have := hbad k hk
      rw [← hm, abs_mul, abs_of_pos hN] at this
      exact pos_of_mul_pos_right (hMpos.trans this) hN.le
    have h := norm_amplitude_le t φ k (-R k) (hd ▸ hd2) (hd ▸ hdpos)
    rw [hd, mul_assoc, ← abs_of_pos hN, ← abs_mul, abs_of_pos hN, hm] at h
    calc ‖amplitude t φ k‖ ^ 2 ≤ (1 / (2 * |(m k : ℝ) - δ|)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = 1 / (4 * ((m k : ℝ) - δ) ^ 2) := by
          rw [div_pow, mul_pow, sq_abs]; norm_num
  have hinj : Set.InjOn m bad := by
    intro k hk k' hk' h
    have h' : ((k : ℕ) : ℤ) - k' = 2 ^ t * (R k - R k') := by
      simp only [m] at h; linarith
    have hk1 : ((k : ℕ) : ℤ) < 2 ^ t := by exact_mod_cast k.2
    have hk2 : ((k' : ℕ) : ℤ) < 2 ^ t := by exact_mod_cast k'.2
    have hk3 : (0 : ℤ) ≤ ((k : ℕ) : ℤ) := by positivity
    have hk4 : (0 : ℤ) ≤ ((k' : ℕ) : ℤ) := by positivity
    have hlt : |((k : ℕ) : ℤ) - k'| < 2 ^ t := by
      rw [abs_lt]; constructor <;> linarith
    have hzero : R k - R k' = 0 := by
      by_contra hne
      have : (2 : ℤ) ^ t ≤ |((k : ℕ) : ℤ) - k'| := by
        rw [h', abs_mul, abs_of_pos (by positivity)]
        exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hne)
      linarith
    rw [hzero, mul_zero, sub_eq_zero] at h'
    exact Fin.ext (by exact_mod_cast h')
  set T := bad.image m
  have hT : ∀ ℓ ∈ T, M < |(ℓ : ℝ) - δ| := by
    intro ℓ hℓ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hℓ
    exact hbad k hk
  have hMint : (2 : ℤ) ≤ 2 ^ (t - n) := by exact_mod_cast hM
  have hMcast : ((2 ^ (t - n) : ℤ) : ℝ) = M := by push_cast; rfl
  have hpos : ∀ ℓ ∈ T.filter (1 ≤ ·), 2 ^ (t - n) ≤ ℓ - 1 ∧
      1 / (4 * ((ℓ : ℝ) - δ) ^ 2) ≤ 1 / 4 * (1 / (((ℓ - 1 : ℤ) : ℝ)) ^ 2) := by
    intro ℓ hℓ
    obtain ⟨hℓT, hℓ1⟩ := Finset.mem_filter.mp hℓ
    have h := hT ℓ hℓT
    have hℓ1' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
    rw [abs_of_pos (by linarith)] at h
    have hlt : ((2 ^ (t - n) : ℤ) : ℝ) < ℓ := by rw [hMcast]; linarith
    have hlt' : (2 : ℤ) ^ (t - n) < ℓ := by exact_mod_cast hlt
    refine ⟨by omega, ?_⟩
    have h2 : (2 : ℝ) ≤ ((ℓ - 1 : ℤ) : ℝ) := by
      have : (2 : ℤ) ≤ ℓ - 1 := by omega
      exact_mod_cast this
    push_cast at h2 ⊢
    rw [one_div_mul_one_div]
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith) (by linarith) 2) (by norm_num))
  have hneg : ∀ ℓ ∈ T.filter (¬ 1 ≤ ·), 2 ^ (t - n) ≤ -ℓ ∧
      1 / (4 * ((ℓ : ℝ) - δ) ^ 2) ≤ 1 / 4 * (1 / (((-ℓ : ℤ) : ℝ)) ^ 2) := by
    intro ℓ hℓ
    obtain ⟨hℓT, hℓ0⟩ := Finset.mem_filter.mp hℓ
    have h := hT ℓ hℓT
    have hℓ0' : (ℓ : ℝ) ≤ 0 := by exact_mod_cast (show ℓ ≤ 0 by omega)
    rw [abs_of_nonpos (by linarith)] at h
    have hlt : ((2 ^ (t - n) : ℤ) : ℝ) - 1 < ((-ℓ : ℤ) : ℝ) := by
      rw [hMcast]; push_cast; linarith
    have hlt' : (2 : ℤ) ^ (t - n) - 1 < -ℓ := by exact_mod_cast hlt
    refine ⟨by omega, ?_⟩
    have h2 : (2 : ℝ) ≤ ((-ℓ : ℤ) : ℝ) := by
      have : (2 : ℤ) ≤ -ℓ := by omega
      exact_mod_cast this
    push_cast at h2 ⊢
    rw [one_div_mul_one_div]
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left
      (by nlinarith) (by norm_num))
  have hsub : ∀ ℓ ∈ T.filter (1 ≤ ·), ∀ ℓ' ∈ T.filter (1 ≤ ·), ℓ - 1 = ℓ' - 1 → ℓ = ℓ' :=
    fun _ _ _ _ h ↦ by omega
  have hnegi : ∀ ℓ ∈ T.filter (¬ 1 ≤ ·), ∀ ℓ' ∈ T.filter (¬ 1 ≤ ·), -ℓ = -ℓ' → ℓ = ℓ' :=
    fun _ _ _ _ h ↦ by omega
  have hP := sum_inv_sq_le hMint ((T.filter (1 ≤ ·)).image (· - 1)) fun a ha ↦ by
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp ha
    exact (hpos ℓ hℓ).1
  have hQ := sum_inv_sq_le hMint ((T.filter (¬ 1 ≤ ·)).image (- ·)) fun a ha ↦ by
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp ha
    exact (hneg ℓ hℓ).1
  rw [Finset.sum_image hsub] at hP
  rw [Finset.sum_image hnegi] at hQ
  rw [hMcast] at hP hQ
  calc ∑ k ∈ bad, ‖amplitude t φ k‖ ^ 2 ≤ ∑ k ∈ bad, 1 / (4 * ((m k : ℝ) - δ) ^ 2) :=
        Finset.sum_le_sum hamp
    _ = ∑ ℓ ∈ T, 1 / (4 * ((ℓ : ℝ) - δ) ^ 2) :=
        (Finset.sum_image (f := fun ℓ : ℤ ↦ 1 / (4 * ((ℓ : ℝ) - δ) ^ 2)) hinj).symm
    _ = ∑ ℓ ∈ T.filter (1 ≤ ·), 1 / (4 * ((ℓ : ℝ) - δ) ^ 2) +
        ∑ ℓ ∈ T.filter (¬ 1 ≤ ·), 1 / (4 * ((ℓ : ℝ) - δ) ^ 2) :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ ∑ ℓ ∈ T.filter (1 ≤ ·), 1 / 4 * (1 / (((ℓ - 1 : ℤ) : ℝ)) ^ 2) +
        ∑ ℓ ∈ T.filter (¬ 1 ≤ ·), 1 / 4 * (1 / (((-ℓ : ℤ) : ℝ)) ^ 2) :=
        add_le_add (Finset.sum_le_sum fun ℓ hℓ ↦ (hpos ℓ hℓ).2)
          (Finset.sum_le_sum fun ℓ hℓ ↦ (hneg ℓ hℓ).2)
    _ ≤ 1 / 4 * (1 / (M - 1)) + 1 / 4 * (1 / (M - 1)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        gcongr
    _ = 1 / (2 * (M - 1)) := by
        have : M - 1 ≠ 0 := by
          have : (2 : ℝ) ≤ M := by rw [← hMcast]; exact_mod_cast hMint
          linarith
        field_simp
        ring

/-- With `t = n + ⌈log₂(2 + 1/(2ε))⌉`, the outcomes within `2^{-n}` of `φ` modulo `1` have total
probability at least `1 - ε` (Nielsen–Chuang, eq. (5.35)). -/
theorem one_sub_le_sum_norm_sq_amplitude (φ : ℝ) (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (ht : t = n + ⌈Real.logb 2 (2 + 1 / (2 * ε))⌉₊) :
    1 - ε ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin (2 ^ t) ↦
        |(k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)| ≤ 1 / 2 ^ n),
      ‖amplitude t φ k‖ ^ 2 := by
  set p := ⌈Real.logb 2 (2 + 1 / (2 * ε))⌉₊
  have hp : 2 + 1 / (2 * ε) ≤ (2 : ℝ) ^ p := by
    have hy : 0 < 2 + 1 / (2 * ε) := by positivity
    calc 2 + 1 / (2 * ε) = (2 : ℝ) ^ Real.logb 2 (2 + 1 / (2 * ε)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hy).symm
      _ ≤ (2 : ℝ) ^ (p : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = 2 ^ p := Real.rpow_natCast _ _
  have htn : t - n = p := by omega
  have hM : 2 ≤ 2 ^ (t - n) := by
    rw [htn]
    have : (2 : ℝ) < 2 ^ p := by
      have : 0 < 1 / (2 * ε) := by positivity
      linarith
    exact_mod_cast this.le
  have hbad := sum_norm_sq_amplitude_far_le t n (by omega) hM φ
  have hε' : 1 / (2 * ((2 : ℝ) ^ (t - n) - 1)) ≤ ε := by
    rw [htn, div_le_iff₀ (by nlinarith [show 0 < 1 / (2 * ε) by positivity])]
    have : 1 / (2 * ε) * (2 * ε) = 1 := by field_simp
    nlinarith
  have hall := sum_norm_sq_amplitude (t := t) φ
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin (2 ^ t) ↦
    |(k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)| ≤ 1 / 2 ^ n)] at hall
  linarith

end PhaseEstimation

end QuantumCircuit
