/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.DoubledSystemGap
import QICLean.Circuit.Algorithm.QFT
import Mathlib.Analysis.PSeries
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
`∑_{a ≥ M} 1/a² ≤ 1/(M - 1)` on each side. The bound is slightly sharper than Nielsen–Chuang's
`1/(2(e - 1))` with `e = 2^{t-n} - 1`, eq. (5.34), which spends one more unit of `e` on each side.

## Main definitions

* `QuantumCircuit.PhaseEstimation.amplitude` — the amplitude of an outcome.

## Main results

* `QuantumCircuit.PhaseEstimation.dft_conjTranspose_mulVec` — the amplitudes are an inverse
  Fourier transform.
* `QuantumCircuit.PhaseEstimation.amplitude_eq_geom_sum` — an amplitude is a geometric sum.
* `QuantumCircuit.PhaseEstimation.sum_norm_sq_amplitude` — the probabilities sum to `1`.
* `QuantumCircuit.PhaseEstimation.one_sub_le_sum_norm_sq_amplitude` — the outcomes within `2^{-n}`
  of `φ` have total probability at least `1 - ε` for `t = n + ⌈log₂(2 + 1/(2ε))⌉`.
-/

open Matrix ManyBody Complex
open QuantumCircuit.Qubit (encode dft)

namespace QuantumCircuit

namespace PhaseEstimation

variable {t : ℕ}

/-- The amplitude `2^{-t} ∑_{j < 2^t} e^{2πi j (φ - k/2^t)}` of the outcome `k` (Nielsen–Chuang,
eq. (5.24)). -/
noncomputable def amplitude (t : ℕ) (φ : ℝ) (k : Fin (2 ^ t)) : ℂ :=
  (2 ^ t : ℂ)⁻¹ * ∑ j : Fin (2 ^ t), exp (2 * Real.pi * I * j * (φ - k / 2 ^ t))

/-- The amplitude is the geometric sum `αₖ = 2^{-t} ∑_{j < 2^t} z^j` with
`z = e^{2πi(φ - k/2^t)}`. -/
theorem amplitude_eq_geom_sum (t : ℕ) (φ : ℝ) (k : Fin (2 ^ t)) :
    amplitude t φ k =
      (2 ^ t : ℂ)⁻¹ * ∑ j ∈ Finset.range (2 ^ t), exp (2 * Real.pi * I * (φ - k / 2 ^ t)) ^ j := by
  rw [amplitude, Fin.sum_univ_eq_sum_range (fun j ↦ exp (2 * Real.pi * I * j * (φ - k / 2 ^ t)))]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- `|e^{2πix}| = 1` for real `x`. -/
private theorem norm_exp_two_pi_I_mul (x : ℝ) : ‖exp (2 * Real.pi * I * x)‖ = 1 := by
  rw [show 2 * Real.pi * I * x = ((2 * Real.pi * x : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The inverse Fourier transform of `2^{-t/2} e^{2πiφ⟨x⟩}` has the amplitudes `αₖ`. -/
theorem dft_conjTranspose_mulVec (φ : ℝ) (y : Config (Qudits (Fin t) 2)) :
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

/-- The probabilities of the outcomes sum to `1`. -/
theorem sum_norm_sq_amplitude (φ : ℝ) : ∑ k, ‖amplitude t φ k‖ ^ 2 = 1 := by
  set v : Config (Qudits (Fin t) 2) → ℂ := fun x ↦ invSqrtTwo ^ t * exp (2 * Real.pi * I * φ) ^ (encode t x : ℕ)
  have hv := congrArg (· ^ 2)
    (norm_toLp_mulVec_of_unitary (Unitary.star_mem (Qubit.dft_mem_unitaryGroup t)) v)
  simp only [EuclideanSpace.norm_sq_eq, star_eq_conjTranspose] at hv
  rw [← (encode t).sum_comp]
  simp only [← dft_conjTranspose_mulVec]
  rw [hv]
  have h : ∀ x, ‖v x‖ ^ 2 = (2 ^ t : ℝ)⁻¹ := fun x ↦ by
    rw [norm_mul, norm_pow, norm_pow, norm_exp_two_pi_I_mul, one_pow, mul_one, ← pow_mul,
      mul_comm t 2, pow_mul, norm_invSqrtTwo_sq, inv_pow]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_pi,
    Fintype.card_fin, Finset.prod_const]
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
  have h := Real.mul_abs_le_abs_sin (x := Real.pi * (x - r))
    (by rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [Real.pi_pos])
  rw [abs_mul, abs_of_pos Real.pi_pos, ← mul_assoc, div_mul_cancel₀ _ Real.pi_ne_zero] at h
  linarith

/-- The geometric series bound `|αₖ| ≤ 1/(2^{t+1} |φ - k/2^t - r|)` (Nielsen–Chuang, eq. (5.29)). -/
private theorem norm_amplitude_le (t : ℕ) (φ : ℝ) (k : Fin (2 ^ t)) (r : ℤ)
    (hr : |φ - k / 2 ^ t - r| ≤ 1 / 2) (hpos : 0 < |φ - k / 2 ^ t - r|) :
    ‖amplitude t φ k‖ ≤ 1 / (2 * 2 ^ t * |φ - k / 2 ^ t - r|) := by
  set x : ℝ := φ - k / 2 ^ t
  have hx : ((x : ℝ) : ℂ) = φ - k / 2 ^ t := by push_cast [x]; ring
  rw [amplitude_eq_geom_sum, ← hx]
  set z := exp (2 * Real.pi * I * x)
  have hz : 4 * |x - r| ≤ ‖z - 1‖ := four_mul_le_norm x r hr
  have hz1 : z ≠ 1 := fun h ↦ by
    rw [h, sub_self, norm_zero] at hz; linarith
  have hnorm : ‖z‖ = 1 := norm_exp_two_pi_I_mul x
  rw [geom_sum_eq hz1, norm_mul, norm_div, norm_inv, norm_pow, Complex.norm_two]
  have hnum : ‖z ^ 2 ^ t - 1‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by rw [norm_pow, hnorm]; simp; norm_num)
  have hden : 0 < ‖z - 1‖ := by linarith
  calc (2 ^ t)⁻¹ * (‖z ^ 2 ^ t - 1‖ / ‖z - 1‖) ≤ (2 ^ t)⁻¹ * (2 / (4 * |x - r|)) := by
        gcongr
    _ = 1 / (2 * 2 ^ t * |x - r|) := by field_simp; ring

/-- The integer `ℓ` with `2^t (k/2^t - φ - r) = ℓ - δ`, where `r` is the integer nearest to
`k/2^t - φ` and `δ` the fractional part of `2^t φ`. -/
private noncomputable def offset (t : ℕ) (φ : ℝ) (k : Fin (2 ^ t)) : ℤ :=
  (k : ℤ) - ⌊(2 : ℝ) ^ t * φ⌋ - 2 ^ t * round ((k : ℝ) / 2 ^ t - φ)

private theorem two_pow_mul_sub_round (t : ℕ) (φ : ℝ) (k : Fin (2 ^ t)) :
    (2 : ℝ) ^ t * ((k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)) =
      offset t φ k - Int.fract ((2 : ℝ) ^ t * φ) := by
  simp only [offset, Int.fract]
  push_cast
  field_simp
  ring

/-- The bound `|αₖ|² ≤ 1/(4(ℓ - δ)²)` of an outcome (Nielsen–Chuang, eq. (5.29)). -/
private theorem norm_sq_amplitude_le_offset (t : ℕ) (φ : ℝ) (k : Fin (2 ^ t))
    (hk : 0 < |(offset t φ k : ℝ) - Int.fract ((2 : ℝ) ^ t * φ)|) :
    ‖amplitude t φ k‖ ^ 2 ≤ (4 * ((offset t φ k : ℝ) - Int.fract ((2 : ℝ) ^ t * φ)) ^ 2)⁻¹ := by
  have hN : (0 : ℝ) < 2 ^ t := by positivity
  set R := round ((k : ℝ) / 2 ^ t - φ)
  have hd : |φ - k / 2 ^ t - ((-R : ℤ) : ℝ)| = |(k : ℝ) / 2 ^ t - φ - R| := by
    rw [← abs_neg]; push_cast; ring_nf
  have hd2 : |(k : ℝ) / 2 ^ t - φ - R| ≤ 1 / 2 := abs_sub_round _
  have hm := two_pow_mul_sub_round t φ k
  have hdpos : 0 < |(k : ℝ) / 2 ^ t - φ - R| := by
    rw [← hm, abs_mul, abs_of_pos hN] at hk
    exact pos_of_mul_pos_right hk hN.le
  have h := norm_amplitude_le t φ k (-R) (hd ▸ hd2) (hd ▸ hdpos)
  rw [hd, mul_assoc, ← abs_of_pos hN, ← abs_mul, abs_of_pos hN, hm] at h
  calc ‖amplitude t φ k‖ ^ 2
      ≤ (1 / (2 * |(offset t φ k : ℝ) - Int.fract ((2 : ℝ) ^ t * φ)|)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by rw [div_pow, mul_pow, sq_abs]; norm_num

/-- Distinct outcomes have distinct offsets. -/
private theorem offset_injective (t : ℕ) (φ : ℝ) : Function.Injective (offset t φ) := by
  intro k k' h
  have h' : ((k : ℕ) : ℤ) - k' =
      2 ^ t * (round ((k : ℝ) / 2 ^ t - φ) - round ((k' : ℝ) / 2 ^ t - φ)) := by
    simp only [offset] at h; linarith
  have hk1 : ((k : ℕ) : ℤ) < 2 ^ t := by exact_mod_cast k.2
  have hk2 : ((k' : ℕ) : ℤ) < 2 ^ t := by exact_mod_cast k'.2
  have hlt : |((k : ℕ) : ℤ) - k'| < 2 ^ t := by
    rw [abs_lt]; constructor <;> omega
  have hzero : round ((k : ℝ) / 2 ^ t - φ) - round ((k' : ℝ) / 2 ^ t - φ) = 0 := by
    by_contra hne
    have : (2 : ℤ) ^ t ≤ |((k : ℕ) : ℤ) - k'| := by
      rw [h', abs_mul, abs_of_pos (by positivity)]
      exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hne)
    omega
  rw [hzero, mul_zero, sub_eq_zero] at h'
  exact Fin.ext (by exact_mod_cast h')

/-- One side of the tail: `∑ 1/(ℓ - d)² ≤ 1/(M - 1)` over finitely many integers `ℓ` with
`ℓ - d > M`, for a natural number `M ≥ 2`. The integer parts of the `ℓ - d` are distinct and at
least `M`, which reduces it to `∑_{M ≤ a ≤ N} 1/a² ≤ 1/(M - 1) - 1/N` (`sum_Ioc_inv_sq_le_sub`). -/
private theorem sum_tail_le {M : ℕ} (hM : 2 ≤ M) (d : ℝ) (T : Finset ℤ)
    (hT : ∀ ℓ ∈ T, (M : ℝ) < ℓ - d) :
    ∑ ℓ ∈ T, (((ℓ : ℝ) - d) ^ 2)⁻¹ ≤ ((M : ℝ) - 1)⁻¹ := by
  set f : ℤ → ℕ := fun ℓ ↦ (⌊(ℓ : ℝ) - d⌋).toNat
  have hfloor : ∀ ℓ ∈ T, (M : ℤ) ≤ ⌊(ℓ : ℝ) - d⌋ := fun ℓ hℓ ↦
    Int.le_floor.mpr (by exact_mod_cast (hT ℓ hℓ).le)
  have hf : ∀ ℓ ∈ T, M ≤ f ℓ ∧ (f ℓ : ℝ) ≤ ℓ - d := fun ℓ hℓ ↦ by
    have h1 := hfloor ℓ hℓ
    have h2 : ((f ℓ : ℕ) : ℤ) = ⌊(ℓ : ℝ) - d⌋ := Int.toNat_of_nonneg (by omega)
    refine ⟨by omega, ?_⟩
    have : ((f ℓ : ℤ) : ℝ) ≤ ℓ - d := h2 ▸ Int.floor_le _
    exact_mod_cast this
  have hinj : Set.InjOn f T := fun ℓ hℓ ℓ' hℓ' h ↦ by
    have h1 := hfloor ℓ hℓ
    have h2 := hfloor ℓ' hℓ'
    have : ⌊(ℓ : ℝ) - d⌋ = ⌊(ℓ' : ℝ) - d⌋ := by
      have := congrArg (fun n : ℕ ↦ (n : ℤ)) h
      simp only [f, Int.toNat_of_nonneg (show 0 ≤ ⌊(ℓ : ℝ) - d⌋ by omega),
        Int.toNat_of_nonneg (show 0 ≤ ⌊(ℓ' : ℝ) - d⌋ by omega)] at this
      exact this
    rw [sub_eq_add_neg, sub_eq_add_neg, Int.floor_intCast_add, Int.floor_intCast_add] at this
    omega
  set N := max (M - 1) ((T.image f).sup id)
  have hN : T.image f ⊆ Finset.Ioc (M - 1) N := fun a ha ↦ by
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_Ioc.mpr ⟨by have := (hf ℓ hℓ).1; omega,
      le_max_of_le_right (Finset.le_sup (f := id) ha)⟩
  calc ∑ ℓ ∈ T, (((ℓ : ℝ) - d) ^ 2)⁻¹ ≤ ∑ ℓ ∈ T, ((f ℓ : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum fun ℓ hℓ ↦ by
          have : (0 : ℝ) < f ℓ := by exact_mod_cast (show 0 < f ℓ by have := (hf ℓ hℓ).1; omega)
          exact inv_anti₀ (by positivity) (pow_le_pow_left₀ this.le (hf ℓ hℓ).2 2)
    _ = ∑ a ∈ T.image f, ((a : ℝ) ^ 2)⁻¹ :=
        (Finset.sum_image (f := fun a : ℕ ↦ ((a : ℝ) ^ 2)⁻¹) hinj).symm
    _ ≤ ∑ a ∈ Finset.Ioc (M - 1) N, ((a : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hN fun _ _ _ ↦ by positivity
    _ ≤ ((M - 1 : ℕ) : ℝ)⁻¹ - (N : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub (by omega) (le_max_left _ _)
    _ ≤ ((M : ℝ) - 1)⁻¹ := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
        linarith [inv_nonneg.mpr (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

/-- The outcomes farther than `2^{-n}` from `φ` modulo `1` have total probability at most
`1/(2(2^{t-n} - 1))` (Nielsen–Chuang, eqs. (5.30)–(5.34)): their offsets `ℓ` are distinct with
`|ℓ - δ| > 2^{t-n}`, and each side of the tail contributes at most `1/(4(2^{t-n} - 1))`. -/
private theorem sum_norm_sq_amplitude_far_le (t n : ℕ) (hn : n ≤ t) (hM : 2 ≤ 2 ^ (t - n))
    (φ : ℝ) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin (2 ^ t) ↦
        ¬ |(k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)| ≤ 1 / 2 ^ n),
      ‖amplitude t φ k‖ ^ 2 ≤ (2 * ((2 : ℝ) ^ (t - n) - 1))⁻¹ := by
  set bad := Finset.univ.filter (fun k : Fin (2 ^ t) ↦
    ¬ |(k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)| ≤ 1 / 2 ^ n)
  set δ := Int.fract ((2 : ℝ) ^ t * φ)
  have hN : (0 : ℝ) < 2 ^ t := by positivity
  have hbad : ∀ k ∈ bad, ((2 ^ (t - n) : ℕ) : ℝ) < |(offset t φ k : ℝ) - δ| := by
    intro k hk
    have hk := (Finset.mem_filter.mp hk).2
    push Not at hk
    rw [← two_pow_mul_sub_round, abs_mul, abs_of_pos hN]
    calc ((2 ^ (t - n) : ℕ) : ℝ) = 2 ^ t * (1 / 2 ^ n) := by
          rw [mul_one_div, eq_div_iff (by positivity)]
          push_cast
          rw [← pow_add, Nat.sub_add_cancel hn]
      _ < _ := mul_lt_mul_of_pos_left hk hN
  set T := bad.image (offset t φ)
  have hT : ∀ ℓ ∈ T, ((2 ^ (t - n) : ℕ) : ℝ) < |(ℓ : ℝ) - δ| := by
    intro ℓ hℓ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hℓ
    exact hbad k hk
  have hpos := sum_tail_le hM δ (T.filter fun ℓ : ℤ ↦ δ < ℓ) fun ℓ hℓ ↦ by
    obtain ⟨hℓT, hℓ⟩ := Finset.mem_filter.mp hℓ
    simpa only [abs_of_pos (sub_pos.mpr hℓ)] using hT ℓ hℓT
  have hneg := sum_tail_le hM (-δ) ((T.filter fun ℓ : ℤ ↦ ¬ δ < ℓ).image Neg.neg) fun ℓ hℓ ↦ by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hℓ
    obtain ⟨haT, hℓ⟩ := Finset.mem_filter.mp ha
    have := hT a haT
    rw [abs_of_nonpos (by linarith [not_lt.mp hℓ])] at this
    push_cast at this ⊢
    linarith
  rw [Finset.sum_image fun _ _ _ _ h ↦ neg_injective h] at hneg
  have hM' : (2 : ℝ) ≤ ((2 ^ (t - n) : ℕ) : ℝ) := by exact_mod_cast hM
  calc ∑ k ∈ bad, ‖amplitude t φ k‖ ^ 2 ≤ ∑ k ∈ bad, (4 * ((offset t φ k : ℝ) - δ) ^ 2)⁻¹ :=
        Finset.sum_le_sum fun k hk ↦ norm_sq_amplitude_le_offset t φ k
          ((by positivity : (0 : ℝ) < _).trans (hbad k hk))
    _ = ∑ ℓ ∈ T, (4 * ((ℓ : ℝ) - δ) ^ 2)⁻¹ :=
        (Finset.sum_image (f := fun ℓ : ℤ ↦ (4 * ((ℓ : ℝ) - δ) ^ 2)⁻¹)
          (offset_injective t φ).injOn).symm
    _ = 4⁻¹ * (∑ ℓ ∈ T.filter (fun ℓ : ℤ ↦ δ < ℓ), (((ℓ : ℝ) - δ) ^ 2)⁻¹ +
        ∑ ℓ ∈ T.filter (fun ℓ : ℤ ↦ ¬ δ < ℓ), ((((-ℓ : ℤ) : ℝ) - -δ) ^ 2)⁻¹) := by
        rw [← Finset.sum_filter_add_sum_filter_not T (fun ℓ : ℤ ↦ δ < ℓ), mul_add,
          Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
        · rw [mul_inv]
        · rw [mul_inv]
          push_cast
          ring
    _ ≤ 4⁻¹ * ((((2 ^ (t - n) : ℕ) : ℝ) - 1)⁻¹ + (((2 ^ (t - n) : ℕ) : ℝ) - 1)⁻¹) := by
        gcongr
    _ = (2 * ((2 : ℝ) ^ (t - n) - 1))⁻¹ := by
        rw [mul_inv]
        push_cast
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
  have hε' : (2 * ((2 : ℝ) ^ (t - n) - 1))⁻¹ ≤ ε := by
    rw [htn, ← one_div, div_le_iff₀ (by nlinarith [show 0 < 1 / (2 * ε) by positivity])]
    have : 1 / (2 * ε) * (2 * ε) = 1 := by field_simp
    nlinarith
  have hall := sum_norm_sq_amplitude (t := t) φ
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin (2 ^ t) ↦
    |(k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)| ≤ 1 / 2 ^ n)] at hall
  linarith

end PhaseEstimation

end QuantumCircuit
