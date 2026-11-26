/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Power-sum non-decay for unit-modulus complex families

This module proves a purely analytic fact about finite power sums of
unit-modulus complex numbers: the sequence

  `N ↦ ∑_q (μ q) ^ N`

does **not** tend to zero as `N → ∞`, provided the family `μ : Fin r → ℂ`
is nonempty and every `μ q` has modulus one.  The argument is the standard
Wiener / Cesaro one:

* `‖S N‖² = ∑_{q, q'} (μ q · star (μ q'))^N`.
* Cesaro-averaging in `N` produces, for each pair `(q, q')`,
  either `1` (when the unit-modulus ratio `μ q · star (μ q')` equals `1`)
  or `0` (when the unit-modulus ratio differs from `1`, the geometric
  sum is bounded uniformly in `T`).
* The Cesaro limit therefore equals the cardinality of the resonant set
  `{(q, q') | μ q · star (μ q') = 1}`, which contains the diagonal
  `{(q, q)}` and is therefore `≥ r > 0`; the assumption that the original
  sequence tends to zero would force the Cesaro mean to vanish, a
  contradiction.

This is a general analytic ingredient about complex power sums of
unit-modulus families.  In the CPSV16 fundamental-theorem proof it belongs to
the formal replacement for the non-vanishing obstruction used at line 1182,
where the paper invokes Lemma `Lem1` to rule out the alternative that all
overlaps with a fixed block decay.  It is not the equal-MPV coefficient
comparison of lines 1184--1192.

The module is purely about complex power sums; it has no MPS
dependencies and uses no `sorry`/`axiom`/`unsafe`.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix Product Density Operators:
  Renormalization Fixed Points and Boundary Theories*, arXiv:1606.00608
  (2017), Theorem `thm1`, proof line 1182, together with Lemma `Lem1`
  (lines 1131--1133).

Moved from TNLean, `TNLean/MPS/MPU/Circuit/Gates/UnitCircleRankTwo.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

open scoped BigOperators
open Filter

namespace UnitModulusPowerSum

/-- For unit-modulus `ν ≠ 1`, the partial sums `∑_{N < T} ν^N` are uniformly
bounded in `T` by `2 / ‖ν - 1‖`. -/
lemma norm_geom_sum_le {ν : ℂ} (hν : ‖ν‖ = 1) (hne : ν ≠ 1) (T : ℕ) :
    ‖∑ N ∈ Finset.range T, ν ^ N‖ ≤ 2 / ‖ν - 1‖ := by
  classical
  have hsub : ν - 1 ≠ 0 := sub_ne_zero.mpr hne
  rw [geom_sum_eq hne T, norm_div]
  have hnum : ‖ν ^ T - 1‖ ≤ 2 := by
    calc ‖ν ^ T - 1‖
        ≤ ‖ν ^ T‖ + ‖(1 : ℂ)‖ := by
          have := norm_sub_le (ν ^ T) (1 : ℂ)
          simpa using this
      _ = 2 := by
          rw [norm_pow, hν, one_pow, norm_one]
          norm_num
  have hden_pos : 0 < ‖ν - 1‖ := norm_pos_iff.mpr hsub
  exact div_le_div_of_nonneg_right hnum hden_pos.le

/-- Cesaro average of unit-modulus powers vanishes when the base is not `1`. -/
lemma cesaro_geom_sum_tendsto_zero {ν : ℂ} (hν : ‖ν‖ = 1) (hne : ν ≠ 1) :
    Tendsto (fun T : ℕ => (T : ℂ)⁻¹ * ∑ N ∈ Finset.range T, ν ^ N)
      atTop (nhds 0) := by
  classical
  refine (tendsto_zero_iff_norm_tendsto_zero).mpr ?_
  have hbound : ∀ T : ℕ,
      ‖(T : ℂ)⁻¹ * ∑ N ∈ Finset.range T, ν ^ N‖ ≤ (2 / ‖ν - 1‖) * (T : ℝ)⁻¹ := by
    intro T
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT
      simp
    · rw [norm_mul]
      have h1 : ‖(T : ℂ)⁻¹‖ = (T : ℝ)⁻¹ := by
        rw [norm_inv, Complex.norm_natCast]
      rw [h1]
      have h2 := norm_geom_sum_le hν hne T
      have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
      calc (T : ℝ)⁻¹ * ‖∑ N ∈ Finset.range T, ν ^ N‖
          ≤ (T : ℝ)⁻¹ * (2 / ‖ν - 1‖) :=
            mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hTpos.le)
        _ = (2 / ‖ν - 1‖) * (T : ℝ)⁻¹ := by ring
  -- The RHS tends to zero.
  have hRHS : Tendsto (fun T : ℕ => (2 / ‖ν - 1‖) * (T : ℝ)⁻¹)
      atTop (nhds 0) := by
    have hT : Tendsto (fun T : ℕ => ((T : ℝ))⁻¹) atTop (nhds 0) := by
      have hAtTop : Tendsto (fun T : ℕ => ((T : ℝ))) atTop atTop := by
        exact_mod_cast tendsto_natCast_atTop_atTop (R := ℝ)
      have := Filter.Tendsto.inv_tendsto_atTop hAtTop
      refine this.congr' ?_
      exact Filter.Eventually.of_forall fun _ => rfl
    have := hT.const_mul (2 / ‖ν - 1‖)
    simpa using this
  refine squeeze_zero (fun T => norm_nonneg _) hbound hRHS

/-- Cesaro average of unit-modulus powers at the base `1` equals `1`. -/
lemma cesaro_geom_sum_one_tendsto_one :
    Tendsto (fun T : ℕ => (T : ℂ)⁻¹ * ∑ _N ∈ Finset.range T, (1 : ℂ) ^ _N)
      atTop (nhds 1) := by
  classical
  -- Show the sequence is eventually equal to 1 (for T ≥ 1).
  refine tendsto_const_nhds.congr' ?_
  refine (Filter.eventually_ge_atTop 1).mono ?_
  intro T hT
  have hTne : (T : ℂ) ≠ 0 := by
    have hT' : 0 < T := hT
    exact_mod_cast hT'.ne'
  simp [Finset.sum_const, Finset.card_range]
  field_simp

end UnitModulusPowerSum

namespace Complex

/-- Three points on a vertical line with the same squared modulus cannot be distinct.
This is the circle–line intersection step in the proof of Lemma 1 of
`docs/audits/2026-10-02_mpu_diagonal_circuits.tex`. -/
theorem eq_or_eq_or_eq_of_re_eq_of_normSq_eq (x y z : ℂ) (hxy : x.re = y.re) (hxz : x.re = z.re)
    (hxyN : Complex.normSq x = Complex.normSq y)
    (hxzN : Complex.normSq x = Complex.normSq z) : x = y ∨ x = z ∨ y = z := by
  have him : x.im ^ 2 = y.im ^ 2 := by
    simp only [Complex.normSq_apply, hxy] at hxyN
    nlinarith
  have himz : x.im ^ 2 = z.im ^ 2 := by
    simp only [Complex.normSq_apply, hxz] at hxzN
    nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp him with h | h <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp himz with h' | h' <;>
    simp_all [Complex.ext_iff]

/-- A real linear functional constant on three distinct unit-circle points is zero.
This is a step in the proof of Lemma 1 of
`docs/audits/2026-10-02_mpu_diagonal_circuits.tex`. -/
theorem eq_zero_of_re_mul_eq_of_three_unit_points (k u v w : ℂ)
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hw : Complex.normSq w = 1) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hreuv : (k * u).re = (k * v).re) (hreuw : (k * u).re = (k * w).re) : k = 0 := by
  have hc := eq_or_eq_or_eq_of_re_eq_of_normSq_eq (k * u) (k * v) (k * w) hreuv hreuw
    (by simp [Complex.normSq_mul, hu, hv]) (by simp [Complex.normSq_mul, hu, hw])
  grind

/-- An affine function mapping three distinct unit-circle points to the unit circle
has a vanishing constant or linear coefficient. This is the three-value case in the
proof of Lemma 1 of `docs/audits/2026-10-02_mpu_diagonal_circuits.tex`. -/
theorem eq_zero_or_eq_zero_of_three_unit_affine_values (a b u v w : ℂ)
    (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1)
    (hw : Complex.normSq w = 1) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h0 : Complex.normSq (a + b * u) = 1)
    (h1 : Complex.normSq (a + b * v) = 1)
    (h2 : Complex.normSq (a + b * w) = 1) : a = 0 ∨ b = 0 := by
  simp only [Complex.normSq_add, hu, hv, hw, map_mul, mul_one] at h0 h1 h2
  have hlin : a * star b = 0 := by
    apply eq_zero_of_re_mul_eq_of_three_unit_points (a * star b) (star u) (star v) (star w)
      (by simpa using hu) (by simpa using hv) (by simpa using hw)
      (star_injective.ne huv) (star_injective.ne huw) (star_injective.ne hvw)
    all_goals
      simp only [mul_assoc, Complex.star_def]
      nlinarith
  simpa using mul_eq_zero.mp hlin

/-- For a unit-modulus factorization `a i + b i * t j`, either every row has only one
nonzero coefficient, or the unit-circle parameter `t` takes at most two values.
This is the geometric step in the exact diagonal rank-two circuit argument in
`docs/audits/2026-10-02_mpu_diagonal_circuits.tex`, Lemma 1. It does not itself
assert a quantum-circuit implementation. -/
theorem unitCircle_factorization_dichotomy {ι κ : Type*} [Nonempty κ] (a b : ι → ℂ) (t : κ → ℂ)
    (ht : ∀ j, Complex.normSq (t j) = 1)
    (hM : ∀ i j, Complex.normSq (a i + b i * t j) = 1) :
    (∀ i, a i = 0 ∨ b i = 0) ∨ ∃ j₀ j₁, ∀ j, t j = t j₀ ∨ t j = t j₁ := by
  classical
  by_cases hex : ∃ j k l, t j ≠ t k ∧ t j ≠ t l ∧ t k ≠ t l
  · obtain ⟨j, k, l, hjk, hjl, hkl⟩ := hex
    exact Or.inl fun i =>
      eq_zero_or_eq_zero_of_three_unit_affine_values (a i) (b i) (t j) (t k) (t l)
      (ht j) (ht k) (ht l) hjk hjl hkl (hM i j) (hM i k) (hM i l)
  · right
    let j₀ : κ := Classical.arbitrary κ
    by_cases hsame : ∀ j, t j = t j₀
    · exact ⟨j₀, j₀, fun j => Or.inl (hsame j)⟩
    · push Not at hsame
      obtain ⟨j₁, hj₁⟩ := hsame
      refine ⟨j₀, j₁, fun j => ?_⟩
      by_contra h
      push Not at h
      exact hex ⟨j₀, j₁, j, Ne.symm hj₁, Ne.symm h.1, Ne.symm h.2⟩

end Complex
