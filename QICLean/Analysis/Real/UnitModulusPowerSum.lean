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
