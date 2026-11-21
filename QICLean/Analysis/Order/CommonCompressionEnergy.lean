/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Energy estimates on a common low-energy compression

A high-sector energy floor bounds the mass outside an orthogonal compression.
When two Hamiltonians agree on that compression and only a bounded connecting
operator couples it to its complement, the projected energy has an explicit
error independent of the norm of the exterior Hamiltonians.

These are abstract auxiliary estimates for AKLV, arXiv:1301.1162v1,
Section 6.3, Lemma 6.5 and the gap-preservation part of Theorem 6.1.
The compression identities and energy floor are hypotheses here; a physical
application must derive them from the actual commuting block truncations.
-/

open scoped InnerProductSpace

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- A high-sector energy floor bounds the mass lost by the low compression.
Abstract auxiliary to AKLV, arXiv:1301.1162v1, Section 6.3, Lemma 6.5(1).
No bound on the full Hamiltonian norm is used. -/
theorem mul_norm_sq_orthogonal_starProjection_le_energy
    (U : Submodule ℂ E) (B : E →L[ℂ] E) (t : ℝ)
    (hfloor : (t : ℂ) • Uᗮ.starProjection ≤ B) (v : E) :
    t * ‖Uᗮ.starProjection v‖ ^ 2 ≤ (⟪v, B v⟫_ℂ).re := by
  have hpos := (ContinuousLinearMap.le_def.mp hfloor).re_inner_nonneg_right v
  have hQ : (⟪v, Uᗮ.starProjection v⟫_ℂ).re = ‖Uᗮ.starProjection v‖ ^ 2 := by
    change RCLike.re ⟪v, Uᗮ.starProjection v⟫_ℂ = _
    rw [inner_re_symm]
    exact Uᗮ.re_inner_starProjection_eq_normSq v
  change 0 ≤ (⟪v, (B - (t : ℂ) • Uᗮ.starProjection) v⟫_ℂ).re at hpos
  simpa only [sub_apply, smul_apply, inner_sub_right, inner_smul_right,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hQ, sub_nonneg] using hpos

/-- A bounded connecting operator controls the change of energy under a
compression on which the two Hamiltonians agree. The positive truncated
Hamiltonian is allowed arbitrary norm. Abstract auxiliary to AKLV,
arXiv:1301.1162v1, Section 6.3, Lemma 6.5(2). -/
theorem projected_energy_le_of_common_compression
    (U : Submodule ℂ E) (H B A : E →L[ℂ] E) (hB : B.IsPositive)
    (hagree : ∀ w ∈ U, H w = B w)
    (hcomm : Commute U.starProjection (B - A)) (v : E) :
    (⟪U.starProjection v, H (U.starProjection v)⟫_ℂ).re ≤
      (⟪v, B v⟫_ℂ).re + 2 * ‖A‖ * ‖v‖ * ‖Uᗮ.starProjection v‖ := by
  let p := U.starProjection v
  let q := Uᗮ.starProjection v
  have hsplit : p + q = v := U.starProjection_add_starProjection_orthogonal v
  have hPQ : U.starProjection q = 0 :=
    U.starProjection_apply_eq_zero_iff.mpr (Uᗮ.starProjection_apply_mem v)
  have hcrossK : ⟪p, (B - A) q⟫_ℂ = 0 := by
    rw [show p = U.starProjection v from rfl, U.inner_starProjection_left_eq_right]
    have happly := congrArg (fun T : E →L[ℂ] E ↦ T q) hcomm.eq
    change U.starProjection ((B - A) q) = (B - A) (U.starProjection q) at happly
    rw [happly, hPQ, map_zero, inner_zero_right]
  have hcross : ⟪p, B q⟫_ℂ = ⟪p, A q⟫_ℂ := by
    simpa only [sub_apply, inner_sub_right, sub_eq_zero] using hcrossK
  have hreverse : ⟪q, B p⟫_ℂ = star ⟪p, B q⟫_ℂ := by
    rw [← hB.inner_left_eq_inner_right]
    exact (inner_conj_symm (𝕜 := ℂ) (B q) p).symm
  have henergy : (⟪v, B v⟫_ℂ).re = (⟪p, B p⟫_ℂ).re +
      (⟪q, B q⟫_ℂ).re + 2 * (⟪p, A q⟫_ℂ).re := by
    conv_lhs => rw [← hsplit]
    simp only [map_add, inner_add_left, inner_add_right, Complex.add_re]
    rw [hreverse, Complex.star_def, Complex.conj_re, hcross]
    ring
  have hnorm : ‖⟪p, A q⟫_ℂ‖ ≤ ‖A‖ * ‖v‖ * ‖q‖ := by
    calc
      _ ≤ ‖p‖ * ‖A q‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖A‖ * ‖q‖) :=
        mul_le_mul (U.norm_starProjection_apply_le v) (A.le_opNorm q)
          (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have hreal : -(‖A‖ * ‖v‖ * ‖q‖) ≤ (⟪p, A q⟫_ℂ).re := by
    calc
      _ ≤ -‖⟪p, A q⟫_ℂ‖ := neg_le_neg_iff.mpr hnorm
      _ ≤ -|(⟪p, A q⟫_ℂ).re| := neg_le_neg_iff.mpr (Complex.abs_re_le_norm _)
      _ ≤ _ := neg_abs_le _
  have hq0 : 0 ≤ (⟪q, B q⟫_ℂ).re := hB.re_inner_nonneg_right q
  rw [hagree p (U.starProjection_apply_mem v)]
  change (⟪p, B p⟫_ℂ).re ≤ _
  linarith

/-- An upper bound on truncated energy gives both the high-sector mass and
the projected original-energy estimate, without a bound on either exterior
Hamiltonian. This is the quantitative common-compression estimate used in
AKLV, arXiv:1301.1162v1, Section 6.3, Lemma 6.5. The common compression and
high-sector floor must be derived in any physical application. -/
theorem norm_high_and_projected_energy_le
    (U : Submodule ℂ E) (H B A : E →L[ℂ] E) (hB : B.IsPositive)
    (hagree : ∀ w ∈ U, H w = B w)
    (hcomm : Commute U.starProjection (B - A))
    (t e : ℝ) (ht : 0 < t) (he : 0 ≤ e)
    (hfloor : (t : ℂ) • Uᗮ.starProjection ≤ B)
    (v : E) (hv : ‖v‖ = 1) (henergy : (⟪v, B v⟫_ℂ).re ≤ e) :
    ‖Uᗮ.starProjection v‖ ≤ Real.sqrt (e / t) ∧
      (⟪U.starProjection v, H (U.starProjection v)⟫_ℂ).re ≤
        e + 2 * ‖A‖ * Real.sqrt (e / t) := by
  have hsquared : ‖Uᗮ.starProjection v‖ ^ 2 ≤ e / t :=
    (le_div_iff₀ ht).mpr (by
      nlinarith [U.mul_norm_sq_orthogonal_starProjection_le_energy B t hfloor v])
  have hhigh : ‖Uᗮ.starProjection v‖ ≤ Real.sqrt (e / t) := by
    nlinarith [Real.sq_sqrt (div_nonneg he ht.le), Real.sqrt_nonneg (e / t),
      norm_nonneg (Uᗮ.starProjection v)]
  refine ⟨hhigh, ?_⟩
  calc
    _ ≤ (⟪v, B v⟫_ℂ).re + 2 * ‖A‖ * ‖v‖ * ‖Uᗮ.starProjection v‖ :=
      U.projected_energy_le_of_common_compression H B A hB hagree hcomm v
    _ ≤ e + 2 * ‖A‖ * Real.sqrt (e / t) := by
      rw [hv, mul_one]
      gcongr

end Submodule
