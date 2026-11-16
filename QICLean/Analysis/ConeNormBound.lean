/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cone ratios and norm bounds

Wolf, *Quantum Channels & Operations*, Chapter 8, Eqs. (8.61), (8.63),
(8.68)–(8.69), source lines 730–795. The norm is assumed monotone on the
cone. No finite-dimensional or interior-point assumption is needed.
The square-root bound includes zero cone ratios; no finite-distance
assumption is hidden in a real-valued logarithm.
-/

noncomputable section

namespace ProperCone

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (C : ProperCone ℝ E)

/-- Monotonicity of the norm on the cone, expressed using positive increments. -/
def NormMonotone : Prop := ∀ ⦃x y : E⦄, x ∈ C → y ∈ C → ‖x‖ ≤ ‖x + y‖

/-- The lower cone ratio, with nonnegative scaling parameters (Wolf Eq. 8.61).
For nonzero positive denominator and a cone-monotone norm the supremum is finite. -/
def lowerRatio (a b : E) : ℝ := sSup {t : ℝ | 0 ≤ t ∧ a - t • b ∈ C}

variable {C} (hm : C.NormMonotone) {a b : E}
include hm

lemma lowerRatio_bddAbove (hb : b ∈ C) (hb0 : b ≠ 0) :
    BddAbove {t : ℝ | 0 ≤ t ∧ a - t • b ∈ C} := by
  refine ⟨‖a‖ / ‖b‖, ?_⟩
  intro t ht
  have h := hm (C.smul_mem hb ht.1) ht.2
  simp only [add_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at h
  exact (le_div_iff₀ (norm_pos_iff.mpr hb0)).mpr h

/-- The lower cone ratio is attained, including when it is zero. -/
lemma lowerRatio_mem (ha : a ∈ C) (hb : b ∈ C) (hb0 : b ≠ 0) :
    0 ≤ C.lowerRatio a b ∧ a - C.lowerRatio a b • b ∈ C := by
  have hclosed : IsClosed {t : ℝ | 0 ≤ t ∧ a - t • b ∈ C} :=
    isClosed_Ici.inter (C.isClosed.preimage (continuous_const.sub
      (continuous_id.smul continuous_const)))
  exact hclosed.csSup_mem ⟨0, by simpa using ha⟩ (lowerRatio_bddAbove hm hb hb0)

/-- Every admissible nonnegative scale is bounded by the lower ratio. -/
lemma le_lowerRatio (hb : b ∈ C) (hb0 : b ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) (hab : a - t • b ∈ C) : t ≤ C.lowerRatio a b :=
  le_csSup (lowerRatio_bddAbove hm hb hb0) ⟨ht, hab⟩

/-- Wolf's asymmetric estimate (8.66), valid for any two admissible scales. -/
lemma norm_sub_le_of_scales {μ ν : ℝ}
    (hν : b - ν • a ∈ C) (hμ : a - μ • b ∈ C) :
    ‖a - b‖ ≤ 2 * (|1 - ν| * ‖a‖) + |1 - μ| * ‖b‖ := by
  have heq : (b - ν • a) + (a - μ • b) = (1 - ν) • a + (1 - μ) • b := by
    simp only [sub_smul, one_smul]
    abel
  have hmono := hm hν hμ
  rw [heq] at hmono
  have hn := norm_add_le ((1 - ν) • a) ((1 - μ) • b)
  have hd : a - b = (1 - ν) • a - (b - ν • a) := by
    simp only [sub_smul, one_smul]
    abel
  have ht := norm_sub_le ((1 - ν) • a) (b - ν • a)
  rw [← hd] at ht
  simp only [norm_smul, Real.norm_eq_abs] at hn ht
  linarith

/-- Wolf Eq. (8.63), without a finite-dimensional restriction. -/
theorem norm_sub_le_lowerRatio (ha : a ∈ C) (hb : b ∈ C)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ‖a - b‖ ≤ |1 - C.lowerRatio b a| * ‖a‖ + |1 - C.lowerRatio a b| * ‖b‖ +
      min (|1 - C.lowerRatio b a| * ‖a‖) (|1 - C.lowerRatio a b| * ‖b‖) := by
  have hν := (lowerRatio_mem hm hb ha ha0).2
  have hμ := (lowerRatio_mem hm ha hb hb0).2
  have h₁ := norm_sub_le_of_scales hm hν hμ
  have h₂ := norm_sub_le_of_scales hm hμ hν
  rw [norm_sub_rev b a] at h₂
  rcases le_total (|1 - C.lowerRatio b a| * ‖a‖)
      (|1 - C.lowerRatio a b| * ‖b‖) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    linarith

/-- Wolf Eq. (8.68), the averaged cone-ratio estimate. -/
theorem norm_sub_le_lowerRatio_average (ha : a ∈ C) (hb : b ∈ C)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hν : C.lowerRatio b a ≤ 1) (hμ : C.lowerRatio a b ≤ 1) :
    ‖a - b‖ ≤ 3 / 2 * (‖a‖ + ‖b‖ -
      (C.lowerRatio b a * ‖a‖ + C.lowerRatio a b * ‖b‖)) := by
  have h₁ := norm_sub_le_of_scales hm (lowerRatio_mem hm hb ha ha0).2
    (lowerRatio_mem hm ha hb hb0).2
  have h₂ := norm_sub_le_of_scales hm (lowerRatio_mem hm ha hb hb0).2
    (lowerRatio_mem hm hb ha ha0).2
  rw [norm_sub_rev b a] at h₂
  simp only [abs_of_nonneg (sub_nonneg.mpr hν), abs_of_nonneg (sub_nonneg.mpr hμ)] at h₁ h₂
  linarith

/-- Wolf Eq. (8.69). This form also covers pairs with zero cone ratio. -/
theorem norm_sub_le_lowerRatio_sqrt (ha : a ∈ C) (hb : b ∈ C)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hν : C.lowerRatio b a ≤ 1) (hμ : C.lowerRatio a b ≤ 1) :
    ‖a - b‖ ≤ 3 * ((‖a‖ + ‖b‖) / 2 -
      Real.sqrt (C.lowerRatio b a * ‖a‖ * (C.lowerRatio a b * ‖b‖))) := by
  have h := norm_sub_le_lowerRatio_average hm ha hb ha0 hb0 hν hμ
  have hx := mul_nonneg (lowerRatio_mem hm hb ha ha0).1 (norm_nonneg a)
  have hy := mul_nonneg (lowerRatio_mem hm ha hb hb0).1 (norm_nonneg b)
  have hs := Real.sq_sqrt (mul_nonneg hx hy)
  have hp := Real.sqrt_nonneg (C.lowerRatio b a * ‖a‖ * (C.lowerRatio a b * ‖b‖))
  have hd := sq_nonneg (C.lowerRatio b a * ‖a‖ - C.lowerRatio a b * ‖b‖)
  nlinarith

/-- Wolf Eq. (8.67), written with the logarithm of the product of lower ratios.
Both ratios are positive here. The square-root theorem above covers zero ratios;
this theorem does not assign a finite distance to those pairs. -/
theorem norm_sub_le_lowerRatio_log (ha : a ∈ C) (hb : b ∈ C)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hν : C.lowerRatio b a ≤ 1) (hμ : C.lowerRatio a b ≤ 1)
    (hνpos : 0 < C.lowerRatio b a) (hμpos : 0 < C.lowerRatio a b) :
    ‖a - b‖ ≤ 3 * ((‖a‖ + ‖b‖) / 2 - Real.sqrt (‖a‖ * ‖b‖) *
      Real.exp (Real.log (C.lowerRatio b a * C.lowerRatio a b) / 2)) := by
  have h := norm_sub_le_lowerRatio_sqrt hm ha hb ha0 hb0 hν hμ
  rw [Real.exp_half, Real.exp_log (mul_pos hνpos hμpos)]
  have heq : C.lowerRatio b a * ‖a‖ * (C.lowerRatio a b * ‖b‖) =
      (‖a‖ * ‖b‖) * (C.lowerRatio b a * C.lowerRatio a b) := by ring
  rwa [heq, Real.sqrt_mul (mul_nonneg (norm_nonneg a) (norm_nonneg b))] at h

/-- A positive linear map increases lower cone ratios, provided its denominator
is nonzero. This is the order-theoretic part of projective nonexpansiveness. -/
theorem lowerRatio_le_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : ProperCone ℝ F} (hK : K.NormMonotone) (T : E →ₗ[ℝ] F)
    (hT : ∀ x ∈ C, T x ∈ K) (ha : a ∈ C) (hb : b ∈ C) (hb0 : b ≠ 0)
    (hTb : T b ≠ 0) : C.lowerRatio a b ≤ K.lowerRatio (T a) (T b) := by
  obtain ⟨hr, hmem⟩ := lowerRatio_mem hm ha hb hb0
  apply le_lowerRatio hK (hT b hb) hTb hr
  simpa only [map_sub, map_smul] using hT _ hmem

/-- Lower cone ratios are bounded by the ratio of norms. -/
lemma lowerRatio_le_norm_div (ha : a ∈ C) (hb : b ∈ C) (hb0 : b ≠ 0) :
    C.lowerRatio a b ≤ ‖a‖ / ‖b‖ := by
  obtain ⟨hr, hmem⟩ := lowerRatio_mem hm ha hb hb0
  have h := hm (C.smul_mem hb hr) hmem
  simp only [add_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] at h
  exact (le_div_iff₀ (norm_pos_iff.mpr hb0)).mpr h

/-- The product of the two lower ratios lies below one. -/
lemma lowerRatio_mul_le_one (ha : a ∈ C) (hb : b ∈ C)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) : C.lowerRatio a b * C.lowerRatio b a ≤ 1 := by
  have h := mul_le_mul (lowerRatio_le_norm_div hm ha hb hb0)
    (lowerRatio_le_norm_div hm hb ha ha0) (lowerRatio_mem hm hb ha ha0).1
    (div_nonneg (norm_nonneg a) (norm_nonneg b))
  have heq : ‖a‖ / ‖b‖ * (‖b‖ / ‖a‖) = 1 := by
    field_simp
  rwa [heq] at h

/-- Positive linear maps cannot increase the finite logarithmic projective distance.
No strict positivity of the vectors, or finite-dimensionality of either space,
is required: positivity is required only of the two cone ratios. -/
theorem neg_log_lowerRatio_map_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : ProperCone ℝ F} (hK : K.NormMonotone) (T : E →ₗ[ℝ] F)
    (hT : ∀ x ∈ C, T x ∈ K) (ha : a ∈ C) (hb : b ∈ C)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hTa : T a ≠ 0) (hTb : T b ≠ 0)
    (hab : 0 < C.lowerRatio a b) (hba : 0 < C.lowerRatio b a) :
    -Real.log (K.lowerRatio (T a) (T b) * K.lowerRatio (T b) (T a)) ≤
      -Real.log (C.lowerRatio a b * C.lowerRatio b a) := by
  have h₁ := lowerRatio_le_map hm hK T hT ha hb hb0 hTb
  have h₂ := lowerRatio_le_map hm hK T hT hb ha ha0 hTa
  exact neg_le_neg (Real.log_le_log (mul_pos hab hba)
    (mul_le_mul h₁ h₂ hba.le (hab.le.trans h₁)))

end ProperCone
