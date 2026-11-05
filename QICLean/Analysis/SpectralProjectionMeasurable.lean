/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ShiftedDensityTruncation
import QICLean.Analysis.SupportProjectionOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Borel spectral cutoffs of finite Hermitian matrices

Continuous scalar ramps stabilize at the closed threshold indicator on every
finite spectrum. Their matrix functional calculi are continuous on Hermitian
matrices, so the hard spectral projection is Borel measurable, including at
threshold eigenvalues. This is a matrix-analysis auxiliary for the collective
trimming operation in ALVV, arXiv:1602.08828v2, `def:trimming`, lines 646–655.
It does not construct an adaptive sampling law or assert algorithm completion.
-/

open Filter MeasureTheory
open scoped Topology Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Real

/-- A continuous approximation to the closed threshold indicator, with
value one at the threshold. -/
def closedThresholdRamp (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  max 0 (min 1 (1 + (n : ℝ) * (x - a)))

/-- The scalar closed-threshold approximants are continuous. -/
theorem continuous_closedThresholdRamp (a : ℝ) (n : ℕ) :
    Continuous (closedThresholdRamp a n) := by
  unfold closedThresholdRamp
  fun_prop

/-- At every fixed real argument, the scalar approximants eventually equal
its closed-threshold indicator. In particular equality is retained at the
threshold, without an exclusion hypothesis. -/
theorem eventually_closedThresholdRamp_eq (a x : ℝ) :
    ∀ᶠ n : ℕ in atTop, closedThresholdRamp a n x = if a ≤ x then 1 else 0 := by
  by_cases hax : a ≤ x
  · apply Filter.Eventually.of_forall
    intro n
    have hnonneg : 0 ≤ (n : ℝ) * (x - a) := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hax)
    simp only [closedThresholdRamp, ite_eq_left hax]
    rw [min_eq_left (by linarith only [hnonneg]), max_eq_right (by norm_num)]
  · have hpos : 0 < a - x := sub_pos.mpr (lt_of_not_ge hax)
    let N := Nat.ceil (1 / (a - x))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hlarge : 1 / (a - x) ≤ (n : ℝ) :=
      (Nat.le_ceil (1 / (a - x))).trans (by exact_mod_cast hn)
    have hmul : 1 ≤ (n : ℝ) * (a - x) := (div_le_iff₀ hpos).mp hlarge
    have hsmall : 1 + (n : ℝ) * (x - a) ≤ 0 := by nlinarith only [hmul]
    simp only [closedThresholdRamp, ite_eq_right hax]
    rw [max_eq_left ((min_le_right _ _).trans hsmall)]

end Real

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- On any fixed finite Hermitian matrix, the continuous ramp functional
calculus eventually equals the actual closed spectral projection. -/
theorem IsHermitian.eventually_cfc_closedThresholdRamp_eq_spectralProjectionGE
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (a : ℝ) :
    ∀ᶠ k : ℕ in atTop, cfc (Real.closedThresholdRamp a k) A = spectralProjectionGE A a := by
  have hvalues : ∀ᶠ k : ℕ in atTop, ∀ i : n,
      Real.closedThresholdRamp a k (hA.eigenvalues i) =
        if a ≤ hA.eigenvalues i then 1 else 0 :=
    Filter.eventually_all.mpr fun i ↦ Real.eventually_closedThresholdRamp_eq a (hA.eigenvalues i)
  filter_upwards [hvalues] with k hk
  apply cfc_congr
  intro x hx
  obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
  exact hk i

/-- The functional calculus of each continuous ramp is continuous on the
Hermitian matrix subtype. -/
theorem continuous_cfc_closedThresholdRamp (a : ℝ) (k : ℕ) :
    Continuous (fun A : {A : Matrix n n ℂ // A.IsHermitian} ↦
      cfc (Real.closedThresholdRamp a k) A.val) := by
  exact Continuous.cfc_of_mem_nhdsSet (s := Set.univ) (Real.closedThresholdRamp a k)
    (by simp) continuous_subtype_val (fun A ↦ A.property.isSelfAdjoint)
    (Real.continuous_closedThresholdRamp a k).continuousOn

/-- The existing closed spectral cutoff is Borel measurable on finite
Hermitian matrices. Eigenvalues at the threshold are included. -/
theorem measurable_spectralProjectionGE_hermitian (a : ℝ) :
    Measurable (fun A : {A : Matrix n n ℂ // A.IsHermitian} ↦
      spectralProjectionGE A.val a) := by
  apply measurable_of_tendsto_metrizable
    (fun k ↦ (continuous_cfc_closedThresholdRamp (n := n) a k).measurable)
  rw [tendsto_pi_nhds]
  intro A
  have heq : (fun k : ℕ ↦ cfc (Real.closedThresholdRamp a k) A.val) =ᶠ[atTop]
      (fun _ ↦ spectralProjectionGE A.val a) :=
    A.property.eventually_cfc_closedThresholdRamp_eq_spectralProjectionGE a
  exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) tendsto_const_nhds


/-- The existing closed spectral cutoff is Borel measurable as a function
of the whole finite complex matrix. On non-Hermitian inputs its functional
calculus definition takes the value zero. -/
theorem measurable_spectralProjectionGE (a : ℝ) :
    Measurable (fun A : Matrix n n ℂ ↦ spectralProjectionGE A a) := by
  have hset : MeasurableSet {A : Matrix n n ℂ | A.IsHermitian} :=
    (show IsClosed {A : Matrix n n ℂ | Aᴴ = A} from
      isClosed_eq (by fun_prop) continuous_id).measurableSet
  apply measurable_of_restrict_of_restrict_compl hset
  · exact measurable_spectralProjectionGE_hermitian a
  · have heq : (fun A : {A : Matrix n n ℂ // ¬ A.IsHermitian} ↦
        spectralProjectionGE A.val a) = (fun _ ↦ 0) := by
      funext A
      exact cfc_apply_of_not_predicate A.val (fun h ↦ A.property h.isHermitian)
    change Measurable (fun A : {A : Matrix n n ℂ // ¬ A.IsHermitian} ↦
      spectralProjectionGE A.val a)
    rw [heq]
    exact measurable_const


/-- The existing range projection of a Hermitian matrix is recovered from
the two closed half-line cutoffs. Their product is the projection onto the
zero eigenspace, including all degeneracies. -/
theorem IsHermitian.supportProj_eq_one_sub_spectralProjectionGE_mul
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hA.supportProj = 1 - spectralProjectionGE A 0 * spectralProjectionGE (-A) 0 := by
  let f : ℝ → ℝ := fun x ↦ if 0 ≤ x then 1 else 0
  let g : ℝ → ℝ := fun x ↦ if 0 ≤ -x then 1 else 0
  have hneg : spectralProjectionGE (-A) 0 = cfc g A := by
    exact (cfc_comp_neg (f := f) (a := A)
      ((A.finite_real_spectrum.image Neg.neg).continuousOn _) hA.isSelfAdjoint).symm
  rw [hA.supportProj_eq_cfc, hneg]
  change cfc (fun x : ℝ ↦ if x ≠ 0 then 1 else 0) A = 1 - cfc f A * cfc g A
  rw [← _root_.cfc_mul f g A (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _),
    ← _root_.cfc_const_one ℝ A hA.isSelfAdjoint,
    ← _root_.cfc_sub (fun _ : ℝ ↦ 1) (fun x ↦ f x * g x) A continuousOn_const
      (A.finite_real_spectrum.continuousOn _)]
  apply cfc_congr
  intro x _
  dsimp only [f, g]
  by_cases hx : x = 0
  · subst x
    norm_num
  · rcases lt_or_gt_of_ne hx with hneg | hpos
    · simp [hx, not_le.mpr hneg, neg_nonneg.mpr hneg.le]
    · simp [hx, hpos.le, not_le.mpr (neg_neg_of_pos hpos)]

/-- The existing orthogonal range projection is Borel measurable on finite
Hermitian matrices. No fixed-rank or nonzero-eigenvalue gap is assumed. -/
theorem measurable_supportProj_hermitian :
    Measurable (fun A : {A : Matrix n n ℂ // A.IsHermitian} ↦ A.property.supportProj) := by
  have heq : (fun A : {A : Matrix n n ℂ // A.IsHermitian} ↦ A.property.supportProj) =
      (fun A ↦ 1 - spectralProjectionGE A.val 0 * spectralProjectionGE (-A.val) 0) := by
    funext A
    exact A.property.supportProj_eq_one_sub_spectralProjectionGE_mul
  rw [heq]
  exact measurable_const.sub ((measurable_spectralProjectionGE 0).comp measurable_subtype_coe |>.mul
    ((measurable_spectralProjectionGE 0).comp measurable_subtype_coe.neg))

end Matrix
