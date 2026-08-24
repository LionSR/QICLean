/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/

import QICLean.Analysis.FiniteCoordinateNowosad.Recursion

/-!
# Nowosad's local-minimum theorem in a finite coordinate algebra

This file derives the variational hypotheses used by the algebraic recursion
from genuine local minima of Nowosad's functional
`L_T(x) = f(x⁻¹ T x)` on the strictly positive coordinate vectors.  It then
states the finite-coordinate conclusion of Theorem 1.8: on
`u · P(u⁻¹v)`, the operator is multiplication by `u⁻¹ T u`.

The Hilbert norm induced by the faithful functional `f(x) = ∑ i, x i` is
made explicit, and every linear operator is proved bounded for that norm by
finite dimensionality.  Nowosad's theorem has the local-**minimum**
orientation; local maxima are obtained separately by applying it to the
negative operator.

## Sources

* P. Nowosad, *Isoperimetric eigenvalue problems in algebras*, Comm. Pure
  Appl. Math. 21 (1968), 401--465, especially pp. 409--418.
* S. Yamagami, *Cyclic inequalities*, Proc. Amer. Math. Soc. 118 (1993),
  521--527, Theorem 1 on p. 522.
-/

open scoped BigOperators
open Filter Topology

namespace Nowosad

variable {ι : Type*} [Fintype ι]

/-- The norm induced by Nowosad's positive functional
`f(x) = ∑ i, x i` on the real coordinate algebra. -/
noncomputable def inducedHilbertNorm (x : ι → ℝ) : ℝ :=
  ‖WithLp.toLp 2 x‖

theorem inducedHilbertNorm_sq (x : ι → ℝ) :
    inducedHilbertNorm x ^ 2 = coordinateSum (x * x) := by
  rw [inducedHilbertNorm,
    PiLp.norm_sq_eq_of_L2 (fun _ : ι ↦ ℝ) (WithLp.toLp 2 x)]
  unfold coordinateSum
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply]
  simp [Real.norm_eq_abs, pow_two]

/-- Every linear operator on a finite coordinate algebra is bounded for the
Hilbert norm induced by the coordinate sum.  Thus the boundedness hypothesis
in Nowosad's Theorem 1.8 is automatic in this specialization. -/
theorem exists_inducedHilbertNorm_bound
    (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      inducedHilbertNorm (T x) ≤ C * inducedHilbertNorm x := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)
  let L : PiLp 2 (fun _ : ι ↦ ℝ) →ₗ[ℝ] PiLp 2 (fun _ : ι ↦ ℝ) :=
    e.symm.toLinearMap.comp (T.comp e.toLinearMap)
  let Lc : PiLp 2 (fun _ : ι ↦ ℝ) →L[ℝ] PiLp 2 (fun _ : ι ↦ ℝ) :=
    ⟨L, L.continuous_of_finiteDimensional⟩
  refine ⟨‖Lc‖, norm_nonneg Lc, ?_⟩
  intro x
  simpa [inducedHilbertNorm, Lc, L, e, PiLp.coe_continuousLinearEquiv,
    PiLp.coe_symm_continuousLinearEquiv] using
    Lc.le_opNorm (WithLp.toLp 2 x)

/-- The positive invertible elements of the real coordinate algebra. -/
def positiveInvertibles : Set (ι → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Ioi 0

omit [Fintype ι] in
@[simp]
theorem mem_positiveInvertibles {x : ι → ℝ} :
    x ∈ positiveInvertibles ↔ ∀ i, 0 < x i := by
  simp [positiveInvertibles]

omit [Fintype ι] in
theorem isOpen_positiveInvertibles [Finite ι] :
    IsOpen (positiveInvertibles : Set (ι → ℝ)) := by
  apply isOpen_set_pi Set.finite_univ
  intro i _
  exact isOpen_Ioi

/-- Nowosad's functional `L_T(x) = f(x⁻¹ T x)` for the faithful coordinate
sum `f`. -/
noncomputable def lambdaT (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (x : ι → ℝ) : ℝ :=
  coordinateSum (x⁻¹ * T x)

private theorem lambdaT_line (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (z : ι → ℝ) (t : ℝ) :
    lambdaT T (1 + t • z) =
      ∑ i, (T 1 i + t * T z i) / (1 + t * z i) := by
  unfold lambdaT coordinateSum
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.inv_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply,
    smul_eq_mul, Pi.mul_apply, map_add, map_smul]
  rw [div_eq_inv_mul]

private theorem hasDerivAt_lambdaT_line_at_zero
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hAone : A 1 = 0)
    (z : ι → ℝ) :
    HasDerivAt (fun t : ℝ ↦ lambdaT A (1 + t • z))
      (coordinateSum (A z)) 0 := by
  rw [show (fun t : ℝ ↦ lambdaT A (1 + t • z)) =
      fun t : ℝ ↦ ∑ i, (A 1 i + t * A z i) / (1 + t * z i) by
    funext t
    exact lambdaT_line A z t]
  unfold coordinateSum
  apply HasDerivAt.fun_sum
  intro i _
  have hnum : HasDerivAt (fun t : ℝ ↦ A 1 i + t * A z i) (A z i) 0 := by
    simpa only [one_mul] using
      ((hasDerivAt_id' (x := (0 : ℝ))).mul_const (A z i)).const_add (A 1 i)
  have hden : HasDerivAt (fun t : ℝ ↦ 1 + t * z i) (z i) 0 := by
    simpa only [one_mul] using
      ((hasDerivAt_id' (x := (0 : ℝ))).mul_const (z i)).const_add 1
  have hAone_i : A 1 i = 0 := by simpa using congrFun hAone i
  simpa [hAone_i] using hnum.fun_div hden (by norm_num)

private theorem isLocalMin_lambdaT_line_at_zero
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (hmin : IsLocalMinOn (lambdaT A) positiveInvertibles 1)
    (z : ι → ℝ) :
    IsLocalMin (fun t : ℝ ↦ lambdaT A (1 + t • z)) 0 := by
  have hone : (1 : ι → ℝ) ∈ positiveInvertibles := by simp
  have hmin' : IsLocalMin (lambdaT A) (1 : ι → ℝ) :=
    hmin.isLocalMin (isOpen_positiveInvertibles.mem_nhds hone)
  have hcurve : ContinuousAt (fun t : ℝ ↦ (1 : ι → ℝ) + t • z) 0 :=
    continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  have hmin0 : IsLocalMin (lambdaT A)
      ((fun t : ℝ ↦ (1 : ι → ℝ) + t • z) 0) := by
    simpa using hmin'
  change IsLocalMin (lambdaT A ∘ fun t : ℝ ↦ (1 : ι → ℝ) + t • z) 0
  exact IsLocalMin.comp_continuous
    (g := fun t : ℝ ↦ (1 : ι → ℝ) + t • z) (b := 0) hmin0 hcurve

private theorem critical_of_localMinOn_at_one
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hAone : A 1 = 0)
    (hmin : IsLocalMinOn (lambdaT A) positiveInvertibles 1) :
    ∀ z, coordinateSum (A z) = 0 := by
  intro z
  exact (isLocalMin_lambdaT_line_at_zero A hmin z).hasDerivAt_eq_zero
    (hasDerivAt_lambdaT_line_at_zero A hAone z)

private noncomputable def secondVariationRatio
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (z : ι → ℝ) (t : ℝ) : ℝ :=
  -∑ i, A z i * z i / (1 + t * z i)

private theorem secondVariationRatio_zero
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (z : ι → ℝ) :
    secondVariationRatio A z 0 = minimumQuadraticForm A z := by
  simp [secondVariationRatio, minimumQuadraticForm, coordinatePairing]

private theorem secondVariationRatio_continuousAt
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (z : ι → ℝ) :
    ContinuousAt (secondVariationRatio A z) 0 := by
  unfold secondVariationRatio
  apply ContinuousAt.neg
  apply tendsto_finsetSum
  intro i _
  apply ContinuousAt.div₀
  · exact continuousAt_const.mul continuousAt_const
  · exact continuousAt_const.add (continuousAt_id.mul continuousAt_const)
  · norm_num

private theorem lambdaT_line_eq_sq_mul_secondVariationRatio
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hAone : A 1 = 0)
    (hcritical : ∀ x, coordinateSum (A x) = 0)
    (z : ι → ℝ) (t : ℝ) (hden : ∀ i, 1 + t * z i ≠ 0) :
    lambdaT A (1 + t • z) = t ^ 2 * secondVariationRatio A z t := by
  rw [lambdaT_line]
  unfold secondVariationRatio
  have hAone_i : ∀ i, A 1 i = 0 := by
    intro i
    simpa using congrFun hAone i
  simp_rw [hAone_i, zero_add]
  rw [show (∑ i, t * A z i / (1 + t * z i)) =
      t * coordinateSum (A z) -
        t ^ 2 * ∑ i, A z i * z i / (1 + t * z i) by
    unfold coordinateSum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hden i]
    ring]
  rw [hcritical z]
  ring

private theorem quadratic_nonneg_of_localMinOn_at_one
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hAone : A 1 = 0)
    (hmin : IsLocalMinOn (lambdaT A) positiveInvertibles 1) :
    ∀ z, 0 ≤ minimumQuadraticForm A z := by
  intro z
  have hcritical := critical_of_localMinOn_at_one A hAone hmin
  have hlocal := isLocalMin_lambdaT_line_at_zero A hmin z
  have hcurve : ContinuousAt (fun t : ℝ ↦ (1 : ι → ℝ) + t • z) 0 :=
    continuousAt_const.add (continuousAt_id.smul continuousAt_const)
  have hcurve_positive : ∀ᶠ t in 𝓝 (0 : ℝ),
      (1 : ι → ℝ) + t • z ∈ positiveInvertibles :=
    hcurve (isOpen_positiveInvertibles.mem_nhds (by simp))
  have hratio_nonneg : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      0 ≤ secondVariationRatio A z t := by
    filter_upwards [hlocal.filter_mono inf_le_left,
      hcurve_positive.filter_mono inf_le_left, self_mem_nhdsWithin]
      with t hmin_t hpositive ht
    rw [mem_positiveInvertibles] at hpositive
    have hden : ∀ i, 1 + t * z i ≠ 0 := fun i ↦ ne_of_gt (hpositive i)
    have hid := lambdaT_line_eq_sq_mul_secondVariationRatio
      A hAone hcritical z t hden
    have hzero : lambdaT A (1 : ι → ℝ) = 0 := by
      simp [lambdaT, hAone, coordinateSum]
    have hineq : 0 ≤ lambdaT A (1 + t • z) := by
      simpa [hzero] using hmin_t
    rw [hid] at hineq
    have ht_ne : t ≠ 0 := by simpa using ht
    exact nonneg_of_mul_nonneg_right hineq (sq_pos_of_ne_zero ht_ne)
  have hlimit : Tendsto (secondVariationRatio A z) (𝓝[≠] (0 : ℝ))
      (𝓝 (minimumQuadraticForm A z)) := by
    rw [← secondVariationRatio_zero A z]
    exact (secondVariationRatio_continuousAt A z).mono_left inf_le_left
  exact ge_of_tendsto hlimit hratio_nonneg

/-- At the unit, an actual local minimum of Nowosad's functional supplies the
first- and second-variation data used in the algebraic recursion. -/
theorem minimumData_of_localMinOn_at_one
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hAone : A 1 = 0)
    (hmin : IsLocalMinOn (lambdaT A) positiveInvertibles 1) :
    MinimumData A where
  map_one := hAone
  critical := critical_of_localMinOn_at_one A hAone hmin
  quadratic_nonneg := quadratic_nonneg_of_localMinOn_at_one A hAone hmin

omit [Fintype ι] in
@[simp]
theorem normalizeAt_apply_one
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : ι → ℝ) :
    normalizeAt A v 1 = 0 := by
  ext i
  simp [normalizeAt]

private theorem lambdaT_normalizeAt
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v x : ι → ℝ)
    (hv : ∀ i, v i ≠ 0) (hx : ∀ i, x i ≠ 0) :
    lambdaT (normalizeAt A v) x = lambdaT A (v * x) - lambdaT A v := by
  unfold lambdaT coordinateSum normalizeAt
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (x i)⁻¹ * ((v i)⁻¹ * A (v * x) i - (v i)⁻¹ * A v i * x i) =
    (v i * x i)⁻¹ * A (v * x) i - (v i)⁻¹ * A v i
  field_simp [hv i, hx i]

private theorem isLocalMinOn_normalizeAt
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v y : ι → ℝ)
    (hvpos : v ∈ positiveInvertibles)
    (hypos : y ∈ positiveInvertibles)
    (hmin : IsLocalMinOn (lambdaT A) positiveInvertibles (v * y)) :
    IsLocalMinOn (lambdaT (normalizeAt A v)) positiveInvertibles y := by
  let g : (ι → ℝ) → (ι → ℝ) := fun x ↦ v * x
  have hg_maps : positiveInvertibles ⊆ g ⁻¹' positiveInvertibles := by
    intro x hx
    rw [mem_positiveInvertibles] at hvpos hx
    change g x ∈ positiveInvertibles
    rw [mem_positiveInvertibles]
    exact fun i ↦ mul_pos (hvpos i) (hx i)
  have hg_cont : ContinuousOn g positiveInvertibles := by
    exact (continuous_const.mul continuous_id).continuousOn
  have hmin_g_y : IsLocalMinOn (lambdaT A) positiveInvertibles (g y) := by
    simpa [g] using hmin
  have hcomp : IsLocalMinOn (lambdaT A ∘ g) positiveInvertibles y :=
    IsLocalMinOn.comp_continuousOn hmin_g_y hg_maps hg_cont hypos
  have hshift : IsLocalMinOn
      ((fun y : ℝ ↦ y - lambdaT A v) ∘ (lambdaT A ∘ g))
      positiveInvertibles y :=
    hcomp.comp_mono (fun _ _ hab ↦ sub_le_sub_right hab _)
  apply hshift.congr
  · filter_upwards [self_mem_nhdsWithin] with x hx
    rw [mem_positiveInvertibles] at hvpos hx
    exact (lambdaT_normalizeAt A v x (fun i ↦ ne_of_gt (hvpos i))
      (fun i ↦ ne_of_gt (hx i))).symm
  · exact hypos

private theorem isLocalMinOn_normalizeAt_at_one
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : ι → ℝ)
    (hvpos : v ∈ positiveInvertibles)
    (hmin : IsLocalMinOn (lambdaT A) positiveInvertibles v) :
    IsLocalMinOn (lambdaT (normalizeAt A v)) positiveInvertibles 1 := by
  apply isLocalMinOn_normalizeAt A v 1 hvpos (by simp)
  simpa using hmin

/-- A local minimum at `v` gives the second normalized variation package
used in Nowosad's comparison argument. -/
theorem minimumData_normalizeAt_of_localMinOn
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : ι → ℝ)
    (hvpos : v ∈ positiveInvertibles)
    (hmin : IsLocalMinOn (lambdaT A) positiveInvertibles v) :
    MinimumData (normalizeAt A v) :=
  minimumData_of_localMinOn_at_one (normalizeAt A v)
    (normalizeAt_apply_one A v)
    (isLocalMinOn_normalizeAt_at_one A v hvpos hmin)

/-- The normalized finite-coordinate specialization of Nowosad's Theorem
1.8, stated with genuine local-minimum hypotheses rather than assumed
variation identities. -/
theorem eq_zero_on_laurentSubalgebra_of_two_localMinOn
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : ι → ℝ)
    (hAone : A 1 = 0) (hvpos : v ∈ positiveInvertibles)
    (hminOne : IsLocalMinOn (lambdaT A) positiveInvertibles 1)
    (hminV : IsLocalMinOn (lambdaT A) positiveInvertibles v)
    (q : laurentSubalgebra v) : A q = 0 := by
  have hv : ∀ i, v i ≠ 0 := by
    rw [mem_positiveInvertibles] at hvpos
    exact fun i ↦ ne_of_gt (hvpos i)
  apply eq_zero_on_laurentSubalgebra_of_two_minimumData A v hv
  · exact minimumData_of_localMinOn_at_one A hAone hminOne
  · exact minimumData_normalizeAt_of_localMinOn A v hvpos hminV

/-- The finite-coordinate conclusion of Nowosad's Theorem 1.8.  If `u` and
`v` are local minima, then on `u · P(u⁻¹v)` the operator is multiplication by
the fixed vector `δ = u⁻¹ A u`.  The null-space error in the general theorem
is absent because `coordinate_null_eq_zero` proves `N = 0` here. -/
theorem multiplication_on_laurentSubalgebra_of_two_localMinOn
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (u v : ι → ℝ)
    (hupos : u ∈ positiveInvertibles) (hvpos : v ∈ positiveInvertibles)
    (hminU : IsLocalMinOn (lambdaT A) positiveInvertibles u)
    (hminV : IsLocalMinOn (lambdaT A) positiveInvertibles v)
    (q : laurentSubalgebra (u⁻¹ * v)) :
    A (u * (q : ι → ℝ)) =
      (u⁻¹ * A u) * (u * (q : ι → ℝ)) := by
  let w : ι → ℝ := u⁻¹ * v
  let D : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := normalizeAt A u
  have hu : ∀ i, u i ≠ 0 := by
    rw [mem_positiveInvertibles] at hupos
    exact fun i ↦ ne_of_gt (hupos i)
  have hwpos : w ∈ positiveInvertibles := by
    rw [mem_positiveInvertibles] at hupos hvpos ⊢
    exact fun i ↦ mul_pos (inv_pos.mpr (hupos i)) (hvpos i)
  have huw : u * w = v := by
    ext i
    dsimp [w]
    field_simp [hu i]
  have hminDOne : IsLocalMinOn (lambdaT D) positiveInvertibles 1 := by
    exact isLocalMinOn_normalizeAt_at_one A u hupos hminU
  have hminDW : IsLocalMinOn (lambdaT D) positiveInvertibles w := by
    apply isLocalMinOn_normalizeAt A u w hupos hwpos
    rw [huw]
    exact hminV
  have hD : MinimumData D :=
    minimumData_of_localMinOn_at_one D (normalizeAt_apply_one A u) hminDOne
  have hwD : MinimumData (normalizeAt D w) :=
    minimumData_normalizeAt_of_localMinOn D w hwpos hminDW
  have hw : ∀ i, w i ≠ 0 := by
    rw [mem_positiveInvertibles] at hwpos
    exact fun i ↦ ne_of_gt (hwpos i)
  have hDq : D q = 0 :=
    eq_zero_on_laurentSubalgebra_of_two_minimumData D w hw hD hwD
      ⟨q, q.property⟩
  ext i
  have hDqi := congrFun hDq i
  change (u i)⁻¹ * A (u * (q : ι → ℝ)) i -
      (u i)⁻¹ * A u i * (q : ι → ℝ) i = 0 at hDqi
  simp only [Pi.mul_apply, Pi.inv_apply]
  field_simp [hu i] at hDqi ⊢
  linarith

end Nowosad
