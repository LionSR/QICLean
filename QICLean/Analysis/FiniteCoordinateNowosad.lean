/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib

/-!
# Nowosad's local-extremum theorem in a finite coordinate algebra

This file isolates the finite-dimensional specialization of Pedro Nowosad's
Theorem 1.8 used by Shigeru Yamagami in the proof of the cyclic inequalities.
The ambient algebra is the coordinate algebra `ι → ℝ`, with coordinatewise
multiplication and the faithful positive functional `x ↦ ∑ i, x i`.

The proof follows Nowosad's argument on pp. 409--418.  First and second
variation at the two local minima give two nonnegative quadratic forms.  Their
common zero vectors yield the recursion corresponding to Nowosad's equations
(1.19)--(1.20), and hence the Laurent-polynomial product rule (1.28).  The
coordinate point derivations are then killed by the value-class Lagrange
idempotents, which are the finite-coordinate replacement for the
Singer--Wermer step in the general Banach-algebra proof.

Nowosad's theorem has the local-**minimum** orientation.  The local-maximum
form used by Yamagami is stated separately and is obtained by replacing the
operator by its negative.

## Sources

* P. Nowosad, *Isoperimetric eigenvalue problems in algebras*, Comm. Pure
  Appl. Math. 21 (1968), 401--465, especially pp. 409--418.
* S. Yamagami, *Cyclic inequalities*, Proc. Amer. Math. Soc. 118 (1993),
  521--527, Theorem 1 and Lemma 3 on pp. 522--523.
-/

open scoped BigOperators
open Filter Topology

namespace Nowosad

variable {ι : Type*} [Fintype ι]

/-- The faithful positive functional used on a finite coordinate algebra. -/
def coordinateSum (x : ι → ℝ) : ℝ := ∑ i, x i

/-- The Euclidean pairing written in coordinate-algebra notation. -/
def coordinatePairing (x y : ι → ℝ) : ℝ := ∑ i, x i * y i

/-- The null space `N = {x | f(x*x) = 0}` in Nowosad's construction is zero
for the faithful coordinate sum.  Thus equation (1.29) descends without an
error term in the finite coordinate algebra. -/
theorem coordinate_null_eq_zero {x : ι → ℝ}
    (hx : coordinateSum (x * x) = 0) : x = 0 := by
  funext i
  have hi : x i * x i = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ mul_self_nonneg (x j))).mp _ i (Finset.mem_univ i)
    simpa [coordinateSum] using hx
  simpa using (mul_self_eq_zero.mp hi)

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

theorem isOpen_positiveInvertibles : IsOpen (positiveInvertibles : Set (ι → ℝ)) := by
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

/-- The quadratic form obtained from the second variation at the unit after
subtracting the multiplication part of the operator. -/
def minimumQuadraticForm (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (x : ι → ℝ) : ℝ :=
  -coordinatePairing (A x) x

/-- The normalized operator at a second strictly positive point `v`.  If
`p = v⁻¹ * A v`, this is `T_v⁻¹ A T_v - V_p` in Nowosad's notation. -/
noncomputable def normalizeAt (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : ι → ℝ) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun x := v⁻¹ * A (v * x) - (v⁻¹ * A v) * x
  map_add' x y := by
    ext i
    simp [mul_add]
    ring
  map_smul' r x := by
    ext i
    simp
    ring

/-- The finite-coordinate first- and second-variation data at the unit.  The
three fields respectively record `A 1 = 0`, equation (1.11), and
nonnegativity of the quadratic form in equations (1.13)--(1.14). -/
structure MinimumData (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : Prop where
  map_one : A 1 = 0
  critical : ∀ x, coordinateSum (A x) = 0
  quadratic_nonneg : ∀ x, 0 ≤ minimumQuadraticForm A x

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

/-- If a nonnegative quadratic form associated with `A` vanishes at `x`, its
polarization against every `y` vanishes.  This is the elementary
finite-dimensional zero-of-positive-form step used in Nowosad's recursion. -/
theorem polarization_eq_zero_of_quadratic_eq_zero
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (hA : ∀ z, 0 ≤ minimumQuadraticForm A z) {x : ι → ℝ}
    (hx : minimumQuadraticForm A x = 0) (y : ι → ℝ) :
    coordinatePairing (A x) y + coordinatePairing (A y) x = 0 := by
  classical
  set c := coordinatePairing (A x) y + coordinatePairing (A y) x
  set d := minimumQuadraticForm A y
  have hx' : -(∑ i, A x i * x i) = 0 := hx
  have hquad : ∀ t : ℝ,
      minimumQuadraticForm A (x + t • y) = -t * c + t ^ 2 * d := by
    intro t
    unfold minimumQuadraticForm coordinatePairing
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp [c, d, coordinatePairing, minimumQuadraticForm]
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
    ring_nf
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    rw [← Finset.mul_sum]
    rw [← Finset.mul_sum]
    rw [hx']
    ring
  have hd : 0 ≤ d := hA y
  rcases eq_or_lt_of_le hd with hd0 | hdpos
  · have hp := hA (x + (1 : ℝ) • y)
    rw [hquad 1, ← hd0] at hp
    have hm := hA (x + (-1 : ℝ) • y)
    rw [hquad (-1), ← hd0] at hm
    norm_num at hp hm
    exact le_antisymm hp hm
  · have hs := hA (x + (c / (2 * d)) • y)
    rw [hquad] at hs
    field_simp [ne_of_gt hdpos] at hs
    nlinarith [sq_nonneg c]

private theorem coordinatePairing_smul_left (r : ℝ) (x y : ι → ℝ) :
    coordinatePairing (r • x) y = r * coordinatePairing x y := by
  unfold coordinatePairing
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

private theorem coordinatePairing_smul_right (r : ℝ) (x y : ι → ℝ) :
    coordinatePairing x (r • y) = r * coordinatePairing x y := by
  unfold coordinatePairing
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (∑ i, x i * (r * y i)) = ∑ i, r * (x i * y i) by
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [← Finset.mul_sum]

private theorem coordinatePairing_comm (x y : ι → ℝ) :
    coordinatePairing x y = coordinatePairing y x := by
  unfold coordinatePairing
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem coordinatePairing_sub_left (x y z : ι → ℝ) :
    coordinatePairing (x - y) z =
      coordinatePairing x z - coordinatePairing y z := by
  simp [coordinatePairing, sub_mul, Finset.sum_sub_distrib]

private theorem coordinatePairing_inv_mul_pow_succ (v x : ι → ℝ)
    (hv : ∀ i, v i ≠ 0) (n : ℕ) :
    coordinatePairing (v⁻¹ * x) (v ^ (n + 1)) =
      coordinatePairing x (v ^ n) := by
  unfold coordinatePairing
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.inv_apply, Pi.mul_apply, Pi.pow_apply]
  rw [pow_succ]
  field_simp [hv i]

private theorem coordinatePairing_inv_mul_mul (v x y : ι → ℝ)
    (hv : ∀ i, v i ≠ 0) :
    coordinatePairing (v⁻¹ * x) (v * y) = coordinatePairing x y := by
  unfold coordinatePairing
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.inv_apply, Pi.mul_apply]
  field_simp [hv i]

private theorem eq_of_coordinatePairing_eq (x y : ι → ℝ)
    (h : ∀ z, coordinatePairing x z = coordinatePairing y z) : x = y := by
  classical
  funext i
  have hi := h (fun j ↦ if j = i then 1 else 0)
  unfold coordinatePairing at hi
  simpa using hi

/-- Nowosad's power recursion, equations (1.19)--(1.20), in the faithful real
coordinate algebra.  The first minimum supplies `MinimumData A`; the second
minimum supplies the same data for `normalizeAt A v`.

The vector `p = v⁻¹ * A v` is Nowosad's multiplication coefficient. -/
theorem power_recursion_of_two_minimumData
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : ι → ℝ)
    (hv : ∀ i, v i ≠ 0) (hA : MinimumData A)
    (hvA : MinimumData (normalizeAt A v)) (n : ℕ) :
    A (v ^ n) = (n : ℝ) • ((v⁻¹ * A v) * v ^ n) := by
  classical
  set p : ι → ℝ := v⁻¹ * A v
  have hstate : ∀ k : ℕ,
      A (v ^ (k + 1)) = ((k + 1 : ℕ) : ℝ) • (p * v ^ (k + 1)) ∧
      ∀ z, coordinatePairing (A z) (v ^ k) =
        coordinatePairing z ((-(k : ℝ)) • (p * v ^ k)) := by
    intro k
    induction k with
    | zero =>
      constructor
      · ext i
        simp [p]
        field_simp [hv i]
      · intro z
        simpa [coordinatePairing, coordinateSum] using hA.critical z
    | succ k ih =>
      rcases ih with ⟨hforward, hbackward⟩
      set m : ℝ := coordinatePairing (p * v ^ (k + 1)) (v ^ (k + 1))
      have hmoment : coordinatePairing (v ^ (k + 1 + 1)) (p * v ^ k) = m := by
        unfold coordinatePairing
        dsimp [m]
        unfold coordinatePairing
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.mul_apply, Pi.pow_apply]
        ring_nf
      have hqA : minimumQuadraticForm A (v ^ (k + 1)) =
          -(((k + 1 : ℕ) : ℝ) * m) := by
        rw [minimumQuadraticForm, hforward, coordinatePairing_smul_left]
      have hqB : minimumQuadraticForm (normalizeAt A v) (v ^ (k + 1)) =
          ((k + 1 : ℕ) : ℝ) * m := by
        unfold minimumQuadraticForm normalizeAt
        change -coordinatePairing
          (v⁻¹ * A (v * v ^ (k + 1)) - p * v ^ (k + 1)) (v ^ (k + 1)) = _
        rw [show v * v ^ (k + 1) = v ^ (k + 1 + 1) by
          simp [pow_succ']]
        rw [show coordinatePairing
            (v⁻¹ * A (v ^ (k + 1 + 1)) - p * v ^ (k + 1)) (v ^ (k + 1)) =
            coordinatePairing (v⁻¹ * A (v ^ (k + 1 + 1))) (v ^ (k + 1)) -
              coordinatePairing (p * v ^ (k + 1)) (v ^ (k + 1)) by
          simp [coordinatePairing, sub_mul, Finset.sum_sub_distrib]]
        rw [coordinatePairing_inv_mul_pow_succ v _ hv k]
        rw [hbackward]
        rw [coordinatePairing_smul_right, hmoment]
        change -(-((k : ℝ)) * m - m) = ((k + 1 : ℕ) : ℝ) * m
        push_cast
        ring
      have hnonnegA := hA.quadratic_nonneg (v ^ (k + 1))
      have hnonnegB := hvA.quadratic_nonneg (v ^ (k + 1))
      rw [hqA] at hnonnegA
      rw [hqB] at hnonnegB
      have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have hmzero : m = 0 := by nlinarith
      have hzeroA : minimumQuadraticForm A (v ^ (k + 1)) = 0 := by
        rw [hqA, hmzero]
        ring
      have hzeroB : minimumQuadraticForm (normalizeAt A v) (v ^ (k + 1)) = 0 := by
        rw [hqB, hmzero]
        ring
      have hbackwardNext : ∀ z, coordinatePairing (A z) (v ^ (k + 1)) =
          coordinatePairing z ((-((k + 1 : ℕ) : ℝ)) • (p * v ^ (k + 1))) := by
        intro z
        have hpolar := polarization_eq_zero_of_quadratic_eq_zero
          A hA.quadratic_nonneg hzeroA z
        rw [hforward, coordinatePairing_smul_left] at hpolar
        rw [coordinatePairing_smul_right]
        rw [coordinatePairing_comm (p * v ^ (k + 1)) z] at hpolar
        linarith
      have hforwardPair : ∀ z, coordinatePairing (A (v ^ (k + 1 + 1))) z =
          coordinatePairing (((k + 1 + 1 : ℕ) : ℝ) •
            (p * v ^ (k + 1 + 1))) z := by
        intro z
        have hpolar := polarization_eq_zero_of_quadratic_eq_zero
          (normalizeAt A v) hvA.quadratic_nonneg hzeroB (v * z)
        change coordinatePairing
            (v⁻¹ * A (v * v ^ (k + 1)) - p * v ^ (k + 1)) (v * z) +
            coordinatePairing
              (v⁻¹ * A (v * (v * z)) - p * (v * z)) (v ^ (k + 1)) = 0
          at hpolar
        rw [coordinatePairing_sub_left, coordinatePairing_sub_left] at hpolar
        rw [coordinatePairing_inv_mul_mul v _ z hv] at hpolar
        rw [coordinatePairing_inv_mul_pow_succ v _ hv k] at hpolar
        rw [hbackward (v * (v * z))] at hpolar
        rw [show v * v ^ (k + 1) = v ^ (k + 1 + 1) by
          simp [pow_succ']] at hpolar
        have htermOne : coordinatePairing (p * v ^ (k + 1)) (v * z) =
            coordinatePairing (p * v ^ (k + 1 + 1)) z := by
          unfold coordinatePairing
          apply Finset.sum_congr rfl
          intro i _
          simp only [Pi.mul_apply, Pi.pow_apply]
          rw [pow_succ]
          ring
        have htermTwo : coordinatePairing (v * (v * z))
              ((-(k : ℝ)) • (p * v ^ k)) =
            -(k : ℝ) * coordinatePairing (p * v ^ (k + 1 + 1)) z := by
          rw [coordinatePairing_smul_right]
          congr 1
          unfold coordinatePairing
          apply Finset.sum_congr rfl
          intro i _
          simp only [Pi.mul_apply, Pi.pow_apply]
          rw [show v i ^ (k + 1 + 1) = v i ^ k * v i * v i by
            rw [pow_succ, pow_succ]]
          ring
        have htermThree : coordinatePairing (p * (v * z)) (v ^ (k + 1)) =
            coordinatePairing (p * v ^ (k + 1 + 1)) z := by
          unfold coordinatePairing
          apply Finset.sum_congr rfl
          intro i _
          simp only [Pi.mul_apply, Pi.pow_apply]
          rw [show v i ^ (k + 1 + 1) = v i * v i ^ (k + 1) by
            rw [pow_succ']]
          ring
        rw [htermOne, htermTwo, htermThree] at hpolar
        rw [coordinatePairing_smul_left]
        push_cast at hpolar ⊢
        linarith
      exact ⟨eq_of_coordinatePairing_eq _ _ hforwardPair, hbackwardNext⟩
  cases n with
  | zero => simpa using hA.map_one
  | succ k => simpa [Nat.succ_eq_add_one] using (hstate k).1

/-- The finite-coordinate form of Nowosad's Laurent-polynomial identity
(1.23), first for ordinary polynomials. -/
theorem polynomial_chain_rule_of_two_minimumData
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : ι → ℝ)
    (hv : ∀ i, v i ≠ 0) (hA : MinimumData A)
    (hvA : MinimumData (normalizeAt A v)) (q : Polynomial ℝ) :
    A (Polynomial.aeval v q) =
      (v * (v⁻¹ * A v)) * Polynomial.aeval v (Polynomial.derivative q) := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    simp only [map_add, hq, hr, mul_add]
  | monomial n a =>
    cases n with
    | zero =>
      simp only [Polynomial.aeval_monomial, pow_zero, mul_one,
        Polynomial.derivative_monomial, Nat.cast_zero]
      rw [show (algebraMap ℝ (ι → ℝ)) a = a • (1 : ι → ℝ) by
        ext i
        simp]
      rw [map_smul, hA.map_one, smul_zero]
      simp
    | succ n =>
      have hpower := power_recursion_of_two_minimumData A v hv hA hvA (n + 1)
      rw [Polynomial.aeval_monomial]
      rw [show (algebraMap ℝ (ι → ℝ)) a * v ^ (n + 1) = a • v ^ (n + 1) by
        ext i
        simp]
      rw [map_smul, hpower]
      rw [Polynomial.derivative_monomial]
      simp only [Nat.add_sub_cancel, Polynomial.aeval_monomial]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.inv_apply,
        Pi.pow_apply, map_mul, map_natCast, Pi.algebraMap_apply,
        Pi.natCast_apply, Algebra.algebraMap_self_apply]
      rw [pow_succ]
      ring

/-- Nowosad's product rule (1.28) on the ordinary polynomial algebra
generated by the second minimum. -/
theorem polynomial_product_rule_of_two_minimumData
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : ι → ℝ)
    (hv : ∀ i, v i ≠ 0) (hA : MinimumData A)
    (hvA : MinimumData (normalizeAt A v)) {q r : ι → ℝ}
    (hq : q ∈ Algebra.adjoin ℝ ({v} : Set (ι → ℝ)))
    (hr : r ∈ Algebra.adjoin ℝ ({v} : Set (ι → ℝ))) :
    A (q * r) = q * A r + r * A q := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hq hr
  rcases hq with ⟨q₀, rfl⟩
  rcases hr with ⟨r₀, rfl⟩
  rw [← map_mul]
  change A (Polynomial.aeval v (q₀ * r₀)) =
    Polynomial.aeval v q₀ * A (Polynomial.aeval v r₀) +
      Polynomial.aeval v r₀ * A (Polynomial.aeval v q₀)
  rw [polynomial_chain_rule_of_two_minimumData A v hv hA hvA]
  rw [Polynomial.derivative_mul, map_add, map_mul, map_mul, mul_add]
  rw [polynomial_chain_rule_of_two_minimumData A v hv hA hvA q₀]
  rw [polynomial_chain_rule_of_two_minimumData A v hv hA hvA r₀]
  ring

/-- The Laurent-polynomial subalgebra generated by a coordinate vector. -/
def laurentSubalgebra (w : ι → ℝ) : Subalgebra ℝ (ι → ℝ) :=
  Algebra.adjoin ℝ ({w, w⁻¹} : Set (ι → ℝ))

/-- The Lagrange idempotent of the value class of `w i`.  It is one precisely
on the coordinates at which `w` has the same value as at `i`. -/
noncomputable def valueClassIdempotent (w : ι → ℝ) (i : ι) : ι → ℝ :=
  fun j ↦ if w j = w i then 1 else 0

omit [Fintype ι] in
theorem valueClassIdempotent_apply (w : ι → ℝ) (i j : ι) :
    valueClassIdempotent w i j = if w j = w i then 1 else 0 := by
  rfl

/-- The value-class idempotent is an ordinary polynomial in `w`. -/
theorem valueClassIdempotent_mem_polynomialSubalgebra (w : ι → ℝ) (i : ι) :
    valueClassIdempotent w i ∈
      Algebra.adjoin ℝ ({w} : Set (ι → ℝ)) := by
  classical
  let e : ι → ℝ := ∏ r ∈ (Finset.univ.image w).erase (w i),
    (w - (algebraMap ℝ (ι → ℝ)) r) *
      (algebraMap ℝ (ι → ℝ)) ((w i - r)⁻¹)
  have he_mem : e ∈ Algebra.adjoin ℝ ({w} : Set (ι → ℝ)) := by
    dsimp [e]
    apply Subalgebra.prod_mem
    intro r hr
    apply Subalgebra.mul_mem
    · apply Subalgebra.sub_mem
      · exact Algebra.subset_adjoin (by simp)
      · exact Subalgebra.algebraMap_mem _ r
    · exact Subalgebra.algebraMap_mem _ _
  have he_eq : e = valueClassIdempotent w i := by
    funext j
    rw [valueClassIdempotent_apply]
    by_cases hji : w j = w i
    · simp only [hji, ↓reduceIte]
      dsimp [e]
      simp only [Finset.prod_apply, Pi.mul_apply, Pi.sub_apply,
        Pi.algebraMap_apply, Algebra.algebraMap_self_apply]
      apply Finset.prod_eq_one
      intro r hr
      have hri : r ≠ w i := (Finset.mem_erase.mp hr).1
      rw [hji]
      field_simp
    · simp only [hji, ↓reduceIte]
      dsimp [e]
      simp only [Finset.prod_apply, Pi.mul_apply, Pi.sub_apply,
        Pi.algebraMap_apply, Algebra.algebraMap_self_apply]
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji,
        Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
      simp
  rw [← he_eq]
  exact he_mem

/-- The value-class idempotent also belongs to Nowosad's Laurent-polynomial
algebra. -/
theorem valueClassIdempotent_mem_laurentSubalgebra (w : ι → ℝ) (i : ι) :
    valueClassIdempotent w i ∈ laurentSubalgebra w := by
  apply Algebra.adjoin_mono (R := ℝ) (show ({w} : Set (ι → ℝ)) ⊆ {w, w⁻¹} by
    simp)
  exact valueClassIdempotent_mem_polynomialSubalgebra w i

/-- In a finite coordinate algebra, the inverse of a pointwise-invertible
generator is already an ordinary polynomial in that generator.  This is the
finite Lagrange-interpolation replacement for the analytic closure argument
in Nowosad's general theorem. -/
theorem inv_mem_polynomialSubalgebra (w : ι → ℝ) :
    w⁻¹ ∈ Algebra.adjoin ℝ ({w} : Set (ι → ℝ)) := by
  classical
  let values : Finset ℝ := Finset.univ.image w
  let representative : ↥values → ι := fun r ↦
    (Finset.mem_image.mp r.property).choose
  have hrepresentative (r : ↥values) : w (representative r) = r := by
    exact (Finset.mem_image.mp r.property).choose_spec.2
  let inverseInterpolation : ι → ℝ :=
    ∑ r : ↥values, (r : ℝ)⁻¹ • valueClassIdempotent w (representative r)
  have hinterpolation_mem : inverseInterpolation ∈
      Algebra.adjoin ℝ ({w} : Set (ι → ℝ)) := by
    dsimp [inverseInterpolation]
    apply Subalgebra.sum_mem
    intro r _
    exact (Algebra.adjoin ℝ ({w} : Set (ι → ℝ))).smul_mem
      (valueClassIdempotent_mem_polynomialSubalgebra w (representative r)) _
  have hinterpolation_eq : inverseInterpolation = w⁻¹ := by
    funext j
    dsimp [inverseInterpolation]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    let rj : ↥values := ⟨w j, Finset.mem_image.mpr
      ⟨j, Finset.mem_univ j, rfl⟩⟩
    rw [Finset.sum_eq_single rj]
    · have hsame : w j = w (representative rj) := (hrepresentative rj).symm
      rw [valueClassIdempotent_apply]
      simp only [hsame, ↓reduceIte, mul_one]
      exact congrArg Inv.inv (hrepresentative rj).symm
    · intro r _ hr
      have hne : w j ≠ w (representative r) := by
        intro hvalue
        apply hr
        apply Subtype.ext
        simpa [rj] using (hvalue.trans (hrepresentative r)).symm
      simp [valueClassIdempotent_apply, hne]
    · simp
  rw [← hinterpolation_eq]
  exact hinterpolation_mem

/-- For a finite coordinate algebra, Nowosad's Laurent-polynomial algebra is
already the ordinary polynomial algebra generated by `w`. -/
theorem laurentSubalgebra_eq_polynomialSubalgebra (w : ι → ℝ) :
    laurentSubalgebra w = Algebra.adjoin ℝ ({w} : Set (ι → ℝ)) := by
  apply le_antisymm
  · unfold laurentSubalgebra
    apply Algebra.adjoin_le
    intro x hx
    rcases hx with (rfl | hx)
    · exact Algebra.subset_adjoin (by simp)
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact inv_mem_polynomialSubalgebra w
  · apply Algebra.adjoin_mono (R := ℝ)
    simp

/-- Nowosad's exact product rule (1.28) on the finite Laurent-polynomial
algebra.  Faithfulness of the coordinate sum means that the null ideal in
(1.29) is zero, so no quotient error remains. -/
theorem laurent_product_rule_of_two_minimumData
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : ι → ℝ)
    (hv : ∀ i, v i ≠ 0) (hA : MinimumData A)
    (hvA : MinimumData (normalizeAt A v))
    (q r : laurentSubalgebra v) :
    A ((q : ι → ℝ) * (r : ι → ℝ)) =
      (q : ι → ℝ) * A r + (r : ι → ℝ) * A q := by
  apply polynomial_product_rule_of_two_minimumData A v hv hA hvA
  · rw [← laurentSubalgebra_eq_polynomialSubalgebra v]
    exact q.property
  · rw [← laurentSubalgebra_eq_polynomialSubalgebra v]
    exact r.property

omit [Fintype ι] in
/-- Every element of the Laurent algebra generated by `w` is constant on each
value class of `w`. -/
theorem eq_on_valueClass_of_mem_laurentSubalgebra {w q : ι → ℝ}
    (hq : q ∈ laurentSubalgebra w) {i j : ι} (hij : w i = w j) :
    q i = q j := by
  unfold laurentSubalgebra at hq
  induction hq using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with (rfl | hx)
    · exact hij
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact congrArg Inv.inv hij
  | algebraMap r => simp [Pi.algebraMap_apply]
  | add x y _ _ hx hy => simpa only [Pi.add_apply] using congrArg₂ (· + ·) hx hy
  | mul x y _ _ hx hy => simpa only [Pi.mul_apply] using congrArg₂ (· * ·) hx hy

/-- A coordinate point derivation on the finite Laurent algebra vanishes.
The proof uses the explicitly named value-class idempotent, exactly as in the
finite-coordinate Singer--Wermer step of Nowosad's proof. -/
theorem coordinate_pointDerivation_eq_zero
    (w : ι → ℝ) (i : ι) (D : (laurentSubalgebra w) →ₗ[ℝ] ℝ)
    (hD : ∀ q r,
      D (q * r) = (q : ι → ℝ) i * D r + (r : ι → ℝ) i * D q) :
    D = 0 := by
  classical
  let e : laurentSubalgebra w :=
    ⟨valueClassIdempotent w i, valueClassIdempotent_mem_laurentSubalgebra w i⟩
  have he_mul : e * e = e := by
    ext j
    simp only [Subalgebra.coe_mul, Pi.mul_apply]
    change valueClassIdempotent w i j * valueClassIdempotent w i j =
      valueClassIdempotent w i j
    rw [valueClassIdempotent_apply]
    split_ifs <;> ring
  have he_apply : (e : ι → ℝ) i = 1 := by
    simp [e, valueClassIdempotent]
  have hDe : D e = 0 := by
    have h := hD e e
    rw [he_mul, he_apply] at h
    linarith
  apply LinearMap.ext
  intro q
  rw [LinearMap.zero_apply]
  have hqe : q * e = ((q : ι → ℝ) i) • e := by
    ext j
    simp only [Subalgebra.coe_mul, Pi.mul_apply, SetLike.val_smul,
      Pi.smul_apply, smul_eq_mul]
    change (q : ι → ℝ) j * valueClassIdempotent w i j =
      (q : ι → ℝ) i * valueClassIdempotent w i j
    rw [valueClassIdempotent_apply]
    by_cases hji : w j = w i
    · simp only [hji, ↓reduceIte]
      congr 1
      exact eq_on_valueClass_of_mem_laurentSubalgebra q.property hji
    · simp only [hji, ↓reduceIte]
      ring
  have h := hD q e
  rw [hqe, map_smul, hDe, smul_zero, he_apply] at h
  simpa using h.symm

/-- In the normalized finite-coordinate situation, the operator vanishes on
the Laurent-polynomial algebra.  This is the finite idempotent conclusion of
Nowosad's Theorem 1.8 after equations (1.28)--(1.29). -/
theorem eq_zero_on_laurentSubalgebra_of_two_minimumData
    (A : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : ι → ℝ)
    (hv : ∀ i, v i ≠ 0) (hA : MinimumData A)
    (hvA : MinimumData (normalizeAt A v))
    (q : laurentSubalgebra v) : A q = 0 := by
  ext i
  change A (q : ι → ℝ) i = 0
  let D : (laurentSubalgebra v) →ₗ[ℝ] ℝ :=
    { toFun := fun r ↦ A (r : ι → ℝ) i
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp }
  have hD : ∀ r s,
      D (r * s) = (r : ι → ℝ) i * D s + (s : ι → ℝ) i * D r := by
    intro r s
    have hproduct := laurent_product_rule_of_two_minimumData
      A v hv hA hvA r s
    exact congrFun hproduct i
  have hzero := coordinate_pointDerivation_eq_zero v i D hD
  have hqzero : D q = 0 := by rw [hzero]; rfl
  exact hqzero

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
