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

end Nowosad
