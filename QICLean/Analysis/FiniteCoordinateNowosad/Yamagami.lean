/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FiniteCoordinateNowosad

/-!
# Yamagami's finite-coordinate application of Nowosad's theorem

This file formalizes the change of variables in Yamagami's Lemma 3.  For an
invertible matrix `S` with `S 1 = s 1`, the functional

`x ↦ L_{S⁻¹}(S x)`

is transferred to Nowosad's coordinate functional.  If a second local
maximum occurs at `a`, the generator to which Nowosad's theorem applies is

`b = (S a) / s`,

not `a`.  The corresponding curve in the original coordinates is

`x(t) = s S⁻¹ (b^t)`.

The proof follows S. Yamagami, *Cyclic inequalities*, Proc. Amer. Math. Soc.
118 (1993), 521--527, Theorem 1 and Lemma 3 on pp. 522--523, using the finite
specialization of P. Nowosad, *Isoperimetric eigenvalue problems in algebras*,
Comm. Pure Appl. Math. 21 (1968), 401--465, Theorem 1.8 on pp. 417--418.
-/

open scoped BigOperators Matrix
open Nowosad

namespace Yamagami

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A coordinate vector is projectively scalar when it lies on the line
through the unit vector. -/
def IsScalarVector (x : ι → ℝ) : Prop :=
  ∃ c : ℝ, x = c • (1 : ι → ℝ)

/-- The operator `S⁻¹` in Yamagami's application, acting on column vectors. -/
noncomputable def inverseOperator (S : Matrix ι ι ℝ) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  Matrix.mulVecLin S⁻¹

/-- The operator at the unit after changing a maximum of `L_{S⁻¹}` into a
minimum of `L_{-S⁻¹}` and subtracting its multiplication part. -/
noncomputable def normalizedNegativeInverse (S : Matrix ι ι ℝ) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  normalizeAt (-(inverseOperator S)) 1

@[simp]
theorem inverseOperator_apply (S : Matrix ι ι ℝ) (x : ι → ℝ) :
    inverseOperator S x = S⁻¹ *ᵥ x := by
  simp [inverseOperator]

/-- Yamagami's normalized Nowosad generator `b = (S a) / s`. -/
noncomputable def transformedGenerator
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ) : ι → ℝ :=
  s⁻¹ • (S *ᵥ a)

omit [DecidableEq ι] in
@[simp]
theorem transformedGenerator_apply
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ) (i : ι) :
    transformedGenerator S s a i = (S *ᵥ a) i / s := by
  simp [transformedGenerator, div_eq_mul_inv, mul_comm]

/-- Coordinatewise real powers of a strictly positive vector. -/
noncomputable def coordinateRpow (b : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun i ↦ b i ^ t

/-- The logarithm of a strictly positive coordinate vector. -/
noncomputable def coordinateLog (b : ι → ℝ) : ι → ℝ :=
  fun i ↦ Real.log (b i)

/-- The curve in the original coordinates prescribed in Yamagami's proof:
`x(t) = s S⁻¹ (b^t)`. -/
noncomputable def pulledBackCurve
    (S : Matrix ι ι ℝ) (s : ℝ) (b : ι → ℝ) (t : ℝ) : ι → ℝ :=
  s • (S⁻¹ *ᵥ coordinateRpow b t)

/-- Yamagami's negative-Hessian representative.  For
`f_S(x) = ∑ i, x i / (Sx) i`, one has
`D²f_S(1)[h,h] = -s⁻³ ⟨h, hessianMatrix S s · h⟩`; the omitted factor
`s⁻³` is positive and therefore does not change positivity or the kernel. -/
def hessianMatrix (S : Matrix ι ι ℝ) (s : ℝ) : Matrix ι ι ℝ :=
  s • (S + S.transpose) - 2 • (S.transpose * S)

omit [DecidableEq ι] in
theorem dotProduct_hessianMatrix_mulVec
    (S : Matrix ι ι ℝ) (s : ℝ) (x : ι → ℝ) :
    x ⬝ᵥ hessianMatrix S s *ᵥ x =
      2 * s * (x ⬝ᵥ S *ᵥ x) -
        2 * ((S *ᵥ x) ⬝ᵥ (S *ᵥ x)) := by
  rw [hessianMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_sub,
    dotProduct_smul, dotProduct_smul, dotProduct_add,
    ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec,
    Matrix.dotProduct_transpose_mulVec]
  ring

omit [DecidableEq ι] in
/-- The row and column sum identities put the unit vector in the kernel of
Yamagami's Hessian representative. -/
theorem hessianMatrix_mulVec_one_eq_zero
    (S : Matrix ι ι ℝ) (s : ℝ)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ)) :
    hessianMatrix S s *ᵥ (1 : ι → ℝ) = 0 := by
  rw [hessianMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    hSone, hSTone, Matrix.mulVec_smul, hSTone]
  ext i
  simp [smul_smul]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem coordinateRpow_mem_laurentSubalgebra [Finite ι]
    (b : ι → ℝ) (t : ℝ) :
    coordinateRpow b t ∈ laurentSubalgebra b := by
  apply mem_laurentSubalgebra_of_eq_on_valueClass
  intro i j hij
  simp [coordinateRpow, hij]

omit [Fintype ι] [DecidableEq ι] in
theorem coordinateLog_mem_laurentSubalgebra [Finite ι] (b : ι → ℝ) :
    coordinateLog b ∈ laurentSubalgebra b := by
  apply mem_laurentSubalgebra_of_eq_on_valueClass
  intro i j hij
  simp [coordinateLog, hij]

omit [DecidableEq ι] in
/-- A nonnegative matrix whose row sum is the positive number `s` maps every
strictly positive coordinate vector to a strictly positive vector. -/
theorem mulVec_mem_positiveInvertibles_of_nonnegative
    (S : Matrix ι ι ℝ) (s : ℝ)
    (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    {x : ι → ℝ} (hx : x ∈ positiveInvertibles) :
    S *ᵥ x ∈ positiveInvertibles := by
  rw [mem_positiveInvertibles] at hx ⊢
  intro i
  have hrow : ∑ j, S i j = s := by
    have hi := congrFun hSone i
    simpa [Matrix.mulVec, dotProduct] using hi
  have hrow_pos : 0 < ∑ j, S i j := by simpa [hrow] using hs
  obtain ⟨j, _, hSij⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) ↦ hSnonneg i j)).mp hrow_pos
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (hSnonneg i k) (le_of_lt (hx k))
  · exact ⟨j, Finset.mem_univ j, mul_pos hSij (hx j)⟩

omit [DecidableEq ι] in
/-- Under the same hypotheses, the normalized vector `b = (S a)/s` is
strictly positive. -/
theorem transformedGenerator_mem_positiveInvertibles
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (ha : a ∈ positiveInvertibles) :
    transformedGenerator S s a ∈ positiveInvertibles := by
  have hSa_pos := mulVec_mem_positiveInvertibles_of_nonnegative
    S s hSnonneg hs hSone ha
  rw [mem_positiveInvertibles] at hSa_pos ⊢
  intro i
  rw [transformedGenerator_apply]
  exact div_pos (hSa_pos i) hs

omit [DecidableEq ι] in
theorem lambdaT_smul (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (c : ℝ) (hc : c ≠ 0) (x : ι → ℝ) :
    lambdaT T (c • x) = lambdaT T x := by
  unfold lambdaT coordinateSum
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.inv_apply, Pi.smul_apply, smul_eq_mul, map_smul, Pi.mul_apply]
  field_simp [hc]

omit [DecidableEq ι] in
/-- Homogeneity normalizes a local maximum at `c • x` to one at `x` when
`c > 0`. -/
theorem isLocalMaxOn_lambdaT_of_smul
    (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (c : ℝ) (hc : 0 < c)
    (x : ι → ℝ) (hx : x ∈ positiveInvertibles)
    (hmax : IsLocalMaxOn (lambdaT T) positiveInvertibles (c • x)) :
    IsLocalMaxOn (lambdaT T) positiveInvertibles x := by
  let g : (ι → ℝ) → (ι → ℝ) := fun y ↦ c • y
  have hmaps : positiveInvertibles ⊆ g ⁻¹' positiveInvertibles := by
    intro y hy
    rw [mem_positiveInvertibles] at hy
    change g y ∈ positiveInvertibles
    rw [mem_positiveInvertibles]
    exact fun i ↦ mul_pos hc (hy i)
  have hcont : ContinuousOn g positiveInvertibles := by
    fun_prop
  have hcomp := IsLocalMaxOn.comp_continuousOn
    (f := lambdaT T) (g := g) hmax hmaps hcont hx
  have hfun : lambdaT T ∘ g = lambdaT T := by
    funext y
    exact lambdaT_smul T c (ne_of_gt hc) y
  rw [hfun] at hcomp
  exact hcomp

/-- An invertible `S` transfers a local maximum of
`x ↦ L_{S⁻¹}(S x)` at `x` to a local maximum of `L_{S⁻¹}` at `S x`.
Only the local homeomorphism is used; no positivity-preservation property is
assumed for `S⁻¹`. -/
theorem isLocalMaxOn_inverseOperator_of_composed
    (S : Matrix ι ι ℝ) (hS : IsUnit S.det) (x : ι → ℝ)
    (hx : x ∈ positiveInvertibles)
    (hmax : IsLocalMaxOn
      (fun y ↦ lambdaT (inverseOperator S) (S *ᵥ y))
      positiveInvertibles x) :
    IsLocalMaxOn (lambdaT (inverseOperator S)) positiveInvertibles
      (S *ᵥ x) := by
  let f : (ι → ℝ) → ℝ :=
    fun y ↦ lambdaT (inverseOperator S) (S *ᵥ y)
  let g : (ι → ℝ) → (ι → ℝ) := fun y ↦ S⁻¹ *ᵥ y
  have hlocal : IsLocalMax f x := by
    exact hmax.isLocalMax
      (isOpen_positiveInvertibles.mem_nhds hx)
  have hgSx : g (S *ᵥ x) = x := by
    dsimp [g]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul S hS,
      Matrix.one_mulVec]
  have hlocal' : IsLocalMax f (g (S *ᵥ x)) := by
    rw [hgSx]
    exact hlocal
  have hgcont : ContinuousAt g (S *ᵥ x) := by
    exact (Matrix.mulVecLin S⁻¹).continuous_of_finiteDimensional.continuousAt
  have hcomp := hlocal'.comp_continuous hgcont
  have hfg : f ∘ g = lambdaT (inverseOperator S) := by
    funext y
    dsimp [f, g]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hS,
      Matrix.one_mulVec]
  rw [hfg] at hcomp
  exact hcomp.on positiveInvertibles

/-- A local maximum at `a` in the original coordinates becomes a local
maximum of `L_{S⁻¹}` at the normalized generator `b = (S a)/s`. -/
theorem normalized_localMaximum_at_transformedGenerator
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (ha : a ∈ positiveInvertibles)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a) :
    IsLocalMaxOn (lambdaT (inverseOperator S)) positiveInvertibles
      (transformedGenerator S s a) := by
  have hb_pos := transformedGenerator_mem_positiveInvertibles
    S s a hSnonneg hs hSone ha
  have hmaxSa := isLocalMaxOn_inverseOperator_of_composed
    S hS a ha hmaxA
  have hscale : s • transformedGenerator S s a = S *ᵥ a := by
    ext i
    simp [transformedGenerator, ne_of_gt hs]
  have hmaxScaledB : IsLocalMaxOn (lambdaT (inverseOperator S))
      positiveInvertibles (s • transformedGenerator S s a) := by
    rw [hscale]
    exact hmaxSa
  exact isLocalMaxOn_lambdaT_of_smul
    (inverseOperator S) s hs (transformedGenerator S s a) hb_pos hmaxScaledB

/-- The two maxima in Yamagami's original coordinates become maxima of
`L_{S⁻¹}` at `1` and at the normalized generator `b = (S a)/s`. -/
theorem normalized_localMaxima
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (ha : a ∈ positiveInvertibles)
    (hmaxOne : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles 1)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a) :
    IsLocalMaxOn (lambdaT (inverseOperator S)) positiveInvertibles 1 ∧
      IsLocalMaxOn (lambdaT (inverseOperator S)) positiveInvertibles
        (transformedGenerator S s a) := by
  have hmaxSOne := isLocalMaxOn_inverseOperator_of_composed
    S hS (1 : ι → ℝ) (by simp) hmaxOne
  have hmaxScaledOne : IsLocalMaxOn (lambdaT (inverseOperator S))
      positiveInvertibles (s • (1 : ι → ℝ)) := by
    rw [← hSone]
    exact hmaxSOne
  have hmaxOne' := isLocalMaxOn_lambdaT_of_smul
    (inverseOperator S) s hs (1 : ι → ℝ) (by simp) hmaxScaledOne
  exact ⟨hmaxOne', normalized_localMaximum_at_transformedGenerator
    S s a hS hSnonneg hs hSone ha hmaxA⟩

/-- The inverse operator sends the unit vector to `s⁻¹ 1` when
`S 1 = s 1`. -/
theorem inverseOperator_apply_one
    (S : Matrix ι ι ℝ) (s : ℝ) (hS : IsUnit S.det) (hs : s ≠ 0)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ)) :
    inverseOperator S 1 = s⁻¹ • (1 : ι → ℝ) := by
  rw [inverseOperator_apply]
  calc
    S⁻¹ *ᵥ (1 : ι → ℝ) =
        S⁻¹ *ᵥ (s⁻¹ • (S *ᵥ (1 : ι → ℝ))) := by
      rw [hSone]
      simp [hs]
    _ = s⁻¹ • (S⁻¹ *ᵥ (S *ᵥ (1 : ι → ℝ))) := by
      rw [Matrix.mulVec_smul]
    _ = s⁻¹ • (1 : ι → ℝ) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul S hS,
        Matrix.one_mulVec]

/-- In coordinates, the normalized negative inverse is
`-S⁻¹ + s⁻¹ I`. -/
theorem normalizedNegativeInverse_apply
    (S : Matrix ι ι ℝ) (s : ℝ) (hS : IsUnit S.det) (hs : s ≠ 0)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (x : ι → ℝ) :
    normalizedNegativeInverse S x =
      -(S⁻¹ *ᵥ x) + s⁻¹ • x := by
  ext i
  simp [normalizedNegativeInverse, normalizeAt,
    inverseOperator_apply_one S s hS hs hSone]

/-- The column-sum condition gives the coordinate-sum eigenfunctional for
`S⁻¹`. -/
theorem coordinateSum_inverseOperator
    (S : Matrix ι ι ℝ) (s : ℝ) (hS : IsUnit S.det) (hs : s ≠ 0)
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (x : ι → ℝ) :
    coordinateSum (inverseOperator S x) = s⁻¹ * coordinateSum x := by
  have hInvTranspose := inverseOperator_apply_one
    S.transpose s (S.isUnit_det_transpose hS) hs hSTone
  have hSinvTranspose :
      S⁻¹.transpose *ᵥ (1 : ι → ℝ) = s⁻¹ • (1 : ι → ℝ) := by
    rw [inverseOperator_apply] at hInvTranspose
    rw [Matrix.transpose_nonsing_inv]
    exact hInvTranspose
  rw [inverseOperator_apply]
  unfold coordinateSum
  calc
    (∑ i, (S⁻¹ *ᵥ x) i) =
        (1 : ι → ℝ) ⬝ᵥ (S⁻¹ *ᵥ x) := by
      simp [dotProduct]
    _ = x ⬝ᵥ (S⁻¹.transpose *ᵥ (1 : ι → ℝ)) := by
      exact (Matrix.dotProduct_transpose_mulVec
        (A := S⁻¹) (x := x) (y := (1 : ι → ℝ))).symm
    _ = x ⬝ᵥ (s⁻¹ • (1 : ι → ℝ)) := by rw [hSinvTranspose]
    _ = s⁻¹ * ∑ i, x i := by
      simp [dotProduct, Finset.sum_mul, mul_comm]

/-- Yamagami's Hessian quadratic form is exactly the second-variation form
of the normalized negative inverse operator. -/
theorem minimumQuadraticForm_normalizedNegativeInverse_eq
    (S : Matrix ι ι ℝ) (s : ℝ) (hS : IsUnit S.det) (hs : s ≠ 0)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (x : ι → ℝ) :
    minimumQuadraticForm (normalizedNegativeInverse S) x =
      (2 * s)⁻¹ *
        ((S⁻¹ *ᵥ x) ⬝ᵥ hessianMatrix S s *ᵥ (S⁻¹ *ᵥ x)) := by
  let y : ι → ℝ := S⁻¹ *ᵥ x
  have hSy : S *ᵥ y = x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hS,
      Matrix.one_mulVec]
  unfold minimumQuadraticForm
  rw [normalizedNegativeInverse_apply S s hS hs hSone]
  change -((-y + s⁻¹ • x) ⬝ᵥ x) =
    (2 * s)⁻¹ * (y ⬝ᵥ hessianMatrix S s *ᵥ y)
  rw [← hSy, dotProduct_hessianMatrix_mulVec]
  simp only [add_dotProduct, neg_dotProduct, smul_dotProduct,
    smul_eq_mul]
  field_simp [hs]
  ring

/-- The positive-semidefinite Hessian and the row/column sum identities give
Nowosad's first normalized variation package at the unit directly.  Thus the
exact Lemma 3 does not need to assume separately that the unit is already a
local maximum. -/
theorem minimumData_normalizedNegativeInverse
    (S : Matrix ι ι ℝ) (s : ℝ) (hS : IsUnit S.det) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hH : (hessianMatrix S s).PosSemidef) :
    MinimumData (normalizedNegativeInverse S) where
  map_one := by
    simp [normalizedNegativeInverse]
  critical := by
    intro x
    rw [normalizedNegativeInverse_apply S s hS (ne_of_gt hs) hSone]
    change coordinateSum (-(inverseOperator S x) + s⁻¹ • x) = 0
    have hsum := coordinateSum_inverseOperator
      S s hS (ne_of_gt hs) hSTone x
    unfold coordinateSum at hsum ⊢
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [hsum, ← Finset.mul_sum]
    ring
  quadratic_nonneg := by
    intro x
    rw [minimumQuadraticForm_normalizedNegativeInverse_eq
      S s hS (ne_of_gt hs) hSone]
    apply mul_nonneg
    · positivity
    · simpa using hH.dotProduct_mulVec_nonneg (S⁻¹ *ᵥ x)

/-- With the first variation package supplied by Yamagami's Hessian, one
actual second local maximum is enough for Nowosad's algebraic theorem.  The
normalized negative inverse vanishes on the full Laurent algebra generated
by `b = (S a)/s`. -/
theorem normalizedNegativeInverse_eq_zero_on_laurentSubalgebra
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hH : (hessianMatrix S s).PosSemidef)
    (ha : a ∈ positiveInvertibles)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a)
    (q : laurentSubalgebra (transformedGenerator S s a)) :
    normalizedNegativeInverse S (q : ι → ℝ) = 0 := by
  let b := transformedGenerator S s a
  change normalizedNegativeInverse S (q : ι → ℝ) = 0
  have hbpos : b ∈ positiveInvertibles :=
    transformedGenerator_mem_positiveInvertibles
      S s a hSnonneg hs hSone ha
  have hmaxB := normalized_localMaximum_at_transformedGenerator
    S s a hS hSnonneg hs hSone ha hmaxA
  have hminB : IsLocalMinOn (lambdaT (-(inverseOperator S)))
      positiveInvertibles b :=
    isLocalMinOn_lambdaT_neg_of_isLocalMaxOn (inverseOperator S) b hmaxB
  have hsecondNeg : MinimumData
      (normalizeAt (-(inverseOperator S)) b) :=
    minimumData_normalizeAt_of_localMinOn
      (-(inverseOperator S)) b hbpos hminB
  have hsecond : MinimumData
      (normalizeAt (normalizedNegativeInverse S) b) := by
    simpa [normalizedNegativeInverse] using hsecondNeg
  have hfirst : MinimumData (normalizedNegativeInverse S) :=
    minimumData_normalizedNegativeInverse
      S s hS hs hSone hSTone hH
  have hb : ∀ i, b i ≠ 0 := by
    rw [mem_positiveInvertibles] at hbpos
    exact fun i ↦ ne_of_gt (hbpos i)
  exact eq_zero_on_laurentSubalgebra_of_two_minimumData
    (normalizedNegativeInverse S) b hb hfirst hsecond q

/-- In particular, the normalized negative inverse vanishes on `log b`, the
tangent generator of Yamagami's power curve. -/
theorem normalizedNegativeInverse_coordinateLog_eq_zero
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hH : (hessianMatrix S s).PosSemidef)
    (ha : a ∈ positiveInvertibles)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a) :
    normalizedNegativeInverse S
        (coordinateLog (transformedGenerator S s a)) = 0 := by
  exact normalizedNegativeInverse_eq_zero_on_laurentSubalgebra
    S s a hS hSnonneg hs hSone hSTone hH ha hmaxA
    ⟨coordinateLog (transformedGenerator S s a),
      coordinateLog_mem_laurentSubalgebra (transformedGenerator S s a)⟩

/-- Consequently, `L_{S⁻¹}` is constant on the regular part of the Laurent
algebra generated by the correctly transformed vector `b = (S a)/s`. -/
theorem lambdaT_eq_one_on_laurentSubalgebra
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hH : (hessianMatrix S s).PosSemidef)
    (ha : a ∈ positiveInvertibles)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a)
    (q : laurentSubalgebra (transformedGenerator S s a))
    (hq : ∀ i, (q : ι → ℝ) i ≠ 0) :
    lambdaT (inverseOperator S) (q : ι → ℝ) =
      lambdaT (inverseOperator S) 1 := by
  have hzero := normalizedNegativeInverse_eq_zero_on_laurentSubalgebra
    S s a hS hSnonneg hs hSone hSTone hH ha hmaxA q
  rw [normalizedNegativeInverse_apply
    S s hS (ne_of_gt hs) hSone] at hzero
  have heigen : inverseOperator S (q : ι → ℝ) =
      s⁻¹ • (q : ι → ℝ) := by
    rw [inverseOperator_apply]
    ext i
    have hi := congrFun hzero i
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hi ⊢
    linarith
  unfold lambdaT
  rw [heigen, inverseOperator_apply_one S s hS (ne_of_gt hs) hSone]
  unfold coordinateSum
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.inv_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
    Pi.one_apply]
  field_simp [hq i]

/-- In particular, the Hessian-based application of Nowosad makes
`L_{S⁻¹}(b^t)` constant for every real `t`. -/
theorem lambdaT_coordinateRpow_eq_of_localMax
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hH : (hessianMatrix S s).PosSemidef)
    (ha : a ∈ positiveInvertibles)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a)
    (t : ℝ) :
    lambdaT (inverseOperator S)
        (coordinateRpow (transformedGenerator S s a) t) =
      lambdaT (inverseOperator S) 1 := by
  let b := transformedGenerator S s a
  have hbpos := transformedGenerator_mem_positiveInvertibles
    S s a hSnonneg hs hSone ha
  let q : laurentSubalgebra b :=
    ⟨coordinateRpow b t, coordinateRpow_mem_laurentSubalgebra b t⟩
  apply lambdaT_eq_one_on_laurentSubalgebra
    S s a hS hSnonneg hs hSone hSTone hH ha hmaxA q
  rw [mem_positiveInvertibles] at hbpos
  intro i
  exact (Real.rpow_pos_of_pos (hbpos i) t).ne'

/-- In the original coordinates the same constancy is realized by the
source-prescribed curve `x(t) = s S⁻¹(b^t)`. -/
theorem composed_lambdaT_pulledBackCurve_eq_of_localMax
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hH : (hessianMatrix S s).PosSemidef)
    (ha : a ∈ positiveInvertibles)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a)
    (t : ℝ) :
    lambdaT (inverseOperator S)
        (S *ᵥ pulledBackCurve S s (transformedGenerator S s a) t) =
      lambdaT (inverseOperator S) (S *ᵥ (1 : ι → ℝ)) := by
  have hconst := lambdaT_coordinateRpow_eq_of_localMax
    S s a hS hSnonneg hs hSone hSTone hH ha hmaxA t
  have hcurve :
      S *ᵥ pulledBackCurve S s (transformedGenerator S s a) t =
        s • coordinateRpow (transformedGenerator S s a) t := by
    unfold pulledBackCurve
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv S hS, Matrix.one_mulVec]
  rw [hcurve, lambdaT_smul _ s (ne_of_gt hs), hSone,
    lambdaT_smul _ s (ne_of_gt hs)]
  exact hconst

/-- Under Yamagami's Lemma 3 hypotheses, the pulled-back logarithmic tangent
`s S⁻¹(log b)` equals `log b`; no local-maximum hypothesis at the unit is
needed. -/
theorem pulledBackTangent_eq_coordinateLog
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hH : (hessianMatrix S s).PosSemidef)
    (ha : a ∈ positiveInvertibles)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a) :
    s • (S⁻¹ *ᵥ coordinateLog (transformedGenerator S s a)) =
      coordinateLog (transformedGenerator S s a) := by
  let b := transformedGenerator S s a
  change s • (S⁻¹ *ᵥ coordinateLog b) = coordinateLog b
  have hzero := normalizedNegativeInverse_coordinateLog_eq_zero
    S s a hS hSnonneg hs hSone hSTone hH ha hmaxA
  change normalizedNegativeInverse S (coordinateLog b) = 0 at hzero
  rw [normalizedNegativeInverse_apply
    S s hS (ne_of_gt hs) hSone] at hzero
  ext i
  have hi := congrFun hzero i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply] at hi ⊢
  field_simp [ne_of_gt hs] at hi
  linarith

/-- Equivalently, `log b` is an eigenvector of `S` with eigenvalue `s`. -/
theorem mulVec_coordinateLog_eq_smul
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hH : (hessianMatrix S s).PosSemidef)
    (ha : a ∈ positiveInvertibles)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a) :
    S *ᵥ coordinateLog (transformedGenerator S s a) =
      s • coordinateLog (transformedGenerator S s a) := by
  let z := coordinateLog (transformedGenerator S s a)
  have htangent := pulledBackTangent_eq_coordinateLog
    S s a hS hSnonneg hs hSone hSTone hH ha hmaxA
  change s • (S⁻¹ *ᵥ z) = z at htangent
  have h := congrArg (fun x ↦ S *ᵥ x) htangent
  change S *ᵥ z = s • z
  symm
  simpa [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv S hS] using h

/-- The logarithmic direction has zero Yamagami Hessian quadratic form and,
by positive semidefiniteness, lies in the Hessian kernel. -/
theorem hessianMatrix_mulVec_coordinateLog_eq_zero
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hH : (hessianMatrix S s).PosSemidef)
    (ha : a ∈ positiveInvertibles)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a) :
    hessianMatrix S s *ᵥ
      coordinateLog (transformedGenerator S s a) = 0 := by
  let z := coordinateLog (transformedGenerator S s a)
  have hSz : S *ᵥ z = s • z := by
    exact mulVec_coordinateLog_eq_smul
      S s a hS hSnonneg hs hSone hSTone hH ha hmaxA
  have hquad : z ⬝ᵥ hessianMatrix S s *ᵥ z = 0 := by
    rw [dotProduct_hessianMatrix_mulVec, hSz]
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  apply (hH.dotProduct_mulVec_zero_iff z).mp
  simpa using hquad

/-- The actual tangent `s S⁻¹(log b)` of the pulled-back curve is therefore a
Hessian-kernel direction. -/
theorem hessianMatrix_mulVec_pulledBackTangent_eq_zero
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hH : (hessianMatrix S s).PosSemidef)
    (ha : a ∈ positiveInvertibles)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a) :
    hessianMatrix S s *ᵥ
      (s • (S⁻¹ *ᵥ coordinateLog (transformedGenerator S s a))) = 0 := by
  rw [pulledBackTangent_eq_coordinateLog
    S s a hS hSnonneg hs hSone hSTone hH ha hmaxA]
  exact hessianMatrix_mulVec_coordinateLog_eq_zero
    S s a hS hSnonneg hs hSone hSTone hH ha hmaxA

/-- If the normalized image `b = (S a)/s` is scalar, then invertibility of
`S` and `S 1 = s 1` force `a` itself to be scalar. -/
theorem isScalarVector_of_transformedGenerator
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hb : IsScalarVector (transformedGenerator S s a)) :
    IsScalarVector a := by
  let b := transformedGenerator S s a
  change IsScalarVector b at hb
  obtain ⟨c, hc⟩ := hb
  refine ⟨c, ?_⟩
  have hscale : s • b = S *ᵥ a := by
    ext i
    simp [b, transformedGenerator, ne_of_gt hs]
  have heq : S *ᵥ a = S *ᵥ (c • (1 : ι → ℝ)) := by
    calc
      S *ᵥ a = s • b := hscale.symm
      _ = s • (c • (1 : ι → ℝ)) := by rw [hc]
      _ = c • (s • (1 : ι → ℝ)) := by
        simp [smul_smul, mul_comm]
      _ = c • (S *ᵥ (1 : ι → ℝ)) := by rw [hSone]
      _ = S *ᵥ (c • (1 : ι → ℝ)) := by rw [Matrix.mulVec_smul]
  have hinv := congrArg (fun x ↦ S⁻¹ *ᵥ x) heq
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul S hS] using hinv

omit [Fintype ι] [DecidableEq ι] in
/-- On the strictly positive cone, scalarity of `log b` is equivalent to
projective scalarity of `b`; only the forward implication is needed here. -/
theorem isScalarVector_of_coordinateLog
    (b : ι → ℝ) (hb : b ∈ positiveInvertibles)
    (hlog : IsScalarVector (coordinateLog b)) :
    IsScalarVector b := by
  rw [mem_positiveInvertibles] at hb
  obtain ⟨c, hc⟩ := hlog
  refine ⟨Real.exp c, ?_⟩
  funext i
  have hi := congrFun hc i
  have hi' : Real.log (b i) = c := by
    simpa [coordinateLog] using hi
  simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← hi', Real.exp_log (hb i)]

/-- A non-scalar second maximum produces the non-scalar tangent
`s S⁻¹(log b)` to Yamagami's pulled-back curve. -/
theorem pulledBackTangent_not_isScalarVector
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hH : (hessianMatrix S s).PosSemidef)
    (ha : a ∈ positiveInvertibles) (ha_nonscalar : ¬IsScalarVector a)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a) :
    ¬IsScalarVector
      (s • (S⁻¹ *ᵥ coordinateLog (transformedGenerator S s a))) := by
  intro htangent
  have htangent_eq := pulledBackTangent_eq_coordinateLog
    S s a hS hSnonneg hs hSone hSTone hH ha hmaxA
  have hlog : IsScalarVector
      (coordinateLog (transformedGenerator S s a)) := by
    rw [← htangent_eq]
    exact htangent
  have hbpos := transformedGenerator_mem_positiveInvertibles
    S s a hSnonneg hs hSone ha
  have hbscalar := isScalarVector_of_coordinateLog
    (transformedGenerator S s a) hbpos hlog
  exact ha_nonscalar
    (isScalarVector_of_transformedGenerator S s a hS hs hSone hbscalar)

/-- A non-scalar local maximum produces the explicitly named non-scalar
Hessian-kernel direction `s S⁻¹ log((S a)/s)`. -/
theorem pulledBackTangent_mem_hessianKernel_and_not_isScalarVector
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hH : (hessianMatrix S s).PosSemidef)
    (ha : a ∈ positiveInvertibles) (ha_nonscalar : ¬IsScalarVector a)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a) :
    hessianMatrix S s *ᵥ
        (s • (S⁻¹ *ᵥ coordinateLog (transformedGenerator S s a))) = 0 ∧
      ¬IsScalarVector
        (s • (S⁻¹ *ᵥ coordinateLog (transformedGenerator S s a))) := by
  exact ⟨hessianMatrix_mulVec_pulledBackTangent_eq_zero
      S s a hS hSnonneg hs hSone hSTone hH ha hmaxA,
    pulledBackTangent_not_isScalarVector
      S s a hS hSnonneg hs hSone hSTone hH ha ha_nonscalar hmaxA⟩

/-- The uniqueness assertion of Yamagami's Lemma 3 in finite coordinates.  If
`s(S+Sᵀ)-2SᵀS` is positive semidefinite and its kernel is contained in the
scalar line, then every strictly positive local maximum of
`x ↦ L_{S⁻¹}(Sx)` is projectively scalar.

The unit maximum is not assumed.  Instead, the Hessian and row/column sum
identities supply Nowosad's first variation package directly; this makes
explicit the variational content behind Yamagami's terse reference to his
Lemma 2.  The row/column identities also put `1` in the kernel by
`hessianMatrix_mulVec_one_eq_zero`, so the kernel-containment premise is
exactly the source's statement that the kernel is spanned by `1`.  This
theorem proves the uniqueness assertion; it does not separately formalize the
transverse second-derivative argument that establishes the unit as a local
maximum. -/
theorem lemma_three_localMax_isScalar
    (S : Matrix ι ι ℝ) (s : ℝ) (a : ι → ℝ)
    (hS : IsUnit S.det) (hSnonneg : ∀ i j, 0 ≤ S i j) (hs : 0 < s)
    (hSone : S *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hSTone : S.transpose *ᵥ (1 : ι → ℝ) = s • (1 : ι → ℝ))
    (hH : (hessianMatrix S s).PosSemidef)
    (hker : ∀ z : ι → ℝ,
      hessianMatrix S s *ᵥ z = 0 → IsScalarVector z)
    (ha : a ∈ positiveInvertibles)
    (hmaxA : IsLocalMaxOn
      (fun x ↦ lambdaT (inverseOperator S) (S *ᵥ x))
      positiveInvertibles a) :
    IsScalarVector a := by
  by_contra ha_nonscalar
  have hnull := hessianMatrix_mulVec_pulledBackTangent_eq_zero
    S s a hS hSnonneg hs hSone hSTone hH ha hmaxA
  have hscalar := hker _ hnull
  exact (pulledBackTangent_not_isScalarVector
    S s a hS hSnonneg hs hSone hSTone hH ha ha_nonscalar hmaxA) hscalar

end Yamagami
