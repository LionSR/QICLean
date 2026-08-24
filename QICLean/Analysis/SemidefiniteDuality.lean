/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.HermitianMatrixCone
import QICLean.Analysis.ConicProgram
import QICLean.Analysis.SemidefiniteProgram

/-!
# Semidefinite duality in Wolf's trace formulation

This file specializes the corrected conic-duality development to Wolf, *Quantum Channels &
Operations*, Chapter 4, lines 85--116.  The analysis map is
`T(X)ᵢ = tr(Fᵢ X)`, its adjoint is `T†(y) = ∑ᵢ yᵢ Fᵢ`, and self-duality of the
positive-semidefinite cone gives the exact Loewner signs in equation (4.3).

The value and optimizer notions remain those of `ConicProgram`; no competing SDP model is
introduced. The Slater statements retain the finite-value hypothesis required by the corrected
conic theorem and absent from the printed paragraph at lines 100--105.
-/

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace RealInnerProductSpace

namespace SemidefiniteProgram

variable {ι n : Type*} [Fintype ι] [Fintype n]

open HermitianMatrix

noncomputable def traceAnalysisMap (F : ι → HermitianMatrix n) :
    HermitianMatrix n →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun X := WithLp.toLp 2 fun i ↦ inner ℝ (F i) X
  map_add' X Y := by
    ext i
    simp [inner_add_right]
  map_smul' r X := by
    ext i
    simp [real_inner_smul_right]

omit [Fintype ι] in
@[simp] theorem traceAnalysisMap_apply (F : ι → HermitianMatrix n) (X : HermitianMatrix n)
    (i : ι) :
    (traceAnalysisMap F X).ofLp i = inner ℝ (F i) X :=
  rfl

omit [Fintype ι] in
theorem traceAnalysisMap_apply_eq_re_trace (F : ι → HermitianMatrix n)
    (X : HermitianMatrix n) (i : ι) :
    (traceAnalysisMap F X).ofLp i =
      (Matrix.trace (toMatrix n (F i) * toMatrix n X)).re := by
  rw [traceAnalysisMap_apply, inner_eq_re_trace_mul]

omit [Fintype ι] in
/-- Wolf's coordinate identity, with the real coordinate coerced to the complex trace scalar. -/
theorem traceAnalysisMap_apply_eq_trace (F : ι → HermitianMatrix n)
    (X : HermitianMatrix n) (i : ι) :
    Matrix.trace (toMatrix n (F i) * toMatrix n X) =
      ((traceAnalysisMap F X).ofLp i : ℂ) := by
  rw [trace_mul_eq_ofReal_inner, traceAnalysisMap_apply]

noncomputable def hermitianSum (F : ι → HermitianMatrix n) (y : EuclideanSpace ℝ ι) :
    HermitianMatrix n :=
  ∑ i, y.ofLp i • F i

@[simp] theorem toMatrix_hermitianSum (F : ι → HermitianMatrix n)
    (y : EuclideanSpace ℝ ι) :
    toMatrix n (hermitianSum F y) = ∑ i, (y.ofLp i : ℂ) • toMatrix n (F i) := by
  classical
  simp [hermitianSum, toMatrix, matrixRealLinearEquiv]

theorem traceAnalysisMap_adjoint (F : ι → HermitianMatrix n) (y : EuclideanSpace ℝ ι) :
    (traceAnalysisMap F).toContinuousLinearMap.adjoint y = hermitianSum F y := by
  apply ext_inner_right ℝ
  intro X
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [PiLp.inner_apply, hermitianSum, sum_inner]
  simp only [RCLike.inner_apply, conj_trivial, real_inner_smul_left]
  change (∑ i, inner ℝ (F i) X * y.ofLp i) =
    ∑ i, y.ofLp i * inner ℝ (F i) X
  simp only [mul_comm]

private theorem euclidean_inner_eq_sum_mul (b y : EuclideanSpace ℝ ι) :
    inner ℝ b y = ∑ i, b.ofLp i * y.ofLp i := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

/-- Wolf's primal constraints are exactly conic feasibility for the trace-analysis map. -/
theorem mem_primalFeasible_iff (F : ι → HermitianMatrix n) (b : EuclideanSpace ℝ ι)
    (X : HermitianMatrix n) :
    X ∈ ConicProgram.primalFeasible (psdCone n) (traceAnalysisMap F) b ↔
      (toMatrix n X).PosSemidef ∧
        ∀ i, (Matrix.trace (toMatrix n (F i) * toMatrix n X)).re = b.ofLp i := by
  change (X ∈ psdCone n ∧ traceAnalysisMap F X = b) ↔ _
  rw [mem_psdCone_iff]
  constructor
  · rintro ⟨hX, hTX⟩
    refine ⟨hX, fun i ↦ ?_⟩
    have hi := congrArg (fun z : EuclideanSpace ℝ ι ↦ z.ofLp i) hTX
    simpa only [traceAnalysisMap_apply_eq_re_trace] using hi
  · rintro ⟨hX, hconstraints⟩
    refine ⟨hX, ?_⟩
    ext i
    rw [traceAnalysisMap_apply_eq_re_trace, hconstraints i]

/-- Wolf's Loewner constraint `F₀ ≥ ∑ᵢ yᵢFᵢ` is exactly conic dual feasibility. -/
theorem mem_dualFeasible_iff (F₀ : HermitianMatrix n) (F : ι → HermitianMatrix n)
    (y : EuclideanSpace ℝ ι) :
    y ∈ ConicProgram.dualFeasible (psdCone n) (traceAnalysisMap F) F₀ ↔
      (toMatrix n F₀ - ∑ i, (y.ofLp i : ℂ) • toMatrix n (F i)).PosSemidef := by
  change F₀ - (traceAnalysisMap F).toContinuousLinearMap.adjoint y ∈
      ProperCone.innerDual (psdCone n : Set (HermitianMatrix n)) ↔ _
  rw [traceAnalysisMap_adjoint, innerDual_psdCone]
  change (toMatrix n (F₀ - hermitianSum F y)).PosSemidef ↔ _
  rw [toMatrix_sub, toMatrix_hermitianSum]

/-- Wolf's strict primal feasibility condition `X > 0` is conic strict feasibility. -/
theorem isPrimalStrictlyFeasible_iff (F : ι → HermitianMatrix n)
    (b : EuclideanSpace ℝ ι) :
    ConicProgram.IsPrimalStrictlyFeasible (psdCone n) (traceAnalysisMap F) b ↔
      ∃ X : HermitianMatrix n, (toMatrix n X).PosDef ∧
        ∀ i, (Matrix.trace (toMatrix n (F i) * toMatrix n X)).re = b.ofLp i := by
  constructor
  · rintro ⟨X, hX, hTX⟩
    refine ⟨X, (mem_interior_psdCone_iff_posDef n X).mp hX, fun i ↦ ?_⟩
    have hi := congrArg (fun z : EuclideanSpace ℝ ι ↦ z.ofLp i) hTX
    simpa only [traceAnalysisMap_apply_eq_re_trace] using hi
  · rintro ⟨X, hX, hconstraints⟩
    refine ⟨X, (mem_interior_psdCone_iff_posDef n X).mpr hX, ?_⟩
    ext i
    rw [traceAnalysisMap_apply_eq_re_trace, hconstraints i]

/-- Wolf's strict dual condition `F₀ > ∑ᵢ yᵢFᵢ` is conic dual strict feasibility. -/
theorem isDualStrictlyFeasible_iff (F₀ : HermitianMatrix n) (F : ι → HermitianMatrix n) :
    ConicProgram.IsDualStrictlyFeasible (psdCone n) (traceAnalysisMap F) F₀ ↔
      ∃ y : EuclideanSpace ℝ ι,
        (toMatrix n F₀ - ∑ i, (y.ofLp i : ℂ) • toMatrix n (F i)).PosDef := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [innerDual_psdCone, traceAnalysisMap_adjoint,
      mem_interior_psdCone_iff_posDef] at hy
    rwa [toMatrix_sub, toMatrix_hermitianSum] at hy
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [innerDual_psdCone, traceAnalysisMap_adjoint,
      mem_interior_psdCone_iff_posDef]
    rwa [toMatrix_sub, toMatrix_hermitianSum]

/-- **Semidefinite pointwise weak duality** in exactly Wolf's trace and Loewner notation. -/
theorem weak_duality_pointwise
    (F₀ : HermitianMatrix n) (F : ι → HermitianMatrix n) (b y : EuclideanSpace ℝ ι)
    (X : HermitianMatrix n) (hX : (toMatrix n X).PosSemidef)
    (hconstraints : ∀ i,
      (Matrix.trace (toMatrix n (F i) * toMatrix n X)).re = b.ofLp i)
    (hslack :
      (toMatrix n F₀ - ∑ i, (y.ofLp i : ℂ) • toMatrix n (F i)).PosSemidef) :
    ∑ i, b.ofLp i * y.ofLp i ≤ (Matrix.trace (toMatrix n F₀ * toMatrix n X)).re := by
  have hconic := ConicProgram.weak_duality_pointwise
    ((mem_primalFeasible_iff F b X).mpr ⟨hX, hconstraints⟩)
    ((mem_dualFeasible_iff F₀ F y).mpr hslack)
  rwa [euclidean_inner_eq_sum_mul, inner_eq_re_trace_mul] at hconic

/-- **Semidefinite weak duality for optimal values**, Wolf's equation (4.3). The values and their
empty/unbounded semantics are the existing conic values, not a parallel SDP model. -/
theorem weak_duality (F₀ : HermitianMatrix n) (F : ι → HermitianMatrix n)
    (b : EuclideanSpace ℝ ι) :
    ConicProgram.dualValue (psdCone n) (traceAnalysisMap F) F₀ b ≤
      ConicProgram.primalValue (psdCone n) (traceAnalysisMap F) F₀ b :=
  ConicProgram.weak_duality

/-- **Primal-strict semidefinite Slater attainment, corrected.** Wolf's `X > 0` condition and a
finite primal value give a dual optimizer. The finite-value hypothesis is the necessary correction
to the original statement at lines 100--105. -/
theorem exists_dualOptimizer_of_primalStrict_of_primalValue_eq_coe
    (F₀ : HermitianMatrix n) (F : ι → HermitianMatrix n) (b : EuclideanSpace ℝ ι) (p : ℝ)
    (hstrict : ∃ X : HermitianMatrix n, (toMatrix n X).PosDef ∧
      ∀ i, (Matrix.trace (toMatrix n (F i) * toMatrix n X)).re = b.ofLp i)
    (hvalue : ConicProgram.primalValue (psdCone n) (traceAnalysisMap F) F₀ b = (p : EReal)) :
    ∃ y : EuclideanSpace ℝ ι,
      ConicProgram.IsDualOptimizer (psdCone n) (traceAnalysisMap F) F₀ b y ∧
        ∑ i, b.ofLp i * y.ofLp i = p := by
  have hstrict' := (isPrimalStrictlyFeasible_iff F b).mpr hstrict
  obtain ⟨y, hy, hyobj⟩ :=
    ConicProgram.exists_isDualOptimizer_of_isPrimalStrictlyFeasible_of_primalValue_eq_coe
      hstrict' hvalue
  refine ⟨y, hy, ?_⟩
  rwa [euclidean_inner_eq_sum_mul] at hyobj

/-- **Primal-strict semidefinite strong duality, corrected.** This is a direct specialization of
the conic theorem and retains its finite-primal-value boundary. -/
theorem values_eq_of_primalStrict_of_primalValue_eq_coe
    (F₀ : HermitianMatrix n) (F : ι → HermitianMatrix n) (b : EuclideanSpace ℝ ι) (p : ℝ)
    (hstrict : ∃ X : HermitianMatrix n, (toMatrix n X).PosDef ∧
      ∀ i, (Matrix.trace (toMatrix n (F i) * toMatrix n X)).re = b.ofLp i)
    (hvalue : ConicProgram.primalValue (psdCone n) (traceAnalysisMap F) F₀ b = (p : EReal)) :
    ConicProgram.primalValue (psdCone n) (traceAnalysisMap F) F₀ b =
      ConicProgram.dualValue (psdCone n) (traceAnalysisMap F) F₀ b := by
  exact ConicProgram.values_eq_of_isPrimalStrictlyFeasible_of_primalValue_eq_coe
    ((isPrimalStrictlyFeasible_iff F b).mpr hstrict) hvalue

/-- **Dual-strict semidefinite Slater attainment, corrected.** Wolf's
`F₀ > ∑ᵢ yᵢFᵢ` condition and a finite dual value give a primal optimizer. -/
theorem exists_primalOptimizer_of_dualStrict_of_dualValue_eq_coe
    (F₀ : HermitianMatrix n) (F : ι → HermitianMatrix n) (b : EuclideanSpace ℝ ι) (p : ℝ)
    (hstrict : ∃ y : EuclideanSpace ℝ ι,
      (toMatrix n F₀ - ∑ i, (y.ofLp i : ℂ) • toMatrix n (F i)).PosDef)
    (hvalue : ConicProgram.dualValue (psdCone n) (traceAnalysisMap F) F₀ b = (p : EReal)) :
    ∃ X : HermitianMatrix n,
      ConicProgram.IsPrimalOptimizer (psdCone n) (traceAnalysisMap F) F₀ b X ∧
        (Matrix.trace (toMatrix n F₀ * toMatrix n X)).re = p := by
  have hstrict' := (isDualStrictlyFeasible_iff F₀ F).mpr hstrict
  obtain ⟨X, hX, hXobj⟩ :=
    ConicProgram.exists_isPrimalOptimizer_of_isDualStrictlyFeasible_of_dualValue_eq_coe
      hstrict' hvalue
  refine ⟨X, hX, ?_⟩
  rwa [inner_eq_re_trace_mul] at hXobj

/-- **Dual-strict semidefinite strong duality, corrected.** This direct conic specialization
retains the finite-dual-value boundary missing from the printed paragraph. -/
theorem values_eq_of_dualStrict_of_dualValue_eq_coe
    (F₀ : HermitianMatrix n) (F : ι → HermitianMatrix n) (b : EuclideanSpace ℝ ι) (p : ℝ)
    (hstrict : ∃ y : EuclideanSpace ℝ ι,
      (toMatrix n F₀ - ∑ i, (y.ofLp i : ℂ) • toMatrix n (F i)).PosDef)
    (hvalue : ConicProgram.dualValue (psdCone n) (traceAnalysisMap F) F₀ b = (p : EReal)) :
    ConicProgram.primalValue (psdCone n) (traceAnalysisMap F) F₀ b =
      ConicProgram.dualValue (psdCone n) (traceAnalysisMap F) F₀ b := by
  exact ConicProgram.values_eq_of_isDualStrictlyFeasible_of_dualValue_eq_coe
    ((isDualStrictlyFeasible_iff F₀ F).mpr hstrict) hvalue

/-- Wolf's optimizer characterization following complementary slackness. Assuming equality of
the conic values and primal attainment, a dual vector is optimal exactly when it participates in
a feasible primal--dual pair satisfying `(F₀ - ∑ᵢ yᵢFᵢ) X = 0`.

Source: Wolf, Chapter 4, lines 107--116. -/
theorem isDualOptimizer_iff_exists_complementary
    (F₀ : HermitianMatrix n) (F : ι → HermitianMatrix n)
    (b y : EuclideanSpace ℝ ι)
    (hvalues : ConicProgram.primalValue (psdCone n) (traceAnalysisMap F) F₀ b =
      ConicProgram.dualValue (psdCone n) (traceAnalysisMap F) F₀ b)
    (hprimalAttained : ∃ X : HermitianMatrix n,
      ConicProgram.IsPrimalOptimizer (psdCone n) (traceAnalysisMap F) F₀ b X) :
    ConicProgram.IsDualOptimizer (psdCone n) (traceAnalysisMap F) F₀ b y ↔
      ∃ X : HermitianMatrix n,
        (toMatrix n X).PosSemidef ∧
        (∀ i, (Matrix.trace (toMatrix n (F i) * toMatrix n X)).re = b.ofLp i) ∧
        (toMatrix n F₀ - ∑ i, (y.ofLp i : ℂ) • toMatrix n (F i)).PosSemidef ∧
        (toMatrix n F₀ - ∑ i, (y.ofLp i : ℂ) • toMatrix n (F i)) * toMatrix n X = 0 := by
  constructor
  · intro hy
    obtain ⟨X, hX⟩ := hprimalAttained
    have hXfeasible := (mem_primalFeasible_iff F b X).mp hX.1
    have hyfeasible := (mem_dualFeasible_iff F₀ F y).mp hy.1
    refine ⟨X, hXfeasible.1, hXfeasible.2, hyfeasible, ?_⟩
    have hp := ConicProgram.primalValue_eq_of_isPrimalOptimizer hX
    have hd := ConicProgram.dualValue_eq_of_isDualOptimizer hy
    have hobjectives : inner ℝ F₀ X = inner ℝ b y := by
      apply EReal.coe_eq_coe_iff.mp
      rw [← hp, hvalues, hd]
    rw [inner_eq_re_trace_mul, euclidean_inner_eq_sum_mul] at hobjectives
    exact complementary_slackness
      (toMatrix n F₀) (fun i ↦ toMatrix n (F i))
      (fun i ↦ b.ofLp i) (fun i ↦ y.ofLp i) (toMatrix n X)
      (toMatrix_isHermitian n F₀) (fun i ↦ toMatrix_isHermitian n (F i))
      hXfeasible.1 hXfeasible.2 hyfeasible hobjectives
  · rintro ⟨X, hX, hconstraints, hslack, hcomplementary⟩
    have hXfeasible := (mem_primalFeasible_iff F b X).mpr ⟨hX, hconstraints⟩
    have hyfeasible := (mem_dualFeasible_iff F₀ F y).mpr hslack
    have hobjectives :
        (Matrix.trace (toMatrix n F₀ * toMatrix n X)).re =
          ∑ i, b.ofLp i * y.ofLp i := by
      have hgap := re_trace_slack_mul_eq_objective_sub
        (toMatrix n F₀) (fun i ↦ toMatrix n (F i))
        (fun i ↦ b.ofLp i) (fun i ↦ y.ofLp i) (toMatrix n X) hconstraints
      rw [hcomplementary, Matrix.trace_zero, Complex.zero_re] at hgap
      linarith
    have hobjectives' : inner ℝ F₀ X = inner ℝ b y := by
      rw [inner_eq_re_trace_mul, euclidean_inner_eq_sum_mul]
      exact hobjectives
    exact (ConicProgram.optimizers_of_feasible_of_objectives_eq
      hXfeasible hyfeasible hobjectives').2

end SemidefiniteProgram
