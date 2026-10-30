/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.HermitianHelpers
import QICLean.Analysis.RectangularTraceNormAlgebra
import QICLean.Analysis.TraceDistance
import QICLean.Channel.MaximalOverlap

/-!
# A nearly pure marginal gives an approximate product vector

A unit bipartite vector whose first marginal is within full trace-norm error
`ε` of a prescribed unit pure state is within Euclidean distance `√(2 * ε)`
of that prescribed vector tensored with a derived unit environment vector.
The environment dimension is unchanged, and no lower bound on its size or
strict upper bound on the error is required.

The proof projects the coefficient matrix onto the prescribed system vector.
The actual environment row has squared norm at least `1 - ε`; normalizing it
provides the product vector. The zero row is handled separately.

This is an elementary consequence of the positive-part trace estimate behind
Wolf, *Quantum Channels & Operations*, Section 8.1 and Theorem 8.16. It supports
trace-norm pure-state conversions such as the criterion in Piroli, Styliaris
and Cirac, arXiv:2103.13367v3, main-text paragraph "Phases of matter"; it does
not assert an additional protocol or an environment reset.
-/

noncomputable section

open scoped Matrix MatrixOrder ComplexOrder

namespace Matrix

variable {S E : Type*} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]

private theorem norm_sq_product_vector (φ : EuclideanSpace ℂ S)
    (η : EuclideanSpace ℂ E) :
    ‖(WithLp.toLp 2 (fun p : S × E ↦ φ p.1 * η p.2) :
      EuclideanSpace ℂ (S × E))‖ ^ 2 = ‖φ‖ ^ 2 * ‖η‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, norm_mul, mul_pow]
  exact (Finset.sum_mul_sum _ _ _ _).symm

private theorem inner_product_vector_eq
    (Ω : EuclideanSpace ℂ (S × E)) (φ : EuclideanSpace ℂ S)
    (η : EuclideanSpace ℂ E) :
    inner ℂ Ω (WithLp.toLp 2 (fun p : S × E ↦ φ p.1 * η p.2)) =
      inner ℂ (WithLp.toLp 2 (star (WithLp.ofLp φ) ᵥ*
        schmidtCoeffMatrix (WithLp.ofLp Ω)) : EuclideanSpace ℂ E) η := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_toLp_toLp]
  rw [dotProduct_comm, star_dotProduct_eq_trace_conjTranspose_mul]
  change ((schmidtCoeffMatrix (WithLp.ofLp Ω))ᴴ *
    vecMulVec (WithLp.ofLp φ) (WithLp.ofLp η)).trace = _
  rw [mul_vecMulVec, trace_vecMulVec, star_vecMul, star_star]
  exact dotProduct_comm _ _

private theorem norm_sq_environment_row_eq
    (Ω : EuclideanSpace ℂ (S × E)) (φ : EuclideanSpace ℂ S) :
    ‖(WithLp.toLp 2 (star (WithLp.ofLp φ) ᵥ*
      schmidtCoeffMatrix (WithLp.ofLp Ω)) : EuclideanSpace ℂ E)‖ ^ 2 =
      ((vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)) *
        partialTraceRight (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).trace).re := by
  let C := schmidtCoeffMatrix (WithLp.ofLp Ω)
  let a := star (WithLp.ofLp φ) ᵥ* C
  have h : star a ⬝ᵥ a =
      (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)) * (C * Cᴴ)).trace := by
    calc
      star a ⬝ᵥ a = a ⬝ᵥ (Cᴴ *ᵥ WithLp.ofLp φ) := by
        rw [dotProduct_comm, star_vecMul, star_star]
      _ = star (WithLp.ofLp φ) ⬝ᵥ ((C * Cᴴ) *ᵥ WithLp.ofLp φ) := by
        rw [dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec]
      _ = _ := by
        rw [trace_mul_comm, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
  rw [@norm_sq_eq_re_inner ℂ, EuclideanSpace.inner_toLp_toLp,
    dotProduct_comm, h, partialTraceRight_vecMulVec_eq]

private theorem one_sub_environment_mass_le
    (Ω : EuclideanSpace ℂ (S × E)) (φ : EuclideanSpace ℂ S)
    (hΩ : ‖Ω‖ = 1) (hφ : ‖φ‖ = 1) {ε : ℝ}
    (herror : rectangularTraceNorm
      (partialTraceRight (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) -
        vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) ≤ ε) :
    1 - ‖(WithLp.toLp 2 (star (WithLp.ofLp φ) ᵥ*
      schmidtCoeffMatrix (WithLp.ofLp Ω)) : EuclideanSpace ℂ E)‖ ^ 2 ≤ ε := by
  let ρ := partialTraceRight (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))
  let P := vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))
  have hρ : ρ.PosSemidef := (posSemidef_vecMulVec_self_star _).partialTraceRight
  have hP : P.PosSemidef := posSemidef_vecMulVec_self_star _
  have hρtr : ρ.trace = 1 := by
    rw [partialTraceRight_vecMulVec_eq]
    exact trace_schmidtCoeffMatrix_mul_conjTranspose_of_norm_one Ω hΩ
  have hPtr : P.trace = 1 := by
    rw [trace_vecMulVec]
    change inner ℂ φ φ = 1
    simp [inner_self_eq_norm_sq_to_K, hφ]
  have hφdot : star (WithLp.ofLp φ) ⬝ᵥ WithLp.ofLp φ = 1 := by
    rw [dotProduct_comm]
    exact hPtr
  have hPP : P * P = P := by
    change vecMulVec _ _ * vecMulVec _ _ = _
    rw [vecMulVec_mul_vecMulVec, hφdot, one_smul]
  have hPle : P ≤ 1 := le_iff.mpr
    (one_sub_vecMulVec_posSemidef_of_sum_normSq_le_one _ (by
      rw [← EuclideanSpace.norm_sq_eq φ, hφ]
      norm_num))
  have hpair := re_trace_mul_sub_le_traceDistance hP.isHermitian hρ.isHermitian
    (hPtr.trans hρtr.symm) hP.nonneg hPle
  have hδ : traceDistance P ρ = rectangularTraceNorm (ρ - P) / 2 := by
    rw [traceDistance_comm, traceDistance, rectangularTraceNorm_eq_re_trace_abs]
  have hmass := norm_sq_environment_row_eq Ω φ
  change _ = ((P * ρ).trace).re at hmass
  change rectangularTraceNorm (ρ - P) ≤ ε at herror
  rw [hPP, hPtr, Complex.one_re, hδ] at hpair
  have hnn := rectangularTraceNorm_nonneg (ρ - P)
  linarith

/-- If the actual first marginal of a unit vector is within full trace-norm
error `ε` of a prescribed normalized pure state, then the actual vector is
within Euclidean distance `√(2 * ε)` of that prescribed vector tensored with
a derived unit environment vector. The environment is not enlarged, and the
error need not be strictly smaller than one. This is the elementary projection
estimate associated with Wolf, Section 8.1, and trace-norm pure-state criteria
such as arXiv:2103.13367v3, paragraph "Phases of matter". -/
theorem exists_unit_product_approx_of_pure_marginal
    (Ω : EuclideanSpace ℂ (S × E)) (φ : EuclideanSpace ℂ S)
    (hΩ : ‖Ω‖ = 1) (hφ : ‖φ‖ = 1) {ε : ℝ}
    (herror : rectangularTraceNorm
      (partialTraceRight (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) -
        vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) ≤ ε) :
    ∃ η : EuclideanSpace ℂ E, ‖η‖ = 1 ∧
      ‖Ω - WithLp.toLp 2 (fun p : S × E ↦ φ p.1 * η p.2)‖ ≤ Real.sqrt (2 * ε) := by
  classical
  let a : EuclideanSpace ℂ E := WithLp.toLp 2
    (star (WithLp.ofLp φ) ᵥ* schmidtCoeffMatrix (WithLp.ofLp Ω))
  have hmass : 1 - ‖a‖ ^ 2 ≤ ε := one_sub_environment_mass_le Ω φ hΩ hφ herror
  have hprod (η : EuclideanSpace ℂ E) (hη : ‖η‖ = 1) :
      ‖(WithLp.toLp 2 (fun p : S × E ↦ φ p.1 * η p.2) :
        EuclideanSpace ℂ (S × E))‖ = 1 := by
    have h := norm_sq_product_vector φ η
    rw [hφ, hη] at h
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun p : S × E ↦ φ p.1 * η p.2) :
      EuclideanSpace ℂ (S × E))]
  have hoverlap (η : EuclideanSpace ℂ E) :
      inner ℂ Ω (WithLp.toLp 2 (fun p : S × E ↦ φ p.1 * η p.2)) = inner ℂ a η :=
    inner_product_vector_eq Ω φ η
  by_cases ha : a = 0
  · have hE : Nonempty E := by
      by_contra hE
      let : IsEmpty E := not_nonempty_iff.mp hE
      have hzero : Ω = 0 := by ext ⟨s, e⟩; exact isEmptyElim e
      simpa [hzero] using hΩ
    let η : EuclideanSpace ℂ E := EuclideanSpace.single (Classical.choice hE) 1
    have hη : ‖η‖ = 1 := by simp [η]
    refine ⟨η, hη, Real.le_sqrt_of_sq_le ?_⟩
    rw [@norm_sub_sq ℂ, hΩ, hprod η hη, hoverlap, ha, inner_zero_left]
    simp only [map_zero]
    simp only [ha, norm_zero, zero_pow two_ne_zero, sub_zero] at hmass
    linarith
  · let η : EuclideanSpace ℂ E := (‖a‖⁻¹ : ℂ) • a
    have hη : ‖η‖ = 1 := norm_smul_inv_norm (𝕜 := ℂ) ha
    have hinner : inner ℂ a η = (‖a‖ : ℂ) := by
      rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
      change ((‖a‖⁻¹ : ℝ) : ℂ) * (‖a‖ : ℂ) ^ 2 = (‖a‖ : ℂ)
      rw [Complex.ofReal_inv]
      field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)] <;> ring
    have hle : ‖a‖ ≤ 1 := by
      have h := norm_inner_le_norm (𝕜 := ℂ) Ω
        (WithLp.toLp 2 (fun p : S × E ↦ φ p.1 * η p.2))
      rw [hoverlap, hinner, hΩ, hprod η hη] at h
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a),
        one_mul] using h
    refine ⟨η, hη, Real.le_sqrt_of_sq_le ?_⟩
    rw [@norm_sub_sq ℂ, hΩ, hprod η hη, hoverlap, hinner, Complex.ofReal_re]
    nlinarith [mul_nonneg (norm_nonneg a) (sub_nonneg.mpr hle)]

end Matrix
