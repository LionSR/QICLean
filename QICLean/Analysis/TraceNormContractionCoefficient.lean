/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import QICLean.Algebra.MatrixSpectralDecomp
import QICLean.Analysis.TraceNormContractivity
import QICLean.Analysis.TraceNormVariational
import QICLean.Channel.Basic

/-!
# Trace-norm contraction coefficient

This file proves Wolf's reduction of the trace-norm contraction coefficient of
an arbitrary complex-linear map to orthogonal pure-state inputs.

## References

Michael M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8,
Lemma 8.3, Eq. (8.81); Notes/WolfNoteTexSource/ch08_distance_measures.tex
lines 920–940.
-/

open scoped Matrix ComplexOrder MatrixOrder InnerProductSpace
open Matrix Finset BigOperators

noncomputable section

namespace Matrix

variable {D D' : ℕ}

/-- The rank-one projector $|\psi\rangle\langle\psi|$. -/
def pureStateProj (ψ : Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  vecMulVec ψ (fun p => star (ψ p))

/-- A vector has unit Euclidean norm, in the unbundled matrix-vector form. -/
def IsUnitVector (ψ : Fin D → ℂ) : Prop :=
  (fun p => star (ψ p)) ⬝ᵥ ψ = 1

/-- Two vectors are orthogonal, in the unbundled matrix-vector form. -/
def AreOrthogonal (ψ φ : Fin D → ℂ) : Prop :=
  (fun p => star (ψ p)) ⬝ᵥ φ = 0

/-- The trace of a pure-state projector is the squared Euclidean norm of its vector. -/
@[simp] lemma trace_pureStateProj (ψ : Fin D → ℂ) :
    (pureStateProj ψ).trace = ψ ⬝ᵥ (fun p => star (ψ p)) := by
  simp [pureStateProj, trace_vecMulVec]

/-- Every pure-state projector is positive semidefinite. -/
lemma pureStateProj_posSemidef (ψ : Fin D → ℂ) :
    (pureStateProj ψ).PosSemidef := by
  exact posSemidef_vecMulVec_self_star ψ

/-- Every column of the eigenvector unitary of a Hermitian matrix is a unit vector. -/
lemma eigenvectorUnitary_isUnitVector {A : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.IsHermitian) (i : Fin D) :
    IsUnitVector (fun p => hA.eigenvectorUnitary p i) := by
  rw [IsUnitVector, dotProduct_comm]
  have hi := orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal i i
  rw [ite_eq_left rfl] at hi
  change (fun p => hA.eigenvectorBasis i p) ⬝ᵥ
    (fun p => star (hA.eigenvectorBasis i p)) = 1
  have hleft : (fun p => hA.eigenvectorBasis i p) = ⇑(hA.eigenvectorBasis i) := rfl
  have hright : (fun p => star (hA.eigenvectorBasis i p)) =
      star ⇑(hA.eigenvectorBasis i) := by ext p; rfl
  rw [hleft, hright]
  exact hi

/-- Positive-eigenvalue eigenvectors of positive semidefinite matrices with
orthogonal supports are orthogonal. -/
lemma eigenvectorUnitary_areOrthogonal_of_mul_eq_zero
    {P Q : Matrix (Fin D) (Fin D) ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (hPQ : P * Q = 0) {i j : Fin D} (hi : hP.1.eigenvalues i ≠ 0)
    (hj : hQ.1.eigenvalues j ≠ 0) :
    AreOrthogonal (fun p => hP.1.eigenvectorUnitary p i)
      (fun p => hQ.1.eigenvectorUnitary p j) := by
  let ψ : Fin D → ℂ := fun p => hP.1.eigenvectorUnitary p i
  let φ : Fin D → ℂ := fun p => hQ.1.eigenvectorUnitary p j
  have hPeig : P *ᵥ ψ = (hP.1.eigenvalues i : ℂ) • ψ := by
    simpa [ψ, IsHermitian.eigenvectorUnitary_apply] using hP.1.mulVec_eigenvectorBasis i
  have hQeig : Q *ᵥ φ = (hQ.1.eigenvalues j : ℂ) • φ := by
    simpa [φ, IsHermitian.eigenvectorUnitary_apply] using hQ.1.mulVec_eigenvectorBasis j
  have hPφ : P *ᵥ φ = 0 := by
    have hz : P *ᵥ (Q *ᵥ φ) = 0 := by
      rw [mulVec_mulVec, hPQ, zero_mulVec]
    rw [hQeig, mulVec_smul] at hz
    exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hj)
  rw [AreOrthogonal]
  have hsymm : star ψ ⬝ᵥ (P *ᵥ φ) = star (P *ᵥ ψ) ⬝ᵥ φ := by
    rw [dotProduct_mulVec, star_mulVec, hP.1.eq]
  rw [hPφ, dotProduct_zero, hPeig, star_smul, smul_dotProduct] at hsymm
  have hiC : (hP.1.eigenvalues i : ℂ) ≠ 0 := by exact_mod_cast hi
  exact (mul_eq_zero.mp hsymm.symm).resolve_left (star_ne_zero.mpr hiC)

/-- The eigenvalues of a positive semidefinite matrix of trace one sum to one. -/
lemma PosSemidef.sum_eigenvalues_eq_one {A : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.PosSemidef) (htr : A.trace = 1) : ∑ i, hA.1.eigenvalues i = 1 := by
  have hc : ∑ i, (hA.1.eigenvalues i : ℂ) = 1 := by
    calc
      ∑ i, (hA.1.eigenvalues i : ℂ) = A.trace := hA.1.trace_eq_sum_eigenvalues.symm
      _ = 1 := htr
  exact_mod_cast hc

/-- The difference of two trace-one positive semidefinite matrices is a product-weighted
sum of differences of their eigenprojectors. -/
lemma PosSemidef.sub_eq_sum_product_eigenprojectors
    {P Q : Matrix (Fin D) (Fin D) ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (hPtr : P.trace = 1) (hQtr : Q.trace = 1) :
    P - Q = ∑ x : Fin D × Fin D,
      (hP.1.eigenvalues x.1 * hQ.1.eigenvalues x.2 : ℂ) •
        (pureStateProj (fun a => hP.1.eigenvectorUnitary a x.1) -
          pureStateProj (fun a => hQ.1.eigenvectorUnitary a x.2)) := by
  have hPdecomp : P = ∑ i, (hP.1.eigenvalues i : ℂ) •
      pureStateProj (fun a => hP.1.eigenvectorUnitary a i) := by
    simpa only [pureStateProj] using hP.eq_sum_eigenvalue_smul_eigenprojector
  have hQdecomp : Q = ∑ j, (hQ.1.eigenvalues j : ℂ) •
      pureStateProj (fun a => hQ.1.eigenvectorUnitary a j) := by
    simpa only [pureStateProj] using hQ.eq_sum_eigenvalue_smul_eigenprojector
  have hPsum : ∑ i, (hP.1.eigenvalues i : ℂ) = 1 := by
    calc
      ∑ i, (hP.1.eigenvalues i : ℂ) = P.trace := hP.1.trace_eq_sum_eigenvalues.symm
      _ = 1 := hPtr
  have hQsum : ∑ j, (hQ.1.eigenvalues j : ℂ) = 1 := by
    calc
      ∑ j, (hQ.1.eigenvalues j : ℂ) = Q.trace := hQ.1.trace_eq_sum_eigenvalues.symm
      _ = 1 := hQtr
  calc
    P - Q = (∑ i, (hP.1.eigenvalues i : ℂ) •
        pureStateProj (fun a => hP.1.eigenvectorUnitary a i)) -
      (∑ j, (hQ.1.eigenvalues j : ℂ) •
        pureStateProj (fun a => hQ.1.eigenvectorUnitary a j)) :=
      congrArg₂ (· - ·) hPdecomp hQdecomp
    _ = _ := by
      simp_rw [smul_sub, Finset.sum_sub_distrib, Fintype.sum_prod_type]
      congr 1
      · refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← Finset.sum_smul]
        congr 1
        rw [← Finset.mul_sum, hQsum, mul_one]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [← Finset.sum_smul]
        congr 1
        rw [← Finset.sum_mul, hPsum, one_mul]

/-- A product-weighted sum has trace norm at most a common bound on its nonzero-weight
terms when both families of nonnegative weights sum to one. -/
theorem traceNorm_sum_product_smul_le
    (l m : Fin D → ℝ) (A : Fin D × Fin D → Matrix (Fin D') (Fin D') ℂ)
    (hl : ∀ i, 0 ≤ l i) (hm : ∀ j, 0 ≤ m j)
    (hlsum : ∑ i, l i = 1) (hmsum : ∑ j, m j = 1) {M : ℝ}
    (hA : ∀ i j, l i ≠ 0 → m j ≠ 0 → traceNorm (A (i, j)) ≤ M) :
    traceNorm (∑ x, (l x.1 * m x.2 : ℂ) • A x) ≤ M := by
  calc
    traceNorm (∑ x, (l x.1 * m x.2 : ℂ) • A x)
        ≤ ∑ x : Fin D × Fin D, traceNorm ((l x.1 * m x.2 : ℂ) • A x) :=
      traceNorm_sum_le _
    _ = ∑ x : Fin D × Fin D, l x.1 * m x.2 * traceNorm (A x) := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [traceNorm_smul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hl x.1), abs_of_nonneg (hm x.2)]
    _ ≤ ∑ x : Fin D × Fin D, l x.1 * m x.2 * M := by
      refine Finset.sum_le_sum fun x _ ↦ ?_
      by_cases hli : l x.1 = 0
      · simp [hli]
      by_cases hmj : m x.2 = 0
      · simp [hmj]
      exact mul_le_mul_of_nonneg_left (hA x.1 x.2 hli hmj)
        (mul_nonneg (hl x.1) (hm x.2))
    _ = M := by
      simp_rw [Fintype.sum_prod_type]
      calc
        ∑ i, ∑ j, l i * m j * M = ∑ i, l i * (∑ j, m j * M) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = M := by
          have hin : (∑ j, m j * M) = M := by
            rw [← Finset.sum_mul, hmsum, one_mul]
          rw [hin, ← Finset.sum_mul, hlsum, one_mul]

/-- Wolf's product-weight convexity step.  If two density matrices have
orthogonal supports, the image of their difference is bounded by any common
bound on images of differences of orthogonal pure states. -/
theorem traceNorm_map_sub_le_of_orthogonal_density
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D') (Fin D') ℂ)
    {P Q : Matrix (Fin D) (Fin D) ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (hPtr : P.trace = 1) (hQtr : Q.trace = 1) (hPQ : P * Q = 0)
    {M : ℝ}
    (hM : ∀ ψ φ, IsUnitVector ψ → IsUnitVector φ → AreOrthogonal ψ φ →
      traceNorm (T (pureStateProj ψ - pureStateProj φ)) ≤ M) :
    traceNorm (T P - T Q) ≤ M := by
  let p : Fin D → Fin D → ℂ := fun i a => hP.1.eigenvectorUnitary a i
  let q : Fin D → Fin D → ℂ := fun j a => hQ.1.eigenvectorUnitary a j
  let l : Fin D → ℝ := hP.1.eigenvalues
  let m : Fin D → ℝ := hQ.1.eigenvalues
  have hl : ∀ i, 0 ≤ l i := hP.eigenvalues_nonneg
  have hm : ∀ j, 0 ≤ m j := hQ.eigenvalues_nonneg
  have hlsum : ∑ i, l i = 1 := hP.sum_eigenvalues_eq_one hPtr
  have hmsum : ∑ j, m j = 1 := hQ.sum_eigenvalues_eq_one hQtr
  have hdiff : P - Q = ∑ x : Fin D × Fin D,
      (l x.1 * m x.2 : ℂ) • (pureStateProj (p x.1) - pureStateProj (q x.2)) := by
    simpa only [l, m, p, q] using hP.sub_eq_sum_product_eigenprojectors hQ hPtr hQtr
  rw [← map_sub, hdiff, map_sum]
  simp_rw [map_smul]
  apply traceNorm_sum_product_smul_le l m _ hl hm hlsum hmsum
  intro i j hi hj
  exact hM _ _
    (eigenvectorUnitary_isUnitVector hP.1 i)
    (eigenvectorUnitary_isUnitVector hQ.1 j)
    (eigenvectorUnitary_areOrthogonal_of_mul_eq_zero hP hQ hPQ hi hj)

/-- Every coordinate of a unit vector has norm at most one. -/
lemma norm_apply_le_one_of_isUnitVector {ψ : Fin D → ℂ} (hψ : IsUnitVector ψ)
    (i : Fin D) : ‖ψ i‖ ≤ 1 := by
  let v : EuclideanSpace ℂ (Fin D) := WithLp.toLp 2 ψ
  have hvnorm : ‖v‖ = 1 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), EuclideanSpace.inner_toLp_toLp]
    have hstar : star ψ = fun p => star (ψ p) := by ext; rfl
    rw [hstar, dotProduct_comm, hψ]
    norm_num
  calc
    ‖ψ i‖ = ‖⟪EuclideanSpace.single i (1 : ℂ), v⟫_ℂ‖ := by
      rw [EuclideanSpace.inner_single_left]
      simp [v]
    _ ≤ ‖EuclideanSpace.single i (1 : ℂ)‖ * ‖v‖ := norm_inner_le_norm _ _
    _ = 1 := by simp [hvnorm]

/-- A uniform finite-dimensional bound for the image trace norm in terms of
matrix entries.  It supplies boundedness of the exact supremum sets without
assuming positivity or trace preservation of the linear map. -/
theorem traceNorm_linearMap_le_sum_entry
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D') (Fin D') ℂ)
    (A : Matrix (Fin D) (Fin D) ℂ) :
    traceNorm (T A) ≤ ∑ x : Fin D × Fin D,
      ‖A x.1 x.2‖ * traceNorm (T (Matrix.single x.1 x.2 1)) := by
  have hA : A = ∑ x : Fin D × Fin D, A x.1 x.2 • Matrix.single x.1 x.2 1 := by
    simpa [Fintype.sum_prod_type] using (Matrix.matrix_eq_sum_single A)
  calc
    traceNorm (T A) = traceNorm (T (∑ x : Fin D × Fin D,
        A x.1 x.2 • Matrix.single x.1 x.2 1)) := by rw [← hA]
    _ = traceNorm (∑ x : Fin D × Fin D,
        T (A x.1 x.2 • Matrix.single x.1 x.2 1)) := by rw [map_sum]
    _ ≤ ∑ x : Fin D × Fin D,
        traceNorm (T (A x.1 x.2 • Matrix.single x.1 x.2 1)) := traceNorm_sum_le _
    _ = ∑ x : Fin D × Fin D,
        ‖A x.1 x.2‖ * traceNorm (T (Matrix.single x.1 x.2 1)) := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [map_smul, traceNorm_smul]

/-- Values on differences of unit pure states form a bounded-above set. -/
theorem bddAbove_orthogonalPureStateTraceNorms
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D') (Fin D') ℂ) :
    BddAbove {r : ℝ | ∃ ψ φ : Fin D → ℂ,
      IsUnitVector ψ ∧ IsUnitVector φ ∧ AreOrthogonal ψ φ ∧
      r = traceNorm (T (pureStateProj ψ - pureStateProj φ))} := by
  refine ⟨∑ x : Fin D × Fin D,
    2 * traceNorm (T (Matrix.single x.1 x.2 1)), ?_⟩
  rintro r ⟨ψ, φ, hψ, hφ, _horth, rfl⟩
  refine (traceNorm_linearMap_le_sum_entry T _).trans ?_
  refine Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_right ?_ (traceNorm_nonneg _)
  rw [pureStateProj, pureStateProj, Matrix.sub_apply, Matrix.vecMulVec_apply,
    Matrix.vecMulVec_apply]
  calc
    ‖ψ x.1 * star (ψ x.2) - φ x.1 * star (φ x.2)‖
        ≤ ‖ψ x.1 * star (ψ x.2)‖ + ‖φ x.1 * star (φ x.2)‖ := norm_sub_le _ _
    _ ≤ 1 * 1 + 1 * 1 := by
      simp only [norm_mul, norm_star]
      exact add_le_add
        (mul_le_mul (norm_apply_le_one_of_isUnitVector hψ x.1)
          (norm_apply_le_one_of_isUnitVector hψ x.2) (norm_nonneg _) zero_le_one)
        (mul_le_mul (norm_apply_le_one_of_isUnitVector hφ x.1)
          (norm_apply_le_one_of_isUnitVector hφ x.2) (norm_nonneg _) zero_le_one)
    _ = 2 := by norm_num

/-- Orthogonal unit pure states have trace-norm distance exactly two. -/
theorem traceNorm_pureStateProj_sub_eq_two {ψ φ : Fin D → ℂ}
    (hψ : IsUnitVector ψ) (hφ : IsUnitVector φ) (horth : AreOrthogonal ψ φ) :
    traceNorm (pureStateProj ψ - pureStateProj φ) = 2 := by
  let P := pureStateProj ψ
  let Q := pureStateProj φ
  have hPH : P.IsHermitian := (pureStateProj_posSemidef ψ).isHermitian
  have hQH : Q.IsHermitian := (pureStateProj_posSemidef φ).isHermitian
  have hPP : P * P = P := by
    change vecMulVec ψ (fun p => star (ψ p)) * vecMulVec ψ (fun p => star (ψ p)) =
      vecMulVec ψ (fun p => star (ψ p))
    rw [Matrix.vecMulVec_mul_vecMulVec, hψ, one_smul]
  have hQQ : Q * Q = Q := by
    change vecMulVec φ (fun p => star (φ p)) * vecMulVec φ (fun p => star (φ p)) =
      vecMulVec φ (fun p => star (φ p))
    rw [Matrix.vecMulVec_mul_vecMulVec, hφ, one_smul]
  have hPQ : P * Q = 0 := by
    change vecMulVec ψ (fun p => star (ψ p)) * vecMulVec φ (fun p => star (φ p)) = 0
    rw [Matrix.vecMulVec_mul_vecMulVec, horth, zero_smul]
    ext
    simp [Matrix.vecMulVec_apply]
  have hQP : Q * P = 0 := by
    have hs := congrArg star hPQ
    simpa [star_mul, Matrix.star_eq_conjTranspose, hPH.eq, hQH.eq] using hs
  have hnonneg : (0 : Matrix (Fin D) (Fin D) ℂ) ≤ P + Q :=
    ((pureStateProj_posSemidef ψ).add (pureStateProj_posSemidef φ)).nonneg
  have habs : CFC.abs (P - Q) = P + Q := by
    apply CFC.sqrt_unique
    · rw [star_eq_conjTranspose]
      have hdiffH : (P - Q)ᴴ = P - Q := (hPH.sub hQH).eq
      rw [hdiffH]
      simp only [add_mul, mul_add, sub_mul, mul_sub, hPP, hQQ, hPQ, hQP,
        add_zero, zero_add, sub_zero]
      abel
    · exact hnonneg
  rw [traceNorm_eq_re_trace_abs, habs, trace_add, Complex.add_re]
  have hPtr : P.trace = 1 := by
    change (pureStateProj ψ).trace = 1
    rw [trace_pureStateProj, dotProduct_comm]
    exact hψ
  have hQtr : Q.trace = 1 := by
    change (pureStateProj φ).trace = 1
    rw [trace_pureStateProj, dotProduct_comm]
    exact hφ
  rw [hPtr, hQtr]
  norm_num

/-- The exact quotient-value set on the left of Wolf's Eq. (8.81). -/
def traceNormContractionRatios
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D') (Fin D') ℂ) : Set ℝ :=
  {r | ∃ ρ₁ ∈ densityMatrices D, ∃ ρ₂ ∈ densityMatrices D, ρ₁ ≠ ρ₂ ∧
    r = traceNorm (T ρ₁ - T ρ₂) / traceNorm (ρ₁ - ρ₂)}

/-- The exact orthogonal-unit-vector value set on the right of Wolf's
Eq. (8.81), before multiplication by one half. -/
def orthogonalPureStateTraceNorms
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D') (Fin D') ℂ) : Set ℝ :=
  {r | ∃ ψ φ : Fin D → ℂ,
    IsUnitVector ψ ∧ IsUnitVector φ ∧ AreOrthogonal ψ φ ∧
    r = traceNorm (T (pureStateProj ψ - pureStateProj φ))}

/-- The projector onto a unit vector is a density matrix. -/
lemma pureStateProj_mem_densityMatrices {ψ : Fin D → ℂ} (hψ : IsUnitVector ψ) :
    pureStateProj ψ ∈ densityMatrices D := by
  refine ⟨pureStateProj_posSemidef ψ, ?_⟩
  rw [trace_pureStateProj, dotProduct_comm]
  exact hψ

/-- The projectors onto a unit vector and an orthogonal vector are distinct. -/
lemma pureStateProj_ne_of_areOrthogonal {ψ φ : Fin D → ℂ}
    (hψ : IsUnitVector ψ) (horth : AreOrthogonal ψ φ) :
    pureStateProj ψ ≠ pureStateProj φ := by
  intro heq
  have hzero : pureStateProj ψ * pureStateProj φ = 0 := by
    change vecMulVec ψ (fun p => star (ψ p)) * vecMulVec φ (fun p => star (φ p)) = 0
    rw [Matrix.vecMulVec_mul_vecMulVec, horth, zero_smul]
    ext
    simp [Matrix.vecMulVec_apply]
  have hidem : pureStateProj ψ * pureStateProj ψ = pureStateProj ψ := by
    change vecMulVec ψ (fun p => star (ψ p)) * vecMulVec ψ (fun p => star (ψ p)) =
      vecMulVec ψ (fun p => star (ψ p))
    rw [Matrix.vecMulVec_mul_vecMulVec, hψ, one_smul]
  have : pureStateProj ψ = 0 := by
    calc
      pureStateProj ψ = pureStateProj ψ * pureStateProj ψ := hidem.symm
      _ = pureStateProj ψ * pureStateProj φ := congrArg (pureStateProj ψ * ·) heq
      _ = 0 := hzero
  have htr := congrArg Matrix.trace this
  rw [(pureStateProj_mem_densityMatrices hψ).2, trace_zero] at htr
  norm_num at htr

/-- Orthogonally supported density matrices yield at least one pair of
orthogonal unit eigenvectors. -/
theorem orthogonalPureStateTraceNorms_nonempty_of_density
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D') (Fin D') ℂ)
    {P Q : Matrix (Fin D) (Fin D) ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (hPtr : P.trace = 1) (hQtr : Q.trace = 1) (hPQ : P * Q = 0) :
    (orthogonalPureStateTraceNorms T).Nonempty := by
  have hi : ∃ i, hP.1.eigenvalues i ≠ 0 := by
    by_contra h
    push Not at h
    have hz : P.trace = 0 := by
      rw [hP.1.trace_eq_sum_eigenvalues]
      simp [h]
    rw [hPtr] at hz
    norm_num at hz
  have hj : ∃ j, hQ.1.eigenvalues j ≠ 0 := by
    by_contra h
    push Not at h
    have hz : Q.trace = 0 := by
      rw [hQ.1.trace_eq_sum_eigenvalues]
      simp [h]
    rw [hQtr] at hz
    norm_num at hz
  obtain ⟨i, hi⟩ := hi
  obtain ⟨j, hj⟩ := hj
  let ψ : Fin D → ℂ := fun p => hP.1.eigenvectorUnitary p i
  let φ : Fin D → ℂ := fun p => hQ.1.eigenvectorUnitary p j
  refine ⟨traceNorm (T (pureStateProj ψ - pureStateProj φ)), ψ, φ,
    eigenvectorUnitary_isUnitVector hP.1 i,
    eigenvectorUnitary_isUnitVector hQ.1 j,
    eigenvectorUnitary_areOrthogonal_of_mul_eq_zero hP hQ hPQ hi hj, rfl⟩

/-- **Wolf's trace-norm contraction coefficient formula** (Lemma 8.3,
Eq. (8.81)).  For an arbitrary complex-linear map, the exact supremum of the
trace-norm quotient over distinct density matrices equals one half of the
exact supremum over differences of rank-one projectors onto orthogonal unit
vectors.

No positivity, complete positivity, or trace-preservation assumption is made
on `T`, exactly as in Wolf's statement.

Wolf Ch. 8, Lemma 8.3, Eq. (8.81);
Notes/WolfNoteTexSource/ch08_distance_measures.tex lines 920–940. -/
theorem traceNorm_contraction_coefficient_eq_half_sSup_orthogonal
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D') (Fin D') ℂ) :
    sSup (traceNormContractionRatios T) =
      (1 / 2 : ℝ) * sSup (orthogonalPureStateTraceNorms T) := by
  let R := traceNormContractionRatios T
  let S := orthogonalPureStateTraceNorms T
  have hbS : BddAbove S := by
    simpa [S, orthogonalPureStateTraceNorms] using
      bddAbove_orthogonalPureStateTraceNorms T
  by_cases hS : S.Nonempty
  · have hpure_le : ∀ ψ φ, IsUnitVector ψ → IsUnitVector φ →
        AreOrthogonal ψ φ →
        traceNorm (T (pureStateProj ψ - pureStateProj φ)) ≤ sSup S := by
      intro ψ φ hψ hφ horth
      apply le_csSup hbS
      exact ⟨ψ, φ, hψ, hφ, horth, rfl⟩
    have hpureRatio : ∀ v ∈ S, v / 2 ∈ R := by
      intro v hv
      rcases hv with ⟨ψ, φ, hψ, hφ, horth, rfl⟩
      refine ⟨pureStateProj ψ, pureStateProj_mem_densityMatrices hψ,
        pureStateProj φ, pureStateProj_mem_densityMatrices hφ,
        pureStateProj_ne_of_areOrthogonal hψ horth, ?_⟩
      rw [← map_sub, traceNorm_pureStateProj_sub_eq_two hψ hφ horth]
    have hR : R.Nonempty := by
      obtain ⟨v, hv⟩ := hS
      exact ⟨v / 2, hpureRatio v hv⟩
    have hrat_le : ∀ r ∈ R, r ≤ (1 / 2 : ℝ) * sSup S := by
      intro r hr
      rcases hr with ⟨ρ₁, hρ₁, ρ₂, hρ₂, hne, rfl⟩
      have hH : (ρ₁ - ρ₂).IsHermitian := hρ₁.1.isHermitian.sub hρ₂.1.isHermitian
      have htr : (ρ₁ - ρ₂).trace = 0 := by
        rw [trace_sub, hρ₁.2, hρ₂.2, sub_self]
      have hHne : ρ₁ - ρ₂ ≠ 0 := sub_ne_zero.mpr hne
      obtain ⟨P, Q, hP, hPtr, hQ, hQtr, hPQ, hratio⟩ :=
        exists_orthogonal_density_traceNorm_ratio T hH htr hHne
      rw [← map_sub, hratio]
      exact mul_le_mul_of_nonneg_left
        (traceNorm_map_sub_le_of_orthogonal_density T hP hQ hPtr hQtr hPQ hpure_le)
        (by norm_num)
    have hbR : BddAbove R := ⟨(1 / 2 : ℝ) * sSup S, hrat_le⟩
    apply le_antisymm
    · exact csSup_le hR hrat_le
    · have heach : ∀ v ∈ S, v ≤ 2 * sSup R := by
        intro v hv
        have := le_csSup hbR (hpureRatio v hv)
        linarith
      have hsup_le : sSup S ≤ 2 * sSup R := csSup_le hS heach
      linarith
  · have hRempty : R = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨r, ρ₁, hρ₁, ρ₂, hρ₂, hne, _hr⟩
      have hH : (ρ₁ - ρ₂).IsHermitian := hρ₁.1.isHermitian.sub hρ₂.1.isHermitian
      have htr : (ρ₁ - ρ₂).trace = 0 := by
        rw [trace_sub, hρ₁.2, hρ₂.2, sub_self]
      obtain ⟨t, ht, P, Q, hP, hPtr, hQ, hQtr, hPQ, _hscale, _hnorm⟩ :=
        exists_orthogonal_density_jordan_normalization hH htr (sub_ne_zero.mpr hne)
      exact hS (by
        simpa [S] using
          orthogonalPureStateTraceNorms_nonempty_of_density T hP hQ hPtr hQtr hPQ)
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    change sSup R = (1 / 2 : ℝ) * sSup S
    rw [hRempty, hSempty]
    simp

end Matrix
