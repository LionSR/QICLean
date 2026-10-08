/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixAux
import QICLean.Algebra.FrobeniusHilbert
import QICLean.Analysis.RectangularTraceNorm
import QICLean.Analysis.CfcConjugation
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Dimension-independent rectangular probability weights

For independent nonnegative probability lists on the row and column spaces,
quarter powers sandwich a rectangular contraction to a Hilbert--Schmidt
operator of norm at most one. Zero probabilities and different row and column
dimensions are allowed. The proof uses row and column bounds and the scalar
arithmetic--geometric mean inequality, avoiding a dimension factor.

These are original proofs of the weighted estimate in *Polynomial PEPS
approximation of gapped square-grid ground states*, Theorem 5.2,
`04-compression.tex:383–538`, especially `eq:compression-dimension-free`.
No OpenAI Lean code is copied or adapted.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

noncomputable section

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Diagonal quarter powers of nonnegative probabilities, with no inverse on
zero entries. Theorem 5.2, `eq:compression-quarter-powers`. -/
def probabilityQuarter (p : m → ℝ) : Matrix m m ℂ :=
  diagonal fun i ↦ (Real.sqrt (Real.sqrt (p i)) : ℂ)

/-- Independent row and column quarter-power weights. Theorem 5.2,
`eq:compression-dimension-free`. -/
def quarterWeighted (p : m → ℝ) (q : n → ℝ) (O : Matrix m n ℂ) : Matrix m n ℂ :=
  probabilityQuarter p * O * probabilityQuarter q

/-- Independent square-root weights in the exterior-input operator of
Theorem 5.2, `eq:compression-exterior-input`. -/
def halfWeighted (p : m → ℝ) (q : n → ℝ) (W : Matrix m n ℂ) : Matrix m n ℂ :=
  diagonal (fun i ↦ (Real.sqrt (p i) : ℂ)) * W *
    diagonal (fun j ↦ (Real.sqrt (q j) : ℂ))

/-- Quarter powers split a square-root probability weight without an inverse. -/
theorem probabilityQuarter_mul_self (p : m → ℝ) :
    probabilityQuarter p * probabilityQuarter p =
      diagonal fun i ↦ (Real.sqrt (p i) : ℂ) := by
  rw [probabilityQuarter, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.ofReal_mul]
  exact congrArg Complex.ofReal (Real.mul_self_sqrt (Real.sqrt_nonneg _))

omit [Fintype m] in
/-- Real diagonal quarter weights are self-adjoint. -/
theorem probabilityQuarter_conjTranspose (p : m → ℝ) :
    (probabilityQuarter p)ᴴ = probabilityQuarter p := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [probabilityQuarter]
  · simp [probabilityQuarter, conjTranspose_apply, hij, Ne.symm hij]

/-- Quarter powers split each square-root weight without an inverse. -/
theorem halfWeighted_eq_quarter_sandwich
    (p : m → ℝ) (q : n → ℝ) (W : Matrix m n ℂ) :
    halfWeighted p q W = probabilityQuarter p * quarterWeighted p q W *
      probabilityQuarter q := by
  rw [halfWeighted, quarterWeighted, ← probabilityQuarter_mul_self p,
    ← probabilityQuarter_mul_self q]
  simp only [Matrix.mul_assoc]

/-- Moving the real diagonal weights to a dual test gives the quarter-weighted
Hilbert--Schmidt pairing. Theorem 5.2, `eq:compression-quarter-powers`. -/
theorem trace_halfWeighted_conjTranspose_mul
    (p : m → ℝ) (q : n → ℝ) (W U : Matrix m n ℂ) :
    ((halfWeighted p q W)ᴴ * U).trace =
      ((quarterWeighted p q W)ᴴ * quarterWeighted p q U).trace := by
  rw [halfWeighted_eq_quarter_sandwich, conjTranspose_mul, conjTranspose_mul,
    probabilityQuarter_conjTranspose p, probabilityQuarter_conjTranspose q]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (probabilityQuarter q)]
  simp only [quarterWeighted, Matrix.mul_assoc]

@[simp]
theorem quarterWeighted_apply (p : m → ℝ) (q : n → ℝ) (O : Matrix m n ℂ)
    (i : m) (j : n) :
    quarterWeighted p q O i j =
      (Real.sqrt (Real.sqrt (p i)) : ℂ) * O i j *
        (Real.sqrt (Real.sqrt (q j)) : ℂ) := by
  simp [quarterWeighted, probabilityQuarter, diagonal_mul, mul_diagonal]

omit [DecidableEq m] in
/-- A contraction has squared Euclidean column norm at most one, independently
of its rectangular dimensions. Auxiliary to Theorem 5.2. -/
theorem sum_norm_sq_column_le_one {O : Matrix m n ℂ} (hO : ‖O‖ ≤ 1) (j : n) :
    ∑ i, ‖O i j‖ ^ 2 ≤ 1 := by
  have hc := O.l2_opNorm_mulVec (EuclideanSpace.single j (1 : ℂ))
  have hcol : O *ᵥ (EuclideanSpace.single j (1 : ℂ)) = fun i ↦ O i j := by
    ext i
    simp [mulVec, dotProduct]
  rw [hcol] at hc
  have hnorm : ‖(WithLp.toLp 2 fun i ↦ O i j : EuclideanSpace ℂ m)‖ ≤ 1 := by
    simpa using hc.trans (by simpa using hO)
  have hsq := (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr hnorm
  simpa [EuclideanSpace.norm_sq_eq] using hsq

omit [DecidableEq m] in
/-- A contraction has squared Euclidean row norm at most one. Auxiliary to
Theorem 5.2; conjugate transpose is used only for this norm estimate. -/
theorem sum_norm_sq_row_le_one {O : Matrix m n ℂ} (hO : ‖O‖ ≤ 1) (i : m) :
    ∑ j, ‖O i j‖ ^ 2 ≤ 1 := by
  classical
  have h := sum_norm_sq_column_le_one
    (O := Oᴴ) (by simpa only [l2_opNorm_conjTranspose] using hO) i
  simpa only [conjTranspose_apply, norm_star] using h

omit [DecidableEq m] [DecidableEq n] in
/-- Two independent probability weights bound a nonnegative matrix whose row
and column sums are at most one. Scalar form of the dimension-independent
Schatten `4,∞,4` estimate in Theorem 5.2. -/
theorem sum_sqrt_probability_mul_le_one
    (p : m → ℝ) (q : n → ℝ) (a : m → n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ j, q j = 1)
    (ha : ∀ i j, 0 ≤ a i j)
    (hrow : ∀ i, ∑ j, a i j ≤ 1) (hcol : ∀ j, ∑ i, a i j ≤ 1) :
    ∑ i, ∑ j, Real.sqrt (p i) * Real.sqrt (q j) * a i j ≤ 1 := by
  have ham : ∀ i j, Real.sqrt (p i) * Real.sqrt (q j) ≤ (p i + q j) / 2 := by
    intro i j
    have hs := sq_nonneg (Real.sqrt (p i) - Real.sqrt (q j))
    nlinarith [Real.sq_sqrt (hp i), Real.sq_sqrt (hq j)]
  calc
    (∑ i, ∑ j, Real.sqrt (p i) * Real.sqrt (q j) * a i j) ≤
        ∑ i, ∑ j, ((p i + q j) / 2) * a i j :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_right (ham i j) (ha i j)
    _ = ((∑ i, p i * ∑ j, a i j) + (∑ j, q j * ∑ i, a i j)) / 2 := by
      calc
        _ = ((∑ i, ∑ j, p i * a i j) + (∑ i, ∑ j, q j * a i j)) / 2 := by
          simp only [add_div, add_mul, Finset.sum_add_distrib, Finset.sum_div]
          congr 1
          · exact Finset.sum_congr rfl fun i _ ↦
              Finset.sum_congr rfl fun j _ ↦ by ring
          · exact Finset.sum_congr rfl fun i _ ↦
              Finset.sum_congr rfl fun j _ ↦ by ring
        _ = _ := by
          rw [Finset.sum_comm (f := fun i j ↦ q j * a i j)]
          simp only [← Finset.mul_sum]
    _ ≤ ((∑ i, p i) + (∑ j, q j)) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply add_le_add
      · exact Finset.sum_le_sum fun i _ ↦ by
          simpa using mul_le_mul_of_nonneg_left (hrow i) (hp i)
      · exact Finset.sum_le_sum fun j _ ↦ by
          simpa using mul_le_mul_of_nonneg_left (hcol j) (hq j)
    _ = 1 := by rw [hpsum, hqsum]; norm_num

/-- Entrywise Hilbert--Schmidt square of a rectangular quarter-weighted matrix.
Theorem 5.2, `eq:compression-block-second-moment` and the block aggregation
preceding `eq:compression-dimension-free`. -/
theorem frobeniusNormSq_quarterWeighted
    (p : m → ℝ) (q : n → ℝ) (O : Matrix m n ℂ) :
    frobeniusNormSq (quarterWeighted p q O) =
      ∑ i, ∑ j, Real.sqrt (p i) * Real.sqrt (q j) * ‖O i j‖ ^ 2 := by
  unfold frobeniusNormSq
  rw [← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq,
    trace_conjTranspose_mul_self_re_eq_sum_norm_sq, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [quarterWeighted_apply, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_pow, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg (p i)),
    Real.sq_sqrt (Real.sqrt_nonneg (q j))]
  ring

/-- Quarter-power weighting of a rectangular contraction has Hilbert--Schmidt
norm at most one. Theorem 5.2, `eq:compression-dimension-free`, with zero
probabilities allowed and no dependence on either private dimension. -/
theorem frobeniusNormSq_quarterWeighted_le_one
    (p : m → ℝ) (q : n → ℝ) (O : Matrix m n ℂ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ j, q j = 1) (hO : ‖O‖ ≤ 1) :
    frobeniusNormSq (quarterWeighted p q O) ≤ 1 := by
  rw [frobeniusNormSq_quarterWeighted]
  exact sum_sqrt_probability_mul_le_one p q (fun i j ↦ ‖O i j‖ ^ 2)
    hp hq hpsum hqsum (fun i j ↦ sq_nonneg _) (sum_norm_sq_row_le_one hO)
    (sum_norm_sq_column_le_one hO)

omit [DecidableEq m] [DecidableEq n] in
open scoped Matrix.Norms.Frobenius in
/-- Hilbert--Schmidt Cauchy--Schwarz for arbitrary rectangular matrices,
expressed without choosing a matrix operator-norm instance. -/
theorem norm_trace_conjTranspose_mul_sq_le_frobeniusNormSq
    (P Q : Matrix m n ℂ) :
    ‖(Pᴴ * Q).trace‖ ^ 2 ≤ frobeniusNormSq P * frobeniusNormSq Q := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (frobeniusEquivEuclidean m n P)
    (frobeniusEquivEuclidean m n Q)
  rw [inner_frobeniusEquivEuclidean, (frobeniusEquivEuclidean m n).norm_map,
    (frobeniusEquivEuclidean m n).norm_map] at h
  unfold frobeniusNormSq
  nlinarith [norm_nonneg P, norm_nonneg Q, norm_nonneg ((Pᴴ * Q).trace)]

/-- The independent two-weight rectangular trace/Hilbert--Schmidt estimate.
Theorem 5.2, `eq:compression-quarter-powers`: trace-one nonnegative diagonal
weights, arbitrary rectangular complex matrix, zeros allowed, no rank factor. -/
theorem rectangularTraceNorm_halfWeighted_le
    (p : m → ℝ) (q : n → ℝ) (W : Matrix m n ℂ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ j, q j = 1) :
    rectangularTraceNorm (halfWeighted p q W) ≤
      Real.sqrt (frobeniusNormSq (quarterWeighted p q W)) := by
  apply rectangularTraceNorm_le_of_forall_contraction
  intro U hU
  rw [trace_halfWeighted_conjTranspose_mul]
  have hcs := norm_trace_conjTranspose_mul_sq_le_frobeniusNormSq
    (quarterWeighted p q W) (quarterWeighted p q U)
  have hweight := frobeniusNormSq_quarterWeighted_le_one p q U hp hq hpsum hqsum hU
  have hnonneg : 0 ≤ frobeniusNormSq (quarterWeighted p q W) := sq_nonneg _
  have hsq : ‖((quarterWeighted p q W)ᴴ * quarterWeighted p q U).trace‖ ^ 2 ≤
      frobeniusNormSq (quarterWeighted p q W) :=
    hcs.trans (by simpa using mul_le_mul_of_nonneg_left hweight hnonneg)
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    (by rwa [Real.sq_sqrt hnonneg])

/-- Hilbert--Schmidt norm form of the dimension-independent contraction
estimate. Theorem 5.2, `eq:compression-dimension-free`. -/
theorem sqrt_frobeniusNormSq_quarterWeighted_le_one
    (p : m → ℝ) (q : n → ℝ) (O : Matrix m n ℂ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ j, q j = 1) (hO : ‖O‖ ≤ 1) :
    Real.sqrt (frobeniusNormSq (quarterWeighted p q O)) ≤ 1 := by
  simpa using Real.sqrt_le_sqrt
    (frobeniusNormSq_quarterWeighted_le_one p q O hp hq hpsum hqsum hO)

/-- Ordinary full transpose swaps the two quarter weights. It does not
conjugate scalar coefficients. Theorem 5.2, the transpose step after
`eq:compression-quarter-powers`. -/
theorem quarterWeighted_transpose (p : m → ℝ) (q : n → ℝ) (W : Matrix m n ℂ) :
    quarterWeighted q p Wᵀ = (quarterWeighted p q W)ᵀ := by
  ext i j
  simp only [quarterWeighted_apply, transpose_apply]
  ring

/-- The Hilbert--Schmidt square is invariant under ordinary full rectangular
transpose. Theorem 5.2, the transpose step after
`eq:compression-quarter-powers`. -/
theorem frobeniusNormSq_quarterWeighted_transpose
    (p : m → ℝ) (q : n → ℝ) (W : Matrix m n ℂ) :
    frobeniusNormSq (quarterWeighted q p Wᵀ) =
      frobeniusNormSq (quarterWeighted p q W) := by
  rw [quarterWeighted_transpose]
  unfold frobeniusNormSq
  rw [frobenius_norm_transpose]

omit [DecidableEq n] in
/-- Hilbert--Schmidt squares are invariant under a unitary change of the
rectangular codomain coordinates. -/
theorem frobeniusNormSq_unitary_mul
    (U : Matrix m m ℂ) (W : Matrix m n ℂ) (hU : U ∈ unitaryGroup m ℂ) :
    frobeniusNormSq (U * W) = frobeniusNormSq W := by
  classical
  have hUU : Uᴴ * U = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hU
  unfold frobeniusNormSq
  rw [← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq,
    ← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq, conjTranspose_mul]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul]

omit [DecidableEq m] in
/-- Hilbert--Schmidt squares are invariant under a unitary change of the
rectangular domain coordinates. -/
theorem frobeniusNormSq_mul_unitary
    (W : Matrix m n ℂ) (V : Matrix n n ℂ) (hV : V ∈ unitaryGroup n ℂ) :
    frobeniusNormSq (W * V) = frobeniusNormSq W := by
  classical
  have hVV : V * Vᴴ = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hV
  unfold frobeniusNormSq
  rw [← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq,
    ← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq, conjTranspose_mul,
    Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc, hVV, Matrix.mul_one]
  exact congrArg Complex.re (Matrix.trace_mul_comm W Wᴴ)

/-- The spectral quarter power of a positive-semidefinite matrix, with zero
eigenvalues permitted, is the diagonal probability quarter power in its
orthonormal eigenbasis. -/
theorem PosSemidef.rpow_quarter_spectral {R : Matrix m m ℂ} (hR : R.PosSemidef) :
    R ^ (1 / 4 : ℝ) = (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) *
      probabilityQuarter hR.isHermitian.eigenvalues *
      (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ)ᴴ := by
  rw [CFC.rpow_eq_cfc_real hR.nonneg, hR.isHermitian.cfc_eq,
    hR.isHermitian.cfc_form]
  congr 2
  ext i j
  simp only [probabilityQuarter, diagonal_apply]
  split_ifs
  · congr 1
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (hR.eigenvalues_nonneg i)]
    norm_num
  · rfl

/-- The dimension-independent `4,∞,4` estimate for arbitrary positive
trace-one states, without faithfulness or equal rectangular dimensions.
This extends the diagonal states used in Theorem 5.2,
`eq:compression-dimension-free`. -/
theorem frobeniusNormSq_rpow_quarter_mul_le_one
    (S : Matrix m m ℂ) (R : Matrix n n ℂ) (O : Matrix m n ℂ)
    (hS : S.PosSemidef) (hR : R.PosSemidef)
    (hStr : S.trace.re = 1) (hRtr : R.trace.re = 1) (hO : ‖O‖ ≤ 1) :
    frobeniusNormSq (S ^ (1 / 4 : ℝ) * O * R ^ (1 / 4 : ℝ)) ≤ 1 := by
  let U : Matrix m m ℂ := hS.isHermitian.eigenvectorUnitary
  let V : Matrix n n ℂ := hR.isHermitian.eigenvectorUnitary
  have hU : U ∈ unitaryGroup m ℂ := hS.isHermitian.eigenvectorUnitary.2
  have hV : V ∈ unitaryGroup n ℂ := hR.isHermitian.eigenvectorUnitary.2
  have hUV : ‖Uᴴ * O * V‖ ≤ 1 := by
    exact l2_opNorm_mul_le_one _ V
      (l2_opNorm_mul_le_one Uᴴ O
        (by simpa only [l2_opNorm_conjTranspose] using l2_opNorm_unitary_le_one hU) hO)
      (l2_opNorm_unitary_le_one hV)
  have hpsum : ∑ i, hS.isHermitian.eigenvalues i = 1 := by
    simpa [hS.isHermitian.trace_eq_sum_eigenvalues] using hStr
  have hqsum : ∑ i, hR.isHermitian.eigenvalues i = 1 := by
    simpa [hR.isHermitian.trace_eq_sum_eigenvalues] using hRtr
  have heq : S ^ (1 / 4 : ℝ) * O * R ^ (1 / 4 : ℝ) =
      U * quarterWeighted hS.isHermitian.eigenvalues hR.isHermitian.eigenvalues
        (Uᴴ * O * V) * Vᴴ := by
    rw [hS.rpow_quarter_spectral, hR.rpow_quarter_spectral]
    simp only [quarterWeighted, U, V, Matrix.mul_assoc]
  rw [heq, frobeniusNormSq_mul_unitary _ _ (by
      simpa only [← star_eq_conjTranspose] using Unitary.star_mem hV),
    frobeniusNormSq_unitary_mul _ _ hU]
  exact frobeniusNormSq_quarterWeighted_le_one _ _ _
    hS.eigenvalues_nonneg hR.eigenvalues_nonneg hpsum hqsum hUV

end Matrix
