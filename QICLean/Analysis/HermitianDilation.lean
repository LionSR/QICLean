/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixBernsteinInputs

/-!
# The Hermitian dilation

The Hermitian dilation of a rectangular matrix `Z` is the block matrix
`𝒟(Z) = [[0, Z], [Z*, 0]]`. It is Hermitian, real-linear in `Z`, its square is the
block-diagonal matrix with blocks `Z Z*` and `Z* Z`, and its operator norm is `‖Z‖`. It
transfers tail bounds for the largest eigenvalue of Hermitian random matrices to tail bounds
for the norm of rectangular random matrices; this is how the rectangular matrix Bernstein
inequality follows from the Hermitian one.

The operator norm of a block-diagonal matrix is the larger of the norms of its blocks. The
tail form needed for the Laplace transform method is `e^{θ‖Z‖} ≤ Tr e^{θ𝒟(Z)}`: with `v` an
eigenvector of `Z* Z` for its largest eigenvalue `‖Z‖²`, the vector `(Zv, ‖Z‖v)` has
Rayleigh quotient `‖Z‖` for `𝒟(Z)`.

## Main results

* `Matrix.hermitianDilation`: the dilation `[[0, Z], [Z*, 0]]`.
* `Matrix.isHermitian_hermitianDilation`, `Matrix.hermitianDilation_sq`.
* `Matrix.l2_opNorm_fromBlocks_zero_zero`: `‖diag(P, Q)‖ = max ‖P‖ ‖Q‖`.
* `Matrix.norm_hermitianDilation`: `‖𝒟(Z)‖ = ‖Z‖`.
* `Matrix.exp_mul_norm_le_re_trace_exp_smul_hermitianDilation`: `e^{θ‖Z‖} ≤ Tr e^{θ𝒟(Z)}`.

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*,
  Found. Comput. Math. 12 (2012) 389–434, §2.6, equations (2.10)–(2.12), Theorem 1.6.
* J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*,
  Found. Trends Mach. Learn. 8 (2015), Definition 2.1.5, equations (2.1.26)–(2.1.28).
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

section BlockNorm

variable {𝕜 : Type*} [RCLike 𝕜] {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m']
  [Fintype n'] [DecidableEq m] [DecidableEq n] [DecidableEq m'] [DecidableEq n']

omit [DecidableEq m] in
/-- The operator norm bound `‖Ax‖² ≤ ‖A‖² ‖x‖²`, written with coordinates. -/
lemma sum_norm_sq_mulVec_le (A : Matrix m n 𝕜) (x : n → 𝕜) :
    ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_mulVec A (WithLp.toLp 2 x)) 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h
  simpa using h

omit [DecidableEq m] in
/-- An operator norm bound from the coordinate form of `‖Ax‖² ≤ c² ‖x‖²`. -/
lemma l2_opNorm_le_of_sum_norm_sq_le (A : Matrix m n 𝕜) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : n → 𝕜, ∑ i, ‖(A *ᵥ x) i‖ ^ 2 ≤ c ^ 2 * ∑ j, ‖x j‖ ^ 2) : ‖A‖ ≤ c := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun y ↦ ?_
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simpa using h y

omit [DecidableEq m] [DecidableEq n] in
/-- **Norm of a block-diagonal matrix.** The operator norm of the block-diagonal matrix with
blocks `P` and `Q` is `max ‖P‖ ‖Q‖`. With `P = Z Z*` and `Q = Z* Z`, this identifies the
norm of the square of the Hermitian dilation (Tropp 2012, equation (2.11); Tropp 2015,
equation (2.1.27)) and the variance parameter of Tropp 2012, Theorem 1.6. -/
theorem l2_opNorm_fromBlocks_zero_zero (P : Matrix m m' 𝕜) (Q : Matrix n n' 𝕜) :
    ‖fromBlocks P 0 0 Q‖ = max ‖P‖ ‖Q‖ := by
  refine le_antisymm ?_ (max_le ?_ ?_)
  · refine l2_opNorm_le_of_sum_norm_sq_le _ (le_max_of_le_left (norm_nonneg _)) fun x ↦ ?_
    have hP := sum_norm_sq_mulVec_le P (x ∘ Sum.inl)
    have hQ := sum_norm_sq_mulVec_le Q (x ∘ Sum.inr)
    have hP' : ‖P‖ ^ 2 ≤ max ‖P‖ ‖Q‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) 2
    have hQ' : ‖Q‖ ^ 2 ≤ max ‖P‖ ‖Q‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) 2
    have h1 : 0 ≤ ∑ j, ‖(x ∘ Sum.inl) j‖ ^ 2 := by positivity
    have h2 : 0 ≤ ∑ j, ‖(x ∘ Sum.inr) j‖ ^ 2 := by positivity
    simp only [fromBlocks_mulVec, zero_mulVec, add_zero, zero_add, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr] at hP hQ ⊢
    simp only [Function.comp_apply] at hP hQ h1 h2
    nlinarith
  · refine l2_opNorm_le_of_sum_norm_sq_le _ (norm_nonneg _) fun x ↦ ?_
    have h := sum_norm_sq_mulVec_le (fromBlocks P 0 0 Q) (Sum.elim x 0)
    simpa [fromBlocks_mulVec, Fintype.sum_sum_type] using h
  · refine l2_opNorm_le_of_sum_norm_sq_le _ (norm_nonneg _) fun x ↦ ?_
    have h := sum_norm_sq_mulVec_le (fromBlocks P 0 0 Q) (Sum.elim 0 x)
    simpa [fromBlocks_mulVec, Fintype.sum_sum_type] using h

end BlockNorm

section Dilation

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The **Hermitian dilation** `𝒟(Z) = [[0, Z], [Z*, 0]]` of a rectangular matrix `Z`
(Tropp 2012, equation (2.10); Tropp 2015, Definition 2.1.5). -/
def hermitianDilation (Z : Matrix m n ℂ) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks 0 Z Zᴴ 0

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The Hermitian dilation is Hermitian (Tropp 2012, §2.6). -/
theorem isHermitian_hermitianDilation (Z : Matrix m n ℂ) : (hermitianDilation Z).IsHermitian := by
  rw [hermitianDilation, isHermitian_fromBlocks_iff]
  simp [IsHermitian]

omit [DecidableEq m] [DecidableEq n] in
/-- The square of the Hermitian dilation is block diagonal with blocks `Z Z*` and `Z* Z`
(Tropp 2012, equation (2.11); Tropp 2015, equation (2.1.27)). -/
theorem hermitianDilation_mul_self (Z : Matrix m n ℂ) :
    hermitianDilation Z * hermitianDilation Z = fromBlocks (Z * Zᴴ) 0 0 (Zᴴ * Z) := by
  simp [hermitianDilation, fromBlocks_multiply]

/-- The square of the Hermitian dilation, as a power (Tropp 2012, equation (2.11)). -/
theorem hermitianDilation_sq (Z : Matrix m n ℂ) :
    hermitianDilation Z ^ 2 = fromBlocks (Z * Zᴴ) 0 0 (Zᴴ * Z) := by
  rw [sq, hermitianDilation_mul_self]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The dilation of zero is zero. -/
@[simp]
theorem hermitianDilation_zero : hermitianDilation (0 : Matrix m n ℂ) = 0 := by
  simp [hermitianDilation]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The Hermitian dilation is additive (Tropp 2015, §2.1.16). -/
theorem hermitianDilation_add (Z W : Matrix m n ℂ) :
    hermitianDilation (Z + W) = hermitianDilation Z + hermitianDilation W := by
  simp [hermitianDilation, fromBlocks_add]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The Hermitian dilation commutes with real scalar multiplication (Tropp 2015, §2.1.16). -/
theorem hermitianDilation_smul (r : ℝ) (Z : Matrix m n ℂ) :
    hermitianDilation (r • Z) = r • hermitianDilation Z := by
  simp [hermitianDilation, fromBlocks_smul, conjTranspose_smul]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The Hermitian dilation of a finite sum is the sum of the dilations. -/
theorem hermitianDilation_sum {ι : Type*} (s : Finset ι) (Z : ι → Matrix m n ℂ) :
    hermitianDilation (∑ k ∈ s, Z k) = ∑ k ∈ s, hermitianDilation (Z k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, hermitianDilation_add, ih]

/-- The Hermitian dilation preserves the operator norm, `‖𝒟(Z)‖ = ‖Z‖` (Tropp 2012,
equation (2.12); Tropp 2015, equation (2.1.28)). The proof uses the C*-identity
`‖𝒟‖² = ‖𝒟* 𝒟‖ = ‖𝒟²‖` and the norm of a block-diagonal matrix. -/
theorem norm_hermitianDilation (Z : Matrix m n ℂ) : ‖hermitianDilation Z‖ = ‖Z‖ := by
  have h := l2_opNorm_conjTranspose_mul_self (hermitianDilation Z)
  rw [(isHermitian_hermitianDilation Z).eq, hermitianDilation_mul_self,
    l2_opNorm_fromBlocks_zero_zero, l2_opNorm_conjTranspose_mul_self,
    show Z * Zᴴ = Zᴴᴴ * Zᴴ by rw [conjTranspose_conjTranspose],
    l2_opNorm_conjTranspose_mul_self, l2_opNorm_conjTranspose, max_self] at h
  have := mul_self_eq_mul_self_iff.mp h
  rcases this with h1 | h1
  · exact h1.symm
  · have : ‖Z‖ = 0 := by linarith [norm_nonneg Z, norm_nonneg (hermitianDilation Z)]
    linarith [norm_nonneg (hermitianDilation Z)]


omit [DecidableEq m] [DecidableEq n] in
/-- The inner product of two vectors on a disjoint union splits into the two blocks. -/
lemma star_sum_elim_dotProduct_sum_elim (u u' : m → ℂ) (v v' : n → ℂ) :
    star (Sum.elim u v) ⬝ᵥ Sum.elim u' v' = star u ⬝ᵥ u' + star v ⬝ᵥ v' := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- **Tail form of the dilation.** For every real `θ`, `e^{θ‖Z‖} ≤ Tr e^{θ𝒟(Z)}`. With
`λ_max(𝒟(Z)) = ‖Z‖` (Tropp 2012, equation (2.12); Tropp 2015, equation (2.1.28)) this is
the bound `e^{λ_max(θY)} ≤ Tr e^{θY}` of Tropp 2012, Proposition 3.1, applied to the dilation,
as in the proof of Tropp 2012, Theorem 1.6. The proof takes an eigenvector `v` of `Z* Z`
for the eigenvalue `‖Z‖²` and uses the vector `(Zv, ‖Z‖v)`, whose Rayleigh quotient for
`𝒟(Z)` is `‖Z‖`. The index type is assumed nonempty, since otherwise both sides are `1`
and `0`. -/
theorem exp_mul_norm_le_re_trace_exp_smul_hermitianDilation [Nonempty (m ⊕ n)]
    (Z : Matrix m n ℂ) (θ : ℝ) :
    Real.exp (θ * ‖Z‖) ≤ (NormedSpace.exp (θ • hermitianDilation Z)).trace.re := by
  by_cases hZ : Z = 0
  · subst hZ
    simp only [norm_zero, mul_zero, Real.exp_zero, hermitianDilation_zero, smul_zero,
      NormedSpace.exp_zero, trace_one]
    have h := Fintype.card_pos (α := m ⊕ n)
    have : (1 : ℝ) ≤ (Fintype.card (m ⊕ n) : ℝ) := by exact_mod_cast h
    simpa using this
  set a := ‖Z‖ with ha_def
  have ha : 0 < a := norm_pos_iff.mpr hZ
  obtain ⟨i₀, j₀, -⟩ : ∃ i j, Z i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hZ (Matrix.ext h)
  have : Nonempty n := ⟨j₀⟩
  have H := isHermitian_conjTranspose_mul_self Z
  have hmem := CStarAlgebra.norm_mem_spectrum_of_nonneg (Zᴴ * Z)
    (posSemidef_conjTranspose_mul_self Z).nonneg
  rw [H.spectrum_real_eq_range_eigenvalues, l2_opNorm_conjTranspose_mul_self] at hmem
  obtain ⟨i, hi⟩ := hmem
  set v : n → ℂ := ⇑(H.eigenvectorBasis i) with hv_def
  have hv : (Zᴴ * Z) *ᵥ v = ((a * a : ℝ) : ℂ) • v := by
    rw [hv_def, H.mulVec_eigenvectorBasis i, hi, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hs : star v ⬝ᵥ v = 1 := by
    rw [dotProduct_comm, hv_def, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, H.eigenvectorBasis.orthonormal.1 i]
    simp
  have hZv : star (Z *ᵥ v) ⬝ᵥ (Z *ᵥ v) = ((a * a : ℝ) : ℂ) := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hv, dotProduct_smul, hs]
    simp
  have hstar_av : star ((a : ℂ) • v) = (a : ℂ) • star v := by
    rw [star_smul, Complex.star_def, Complex.conj_ofReal]
  set x : m ⊕ n → ℂ := Sum.elim (Z *ᵥ v) ((a : ℂ) • v) with hx_def
  have hx0 : x ≠ 0 := by
    intro h0
    have hav : (a : ℂ) • v = 0 := funext fun j ↦ by
      simpa [hx_def] using congrFun h0 (Sum.inr j)
    rcases smul_eq_zero.mp hav with h | h
    · exact ha.ne' (by exact_mod_cast h)
    · simp [h] at hs
  have hDx : hermitianDilation Z *ᵥ x = Sum.elim ((a : ℂ) • (Z *ᵥ v)) (((a * a : ℝ) : ℂ) • v) := by
    rw [hermitianDilation, fromBlocks_mulVec, hx_def]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, mulVec_smul, smul_zero,
      zero_add, add_zero]
    rw [mulVec_mulVec, hv]
  have hquad : star x ⬝ᵥ ((θ • hermitianDilation Z) *ᵥ x) = ((2 * θ * a ^ 3 : ℝ) : ℂ) := by
    rw [smul_mulVec, dotProduct_smul, hDx, hx_def, star_sum_elim_dotProduct_sum_elim,
      dotProduct_smul, hZv, hstar_av, smul_dotProduct, dotProduct_smul, hs]
    simp only [smul_eq_mul, Complex.real_smul]
    push_cast; ring
  have hnorm : star x ⬝ᵥ x = ((2 * a ^ 2 : ℝ) : ℂ) := by
    rw [hx_def, star_sum_elim_dotProduct_sum_elim, hZv, hstar_av, smul_dotProduct,
      dotProduct_smul, hs]
    simp only [smul_eq_mul]
    push_cast; ring
  have key := ((isHermitian_hermitianDilation Z).smul
    (IsSelfAdjoint.all θ)).exp_re_dotProduct_div_le_re_trace_exp hx0
  rw [hquad, hnorm, Complex.ofReal_re, Complex.ofReal_re] at key
  refine le_of_eq_of_le ?_ key
  congr 1
  field_simp

end Dilation

end Matrix
