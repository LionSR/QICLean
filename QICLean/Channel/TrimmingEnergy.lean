/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OrthogonalProjection
import QICLean.Channel.SchmidtTrimming

/-!
# The energy of a trimmed vector

Let `H = A ⊗ 1 + 1 ⊗ B + K` act on a bipartite space, where `A` acts on the first factor,
`B` on the second, and `0 ≤ K ≤ 1` is the term across the cut, and let `E₀` be a lower bound
for `H`.  Trimming a unit vector `ψ` to its `D` leading Schmidt terms gives
`w₀ = (P ⊗ 1) ψ` and the discarded part `w₁ = ψ - w₀`.  Since the trimming projection `P`
commutes with the left marginal of `ψ`, the one-sided operator `A ⊗ 1 + 1 ⊗ B` has no
cross terms between `w₀` and `w₁`, so the energy of `ψ` splits as the energy of `w₀`, the
energy of `w₁` and a cross term of `K` bounded by `2 ‖w₁‖`.  With `t = ‖w₁‖²` this gives
`⟨w₀, H w₀⟩ ≤ E₀ (1 - t) + δ + 2 √t` when `⟨ψ, H ψ⟩ ≤ E₀ + δ`, and the normalized trimmed
vector has energy at most `E₀ + (δ + 2 √t) / (1 - t)`.  The Eckart–Young theorem bounds
`t ≤ 2η` when some unit vector of Schmidt rank at most `D` has overlap at least `1 - η`
with `ψ`.  Finally the trimmed vector is `(1 ⊗ W)(1 ⊗ Wᴴ) ψ` for an isometry `W` from a
space of dimension at most `D` into the second factor.

**Local fix (energy after trimming):** the proof of Lemma `l:2` of the source
(algo53.tex, lines 351–359) drops three constants.  It writes `1 - δ(1 + 1/ε)` for the
overlap `1 - 2δ(1 + 1/ε)` given by Lemma `claim:overlap`; it writes `‖trim w‖² ≥ 1 - δ'`
where the Eckart–Young theorem gives only `‖trim w‖ ≥ 1 - δ'`; and its lower bound
`⟨w₁, (H - Hᵢ) w₁⟩ ≥ (ε₀ - 1) t` leaves a term `t` that the next display drops, together
with `2 √δ` in place of `2 √δ'` (line 355).  The formalized bound keeps
`⟨w₁, Hᵢ w₁⟩ ≥ 0`, which removes the term `t`, and reads `E₀ + (δ + 2 √t) / (1 - t)` with
`t ≤ 2η` and `η = 2δ(1 + 1/ε)`.  This depends on `1/ε`, so the printed bound
`ε₀ + 6 √δ` does not follow from the printed argument.  See
`docs/paper-gaps/lvv13_trimming_energy.tex`.

## Main results

* `Matrix.IsTrimmingProjection.norm_leftApply_sq_add_norm_sub_sq`: the trimmed vector and
  the discarded part are orthogonal, so their squared norms add up to `‖ψ‖²`.
* `Matrix.IsTrimmingProjection.inner_toEuclideanLin_eq_add`: for `X = A ⊗ 1 + 1 ⊗ B`,
  `⟨ψ, X ψ⟩ = ⟨w₀, X w₀⟩ + ⟨w₁, X w₁⟩`.
* `Matrix.IsTrimmingProjection.re_inner_leftApply_le`: the energy of the trimmed vector.
* `Matrix.IsTrimmingProjection.re_inner_normalized_le`,
  `Matrix.IsTrimmingProjection.re_inner_normalized_le_of_le_half`: the energy of the
  normalized trimmed vector.
* `Matrix.IsTrimmingProjection.norm_sub_leftApply_sq_le`: the trimmed mass is at most `2η`.
* `Matrix.IsTrimmingProjection.re_inner_normalized_le_of_norm_inner`: the corrected
  Lemma `l:2`, with the trimmed mass bounded through an overlap.
* `Matrix.exists_isometry_mul_conjTranspose_eq`: an orthogonal projection is `W Wᴴ` for an
  isometry `W`.
* `Matrix.IsTrimmingProjection.exists_isometry_leftApply_eq_rightApply`: the trimmed vector
  factors through an isometry on the second factor.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of
  1D gapped local Hamiltonians*, arXiv:1307.5143v1, algo53.tex: the Hamiltonian with
  `0 ≤ Hᵢ ≤ 1`, line 283; Lemma `claim:overlap`, lines 307–317; Lemma `l:2`,
  lines 347–359; the isometry `U_v` and the left state, lines 409–417.
-/

open scoped Matrix Kronecker InnerProductSpace ComplexOrder

namespace Matrix

/-! ### Quadratic forms of matrices between `0` and `1` -/

section PositiveForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℂ}

/-- The quadratic form of a positive semidefinite matrix is nonnegative. -/
theorem PosSemidef.re_inner_toEuclideanLin_self_nonneg (hK : K.PosSemidef)
    (x : EuclideanSpace ℂ ι) : 0 ≤ (⟪x, toEuclideanLin K x⟫_ℂ).re :=
  (isPositive_toEuclideanLin_iff.mpr hK).re_inner_nonneg_right x

/-- If `K ≤ 1`, the quadratic form of `K` is at most the squared norm. -/
theorem PosSemidef.re_inner_toEuclideanLin_self_le_of_one_sub (hK : (1 - K).PosSemidef)
    (x : EuclideanSpace ℂ ι) : (⟪x, toEuclideanLin K x⟫_ℂ).re ≤ ‖x‖ ^ 2 := by
  have h := hK.re_inner_toEuclideanLin_self_nonneg x
  rw [map_sub, LinearMap.sub_apply, inner_sub_right, Complex.sub_re] at h
  have h1 : toEuclideanLin (1 : Matrix ι ι ℂ) x = x := by simp [toLpLin_one]
  have h2 : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [h1, h2] at h
  linarith

/-- **Cauchy–Schwarz inequality for a positive semidefinite form**, real part:
`(Re ⟨x, K y⟩)² ≤ ⟨x, K x⟩ ⟨y, K y⟩`. -/
theorem PosSemidef.re_inner_toEuclideanLin_sq_le (hK : K.PosSemidef)
    (x y : EuclideanSpace ℂ ι) :
    (⟪x, toEuclideanLin K y⟫_ℂ).re ^ 2 ≤
      (⟪x, toEuclideanLin K x⟫_ℂ).re * (⟪y, toEuclideanLin K y⟫_ℂ).re := by
  set T := toEuclideanLin K
  have hsym : T.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hK.isHermitian
  have hyx : (⟪y, T x⟫_ℂ).re = (⟪x, T y⟫_ℂ).re := by
    rw [← hsym, ← inner_conj_symm, Complex.conj_re]
  have hq : ∀ s : ℝ, 0 ≤ (⟪y, T y⟫_ℂ).re * (s * s) + (2 * (⟪x, T y⟫_ℂ).re) * s +
      (⟪x, T x⟫_ℂ).re := by
    intro s
    have h0 := hK.re_inner_toEuclideanLin_self_nonneg (x + (s : ℂ) • y)
    rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
      inner_smul_right, inner_smul_left, inner_smul_right] at h0
    simp only [Complex.add_re, Complex.conj_ofReal, Complex.re_ofReal_mul] at h0
    change 0 ≤ (⟪x, T x⟫_ℂ).re + s * (⟪x, T y⟫_ℂ).re +
      (s * (⟪y, T x⟫_ℂ).re + s * (s * (⟪y, T y⟫_ℂ).re)) at h0
    rw [hyx] at h0
    nlinarith
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith

/-- If `0 ≤ K ≤ 1`, then `|Re ⟨x, K y⟩| ≤ ‖x‖ ‖y‖`. -/
theorem PosSemidef.abs_re_inner_toEuclideanLin_le (hK0 : K.PosSemidef)
    (hK1 : (1 - K).PosSemidef) (x y : EuclideanSpace ℂ ι) :
    |(⟪x, toEuclideanLin K y⟫_ℂ).re| ≤ ‖x‖ * ‖y‖ := by
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  refine (hK0.re_inner_toEuclideanLin_sq_le x y).trans ?_
  rw [mul_pow]
  exact mul_le_mul (hK1.re_inner_toEuclideanLin_self_le_of_one_sub x)
    (hK1.re_inner_toEuclideanLin_self_le_of_one_sub y)
    (hK0.re_inner_toEuclideanLin_self_nonneg y) (sq_nonneg _)

/-- If `H ≥ E₀`, that is `H - E₀ 1` is positive semidefinite, then
`E₀ ‖x‖² ≤ Re ⟨x, H x⟩`. -/
theorem PosSemidef.mul_sq_norm_le_re_inner_toEuclideanLin {H : Matrix ι ι ℂ} {E₀ : ℝ}
    (hH : (H - (E₀ : ℂ) • 1).PosSemidef) (x : EuclideanSpace ℂ ι) :
    E₀ * ‖x‖ ^ 2 ≤ (⟪x, toEuclideanLin H x⟫_ℂ).re := by
  have h := hH.re_inner_toEuclideanLin_self_nonneg x
  rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, inner_sub_right,
    inner_smul_right, Complex.sub_re, Complex.re_ofReal_mul] at h
  have h1 : toEuclideanLin (1 : Matrix ι ι ℂ) x = x := by simp [toLpLin_one]
  have h2 : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [h1, h2] at h
  linarith

end PositiveForm

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ### Operators on one factor -/

/-- The operator `A ⊗ 1` acts on a bipartite vector as `leftApply A`. -/
theorem toEuclideanLin_kronecker_one_apply (A : Matrix m m ℂ)
    (ψ : EuclideanSpace ℂ (m × n)) :
    toEuclideanLin (A ⊗ₖ (1 : Matrix n n ℂ)) ψ = leftApply A ψ := by
  ext ⟨i, j⟩
  simp [leftApply, toEuclid, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, one_apply,
    Matrix.mul_apply]

/-- The operator `1 ⊗ B` acts on a bipartite vector as `rightApply B`. -/
theorem toEuclideanLin_one_kronecker_apply (B : Matrix n n ℂ)
    (ψ : EuclideanSpace ℂ (m × n)) :
    toEuclideanLin ((1 : Matrix m m ℂ) ⊗ₖ B) ψ = rightApply B ψ := by
  ext ⟨i, j⟩
  simp [rightApply, toEuclid, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, one_apply,
    Matrix.mul_apply, mul_comm]

omit [Fintype n] [DecidableEq n] in
/-- The discarded part `ψ - (P ⊗ 1) ψ` is `((1 - P) ⊗ 1) ψ`. -/
theorem sub_leftApply (P : Matrix m m ℂ) (ψ : EuclideanSpace ℂ (m × n)) :
    ψ - leftApply P ψ = leftApply (1 - P) ψ := by
  ext ⟨i, j⟩
  simp [leftApply, toEuclid, Matrix.sub_mul]

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- Operators on the first factor compose: `(A ⊗ 1) (X ⊗ 1) ψ = (A X ⊗ 1) ψ`. -/
theorem leftApply_leftApply (A X : Matrix m m ℂ) (ψ : EuclideanSpace ℂ (m × n)) :
    leftApply A (leftApply X ψ) = leftApply (A * X) ψ := by
  unfold leftApply
  rw [Matrix.mul_assoc]
  rfl

omit [DecidableEq m] [DecidableEq n] in
/-- The pairing of `(X ⊗ 1) ψ` with `(Y ⊗ 1) ψ` is `tr(Xᴴ Y ρ)`, where `ρ` is the left
marginal of `ψ`. -/
theorem inner_leftApply_leftApply (X Y : Matrix m m ℂ) (ψ : EuclideanSpace ℂ (m × n)) :
    ⟪leftApply X ψ, leftApply Y ψ⟫_ℂ = (Xᴴ * Y * leftMarginal ψ).trace := by
  rw [inner_eq_trace_schmidtCoeffMatrix, schmidtCoeffMatrix_ofLp_leftApply,
    schmidtCoeffMatrix_ofLp_leftApply, conjTranspose_mul, Matrix.mul_assoc, trace_mul_comm,
    leftMarginal]
  simp only [Matrix.mul_assoc]

omit [DecidableEq m] [DecidableEq n] in
/-- `(X ⊗ 1) ψ` is orthogonal to `(1 ⊗ B) (Y ⊗ 1) ψ` when `Xᴴ Y = 0`. -/
theorem inner_leftApply_rightApply_leftApply_eq_zero {X Y : Matrix m m ℂ}
    (hXY : Xᴴ * Y = 0) (B : Matrix n n ℂ) (ψ : EuclideanSpace ℂ (m × n)) :
    ⟪leftApply X ψ, rightApply B (leftApply Y ψ)⟫_ℂ = 0 := by
  rw [inner_eq_trace_schmidtCoeffMatrix, schmidtCoeffMatrix_ofLp_rightApply,
    schmidtCoeffMatrix_ofLp_leftApply, schmidtCoeffMatrix_ofLp_leftApply, conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Xᴴ, hXY, Matrix.zero_mul, Matrix.mul_zero, trace_zero]

omit [DecidableEq n] in
/-- **Isometric factorization of an orthogonal projection.**  A Hermitian idempotent
`Q : Matrix n n ℂ` is `W Wᴴ` for an isometry `W : Matrix n (Fin k) ℂ`, `Wᴴ W = 1`, with
`k` the rank of `Q`. -/
theorem exists_isometry_mul_conjTranspose_eq {Q : Matrix n n ℂ} (hQh : Q.IsHermitian)
    (hQi : Q * Q = Q) :
    ∃ (k : ℕ) (W : Matrix n (Fin k) ℂ), Wᴴ * W = 1 ∧ W * Wᴴ = Q ∧ k = Q.rank := by
  let e := Fintype.equivFin n
  have hQ' : IsOrthogonalProjection (Q.submatrix e.symm e.symm) :=
    ⟨hQh.submatrix _, by rw [submatrix_mul_equiv, hQi]⟩
  obtain ⟨k, V, hV1, hV2⟩ := hQ'.exists_range_isometry
  have hW1 : (V.submatrix e id)ᴴ * V.submatrix e id = 1 := by
    rw [conjTranspose_submatrix, submatrix_mul_equiv, hV1, submatrix_id_id]
  have hW2 : V.submatrix e id * (V.submatrix e id)ᴴ = Q := by
    rw [conjTranspose_submatrix]
    have h := submatrix_mul_equiv V Vᴴ e (Equiv.refl (Fin k)) e
    simp only [Equiv.coe_refl] at h
    rw [h, hV2, submatrix_submatrix]
    simp
  refine ⟨k, V.submatrix e id, hW1, hW2, ?_⟩
  rw [← hW2, rank_self_mul_conjTranspose, ← rank_conjTranspose_mul_self, hW1, rank_one,
    Fintype.card_fin]

namespace IsTrimmingProjection

variable {ψ : EuclideanSpace ℂ (m × n)} {D : ℕ} {P : Matrix m m ℂ}

omit [DecidableEq n] in
private theorem mul_one_sub (hP : IsTrimmingProjection ψ D P) : P * (1 - P) = 0 := by
  rw [mul_sub, mul_one, hP.mul_self, sub_self]

omit [DecidableEq n] in
private theorem one_sub_mul (hP : IsTrimmingProjection ψ D P) : (1 - P) * P = 0 := by
  rw [sub_mul, one_mul, hP.mul_self, sub_self]

omit [DecidableEq n] in
/-- The trimmed vector is orthogonal to the discarded part. -/
theorem inner_leftApply_sub_eq_zero (hP : IsTrimmingProjection ψ D P) :
    ⟪leftApply P ψ, ψ - leftApply P ψ⟫_ℂ = 0 := by
  rw [sub_leftApply, inner_leftApply_leftApply, hP.isHermitian.eq, hP.mul_one_sub,
    Matrix.zero_mul, trace_zero]

omit [DecidableEq n] in
/-- **Pythagoras for trimming**: `‖trim ψ‖² + ‖ψ - trim ψ‖² = ‖ψ‖²`. -/
theorem norm_leftApply_sq_add_norm_sub_sq (hP : IsTrimmingProjection ψ D P) :
    ‖leftApply P ψ‖ ^ 2 + ‖ψ - leftApply P ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _
    hP.inner_leftApply_sub_eq_zero
  rw [add_sub_cancel] at h
  simp only [sq]
  exact h.symm

omit [DecidableEq n] in
/-- The trimmed vector is orthogonal to `(A ⊗ 1)` applied to the discarded part. -/
theorem inner_leftApply_leftApply_sub_eq_zero (hP : IsTrimmingProjection ψ D P)
    (A : Matrix m m ℂ) :
    ⟪leftApply P ψ, leftApply A (ψ - leftApply P ψ)⟫_ℂ = 0 := by
  have hc : Commute (1 - P) (leftMarginal ψ) :=
    (Commute.one_left _).sub_left hP.commute_leftMarginal
  rw [sub_leftApply, leftApply_leftApply, inner_leftApply_leftApply, hP.isHermitian.eq,
    Matrix.mul_assoc, Matrix.mul_assoc, hc.eq, trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, hP.one_sub_mul, Matrix.mul_zero, Matrix.mul_zero, trace_zero]

omit [DecidableEq n] in
/-- The discarded part is orthogonal to `(A ⊗ 1)` applied to the trimmed vector. -/
theorem inner_sub_leftApply_leftApply_eq_zero (hP : IsTrimmingProjection ψ D P)
    (A : Matrix m m ℂ) :
    ⟪ψ - leftApply P ψ, leftApply A (leftApply P ψ)⟫_ℂ = 0 := by
  have hc : Commute P (leftMarginal ψ) := hP.commute_leftMarginal
  have hQ : (1 - P)ᴴ = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, hP.isHermitian.eq]
  rw [sub_leftApply, leftApply_leftApply, inner_leftApply_leftApply, hQ,
    Matrix.mul_assoc, Matrix.mul_assoc, hc.eq, trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, hP.mul_one_sub, Matrix.mul_zero, Matrix.mul_zero, trace_zero]

omit [DecidableEq n] in
/-- The trimmed vector is orthogonal to `(1 ⊗ B)` applied to the discarded part. -/
theorem inner_leftApply_rightApply_sub_eq_zero (hP : IsTrimmingProjection ψ D P)
    (B : Matrix n n ℂ) :
    ⟪leftApply P ψ, rightApply B (ψ - leftApply P ψ)⟫_ℂ = 0 := by
  rw [sub_leftApply]
  exact inner_leftApply_rightApply_leftApply_eq_zero
    (by rw [hP.isHermitian.eq, hP.mul_one_sub]) B ψ

omit [DecidableEq n] in
/-- The discarded part is orthogonal to `(1 ⊗ B)` applied to the trimmed vector. -/
theorem inner_sub_leftApply_rightApply_eq_zero (hP : IsTrimmingProjection ψ D P)
    (B : Matrix n n ℂ) :
    ⟪ψ - leftApply P ψ, rightApply B (leftApply P ψ)⟫_ℂ = 0 := by
  rw [sub_leftApply]
  exact inner_leftApply_rightApply_leftApply_eq_zero
    (by rw [conjTranspose_sub, conjTranspose_one, hP.isHermitian.eq, hP.one_sub_mul]) B ψ

/-- **No cross terms for a one-sided operator.** For `X = A ⊗ 1 + 1 ⊗ B`, the expectation
of `X` in `ψ` splits along `ψ = w₀ + w₁`, `w₀ = trim ψ`:
`⟨ψ, X ψ⟩ = ⟨w₀, X w₀⟩ + ⟨w₁, X w₁⟩`. -/
theorem inner_toEuclideanLin_eq_add (hP : IsTrimmingProjection ψ D P) (A : Matrix m m ℂ)
    (B : Matrix n n ℂ) :
    ⟪ψ, toEuclideanLin (A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B) ψ⟫_ℂ =
      ⟪leftApply P ψ, toEuclideanLin (A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B)
          (leftApply P ψ)⟫_ℂ +
        ⟪ψ - leftApply P ψ, toEuclideanLin (A ⊗ₖ (1 : Matrix n n ℂ) +
          (1 : Matrix m m ℂ) ⊗ₖ B) (ψ - leftApply P ψ)⟫_ℂ := by
  set w₀ := leftApply P ψ
  set w₁ := ψ - leftApply P ψ
  have hψ : ψ = w₀ + w₁ := (add_sub_cancel _ _).symm
  have hX : ∀ x, toEuclideanLin (A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B) x =
      leftApply A x + rightApply B x := fun x => by
    rw [map_add, LinearMap.add_apply, toEuclideanLin_kronecker_one_apply,
      toEuclideanLin_one_kronecker_apply]
  have h01 : ⟪w₀, toEuclideanLin (A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B) w₁⟫_ℂ
      = 0 := by
    rw [hX, inner_add_right, hP.inner_leftApply_leftApply_sub_eq_zero,
      hP.inner_leftApply_rightApply_sub_eq_zero, add_zero]
  have h10 : ⟪w₁, toEuclideanLin (A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B) w₀⟫_ℂ
      = 0 := by
    rw [hX, inner_add_right, hP.inner_sub_leftApply_leftApply_eq_zero,
      hP.inner_sub_leftApply_rightApply_eq_zero, add_zero]
  conv_lhs => rw [hψ]
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, h01, h10, add_zero,
    zero_add]

/-! ### The energy of the trimmed vector -/

/-- **The energy of the trimmed vector** (corrected core of Lemma `l:2` of
arXiv:1307.5143v1, algo53.tex, lines 347–359).  Let `H = A ⊗ 1 + 1 ⊗ B + K` with
`H ≥ E₀` and `0 ≤ K ≤ 1`, let `ψ` be a unit vector with `Re ⟨ψ, H ψ⟩ ≤ E₀ + δ`, and write
`w₀ = trim ψ`, `w₁ = ψ - w₀`.  Then `Re ⟨w₀, H w₀⟩ ≤ E₀ (1 - ‖w₁‖²) + δ + 2 ‖w₁‖`. -/
theorem re_inner_leftApply_le (hP : IsTrimmingProjection ψ D P) {A : Matrix m m ℂ}
    {B : Matrix n n ℂ} {K H : Matrix (m × n) (m × n) ℂ}
    (hHK : H = A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B + K) {E₀ δ : ℝ}
    (hH : (H - (E₀ : ℂ) • 1).PosSemidef) (hK0 : K.PosSemidef) (hK1 : (1 - K).PosSemidef)
    (hψ : ‖ψ‖ = 1) (hE : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re ≤ E₀ + δ) :
    (⟪leftApply P ψ, toEuclideanLin H (leftApply P ψ)⟫_ℂ).re ≤
      E₀ * (1 - ‖ψ - leftApply P ψ‖ ^ 2) + δ + 2 * ‖ψ - leftApply P ψ‖ := by
  have hX := hP.inner_toEuclideanLin_eq_add A B
  have hcs := hK0.abs_re_inner_toEuclideanLin_le hK1 (leftApply P ψ) (ψ - leftApply P ψ)
  have hn0 : ‖leftApply P ψ‖ ≤ 1 := hψ ▸ hP.norm_leftApply_le
  have hlow := hH.mul_sq_norm_le_re_inner_toEuclideanLin (ψ - leftApply P ψ)
  have hKsym : (toEuclideanLin K).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr hK0.isHermitian
  set w₀ := leftApply P ψ with hw₀
  set w₁ := ψ - leftApply P ψ with hw₁
  set X := A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B with hXdef
  have hψ01 : ψ = w₀ + w₁ := (add_sub_cancel _ _).symm
  have hTH : ∀ x, (⟪x, toEuclideanLin H x⟫_ℂ).re =
      (⟪x, toEuclideanLin X x⟫_ℂ).re + (⟪x, toEuclideanLin K x⟫_ℂ).re := fun x => by
    rw [hHK, map_add, LinearMap.add_apply, inner_add_right, Complex.add_re]
  have hK10 : (⟪w₁, toEuclideanLin K w₀⟫_ℂ).re = (⟪w₀, toEuclideanLin K w₁⟫_ℂ).re := by
    rw [← hKsym, ← inner_conj_symm, Complex.conj_re]
  have hKexp : (⟪ψ, toEuclideanLin K ψ⟫_ℂ).re = (⟪w₀, toEuclideanLin K w₀⟫_ℂ).re +
      2 * (⟪w₀, toEuclideanLin K w₁⟫_ℂ).re + (⟪w₁, toEuclideanLin K w₁⟫_ℂ).re := by
    conv_lhs => rw [hψ01]
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, Complex.add_re,
      Complex.add_re, Complex.add_re, hK10]
    ring
  have hXre : (⟪ψ, toEuclideanLin X ψ⟫_ℂ).re =
      (⟪w₀, toEuclideanLin X w₀⟫_ℂ).re + (⟪w₁, toEuclideanLin X w₁⟫_ℂ).re := by
    rw [hX, Complex.add_re]
  have hc : -(‖w₀‖ * ‖w₁‖) ≤ (⟪w₀, toEuclideanLin K w₁⟫_ℂ).re := (abs_le.mp hcs).1
  have hc' : ‖w₀‖ * ‖w₁‖ ≤ ‖w₁‖ := mul_le_of_le_one_left (norm_nonneg _) hn0
  have h0 := hTH w₀
  have h1 := hTH w₁
  have hψH := hTH ψ
  nlinarith

/-- **The energy of the normalized trimmed vector** (corrected Lemma `l:2` of
arXiv:1307.5143v1, algo53.tex, lines 347–359).  Under the hypotheses of
`Matrix.IsTrimmingProjection.re_inner_leftApply_le`, if `t = ‖ψ - trim ψ‖² < 1`, the
normalized trimmed vector `v = trim ψ / ‖trim ψ‖` satisfies
`Re ⟨v, H v⟩ ≤ E₀ + (δ + 2 √t) / (1 - t)`. -/
theorem re_inner_normalized_le (hP : IsTrimmingProjection ψ D P) {A : Matrix m m ℂ}
    {B : Matrix n n ℂ} {K H : Matrix (m × n) (m × n) ℂ}
    (hHK : H = A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B + K) {E₀ δ : ℝ}
    (hH : (H - (E₀ : ℂ) • 1).PosSemidef) (hK0 : K.PosSemidef) (hK1 : (1 - K).PosSemidef)
    (hψ : ‖ψ‖ = 1) (hE : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re ≤ E₀ + δ)
    (ht : ‖ψ - leftApply P ψ‖ ^ 2 < 1) :
    (⟪‖leftApply P ψ‖⁻¹ • leftApply P ψ,
        toEuclideanLin H (‖leftApply P ψ‖⁻¹ • leftApply P ψ)⟫_ℂ).re ≤
      E₀ + (δ + 2 * ‖ψ - leftApply P ψ‖) / (1 - ‖ψ - leftApply P ψ‖ ^ 2) := by
  have hE₀ := hP.re_inner_leftApply_le hHK hH hK0 hK1 hψ hE
  have hpyth := hP.norm_leftApply_sq_add_norm_sub_sq
  rw [hψ, one_pow] at hpyth
  set s := ‖ψ - leftApply P ψ‖
  set r := ‖leftApply P ψ‖
  set e := (⟪leftApply P ψ, toEuclideanLin H (leftApply P ψ)⟫_ℂ).re
  have hpos : 0 < 1 - s ^ 2 := by linarith
  have hr2 : r ^ 2 = 1 - s ^ 2 := by linarith
  have hscale : (⟪r⁻¹ • leftApply P ψ, toEuclideanLin H (r⁻¹ • leftApply P ψ)⟫_ℂ).re =
      (r ^ 2)⁻¹ * e := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, inner_smul_left, inner_smul_right]
    simp [e, Complex.mul_re, sq, mul_assoc]
  rw [hscale, hr2, inv_mul_eq_div, div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne']
  linarith

/-- **The energy of the normalized trimmed vector when little is trimmed.**  Under the
hypotheses of `Matrix.IsTrimmingProjection.re_inner_leftApply_le`, if
`t = ‖ψ - trim ψ‖² ≤ 1/2`, the normalized trimmed vector `v` satisfies
`Re ⟨v, H v⟩ ≤ E₀ + 2 (δ + 2 √t)`. -/
theorem re_inner_normalized_le_of_le_half (hP : IsTrimmingProjection ψ D P)
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} {K H : Matrix (m × n) (m × n) ℂ}
    (hHK : H = A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B + K) {E₀ δ : ℝ}
    (hH : (H - (E₀ : ℂ) • 1).PosSemidef) (hK0 : K.PosSemidef) (hK1 : (1 - K).PosSemidef)
    (hψ : ‖ψ‖ = 1) (hE : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re ≤ E₀ + δ)
    (ht : ‖ψ - leftApply P ψ‖ ^ 2 ≤ 1 / 2) :
    (⟪‖leftApply P ψ‖⁻¹ • leftApply P ψ,
        toEuclideanLin H (‖leftApply P ψ‖⁻¹ • leftApply P ψ)⟫_ℂ).re ≤
      E₀ + 2 * (δ + 2 * ‖ψ - leftApply P ψ‖) := by
  have h := hP.re_inner_normalized_le hHK hH hK0 hK1 hψ hE (by linarith)
  have hδ : 0 ≤ δ := by
    have := hH.mul_sq_norm_le_re_inner_toEuclideanLin ψ
    rw [hψ, one_pow, mul_one] at this
    linarith
  set s := ‖ψ - leftApply P ψ‖
  have hs : 0 ≤ s := norm_nonneg _
  have hpos : 0 < 1 - s ^ 2 := by linarith
  have hR : (δ + 2 * s) / (1 - s ^ 2) ≤ 2 * (δ + 2 * s) := by
    rw [div_le_iff₀ hpos]
    nlinarith
  linarith

/-! ### The trimmed mass -/

omit [DecidableEq n] in
/-- **The trimmed mass from an overlap** (the Eckart–Young step of the proof of Lemma `l:2`
of arXiv:1307.5143v1, algo53.tex, lines 350–351, with the square restored).  If `ψ` is a
unit vector, `u` a unit vector of Schmidt rank at most `D`, and `1 - η ≤ |⟨u, ψ⟩|`, then the
discarded part of `ψ` has squared norm at most `2η`. -/
theorem norm_sub_leftApply_sq_le (hP : IsTrimmingProjection ψ D P) (hψ : ‖ψ‖ = 1)
    {u : EuclideanSpace ℂ (m × n)} (hu : ‖u‖ = 1) (huD : HasSchmidtRankLE D (WithLp.ofLp u))
    {η : ℝ} (hη : 1 - η ≤ ‖⟪u, ψ⟫_ℂ‖) :
    ‖ψ - leftApply P ψ‖ ^ 2 ≤ 2 * η := by
  have hEY := hP.norm_inner_le_re_inner_normalized u hu huD
  rw [hP.inner_normalized_eq_sqrt, Complex.ofReal_re, ← hP.norm_leftApply] at hEY
  have hpyth := hP.norm_leftApply_sq_add_norm_sub_sq
  rw [hψ, one_pow] at hpyth
  have h1 : 1 - η ≤ ‖leftApply P ψ‖ := hη.trans hEY
  rcases le_or_gt 0 (1 - η) with h | h
  · have h2 : (1 - η) ^ 2 ≤ ‖leftApply P ψ‖ ^ 2 := pow_le_pow_left₀ h h1 2
    nlinarith
  · nlinarith [sq_nonneg ‖leftApply P ψ‖]

/-- **The corrected Lemma `l:2`** of arXiv:1307.5143v1, algo53.tex, lines 347–359, in
terms of an overlap.  Under the hypotheses of
`Matrix.IsTrimmingProjection.re_inner_leftApply_le`, if a unit vector `u` of Schmidt rank at
most `D` has `|⟨u, ψ⟩| ≥ 1 - η` with `2η < 1`, the normalized trimmed vector `v` satisfies
`Re ⟨v, H v⟩ ≤ E₀ + (δ + 2 √(2η)) / (1 - 2η)`. -/
theorem re_inner_normalized_le_of_norm_inner (hP : IsTrimmingProjection ψ D P)
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} {K H : Matrix (m × n) (m × n) ℂ}
    (hHK : H = A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B + K) {E₀ δ : ℝ}
    (hH : (H - (E₀ : ℂ) • 1).PosSemidef) (hK0 : K.PosSemidef) (hK1 : (1 - K).PosSemidef)
    (hψ : ‖ψ‖ = 1) (hE : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re ≤ E₀ + δ)
    {u : EuclideanSpace ℂ (m × n)} (hu : ‖u‖ = 1) (huD : HasSchmidtRankLE D (WithLp.ofLp u))
    {η : ℝ} (hη : 1 - η ≤ ‖⟪u, ψ⟫_ℂ‖) (hη2 : 2 * η < 1) :
    (⟪‖leftApply P ψ‖⁻¹ • leftApply P ψ,
        toEuclideanLin H (‖leftApply P ψ‖⁻¹ • leftApply P ψ)⟫_ℂ).re ≤
      E₀ + (δ + 2 * √(2 * η)) / (1 - 2 * η) := by
  have ht := hP.norm_sub_leftApply_sq_le hψ hu huD hη
  have h := hP.re_inner_normalized_le hHK hH hK0 hK1 hψ hE (by linarith)
  have hδ : 0 ≤ δ := by
    have := hH.mul_sq_norm_le_re_inner_toEuclideanLin ψ
    rw [hψ, one_pow, mul_one] at this
    linarith
  set s := ‖ψ - leftApply P ψ‖
  have hs : 0 ≤ s := norm_nonneg _
  have hs' : s ≤ √(2 * η) := Real.le_sqrt_of_sq_le ht
  have hR : (δ + 2 * s) / (1 - s ^ 2) ≤ (δ + 2 * √(2 * η)) / (1 - 2 * η) :=
    div_le_div₀ (by positivity) (by linarith) (by linarith) (by linarith)
  linarith

/-! ### The trimmed vector through an isometry on the second factor -/

omit [DecidableEq n] in
/-- The trimmed vector factors through an isometry `W : ℂ^k → ℂ^n` on the second factor,
with `k ≤ D`: `trim ψ = (1 ⊗ W) x` for `x = (1 ⊗ Wᴴ) ψ`.  The isometry is the map `U_v` of
arXiv:1307.5143v1, algo53.tex, lines 409–417, sending the `j`-th basis vector to the `j`-th
kept right Schmidt vector, and `x` is the left state of the trimmed vector. -/
theorem exists_isometry_leftApply_eq_rightApply (hP : IsTrimmingProjection ψ D P) :
    ∃ (k : ℕ) (W : Matrix n (Fin k) ℂ), Wᴴ * W = 1 ∧ k ≤ D ∧ k ≤ Fintype.card n ∧
      leftApply P ψ = rightApply W (rightApply Wᴴ ψ) := by
  obtain ⟨Q, hQh, hQi, hQr, hPQ⟩ := hP.exists_leftApply_eq_rightApply
  obtain ⟨k, W, h1, h2, hk⟩ := exists_isometry_mul_conjTranspose_eq hQh hQi
  refine ⟨k, W, h1, hk ▸ hQr, hk ▸ Q.rank_le_card_width, ?_⟩
  rw [hPQ]
  change toEuclid (schmidtCoeffMatrix (WithLp.ofLp ψ) * Qᵀ) =
    toEuclid (schmidtCoeffMatrix (WithLp.ofLp (rightApply Wᴴ ψ)) * Wᵀ)
  rw [schmidtCoeffMatrix_ofLp_rightApply, Matrix.mul_assoc, ← transpose_mul, h2]

end IsTrimmingProjection

end Matrix
