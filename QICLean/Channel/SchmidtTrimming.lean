/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.MaximalOverlap

/-!
# Trimming a bipartite vector to its leading Schmidt terms

For a bipartite vector `ψ` with coefficient matrix `C` and left marginal `ρ = C Cᴴ`,
trimming `ψ` to `D` Schmidt terms keeps the Schmidt terms with the `D` largest
coefficients.  In operator form the trimmed vector is `(P ⊗ 1) ψ`, whose coefficient
matrix is `P C`, where `P` is an orthogonal projection of rank at most `D` capturing
the `D` largest eigenvalues of `ρ`, that is `tr(P ρ)` equals the Ky Fan `D`-norm of `ρ`.
When a Schmidt coefficient is degenerate the projection is not unique; the predicate
below admits every such choice, so the results hold whichever eigenvectors of a
repeated eigenvalue are kept.

The first result is the Eckart–Young theorem in the form used by Landau, Vazirani and
Vidick: the normalized trimmed vector has the largest overlap with `ψ` among unit vectors
of Schmidt rank at most `D`.  The second result bounds the error of trimming a vector
`u` to `k` terms when it is paired with a vector `v` of Schmidt rank at most `D`:
`|⟨u - trim u, v⟩| ≤ ‖u‖ ‖v‖ √(D / (k + 1))`.  The proof places the support projection
of the paired part of `v` next to the trimming projection, which gives a projection of
rank at most `k + D`, and compares with Ky Fan's maximum principle: the extra mass is at
most `D` times the `(k + 1)`-st eigenvalue of `ρ`, which is at most `‖u‖² / (k + 1)`.

**Local fix (trimming radius):** Lemma `l:trim1` of the source (algo53.tex,
lines 531–537) asserts the bound `|⟨trim_{D/ε} u, v⟩| ≥ |⟨u, v⟩| - ε` for unit `u, v`
with `v` of Schmidt rank `D`, and this is false.  Take `u` with `D/ε + D` equal Schmidt
coefficients and `v` the normalized sum of the `D` removed Schmidt terms: the overlap is
`0` after trimming and `(ε / (1 + ε))^{1/2}` before, which exceeds `ε` when
`ε < (√5 - 1) / 2`.  The formalized bound has error `√(D / (k + 1))`, so trimming radius
`D / ε²` gives error `ε`.  See `docs/paper-gaps/lvv13_trimming_radius.tex`.

## Main definitions

* `Matrix.leftMarginal`: the left marginal `C Cᴴ` of a bipartite vector.
* `Matrix.leftApply`: the vector `(P ⊗ 1) ψ`, with coefficient matrix `P C`.
* `Matrix.rightApply`: the vector `(1 ⊗ Q) ψ`, with coefficient matrix `C Qᵀ`, for a possibly
  rectangular `Q`.
* `Matrix.IsTrimmingProjection`: an orthogonal projection of rank at most `D` that
  captures the Ky Fan `D`-norm of the left marginal.

## Main results

* `Matrix.exists_isTrimmingProjection`: a trimming projection exists for every `D`.
* `Matrix.schmidtRank_leftApply_le`, `Matrix.schmidtRank_rightApply_le`: an operator on one
  factor does not increase the Schmidt rank.
* `Matrix.IsTrimmingProjection.inner_leftApply_self`,
  `Matrix.IsTrimmingProjection.norm_leftApply_sq`: the trimmed vector has overlap and
  squared norm equal to the Ky Fan `D`-norm of the left marginal.
* `Matrix.IsTrimmingProjection.hasSchmidtRankLE_leftApply`: the trimmed vector has
  Schmidt rank at most `D`.
* `Matrix.IsTrimmingProjection.norm_leftApply_le`: the trimmed vector is no longer than
  the original.
* `Matrix.IsHermitian.commute_of_forall_trace_mul_re_le` and
  `Matrix.IsTrimmingProjection.commute_leftMarginal`: a projection maximizing its trace
  against a Hermitian matrix among projections of the same trace commutes with it; in
  particular a trimming projection commutes with the left marginal.
* `Matrix.IsTrimmingProjection.exists_mul_eq_mul_transpose` and
  `Matrix.IsTrimmingProjection.exists_leftApply_eq_rightApply`: the trimmed vector is also
  `(1 ⊗ Q) ψ` for an orthogonal projection `Q` of rank at most `D` on the second factor.
* `Matrix.IsTrimmingProjection.norm_inner_le_re_inner_normalized`: the Eckart–Young
  theorem, Lemma `lem:eckart` of the source.
* `Matrix.IsTrimmingProjection.norm_inner_sub_leftApply_le` and
  `Matrix.IsTrimmingProjection.norm_inner_sub_le_norm_inner_leftApply`: the corrected
  form of Lemma `l:trim1` of the source.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of
  1D gapped local Hamiltonians*, arXiv:1307.5143v1, algo53.tex: trimming, lines 330–333;
  Lemma `lem:eckart`, lines 335–339; Lemma `l:trim1`, lines 531–542; trimming as a
  projection on the second factor, lines 544–553.
-/

open scoped Matrix ComplexOrder

namespace Matrix

/-! ### Ky Fan bounds for projections of arbitrary rank -/

namespace PosSemidef

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The descending eigenvalues of a positive semidefinite matrix are antitone, including
past the dimension, where they vanish. -/
theorem descEigenvalue_antitone (hA : A.PosSemidef) :
    Antitone hA.isHermitian.descEigenvalue := by
  intro i j hij
  by_cases hj : j < Fintype.card n
  · rw [IsHermitian.descEigenvalue, IsHermitian.descEigenvalue,
      dite_eq_left (lt_of_le_of_lt hij hj), dite_eq_left hj]
    exact hA.isHermitian.eigenvalues₀_antitone (by exact_mod_cast hij)
  · rw [IsHermitian.descEigenvalue, dite_eq_right hj]
    exact hA.descEigenvalue_nonneg i

/-- The Ky Fan norm of a positive semidefinite matrix is at most its real trace. -/
theorem kyFanNorm_le_trace_re (hA : A.PosSemidef) (k : ℕ) :
    hA.isHermitian.kyFanNorm k ≤ (A.trace).re := by
  rw [← hA.isHermitian.kyFanNorm_card_eq_trace_re]
  by_cases hk : k ≤ Fintype.card n
  · exact hA.kyFanNorm_mono hk
  · have hle : Fintype.card n ≤ k := (Nat.lt_of_not_le hk).le
    rw [IsHermitian.kyFanNorm, IsHermitian.kyFanNorm,
      ← Finset.sum_range_add_sum_Ico _ hle, add_le_iff_nonpos_right]
    refine (Finset.sum_eq_zero fun i hi => ?_).le
    rw [IsHermitian.descEigenvalue, dite_eq_right (by simp at hi; omega)]

/-- The Ky Fan norm grows by at most `j` times the `(k + 1)`-st eigenvalue from `k` to
`k + j`. -/
theorem kyFanNorm_add_le (hA : A.PosSemidef) (k j : ℕ) :
    hA.isHermitian.kyFanNorm (k + j) ≤
      hA.isHermitian.kyFanNorm k + j * hA.isHermitian.descEigenvalue k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, hA.isHermitian.kyFanNorm_succ]
    have := hA.descEigenvalue_antitone (Nat.le_add_right k j)
    push_cast
    linarith

/-- The `(k + 1)`-st eigenvalue of a positive semidefinite matrix is at most its real
trace divided by `k + 1`. -/
theorem succ_mul_descEigenvalue_le_trace_re (hA : A.PosSemidef) (k : ℕ) :
    ((k : ℝ) + 1) * hA.isHermitian.descEigenvalue k ≤ (A.trace).re := by
  refine le_trans ?_ (hA.kyFanNorm_le_trace_re (k + 1))
  have h : ∑ _i ∈ Finset.range (k + 1), hA.isHermitian.descEigenvalue k ≤
      hA.isHermitian.kyFanNorm (k + 1) :=
    Finset.sum_le_sum fun i hi =>
      hA.descEigenvalue_antitone (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  simpa [Finset.sum_const, nsmul_eq_mul] using h

omit [DecidableEq n] in
/-- An orthogonal projection pairs with a positive semidefinite matrix to at most its
real trace. -/
theorem trace_mul_re_le_trace_re_of_isHermitian_idem (hA : A.PosSemidef)
    {R : Matrix n n ℂ} (hRh : R.IsHermitian) (hRi : R * R = R) :
    (R * A).trace.re ≤ (A.trace).re := by
  classical
  have hQh : (1 - R)ᴴ = 1 - R := by
    rw [conjTranspose_sub, conjTranspose_one, hRh.eq]
  have hQi : (1 - R) * (1 - R) = 1 - R := by
    simp [sub_mul, mul_sub, hRi]
  have hpsd : ((1 - R)ᴴ * A * (1 - R)).PosSemidef := hA.conjTranspose_mul_mul_same _
  have htr : (A.trace).re - (R * A).trace.re = ((1 - R)ᴴ * A * (1 - R)).trace.re := by
    rw [hQh, trace_mul_comm ((1 - R) * A) (1 - R), ← Matrix.mul_assoc, hQi, sub_mul,
      one_mul, trace_sub, Complex.sub_re]
  have := (Complex.nonneg_iff.mp hpsd.trace_nonneg).1
  linarith

/-- **Ky Fan's maximum principle for projections of bounded rank.** For a positive
semidefinite matrix `A` and an orthogonal projection `R` of rank at most `k`, the real
trace `tr(R A)` is at most the Ky Fan `k`-norm of `A`.  Unlike
`Matrix.PosSemidef.trace_mul_re_le_kyFanNorm_of_rank_le`, `k` may reach or exceed the
dimension. -/
theorem trace_mul_re_le_kyFanNorm_of_isHermitian_idem (hA : A.PosSemidef)
    {R : Matrix n n ℂ} (hRh : R.IsHermitian) (hRi : R * R = R) {k : ℕ}
    (hRk : R.rank ≤ k) :
    (R * A).trace.re ≤ hA.isHermitian.kyFanNorm k := by
  by_cases hk : k < Fintype.card n
  · exact hA.trace_mul_re_le_kyFanNorm_of_rank_le hRk hk hRh hRi
      (hRh.rank_eq_trace_re_of_idem hRi).symm
  · calc (R * A).trace.re ≤ (A.trace).re :=
          hA.trace_mul_re_le_trace_re_of_isHermitian_idem hRh hRi
      _ = hA.isHermitian.kyFanNorm (Fintype.card n) :=
          (hA.isHermitian.kyFanNorm_card_eq_trace_re).symm
      _ ≤ hA.isHermitian.kyFanNorm k := hA.kyFanNorm_mono (Nat.le_of_not_lt hk)

end PosSemidef

/-! ### Projections maximizing a trace commute with the matrix -/

namespace IsHermitian

variable {n : Type*} [Fintype n] {ρ P : Matrix n n ℂ}

/-- **A trace-maximizing projection commutes with the matrix.**  Let `ρ` be Hermitian and
`P` an orthogonal projection such that no orthogonal projection `R` of the same trace
has a larger real trace `tr(R ρ)`.  Then `P` commutes with `ρ`.

If `P ρ (1 - P)` were nonzero, it would map some vector to a nonzero `y`; with
`z = (1 - P) v` and `y = P ρ z` one has `⟨y, ρ z⟩ = ‖y‖²`.  Replacing the line through
`y` in the range of `P` by the line through `y + t z` gives a projection of the same
trace, whose trace against `ρ` exceeds that of `P` by a positive multiple of
`2 t ‖y‖⁴ + O(t²)`, which is positive for small `t > 0`. -/
theorem commute_of_forall_trace_mul_re_le (hρ : ρ.IsHermitian) (hPh : P.IsHermitian)
    (hPi : P * P = P)
    (hmax : ∀ R : Matrix n n ℂ, R.IsHermitian → R * R = R → R.trace = P.trace →
      (R * ρ).trace.re ≤ (P * ρ).trace.re) :
    Commute P ρ := by
  classical
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPi, sub_self]
  have hX : P * ρ * (1 - P) = 0 := by
    by_contra hX
    obtain ⟨v, hv⟩ : ∃ v, (P * ρ * (1 - P)) *ᵥ v ≠ 0 := by
      by_contra h
      simp only [ne_eq, not_exists, not_not] at h
      exact hX (ext_of_mulVec_single fun i => by rw [h, zero_mulVec])
    set z := (1 - P) *ᵥ v with hz
    set y := P *ᵥ (ρ *ᵥ z) with hy
    have hy0 : y ≠ 0 := by rwa [hy, hz, mulVec_mulVec, mulVec_mulVec]
    -- Bookkeeping for `y ∈ range P` and `z ∈ ker P`.
    have hPy : P *ᵥ y = y := by rw [hy, mulVec_mulVec, hPi]
    have hPz : P *ᵥ z = 0 := by rw [hz, mulVec_mulVec, hPQ, zero_mulVec]
    have hyP : star y ᵥ* P = star y := by rw [← hPh.eq, ← star_mulVec, hPy]
    have hzP : star z ᵥ* P = 0 := by rw [← hPh.eq, ← star_mulVec, hPz, star_zero]
    have hyz : star y ⬝ᵥ z = 0 := by rw [← hyP, ← dotProduct_mulVec, hPz, dotProduct_zero]
    have hzy : star z ⬝ᵥ y = 0 := by rw [← hPy, dotProduct_mulVec, hzP, zero_dotProduct]
    have hyρz : star y ⬝ᵥ ρ *ᵥ z = star y ⬝ᵥ y := by
      conv_lhs => rw [← hyP, ← dotProduct_mulVec]
    -- The scalars of the computation are real.
    have hreal : ∀ x : ℂ, x.im = 0 → x = (x.re : ℂ) := fun x hx => Complex.ext (by simp)
      (by simp [hx])
    set a := (star y ⬝ᵥ y).re with ha_def
    set b := (star z ⬝ᵥ z).re with hb_def
    set c := (star y ⬝ᵥ ρ *ᵥ y).re with hc_def
    set e := (star z ⬝ᵥ ρ *ᵥ z).re with he_def
    have ha : star y ⬝ᵥ y = a :=
      hreal _ (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg y)).2.symm
    have hb : star z ⬝ᵥ z = b :=
      hreal _ (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg z)).2.symm
    have hc : star y ⬝ᵥ ρ *ᵥ y = c := hreal _ (hρ.im_star_dotProduct_mulVec_self y)
    have he : star z ⬝ᵥ ρ *ᵥ z = e := hreal _ (hρ.im_star_dotProduct_mulVec_self z)
    have hzρy : star z ⬝ᵥ ρ *ᵥ y = a := by
      rw [← hρ.star_dotProduct_mulVec_comm y z, hyρz, ha, Complex.star_def, Complex.conj_ofReal]
    have ha0 : 0 < a := by
      have h := (dotProduct_star_self_pos_iff (v := y)).mpr hy0
      rw [ha] at h
      exact_mod_cast h
    have hb0 : 0 ≤ b := by
      have h := dotProduct_star_self_nonneg z
      rw [hb] at h
      exact_mod_cast h
    -- The rotation parameter.
    set t : ℝ := a ^ 2 / (|a * e - c * b| + 1) with ht
    have ht0 : 0 < t := by positivity
    set w := y + (t : ℂ) • z with hw
    set s : ℝ := a + t ^ 2 * b with hs
    have hs0 : 0 < s := by positivity
    have hstarw : star w = star y + (t : ℂ) • star z := by
      rw [hw, star_add, star_smul, Complex.star_def, Complex.conj_ofReal]
    have hPw : P *ᵥ w = y := by rw [hw, mulVec_add, mulVec_smul, hPy, hPz, smul_zero, add_zero]
    have hwP : star w ᵥ* P = star y := by
      rw [hstarw, add_vecMul, smul_vecMul, hyP, hzP, smul_zero, add_zero]
    have hyw : star y ⬝ᵥ w = a := by
      rw [hw, dotProduct_add, dotProduct_smul, hyz, smul_zero, add_zero, ha]
    have hwy : star w ⬝ᵥ y = a := by
      rw [hstarw, add_dotProduct, smul_dotProduct, hzy, smul_zero, add_zero, ha]
    have hww : star w ⬝ᵥ w = s := by
      rw [hstarw, hw]
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, hyz, hzy, ha,
        hb, smul_eq_mul, hs]
      push_cast
      ring
    have hwρw : star w ⬝ᵥ ρ *ᵥ w = c + 2 * t * a + t ^ 2 * e := by
      rw [hstarw, hw]
      simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, hc, hyρz, ha, hzρy, he, smul_eq_mul]
      ring
    -- The rotated projection.
    set R : Matrix n n ℂ := P - (a : ℂ)⁻¹ • vecMulVec y (star y) +
      (s : ℂ)⁻¹ • vecMulVec w (star w) with hR
    have hRh : R.IsHermitian := by
      rw [IsHermitian, hR, conjTranspose_add, conjTranspose_sub, conjTranspose_smul,
        conjTranspose_smul, conjTranspose_vecMulVec, conjTranspose_vecMulVec, star_star,
        star_star, hPh.eq]
      simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    have hRi : R * R = R := by
      rw [hR]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
        Matrix.mul_smul]
      simp only [vecMulVec_mul_vecMulVec, hyw, hwy, ha, hww, vecMulVec_smul]
      simp only [hPi, mul_vecMulVec, vecMulVec_mul, hPy, hPw, hyP, hwP]
      match_scalars <;> field_simp <;> ring
    have hRt : R.trace = P.trace := by
      rw [hR, trace_add, trace_sub, trace_smul, trace_smul, trace_vecMulVec, trace_vecMulVec,
        dotProduct_comm y, dotProduct_comm w, ha, hww, smul_eq_mul, smul_eq_mul,
        inv_mul_cancel₀ ha', inv_mul_cancel₀ hs', sub_add_cancel]
    have hRρ : (R * ρ).trace = (P * ρ).trace - (a : ℂ)⁻¹ * c +
        (s : ℂ)⁻¹ * (c + 2 * t * a + t ^ 2 * e) := by
      rw [hR, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, vecMulVec_mul,
        vecMulVec_mul, trace_add, trace_sub, trace_smul, trace_smul, trace_vecMulVec,
        trace_vecMulVec, dotProduct_comm y, dotProduct_comm w, ← dotProduct_mulVec,
        ← dotProduct_mulVec, hc, hwρw, smul_eq_mul, smul_eq_mul]
    have hle := hmax R hRh hRi hRt
    rw [hRρ] at hle
    have hle' : -c / a + (c + 2 * t * a + t ^ 2 * e) / s ≤ 0 := by
      have h : ((P * ρ).trace - (a : ℂ)⁻¹ * c + (s : ℂ)⁻¹ * (c + 2 * t * a + t ^ 2 * e)).re =
          (P * ρ).trace.re + (-c / a + (c + 2 * t * a + t ^ 2 * e) / s) := by
        rw [show (P * ρ).trace - (a : ℂ)⁻¹ * c + (s : ℂ)⁻¹ * (c + 2 * t * a + t ^ 2 * e) =
          (P * ρ).trace + ((-c / a + (c + 2 * t * a + t ^ 2 * e) / s : ℝ) : ℂ) by
            push_cast; ring]
        rw [Complex.add_re, Complex.ofReal_re]
      rw [h] at hle
      linarith
    -- Clearing denominators: `2 t a² + t² (a e - c b) ≤ 0`.
    have hkey : 2 * a ^ 2 + t * (a * e - c * b) ≤ 0 := by
      have hexp : -c / a + (c + 2 * t * a + t ^ 2 * e) / s =
          t * (2 * a ^ 2 + t * (a * e - c * b)) / (a * s) := by
        rw [hs]
        field_simp
        ring
      rw [hexp, div_nonpos_iff] at hle'
      rcases hle' with ⟨_, h⟩ | ⟨h, _⟩
      · nlinarith [mul_pos ha0 hs0]
      · by_contra hneg
        rw [not_le] at hneg
        nlinarith [mul_pos ht0 hneg]
    have hsmall : t * |a * e - c * b| < a ^ 2 := by
      rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg (a * e - c * b), sq_pos_of_pos ha0]
    have hlow : -(t * |a * e - c * b|) ≤ t * (a * e - c * b) := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_abs_le _) ht0.le
    nlinarith [sq_pos_of_pos ha0]
  -- From `P ρ (1 - P) = 0`: `P ρ = P ρ P`, which is Hermitian, so `ρ P = P ρ`.
  have hPρ : P * ρ = P * ρ * P := by
    rw [mul_sub, mul_one, sub_eq_zero] at hX
    exact hX
  have hρP : ρ * P = P * ρ * P := by
    have h : (P * ρ)ᴴ = (P * ρ * P)ᴴ := by rw [← hPρ]
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_mul, hPh.eq, hρ.eq,
      ← Matrix.mul_assoc] at h
  exact hPρ.trans hρP.symm

end IsHermitian

/-! ### Trimming projections -/

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-- The left marginal `C Cᴴ` of a bipartite vector with coefficient matrix `C`, that is
the reduced density matrix of `|ψ⟩⟨ψ|` on the first factor. -/
noncomputable def leftMarginal (ψ : EuclideanSpace ℂ (m × n)) : Matrix m m ℂ :=
  schmidtCoeffMatrix (WithLp.ofLp ψ) * (schmidtCoeffMatrix (WithLp.ofLp ψ))ᴴ

omit [Fintype m] [DecidableEq m] in
/-- The left marginal is positive semidefinite. -/
theorem posSemidef_leftMarginal [Finite m] (ψ : EuclideanSpace ℂ (m × n)) :
    (leftMarginal ψ).PosSemidef :=
  posSemidef_self_mul_conjTranspose _

/-- The vector `(P ⊗ 1) ψ`: the operator `P` acts on the first factor, so the
coefficient matrix becomes `P C`. -/
noncomputable def leftApply (P : Matrix m m ℂ) (ψ : EuclideanSpace ℂ (m × n)) :
    EuclideanSpace ℂ (m × n) :=
  toEuclid (P * schmidtCoeffMatrix (WithLp.ofLp ψ))

omit [Fintype n] [DecidableEq m] in
@[simp]
theorem schmidtCoeffMatrix_ofLp_leftApply (P : Matrix m m ℂ)
    (ψ : EuclideanSpace ℂ (m × n)) :
    schmidtCoeffMatrix (WithLp.ofLp (leftApply P ψ)) =
      P * schmidtCoeffMatrix (WithLp.ofLp ψ) :=
  rfl

omit [DecidableEq m] in
/-- The squared norm of a bipartite vector is the real trace of its left marginal. -/
theorem sq_norm_eq_trace_leftMarginal_re (ψ : EuclideanSpace ℂ (m × n)) :
    ‖ψ‖ ^ 2 = (leftMarginal ψ).trace.re := by
  have hCψ : toEuclid (schmidtCoeffMatrix (WithLp.ofLp ψ)) = ψ := rfl
  have h := normSq_toEuclid (schmidtCoeffMatrix (WithLp.ofLp ψ))
  rw [hCψ, trace_mul_comm] at h
  exact h

/-- The vector `(1 ⊗ Q) ψ`: the operator `Q`, possibly rectangular, acts on the second
factor, so the coefficient matrix becomes `C Qᵀ`, since `((1 ⊗ Q) ψ)(i, k) = ∑ⱼ Q k j C i j`. -/
noncomputable def rightApply {n' : Type*} [Fintype n'] (Q : Matrix n' n ℂ)
    (ψ : EuclideanSpace ℂ (m × n)) : EuclideanSpace ℂ (m × n') :=
  toEuclid (schmidtCoeffMatrix (WithLp.ofLp ψ) * Qᵀ)

omit [Fintype m] [DecidableEq m] in
@[simp]
theorem schmidtCoeffMatrix_ofLp_rightApply {n' : Type*} [Fintype n'] (Q : Matrix n' n ℂ)
    (ψ : EuclideanSpace ℂ (m × n)) :
    schmidtCoeffMatrix (WithLp.ofLp (rightApply Q ψ)) =
      schmidtCoeffMatrix (WithLp.ofLp ψ) * Qᵀ :=
  rfl

omit [DecidableEq m] in
/-- An operator on the first factor does not increase the Schmidt rank: `(P ⊗ 1) ψ` has
Schmidt rank at most that of `ψ`. -/
theorem schmidtRank_leftApply_le (P : Matrix m m ℂ) (ψ : EuclideanSpace ℂ (m × n)) :
    schmidtRank (WithLp.ofLp (leftApply P ψ)) ≤ schmidtRank (WithLp.ofLp ψ) := by
  rw [schmidtRank, schmidtRank, schmidtCoeffMatrix_ofLp_leftApply]
  exact rank_mul_le_right _ _

omit [Fintype m] [DecidableEq m] in
/-- An operator on the second factor does not increase the Schmidt rank: `(1 ⊗ Q) ψ` has
Schmidt rank at most that of `ψ`. This is the step of the proof of Lemma `l:trim2` of
Landau, Vazirani and Vidick (arXiv:1307.5143v1, algo53.tex, lines 544–553) for an operator
acting on one side of a cut. -/
theorem schmidtRank_rightApply_le {n' : Type*} [Fintype n'] (Q : Matrix n' n ℂ)
    (ψ : EuclideanSpace ℂ (m × n)) :
    schmidtRank (WithLp.ofLp (rightApply Q ψ)) ≤ schmidtRank (WithLp.ofLp ψ) := by
  rw [schmidtRank, schmidtRank, schmidtCoeffMatrix_ofLp_rightApply]
  exact rank_mul_le_left _ _

omit [DecidableEq m] in
/-- A Schmidt-rank bound survives an operator on the first factor. -/
theorem HasSchmidtRankLE.leftApply {k : ℕ} {ψ : EuclideanSpace ℂ (m × n)}
    (h : HasSchmidtRankLE k (WithLp.ofLp ψ)) (P : Matrix m m ℂ) :
    HasSchmidtRankLE k (WithLp.ofLp (leftApply P ψ)) :=
  (schmidtRank_leftApply_le P ψ).trans h

omit [Fintype m] [DecidableEq m] in
/-- A Schmidt-rank bound survives an operator on the second factor. -/
theorem HasSchmidtRankLE.rightApply {k : ℕ} {ψ : EuclideanSpace ℂ (m × n)}
    (h : HasSchmidtRankLE k (WithLp.ofLp ψ)) {n' : Type*} [Fintype n'] (Q : Matrix n' n ℂ) :
    HasSchmidtRankLE k (WithLp.ofLp (rightApply Q ψ)) :=
  (schmidtRank_rightApply_le Q ψ).trans h

omit [DecidableEq m] in
/-- The inner product of bipartite vectors is the Frobenius pairing of their coefficient
matrices. -/
theorem inner_eq_trace_schmidtCoeffMatrix (φ ψ : EuclideanSpace ℂ (m × n)) :
    inner ℂ φ ψ =
      ((schmidtCoeffMatrix (WithLp.ofLp φ))ᴴ * schmidtCoeffMatrix (WithLp.ofLp ψ)).trace := by
  rw [← inner_toEuclid]
  rfl

/-- A *trimming projection* of `ψ` at `D`: an orthogonal projection of rank at most `D`
on the first factor whose trace against the left marginal is the Ky Fan `D`-norm, that
is the sum of the `D` largest squared Schmidt coefficients.  The vector `(P ⊗ 1) ψ` is
then the trimmed vector `trim_D ψ` of Landau, Vazirani and Vidick (arXiv:1307.5143v1,
algo53.tex, lines 330–333).  Every choice of kept eigenvectors in a degenerate Schmidt
coefficient (footnote, line 332) gives a trimming projection. -/
structure IsTrimmingProjection (ψ : EuclideanSpace ℂ (m × n)) (D : ℕ)
    (P : Matrix m m ℂ) : Prop where
  isHermitian : P.IsHermitian
  mul_self : P * P = P
  rank_le : P.rank ≤ D
  trace_mul_leftMarginal :
    (P * leftMarginal ψ).trace.re = (posSemidef_leftMarginal ψ).isHermitian.kyFanNorm D

/-- Every bipartite vector has a trimming projection at every `D`
(arXiv:1307.5143v1, algo53.tex, lines 330–333). -/
theorem exists_isTrimmingProjection (ψ : EuclideanSpace ℂ (m × n)) (D : ℕ) :
    ∃ P : Matrix m m ℂ, IsTrimmingProjection ψ D P := by
  obtain ⟨P, hPh, hPi, hPr, hPt⟩ :=
    (posSemidef_leftMarginal ψ).isHermitian.exists_isProj_trace_eq_kyFanNorm D
  refine ⟨P, hPh, hPi, ?_, hPt⟩
  have h : (P.rank : ℝ) ≤ D := by
    rw [hPh.rank_eq_trace_re_of_idem hPi, hPr]
    exact_mod_cast min_le_left _ _
  exact_mod_cast h

namespace IsTrimmingProjection

variable {ψ : EuclideanSpace ℂ (m × n)} {D : ℕ} {P : Matrix m m ℂ}

/-- `Cᴴ P C` has the Ky Fan `D`-norm of the left marginal as its trace. -/
private theorem trace_conjTranspose_mul_mul (hP : IsTrimmingProjection ψ D P) :
    ((schmidtCoeffMatrix (WithLp.ofLp ψ))ᴴ * (P * schmidtCoeffMatrix (WithLp.ofLp ψ))).trace =
      ((posSemidef_leftMarginal ψ).isHermitian.kyFanNorm D : ℂ) := by
  set C := schmidtCoeffMatrix (WithLp.ofLp ψ)
  have hH : (Cᴴ * (P * C)).IsHermitian := by
    have : Cᴴ * (P * C) = Cᴴ * P * C := (Matrix.mul_assoc _ _ _).symm
    rw [this]
    simpa using isHermitian_conjTranspose_mul_mul C hP.isHermitian
  rw [hH.trace_eq_ofReal_re, ← hP.trace_mul_leftMarginal, trace_mul_comm, Matrix.mul_assoc]
  rfl

/-- The trimmed vector has overlap with `ψ` equal to the Ky Fan `D`-norm of the left
marginal, the sum of the `D` largest squared Schmidt coefficients
(arXiv:1307.5143v1, algo53.tex, lines 330–333). -/
theorem inner_leftApply_self (hP : IsTrimmingProjection ψ D P) :
    inner ℂ (leftApply P ψ) ψ =
      ((posSemidef_leftMarginal ψ).isHermitian.kyFanNorm D : ℂ) := by
  rw [inner_eq_trace_schmidtCoeffMatrix, schmidtCoeffMatrix_ofLp_leftApply,
    conjTranspose_mul, hP.isHermitian.eq, Matrix.mul_assoc, hP.trace_conjTranspose_mul_mul]

/-- The squared norm of the trimmed vector is the Ky Fan `D`-norm of the left marginal
(arXiv:1307.5143v1, algo53.tex, lines 330–333). -/
theorem norm_leftApply_sq (hP : IsTrimmingProjection ψ D P) :
    ‖leftApply P ψ‖ ^ 2 = (posSemidef_leftMarginal ψ).isHermitian.kyFanNorm D := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (leftApply P ψ)
  rw [inner_eq_trace_schmidtCoeffMatrix, schmidtCoeffMatrix_ofLp_leftApply,
    conjTranspose_mul, hP.isHermitian.eq, Matrix.mul_assoc, ← Matrix.mul_assoc P P,
    hP.mul_self, hP.trace_conjTranspose_mul_mul] at h
  exact Complex.ofReal_injective (by rw [Complex.ofReal_pow]; exact h.symm)

/-- The trimmed vector has Schmidt rank at most `D`
(arXiv:1307.5143v1, algo53.tex, lines 330–333). -/
theorem hasSchmidtRankLE_leftApply (hP : IsTrimmingProjection ψ D P) :
    HasSchmidtRankLE D (WithLp.ofLp (leftApply P ψ)) := by
  rw [HasSchmidtRankLE, schmidtRank, schmidtCoeffMatrix_ofLp_leftApply]
  exact (rank_mul_le_left _ _).trans hP.rank_le

/-- The norm of the trimmed vector is the square root of the Ky Fan `D`-norm of the left
marginal. -/
theorem norm_leftApply (hP : IsTrimmingProjection ψ D P) :
    ‖leftApply P ψ‖ = √((posSemidef_leftMarginal ψ).isHermitian.kyFanNorm D) := by
  rw [← hP.norm_leftApply_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The normalized trimmed vector `v' = trim_D ψ / ‖trim_D ψ‖` has real nonnegative
overlap `⟨v'|ψ⟩` with `ψ`, equal to the square root of the Ky Fan `D`-norm of the left
marginal (arXiv:1307.5143v1, algo53.tex, Lemma `lem:eckart`, lines 335–339).  When the
trimmed vector vanishes, both sides are zero. -/
theorem inner_normalized_eq_sqrt (hP : IsTrimmingProjection ψ D P) :
    inner ℂ (‖leftApply P ψ‖⁻¹ • leftApply P ψ) ψ =
      (√((posSemidef_leftMarginal ψ).isHermitian.kyFanNorm D) : ℂ) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_left, hP.inner_leftApply_self,
    hP.norm_leftApply, Complex.real_smul, ← Complex.ofReal_mul, ← div_eq_inv_mul,
    Real.div_sqrt]

/-- **Eckart–Young theorem** (arXiv:1307.5143v1, algo53.tex, Lemma `lem:eckart`,
lines 335–339).  For a trimming projection `P` of `ψ` at `D`, the normalized trimmed
vector `v' = trim_D ψ / ‖trim_D ψ‖` satisfies `⟨v'|ψ⟩ ≥ |⟨w|ψ⟩|` for every unit vector
`w` of Schmidt rank at most `D`.  The overlap `⟨v'|ψ⟩` is real by
`Matrix.IsTrimmingProjection.inner_normalized_eq_sqrt`.  The vector `ψ` need not be
normalized. -/
theorem norm_inner_le_re_inner_normalized (hP : IsTrimmingProjection ψ D P)
    (w : EuclideanSpace ℂ (m × n)) (hw : ‖w‖ = 1)
    (hwD : HasSchmidtRankLE D (WithLp.ofLp w)) :
    ‖inner ℂ w ψ‖ ≤ (inner ℂ (‖leftApply P ψ‖⁻¹ • leftApply P ψ) ψ).re := by
  rw [hP.inner_normalized_eq_sqrt, Complex.ofReal_re, norm_inner_symm]
  exact Real.le_sqrt_of_sq_le (normSq_inner_le_kyFanNorm ψ w hw D hwD)

/-- The squared overlap of the discarded part `u - trim_k u` with a vector `v` of Schmidt
rank at most `D` is at most `D` times the `(k + 1)`-st eigenvalue of the left marginal of
`u`, times `‖v‖²`.  This is the key estimate behind the corrected Lemma `l:trim1`. -/
private theorem norm_inner_sub_leftApply_sq_le {u : EuclideanSpace ℂ (m × n)} {k : ℕ}
    (hP : IsTrimmingProjection u k P) (v : EuclideanSpace ℂ (m × n))
    (hv : HasSchmidtRankLE D (WithLp.ofLp v)) :
    ‖inner ℂ (u - leftApply P u) v‖ ^ 2 ≤
      (D * (posSemidef_leftMarginal u).isHermitian.descEigenvalue k) * ‖v‖ ^ 2 := by
  set C := schmidtCoeffMatrix (WithLp.ofLp u) with hC
  set B := schmidtCoeffMatrix (WithLp.ofLp v) with hB
  set hρ := posSemidef_leftMarginal u
  set Q : Matrix m m ℂ := 1 - P with hQ
  have hQh : Qᴴ = Q := by rw [hQ, conjTranspose_sub, conjTranspose_one, hP.isHermitian.eq]
  have hQi : Q * Q = Q := by
    rw [hQ]
    simp [sub_mul, mul_sub, hP.mul_self]
  have hPQ : P * Q = 0 := by rw [hQ, mul_sub, mul_one, hP.mul_self, sub_self]
  set Y : Matrix m n ℂ := Q * B with hY
  set hYY := isHermitian_mul_conjTranspose_self Y
  set T := hYY.supportProj with hT
  have hTh : T.IsHermitian := hYY.supportProj_isHermitian
  have hTi : T * T = T := hYY.supportProj_idem
  have hTY : T * Y = Y := supportProj_mul_conjTranspose_mul_self Y
  have hPT : P * T = 0 := by
    obtain ⟨W, hW⟩ := hYY.exists_supportProj_eq_mul
    rw [hT, hW, hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ,
      Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]
  have hTP : T * P = 0 := by
    have := congrArg conjTranspose hPT
    rwa [conjTranspose_mul, hTh.eq, hP.isHermitian.eq, conjTranspose_zero] at this
  -- The coefficient matrix of `u - trim u` is `Q C`.
  have hcoef : schmidtCoeffMatrix (WithLp.ofLp (u - leftApply P u)) = Q * C := by
    rw [hQ, Matrix.sub_mul, Matrix.one_mul]
    rfl
  -- The overlap is the Frobenius pairing of `T C` with `Y`.
  have hinner : inner ℂ (u - leftApply P u) v = inner ℂ (toEuclid (T * C)) (toEuclid Y) := by
    rw [inner_eq_trace_schmidtCoeffMatrix, hcoef, inner_toEuclid, conjTranspose_mul,
      conjTranspose_mul, hQh, hTh.eq, Matrix.mul_assoc, Matrix.mul_assoc, hTY, hY]
  -- The norm of `Y` is at most the norm of `v`.
  have hYnorm : ‖toEuclid Y‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    have hv' : ‖v‖ ^ 2 = ((Bᴴ * B).trace).re := normSq_toEuclid B
    have hsplit : (Bᴴ * B).trace.re = ((Q * B)ᴴ * (Q * B)).trace.re +
        ((P * B)ᴴ * (P * B)).trace.re := by
      rw [← Complex.add_re, ← trace_add, conjTranspose_mul, conjTranspose_mul, hQh,
        hP.isHermitian.eq, Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQi, Matrix.mul_assoc,
        ← Matrix.mul_assoc P, hP.mul_self, ← Matrix.mul_add, ← Matrix.add_mul, hQ,
        sub_add_cancel, Matrix.one_mul]
    have hnn := (Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self (P * B)).trace_nonneg).1
    rw [hv', normSq_toEuclid]
    linarith
  -- The norm of `T C` squared is the trace of `T` against the left marginal.
  have hTC : ‖toEuclid (T * C)‖ ^ 2 = (T * leftMarginal u).trace.re := by
    rw [normSq_toEuclid, conjTranspose_mul, hTh.eq, Matrix.mul_assoc, ← Matrix.mul_assoc T T,
      hTi, trace_mul_comm, Matrix.mul_assoc]
    rfl
  -- The projection `P + T` has rank at most `k + D`.
  have hRh : (P + T).IsHermitian := hP.isHermitian.add hTh
  have hRi : (P + T) * (P + T) = P + T := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hP.mul_self, hPT, hTP, hTi, add_zero,
      zero_add]
  have hTrank : (T.rank : ℝ) ≤ D := by
    rw [hTh.rank_eq_trace_re_of_idem hTi, hT, hYY.supportProj_trace, rank_self_mul_conjTranspose,
      Complex.natCast_re]
    exact_mod_cast (rank_mul_le_right Q B).trans hv
  have hRrank : (P + T).rank ≤ k + D := by
    have h : ((P + T).rank : ℝ) ≤ k + D := by
      rw [hRh.rank_eq_trace_re_of_idem hRi, trace_add, Complex.add_re,
        ← hP.isHermitian.rank_eq_trace_re_of_idem hP.mul_self,
        ← hTh.rank_eq_trace_re_of_idem hTi]
      have : (P.rank : ℝ) ≤ k := by exact_mod_cast hP.rank_le
      linarith
    exact_mod_cast h
  have hKF := hρ.trace_mul_re_le_kyFanNorm_of_isHermitian_idem hRh hRi hRrank
  rw [Matrix.add_mul, trace_add, Complex.add_re, hP.trace_mul_leftMarginal] at hKF
  have hgrow := hρ.kyFanNorm_add_le k D
  have hTbound : ‖toEuclid (T * C)‖ ^ 2 ≤ D * hρ.isHermitian.descEigenvalue k := by
    rw [hTC]; linarith
  rw [hinner]
  calc ‖inner ℂ (toEuclid (T * C)) (toEuclid Y)‖ ^ 2
      ≤ (‖toEuclid (T * C)‖ * ‖toEuclid Y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
    _ = ‖toEuclid (T * C)‖ ^ 2 * ‖toEuclid Y‖ ^ 2 := mul_pow _ _ _
    _ ≤ (D * hρ.isHermitian.descEigenvalue k) * ‖v‖ ^ 2 :=
        mul_le_mul hTbound hYnorm (sq_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (hρ.descEigenvalue_nonneg k))

/-- The trimmed vector is no longer than `ψ`: its squared norm, the sum of the `D` largest
squared Schmidt coefficients, is at most their total sum `‖ψ‖²`. -/
theorem norm_leftApply_le (hP : IsTrimmingProjection ψ D P) : ‖leftApply P ψ‖ ≤ ‖ψ‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [hP.norm_leftApply_sq, sq_norm_eq_trace_leftMarginal_re]
  exact (posSemidef_leftMarginal ψ).kyFanNorm_le_trace_re D

/-- **A trimming projection commutes with the left marginal.**  Equality in Ky Fan's
maximum principle forces `P ρ = ρ P`: a projection of the same trace never captures more
of `ρ`, so `P` is a trace-maximizing projection and
`Matrix.IsHermitian.commute_of_forall_trace_mul_re_le` applies. -/
theorem commute_leftMarginal (hP : IsTrimmingProjection ψ D P) :
    Commute P (leftMarginal ψ) := by
  set hρ := posSemidef_leftMarginal ψ
  refine hρ.isHermitian.commute_of_forall_trace_mul_re_le hP.isHermitian hP.mul_self
    fun R hRh hRi hRt => ?_
  have hRrank : R.rank ≤ D := by
    have h : (R.rank : ℝ) = P.rank := by
      rw [hRh.rank_eq_trace_re_of_idem hRi, hP.isHermitian.rank_eq_trace_re_of_idem hP.mul_self,
        hRt]
    exact (Nat.cast_injective h).le.trans hP.rank_le
  rw [hP.trace_mul_leftMarginal]
  exact hρ.trace_mul_re_le_kyFanNorm_of_isHermitian_idem hRh hRi hRrank

/-- **The trimmed vector as a projection on the second factor**, coefficient form
(arXiv:1307.5143v1, algo53.tex, lines 544–553).  For a trimming projection `P` of `ψ` with
coefficient matrix `C`, there is an orthogonal projection `Q` on the second factor, of rank
at most that of `P`, with `P C = C Qᵀ`; that is, `(P ⊗ 1) ψ = (1 ⊗ Q) ψ`.  The projection
`Qᵀ` is the support projection of `Cᴴ P C`: it fixes the rows of `P C`, and it kills the
rows of `(1 - P) C` because `(1 - P) C Cᴴ P = (1 - P) P C Cᴴ = 0` by
`Matrix.IsTrimmingProjection.commute_leftMarginal`. -/
theorem exists_mul_eq_mul_transpose (hP : IsTrimmingProjection ψ D P) :
    ∃ Q : Matrix n n ℂ, Q.IsHermitian ∧ Q * Q = Q ∧ Q.rank ≤ P.rank ∧
      P * schmidtCoeffMatrix (WithLp.ofLp ψ) = schmidtCoeffMatrix (WithLp.ofLp ψ) * Qᵀ := by
  classical
  set C := schmidtCoeffMatrix (WithLp.ofLp ψ) with hC
  set B : Matrix n m ℂ := (P * C)ᴴ with hB
  set hBB := isHermitian_mul_conjTranspose_self B
  set Q₀ := hBB.supportProj with hQ₀
  have hQh : Q₀.IsHermitian := hBB.supportProj_isHermitian
  have hQi : Q₀ * Q₀ = Q₀ := hBB.supportProj_idem
  have hQB : Q₀ * B = B := supportProj_mul_conjTranspose_mul_self B
  have hPCQ : P * C * Q₀ = P * C := by
    have h : (Q₀ * B)ᴴ = Bᴴ := by rw [hQB]
    rwa [conjTranspose_mul, hQh.eq, hB, conjTranspose_conjTranspose] at h
  have hcomm : P * (C * Cᴴ) = C * Cᴴ * P := hP.commute_leftMarginal.eq
  obtain ⟨W, hW⟩ := hBB.exists_supportProj_eq_mul
  have hQPC : (1 - P) * C * Q₀ = 0 := by
    have h : (1 - P) * C * Q₀ = (1 - P) * (C * Cᴴ * P) * (P * C * W) := by
      rw [hQ₀, hW, hB]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP.isHermitian.eq,
        Matrix.mul_assoc]
    rw [h, ← hcomm, ← Matrix.mul_assoc (1 - P) P, Matrix.sub_mul, Matrix.one_mul, hP.mul_self,
      sub_self, Matrix.zero_mul, Matrix.zero_mul]
  have hCQ : C * Q₀ = P * C := by
    have h : C * Q₀ = P * C * Q₀ + (1 - P) * C * Q₀ := by
      rw [← Matrix.add_mul, ← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    rw [h, hPCQ, hQPC, add_zero]
  refine ⟨Q₀ᵀ, hQh.transpose, by rw [← transpose_mul, hQi], ?_, by rw [transpose_transpose, hCQ]⟩
  have h : (Q₀.rank : ℝ) = (P * C).rank := by
    rw [hQh.rank_eq_trace_re_of_idem hQi, hQ₀, hBB.supportProj_trace,
      rank_self_mul_conjTranspose, hB, rank_conjTranspose, Complex.natCast_re]
  rw [rank_transpose, Nat.cast_injective h]
  exact rank_mul_le_left _ _

/-- **The trimmed vector as a projection on the second factor** (arXiv:1307.5143v1,
algo53.tex, lines 544–553).  For a trimming projection `P` of `ψ` at `D`, there is an
orthogonal projection `Q` of rank at most `D` on the second factor with
`(P ⊗ 1) ψ = (1 ⊗ Q) ψ`.  This is the form `trim_D(ψ) = (Id ⊗ Σ_{k ≤ D} |β_k⟩⟨β_k|) ψ` used
in the proof of Lemma `l:trim2` of the source. -/
theorem exists_leftApply_eq_rightApply (hP : IsTrimmingProjection ψ D P) :
    ∃ Q : Matrix n n ℂ, Q.IsHermitian ∧ Q * Q = Q ∧ Q.rank ≤ D ∧
      leftApply P ψ = rightApply Q ψ := by
  obtain ⟨Q, hQh, hQi, hQr, hPQ⟩ := hP.exists_mul_eq_mul_transpose
  exact ⟨Q, hQh, hQi, hQr.trans hP.rank_le, by rw [leftApply, rightApply, hPQ]⟩

/-- **Trimming error against a vector of bounded Schmidt rank** (corrected form of
arXiv:1307.5143v1, algo53.tex, Lemma `l:trim1`, lines 531–542).  If `P` is a trimming
projection of `u` at `k` and `v` has Schmidt rank at most `D`, then the discarded part
`u - trim_k u` satisfies `|⟨u - trim_k u, v⟩| ≤ ‖u‖ ‖v‖ √(D / (k + 1))`.  No
normalization is assumed, and `k` and `D` are arbitrary. -/
theorem norm_inner_sub_leftApply_le {u : EuclideanSpace ℂ (m × n)} {k : ℕ}
    (hP : IsTrimmingProjection u k P) (v : EuclideanSpace ℂ (m × n))
    (hv : HasSchmidtRankLE D (WithLp.ofLp v)) :
    ‖inner ℂ (u - leftApply P u) v‖ ≤ ‖u‖ * ‖v‖ * √((D : ℝ) / (k + 1)) := by
  set hρ := posSemidef_leftMarginal u
  set lam := hρ.isHermitian.descEigenvalue k
  have hsq := hP.norm_inner_sub_leftApply_sq_le v hv
  have hlam : ((k : ℝ) + 1) * lam ≤ ‖u‖ ^ 2 := by
    rw [sq_norm_eq_trace_leftMarginal_re]
    exact hρ.succ_mul_descEigenvalue_le_trace_re k
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hrhs : (‖u‖ * ‖v‖ * √((D : ℝ) / (k + 1))) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 * (D / (k + 1)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hD hk.le)]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [hrhs]
  refine hsq.trans ?_
  have hlam' : lam ≤ ‖u‖ ^ 2 / (k + 1) := by
    rw [le_div_iff₀ hk]; linarith
  calc (D : ℝ) * lam * ‖v‖ ^ 2 ≤ D * (‖u‖ ^ 2 / (k + 1)) * ‖v‖ ^ 2 := by
        gcongr
    _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 * (D / (k + 1)) := by ring

/-- **Corrected Lemma `l:trim1`** (arXiv:1307.5143v1, algo53.tex, lines 531–542).  If
`P` is a trimming projection of `u` at `k` and `v` has Schmidt rank at most `D`, then
`|⟨trim_k u, v⟩| ≥ |⟨u, v⟩| - ‖u‖ ‖v‖ √(D / (k + 1))`.  For unit `u` and `v`, trimming
to `k + 1 ≥ D / ε²` terms costs at most `ε` in overlap; the printed radius `D / ε` does
not suffice (`docs/paper-gaps/lvv13_trimming_radius.tex`). -/
theorem norm_inner_sub_le_norm_inner_leftApply {u : EuclideanSpace ℂ (m × n)} {k : ℕ}
    (hP : IsTrimmingProjection u k P) (v : EuclideanSpace ℂ (m × n))
    (hv : HasSchmidtRankLE D (WithLp.ofLp v)) :
    ‖inner ℂ u v‖ - ‖u‖ * ‖v‖ * √((D : ℝ) / (k + 1)) ≤ ‖inner ℂ (leftApply P u) v‖ := by
  have h := hP.norm_inner_sub_leftApply_le v hv
  have hsplit : inner ℂ u v = inner ℂ (leftApply P u) v + inner ℂ (u - leftApply P u) v := by
    rw [inner_sub_left, add_sub_cancel]
  have htri := norm_add_le (inner ℂ (leftApply P u) v) (inner ℂ (u - leftApply P u) v)
  rw [← hsplit] at htri
  linarith

end IsTrimmingProjection

end Matrix
