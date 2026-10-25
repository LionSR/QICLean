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
* `Matrix.IsTrimmingProjection`: an orthogonal projection of rank at most `D` that
  captures the Ky Fan `D`-norm of the left marginal.

## Main results

* `Matrix.exists_isTrimmingProjection`: a trimming projection exists for every `D`.
* `Matrix.IsTrimmingProjection.inner_leftApply_self`,
  `Matrix.IsTrimmingProjection.norm_leftApply_sq`: the trimmed vector has overlap and
  squared norm equal to the Ky Fan `D`-norm of the left marginal.
* `Matrix.IsTrimmingProjection.hasSchmidtRankLE_leftApply`: the trimmed vector has
  Schmidt rank at most `D`.
* `Matrix.IsTrimmingProjection.norm_inner_le_re_inner_normalized`: the Eckart–Young
  theorem, Lemma `lem:eckart` of the source.
* `Matrix.IsTrimmingProjection.norm_inner_sub_leftApply_le` and
  `Matrix.IsTrimmingProjection.norm_inner_sub_le_norm_inner_leftApply`: the corrected
  form of Lemma `l:trim1` of the source.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of
  1D gapped local Hamiltonians*, arXiv:1307.5143v1, algo53.tex: trimming, lines 330–333;
  Lemma `lem:eckart`, lines 335–339; Lemma `l:trim1`, lines 531–542.
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
    have h := hρ.succ_mul_descEigenvalue_le_trace_re k
    have hCu : toEuclid (schmidtCoeffMatrix (WithLp.ofLp u)) = u := rfl
    have hu := normSq_toEuclid (schmidtCoeffMatrix (WithLp.ofLp u))
    rw [hCu, ← trace_mul_comm] at hu
    rw [hu]
    exact h
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
