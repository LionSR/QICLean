/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.TrimmingEnergy

/-!
# A trimmed low-energy witness on a subspace of the left factor

Let `ψ` be a unit vector of energy at most `E₀ + δ` whose left factor lies in a subspace `V`,
`(Pv ⊗ 1) ψ = ψ` for the orthogonal projection `Pv` onto `V`, and let some unit vector of Schmidt
rank at most `D` overlap `ψ` by at least `1 - η`, with `2η < 1`. Trimming `ψ` to its `D`
largest Schmidt terms and normalizing gives a unit vector `w` that
* has Schmidt rank at most `D`;
* has energy at most `E₀ + (δ + 2√(2η))/(1 - 2η)`;
* still has its left factor in `V`;
* is `(1 ⊗ W) x` for an isometry `W : ℂ^k → ℂ^n`, `k ≤ D`, and a left state `x` on
  `m × Fin k`.

This is Lemma `l:within` of Landau, Vazirani and Vidick, in the corrected form of the energy
bound of `Matrix.IsTrimmingProjection.re_inner_normalized_le_of_norm_inner`. The printed
energy `ε₀ + 6√c_ε` is not established by the printed argument. Documented in
`docs/paper-gaps/lvv13_trimming_energy.tex`.

## Main results

* `Matrix.ofLp_rightApply`: `(1 ⊗ Q) ψ` as a matrix-vector product, for rectangular `Q`.
* `Matrix.IsTrimmingProjection.leftApply_leftApply_of_leftApply_eq`: trimming keeps the left
  factor in `V`.
* `Matrix.leftApply_smul`, `Matrix.leftApply_rightApply`, `Matrix.schmidtRank_leftApply_le_rank`:
  linearity, commutation with an operator on the second factor, and a rank bound.
* `Matrix.IsTrimmingProjection.exists_trimmed_witness`: Lemma `l:within`.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of
  1D gapped local Hamiltonians*, arXiv:1307.5143v1, `algo53.tex`, Lemma `l:within`,
  lines 509–515.
-/

open scoped Matrix Kronecker ComplexOrder InnerProductSpace

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq n] in
/-- The vector `(1 ⊗ Q) ψ` of `rightApply` is the matrix-vector product with `1 ⊗ Q`, also for
a rectangular `Q`. -/
theorem ofLp_rightApply {n' : Type*} [Fintype n'] (Q : Matrix n' n ℂ)
    (ψ : EuclideanSpace ℂ (m × n)) :
    WithLp.ofLp (rightApply Q ψ) = ((1 : Matrix m m ℂ) ⊗ₖ Q) *ᵥ WithLp.ofLp ψ := by
  ext ⟨i, j⟩
  simp [rightApply, toEuclid, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, one_apply,
    Matrix.mul_apply, mul_comm]

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- `leftApply` is linear in the vector. -/
theorem leftApply_smul (A : Matrix m m ℂ) (c : ℂ) (ψ : EuclideanSpace ℂ (m × n)) :
    leftApply A (c • ψ) = c • leftApply A ψ := by
  ext ⟨i, j⟩
  simp [leftApply, toEuclid, schmidtCoeffMatrix_apply, Matrix.mul_apply, Finset.mul_sum,
    mul_left_comm]

omit [DecidableEq m] [DecidableEq n] in
/-- Operators on the two factors commute: `(A ⊗ 1)(1 ⊗ Q) ψ = (1 ⊗ Q)(A ⊗ 1) ψ`. -/
theorem leftApply_rightApply {n' : Type*} [Fintype n'] (A : Matrix m m ℂ) (Q : Matrix n' n ℂ)
    (ψ : EuclideanSpace ℂ (m × n)) :
    leftApply A (rightApply Q ψ) = rightApply Q (leftApply A ψ) := by
  change toEuclid (A * schmidtCoeffMatrix (WithLp.ofLp (rightApply Q ψ))) =
    toEuclid (schmidtCoeffMatrix (WithLp.ofLp (leftApply A ψ)) * Qᵀ)
  rw [schmidtCoeffMatrix_ofLp_rightApply, schmidtCoeffMatrix_ofLp_leftApply, Matrix.mul_assoc]

omit [DecidableEq m] [DecidableEq n] in
/-- `(P ⊗ 1) φ` has Schmidt rank at most the rank of `P`. -/
theorem schmidtRank_leftApply_le_rank (P : Matrix m m ℂ) (φ : EuclideanSpace ℂ (m × n)) :
    schmidtRank (WithLp.ofLp (leftApply P φ)) ≤ P.rank := by
  rw [schmidtRank, schmidtCoeffMatrix_ofLp_leftApply]
  exact rank_mul_le_left _ _

namespace IsTrimmingProjection

variable {ψ : EuclideanSpace ℂ (m × n)} {D : ℕ} {P : Matrix m m ℂ}

omit [DecidableEq n] in
/-- **Trimming keeps the left factor in a subspace.** If `(Pv ⊗ 1) ψ = ψ`, then
`(Pv ⊗ 1) (P ⊗ 1) ψ = (P ⊗ 1) ψ` for a trimming projection `P`: the trimmed vector is
`(1 ⊗ Q) ψ` for some `Q`, and `Pv ⊗ 1` commutes with `1 ⊗ Q`. -/
theorem leftApply_leftApply_of_leftApply_eq (hP : IsTrimmingProjection ψ D P)
    {Pv : Matrix m m ℂ} (hPv : leftApply Pv ψ = ψ) :
    leftApply Pv (leftApply P ψ) = leftApply P ψ := by
  obtain ⟨Q, -, -, -, hPQ⟩ := hP.exists_mul_eq_mul_transpose
  have hPvC : Pv * schmidtCoeffMatrix (WithLp.ofLp ψ) = schmidtCoeffMatrix (WithLp.ofLp ψ) := by
    have h := congrArg (fun v ↦ schmidtCoeffMatrix (WithLp.ofLp v)) hPv
    simpa only [schmidtCoeffMatrix_ofLp_leftApply] using h
  rw [leftApply_leftApply]
  change toEuclid (Pv * P * schmidtCoeffMatrix (WithLp.ofLp ψ)) =
    toEuclid (P * schmidtCoeffMatrix (WithLp.ofLp ψ))
  rw [Matrix.mul_assoc, hPQ, ← Matrix.mul_assoc, hPvC]

/-- **Lemma `l:within`** of Landau, Vazirani and Vidick (arXiv:1307.5143v1, `algo53.tex`,
lines 509–515), with the corrected energy bound. Let `H = A ⊗ 1 + 1 ⊗ B + K` with
`H ≥ E₀` and `0 ≤ K ≤ 1`, let `ψ` be a unit vector with `Re ⟨ψ, H ψ⟩ ≤ E₀ + δ` whose left
factor lies in the range of `Pv`, `(Pv ⊗ 1) ψ = ψ`, and let a unit vector `u` of Schmidt rank
at most `D` satisfy `|⟨u, ψ⟩| ≥ 1 - η` with `2η < 1`. Then there is a unit vector `w` of
Schmidt rank at most `D`, with energy at most `E₀ + (δ + 2√(2η))/(1 - 2η)` and left factor in
the range of `Pv`, together with an isometry `W : ℂ^k → ℂ^n`, `k ≤ D`, and a left state `x`
whose left factor also lies in the range of `Pv`, such that `w = (1 ⊗ W) x`. The vector `w` is
the normalized trimming of `ψ` to its `D` largest Schmidt terms. -/
theorem exists_trimmed_witness {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    {K H : Matrix (m × n) (m × n) ℂ}
    (hHK : H = A ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ B + K) {E₀ δ : ℝ}
    (hH : (H - (E₀ : ℂ) • 1).PosSemidef) (hK0 : K.PosSemidef) (hK1 : (1 - K).PosSemidef)
    {ψ : EuclideanSpace ℂ (m × n)} (hψ : ‖ψ‖ = 1)
    (hE : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re ≤ E₀ + δ) {D : ℕ}
    {u : EuclideanSpace ℂ (m × n)} (hu : ‖u‖ = 1) (huD : HasSchmidtRankLE D (WithLp.ofLp u))
    {η : ℝ} (hη : 1 - η ≤ ‖⟪u, ψ⟫_ℂ‖) (hη2 : 2 * η < 1) {Pv : Matrix m m ℂ}
    (hPv : leftApply Pv ψ = ψ) :
    ∃ (w : EuclideanSpace ℂ (m × n)) (k : ℕ) (W : Matrix n (Fin k) ℂ)
      (x : EuclideanSpace ℂ (m × Fin k)),
      ‖w‖ = 1 ∧ HasSchmidtRankLE D (WithLp.ofLp w) ∧
      (⟪w, toEuclideanLin H w⟫_ℂ).re ≤ E₀ + (δ + 2 * √(2 * η)) / (1 - 2 * η) ∧
      leftApply Pv w = w ∧ Wᴴ * W = 1 ∧ k ≤ D ∧
      WithLp.ofLp w = ((1 : Matrix m m ℂ) ⊗ₖ W) *ᵥ WithLp.ofLp x ∧ leftApply Pv x = x := by
  obtain ⟨P, hP⟩ := exists_isTrimmingProjection ψ D
  set t := leftApply P ψ with ht
  have hs := hP.norm_sub_leftApply_sq_le hψ hu huD hη
  have hpy := hP.norm_leftApply_sq_add_norm_sub_sq
  rw [hψ, one_pow] at hpy
  have ht0 : ‖t‖ ≠ 0 := by
    intro h0
    rw [← ht, h0] at hpy
    linarith
  set c : ℂ := ((‖t‖⁻¹ : ℝ) : ℂ)
  have hw : (‖t‖⁻¹ : ℝ) • t = c • t := by rw [Complex.coe_smul]
  obtain ⟨k, W, hW, hkD, -, hWt⟩ := hP.exists_isometry_leftApply_eq_rightApply
  refine ⟨(‖t‖⁻¹ : ℝ) • t, k, W, c • rightApply Wᴴ ψ, ?_, ?_, ?_, ?_, hW, hkD, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ht0]
  · rw [hw, ← leftApply_smul]
    exact (schmidtRank_leftApply_le_rank P _).trans hP.rank_le
  · exact hP.re_inner_normalized_le_of_norm_inner hHK hH hK0 hK1 hψ hE hu huD hη hη2
  · rw [hw, leftApply_smul, hP.leftApply_leftApply_of_leftApply_eq hPv]
  · rw [hw, WithLp.ofLp_smul, WithLp.ofLp_smul, mulVec_smul, ← ofLp_rightApply, ← hWt]
  · rw [leftApply_smul, leftApply_rightApply, hPv]

end IsTrimmingProjection

end Matrix
