/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Order.PowerAmplification
import QICLean.Channel.Entanglement.LocalTensorCopies
import QICLean.Spectral.Projection.TwoForms

/-!
# Dimension-independent rank-one coherence bound for locally factorized maps

This file establishes the all-copy rank-one coherence inequality

  `‖⟨a₀ ⊗ b₀ | ρ^{⊗ N} | a₁ ⊗ b₁⟩‖ ^ 4 ≤ p₀₀ p₀₁ p₁₀ p₁₁`

where `pᵢⱼ = Re ⟨aᵢ ⊗ bⱼ | ρ^{⊗ N} | aᵢ ⊗ bⱼ⟩`, for any bipartite operator
`ρ = c • C(|u⟩⟨u|)` (`c ≥ 0`) produced by a locally factorized rectangular completely
positive map `C = L ⊗ M` acting on an arbitrary complex vector `u`, whenever `C`
admits a single-copy reverse-block certificate `S` satisfying:
1. `IsKrausCP (C + S)` and `IsKrausCP (C - S)`,
2. `IsCompletelyCopositiveMap S`,
3. `C(|u⟩⟨u|) = S(|u⟩⟨u|)`.

## Proof architecture

No general trace-norm or Schatten-norm machinery is used:
1. **Scalar 2×2 compression:** `Matrix.norm_quad_le_sqrt_of_fromBlocks_posSemidef`
   bounds `‖⟨x | G₁₂ | y⟩‖ ≤ √(Re ⟨x | G₁₁ | x⟩ · Re ⟨y | G₂₂ | y⟩)` directly from
   `PosSemidef` of the `2 × 2` block matrix, including all zero-vector / zero-diagonal cases.
2. **Spectral split and reverse-block bound:** pulling `|aᵢ⟩⟨aᵢ| ⊗ |bⱼ⟩⟨bⱼ|` back
   through `L^{⊗ N}` and `M^{⊗ N}` via `Matrix.traceAdjointMap`, applying the
   noncommuting singular two-form split `Matrix.exists_twoForms_bipartite_split` and
   the `N`-copy reverse-block theorem `piTensorMap_const_reverseBlock_posSemidef`, yields
   the four-term coherence inequality
   `k ≤ √(p₀₀ p₀₁) + √(p₁₀ p₁₁) + 2 √(p₀₁ p₁₀)`.
3. **Rescaling and tensor-power amplification:** rank-one matrix elements of
   `bipartiteCopies (N * t) R` multiply exactly as `t`-th powers on product filter
   vectors `vecPower t` (`QuantumInfo.quad_bipartiteCopies_mul_vecPower`), so
   `Real.pow_four_le_of_rescaled_four_term_bound` amplifies the four-term bound into
   `k ^ 4 ≤ p₀₀ p₀₁ p₁₀ p₁₁` for all `N : ℕ`, with all zero-population and zero-filter
   cases handled explicitly.

## Main declarations

* `Matrix.norm_quad_le_sqrt_of_fromBlocks_posSemidef` — scalar 2×2 block compression bound.
* `Matrix.norm_quad_le_sqrt_of_posSemidef` — specialization to a single PSD matrix.
* `QuantumInfo.rankOne_coherence_four_term_le` — `N`-copy four-term coherence bound.
* `QuantumInfo.rankOne_coherence_pow_four_le` — sharp all-copy `k ^ 4 ≤ p₀₀ p₀₁ p₁₀ p₁₁`
  bound for `C(|u⟩⟨u|)`.
* `QuantumInfo.rankOne_coherence_pow_four_le_of_smul` — same bound for any nonnegative
  real multiple `ρ = c • C(|u⟩⟨u|)`.
-/

open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

/-! ## Section 1: Scalar 2×2 compression bound -/

section ScalarCompression

private theorem dotProduct_sumElim {β : Type*} [Fintype β] (u₁ u₂ v₁ v₂ : β → ℂ) :
    Sum.elim u₁ u₂ ⬝ᵥ Sum.elim v₁ v₂ = u₁ ⬝ᵥ v₁ + u₂ ⬝ᵥ v₂ := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- **Scalar 2×2 compression bound.** If the block matrix `[[G₁₁, G₁₂], [G₂₁, G₂₂]]`
is positive semidefinite, then for any vectors `x, y : β → ℂ` (including zero),
`‖⟨x | G₁₂ | y⟩‖ ≤ √(Re ⟨x | G₁₁ | x⟩ · Re ⟨y | G₂₂ | y⟩)`. -/
theorem Matrix.norm_quad_le_sqrt_of_fromBlocks_posSemidef
    {β : Type*} [Fintype β]
    {G₁₁ G₁₂ G₂₁ G₂₂ : Matrix β β ℂ}
    (hM : (Matrix.fromBlocks G₁₁ G₁₂ G₂₁ G₂₂).PosSemidef)
    (x y : β → ℂ) :
    ‖star x ⬝ᵥ G₁₂ *ᵥ y‖ ≤
      Real.sqrt ((star x ⬝ᵥ G₁₁ *ᵥ x).re * (star y ⬝ᵥ G₂₂ *ᵥ y).re) := by
  set a : ℂ := star x ⬝ᵥ G₁₁ *ᵥ x
  set b : ℂ := star x ⬝ᵥ G₁₂ *ᵥ y
  set c : ℂ := star y ⬝ᵥ G₂₁ *ᵥ x
  set d : ℂ := star y ⬝ᵥ G₂₂ *ᵥ y
  have hHerm : (Matrix.fromBlocks G₁₁ G₁₂ G₂₁ G₂₂)ᴴ = Matrix.fromBlocks G₁₁ G₁₂ G₂₁ G₂₂ :=
    hM.isHermitian.eq
  have hG₂₁ : G₂₁ = G₁₂ᴴ := by
    ext i j
    have := congrFun (congrFun hHerm (Sum.inr i)) (Sum.inl j)
    simpa [Matrix.fromBlocks_conjTranspose] using this.symm
  have ha0_nonneg : 0 ≤ a := by
    have h0 := hM.dotProduct_mulVec_nonneg (Sum.elim x (0 : β → ℂ))
    have hstar : star (Sum.elim x (0 : β → ℂ)) = Sum.elim (star x) (0 : β → ℂ) := by
      ext p; cases p <;> simp
    have heq : star (Sum.elim x (0 : β → ℂ)) ⬝ᵥ
        Matrix.fromBlocks G₁₁ G₁₂ G₂₁ G₂₂ *ᵥ Sum.elim x (0 : β → ℂ) = a := by
      rw [hstar, Matrix.fromBlocks_mulVec, dotProduct_sumElim]
      simp [a]
    rwa [heq] at h0
  have hd0_nonneg : 0 ≤ d := by
    have h0 := hM.dotProduct_mulVec_nonneg (Sum.elim (0 : β → ℂ) y)
    have hstar : star (Sum.elim (0 : β → ℂ) y) = Sum.elim (0 : β → ℂ) (star y) := by
      ext p; cases p <;> simp
    have heq : star (Sum.elim (0 : β → ℂ) y) ⬝ᵥ
        Matrix.fromBlocks G₁₁ G₁₂ G₂₁ G₂₂ *ᵥ Sum.elim (0 : β → ℂ) y = d := by
      rw [hstar, Matrix.fromBlocks_mulVec, dotProduct_sumElim]
      simp [d]
    rwa [heq] at h0
  have ha_nonneg : 0 ≤ a.re := (Complex.nonneg_iff.mp ha0_nonneg).1
  have hd_nonneg : 0 ≤ d.re := (Complex.nonneg_iff.mp hd0_nonneg).1
  have ha_im : a.im = 0 := (Complex.nonneg_iff.mp ha0_nonneg).2.symm
  have hd_im : d.im = 0 := (Complex.nonneg_iff.mp hd0_nonneg).2.symm
  have hc_eq : c = star b := by
    change star y ⬝ᵥ G₂₁ *ᵥ x = star (star x ⬝ᵥ G₁₂ *ᵥ y)
    rw [hG₂₁]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.conjTranspose_apply,
      star_sum, star_mul', star_star, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hquad : ∀ t : ℝ, 0 ≤ t ^ 2 * a.re - 2 * t * ‖b‖ ^ 2 + ‖b‖ ^ 2 * d.re := by
    intro t
    let z : β ⊕ β → ℂ := Sum.elim ((t : ℂ) • x) ((-(star b)) • y)
    have hz := (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg z)).1
    have hval :
        star z ⬝ᵥ Matrix.fromBlocks G₁₁ G₁₂ G₂₁ G₂₂ *ᵥ z =
          ((t : ℂ) * (t : ℂ)) * a + (t : ℂ) * (-(star b)) * b +
            (-b) * (t : ℂ) * star b + (b * star b) * d := by
      have hstar : star z = Sum.elim ((t : ℂ) • star x) ((-b) • star y) := by
        ext p
        cases p <;> simp [z]
      have hmul : Matrix.fromBlocks G₁₁ G₁₂ G₂₁ G₂₂ *ᵥ z =
          Sum.elim
            ((t : ℂ) • (G₁₁ *ᵥ x) + (-(star b)) • (G₁₂ *ᵥ y))
            ((t : ℂ) • (G₂₁ *ᵥ x) + (-(star b)) • (G₂₂ *ᵥ y)) := by
        ext p
        cases p <;>
          simp [z, Matrix.fromBlocks_mulVec, Matrix.mulVec_smul, Matrix.mulVec_neg]
      rw [hstar, hmul, dotProduct_sumElim]
      simp only [dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      have ha' : star x ⬝ᵥ G₁₁ *ᵥ x = a := rfl
      have hb' : star x ⬝ᵥ G₁₂ *ᵥ y = b := rfl
      have hc' : star y ⬝ᵥ G₂₁ *ᵥ x = star b := hc_eq
      have hd' : star y ⬝ᵥ G₂₂ *ᵥ y = d := rfl
      rw [ha', hb', hc', hd']
      ring
    rw [hval] at hz
    have hbb : b * star b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hbb' : star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, hbb]
    have hre :
        (((t : ℂ) * (t : ℂ)) * a + (t : ℂ) * (-(star b)) * b +
            (-b) * (t : ℂ) * star b + (b * star b) * d).re =
          t ^ 2 * a.re - 2 * t * ‖b‖ ^ 2 + ‖b‖ ^ 2 * d.re := by
      have h1 : (t : ℂ) * (-(star b)) * b = -((t : ℂ) * ((‖b‖ ^ 2 : ℝ) : ℂ)) := by
        rw [← hbb']; ring
      have h2 : (-b) * (t : ℂ) * star b = -((t : ℂ) * ((‖b‖ ^ 2 : ℝ) : ℂ)) := by
        rw [← hbb]; ring
      rw [h1, h2, hbb]
      simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, ha_im, hd_im]
      ring
    linarith
  have hsq : ‖b‖ ^ 2 ≤ a.re * d.re := by
    rcases eq_or_lt_of_le ha_nonneg with ha0 | hapos
    · have h0 := hquad (d.re + 1)
      rw [← ha0] at h0
      nlinarith [sq_nonneg ‖b‖]
    · have h0 := hquad (‖b‖ ^ 2 / a.re)
      have hmul : a.re * ((‖b‖ ^ 2 / a.re) ^ 2 * a.re -
          2 * (‖b‖ ^ 2 / a.re) * ‖b‖ ^ 2 + ‖b‖ ^ 2 * d.re) =
          ‖b‖ ^ 2 * (a.re * d.re - ‖b‖ ^ 2) := by
        field_simp [ne_of_gt hapos]
        ring
      have hprod : 0 ≤ ‖b‖ ^ 2 * (a.re * d.re - ‖b‖ ^ 2) := by
        rw [← hmul]
        exact mul_nonneg hapos.le h0
      by_cases hb0 : ‖b‖ = 0
      · rw [hb0]; nlinarith
      · have hbpos : 0 < ‖b‖ ^ 2 := sq_pos_of_ne_zero hb0
        nlinarith
  exact (Real.le_sqrt (norm_nonneg b) (mul_nonneg ha_nonneg hd_nonneg)).mpr hsq

/-- Specialization of `Matrix.norm_quad_le_sqrt_of_fromBlocks_posSemidef` to a single
positive-semidefinite matrix `R`: `‖⟨x | R | y⟩‖ ≤ √(Re ⟨x | R | x⟩ · Re ⟨y | R | y⟩)`. -/
theorem Matrix.norm_quad_le_sqrt_of_posSemidef
    {β : Type*} [Fintype β] {R : Matrix β β ℂ} (hR : R.PosSemidef) (x y : β → ℂ) :
    ‖star x ⬝ᵥ R *ᵥ y‖ ≤
      Real.sqrt ((star x ⬝ᵥ R *ᵥ x).re * (star y ⬝ᵥ R *ᵥ y).re) := by
  have hblk : (Matrix.fromBlocks R R R R).PosSemidef := by
    convert hR.submatrix (Sum.elim id id) using 1
    ext p q
    cases p <;> cases q <;> rfl
  exact Matrix.norm_quad_le_sqrt_of_fromBlocks_posSemidef hblk x y

end ScalarCompression

/-! ## Section 2: Four-term coherence inequality on `N` copies -/

section FourTermBound

/-- **All-copy four-term rank-one coherence inequality.**
Given locally factorized rectangular CP maps `L, M` with `C(X ⊗ Y) = L(X) ⊗ M(Y)`,
a single-copy reverse-block certificate `S` (`C + S, C - S` CP, `S` coCP,
`C(|u⟩⟨u|) = S(|u⟩⟨u|)`), and arbitrary rank-one local filters `a₀, a₁, b₀, b₁` on
`N` output copies, the matrix `R_N = bipartiteCopies N (C(|u⟩⟨u|))` satisfies

  `‖⟨a₀ ⊗ b₀ | R_N | a₁ ⊗ b₁⟩‖ ≤ √(p₀₀ p₀₁) + √(p₁₀ p₁₁) + 2 √(p₀₁ p₁₀)`

with `pᵢⱼ = Re ⟨aᵢ ⊗ bⱼ | R_N | aᵢ ⊗ bⱼ⟩`. No invertibility, commutativity, or
nonvanishing assumption is made on the filters or on `L, M, u`. -/
theorem QuantumInfo.rankOne_coherence_four_term_le
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    [Fintype A_out] [DecidableEq A_out] [Fintype B_out] [DecidableEq B_out]
    {L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ}
    {M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ}
    {C S : Matrix (A_in × B_in) (A_in × B_in) ℂ →ₗ[ℂ] Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hL : IsKrausCP L) (hM : IsKrausCP M)
    (hC : ∀ X Y, C (X ⊗ₖ Y) = L X ⊗ₖ M Y)
    (hadd : IsKrausCP (C + S)) (hsub : IsKrausCP (C - S))
    (hcop : IsCompletelyCopositiveMap S)
    {u : A_in × B_in → ℂ}
    (hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)))
    (N : ℕ)
    (a₀ a₁ : (Fin N → A_out) → ℂ) (b₀ b₁ : (Fin N → B_out) → ℂ) :
    let R_N := QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u)))
    let p00 := (star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ R_N *ᵥ Matrix.vecKronecker a₀ b₀).re
    let p01 := (star (Matrix.vecKronecker a₀ b₁) ⬝ᵥ R_N *ᵥ Matrix.vecKronecker a₀ b₁).re
    let p10 := (star (Matrix.vecKronecker a₁ b₀) ⬝ᵥ R_N *ᵥ Matrix.vecKronecker a₁ b₀).re
    let p11 := (star (Matrix.vecKronecker a₁ b₁) ⬝ᵥ R_N *ᵥ Matrix.vecKronecker a₁ b₁).re
    ‖star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ R_N *ᵥ Matrix.vecKronecker a₁ b₁‖ ≤
      Real.sqrt (p00 * p01) + Real.sqrt (p10 * p11) + 2 * Real.sqrt (p01 * p10) := by
  intro R_N p00 p01 p10 p11
  let L_N := Matrix.piTensorMap (fun _ : Fin N => L)
  let M_N := Matrix.piTensorMap (fun _ : Fin N => M)
  let C_N := QuantumInfo.localTensorCopies N L M
  let u_N := QuantumInfo.bipartiteVecCopies N u
  have hCN_cp : IsKrausCP C_N := QuantumInfo.isKrausCP_localTensorCopies N hL hM
  have hLN_cp : IsKrausCP L_N := Matrix.isKrausCP_piTensorMap (fun _ => hL)
  have hMN_cp : IsKrausCP M_N := Matrix.isKrausCP_piTensorMap (fun _ => hM)
  let E₀ : Matrix (Fin N → A_in) (Fin N → A_in) ℂ :=
    Matrix.traceAdjointMap L_N (Matrix.vecMulVec a₀ (star a₀))
  let E₁ : Matrix (Fin N → A_in) (Fin N → A_in) ℂ :=
    Matrix.traceAdjointMap L_N (Matrix.vecMulVec a₁ (star a₁))
  let F₀ : Matrix (Fin N → B_in) (Fin N → B_in) ℂ :=
    Matrix.traceAdjointMap M_N (Matrix.vecMulVec b₀ (star b₀))
  let F₁ : Matrix (Fin N → B_in) (Fin N → B_in) ℂ :=
    Matrix.traceAdjointMap M_N (Matrix.vecMulVec b₁ (star b₁))
  have hE₀ : E₀.PosSemidef :=
    hLN_cp.traceAdjointMap_isKrausCP.map_posSemidef (Matrix.posSemidef_vecMulVec_self_star a₀)
  have hE₁ : E₁.PosSemidef :=
    hLN_cp.traceAdjointMap_isKrausCP.map_posSemidef (Matrix.posSemidef_vecMulVec_self_star a₁)
  have hF₀ : F₀.PosSemidef :=
    hMN_cp.traceAdjointMap_isKrausCP.map_posSemidef (Matrix.posSemidef_vecMulVec_self_star b₀)
  have hF₁ : F₁.PosSemidef :=
    hMN_cp.traceAdjointMap_isKrausCP.map_posSemidef (Matrix.posSemidef_vecMulVec_self_star b₁)
  obtain ⟨v, w, hvw, hcross, hdiff⟩ :=
    Matrix.exists_twoForms_bipartite_split hE₀ hE₁ u_N ![F₀, F₁]
      (fun j => by fin_cases j <;> assumption)
  let R_vv := C_N (Matrix.vecMulVec v (star v))
  let R_ww := C_N (Matrix.vecMulVec w (star w))
  let R_wv := C_N (Matrix.vecMulVec w (star v))
  let R_vw := C_N (Matrix.vecMulVec v (star w))
  have hR_N_eq : R_N = C_N (Matrix.vecMulVec u_N (star u_N)) :=
    (QuantumInfo.localTensorCopies_vecMulVec_eq_bipartiteCopies N L M C hC u).symm
  have hsplit : R_N = R_vv + R_ww + R_wv + R_vw := by
    rw [hR_N_eq, ← hvw]
    have houter :
        Matrix.vecMulVec (v + w) (star (v + w)) =
          Matrix.vecMulVec v (star v) + Matrix.vecMulVec w (star w) +
            Matrix.vecMulVec w (star v) + Matrix.vecMulVec v (star w) := by
      ext i j
      simp only [Matrix.vecMulVec_apply, Pi.add_apply, Pi.star_apply, star_add, Matrix.add_apply]
      ring
    rw [houter]
    simp only [map_add, R_vv, R_ww, R_wv, R_vw]
  have hpull : ∀ (a : (Fin N → A_out) → ℂ) (b : (Fin N → B_out) → ℂ)
      (x y : (Fin N → A_in) × (Fin N → B_in) → ℂ),
      star (Matrix.vecKronecker a b) ⬝ᵥ
          C_N (Matrix.vecMulVec x (star y)) *ᵥ Matrix.vecKronecker a b =
        star y ⬝ᵥ (Matrix.traceAdjointMap L_N (Matrix.vecMulVec a (star a)) ⊗ₖ
          Matrix.traceAdjointMap M_N (Matrix.vecMulVec b (star b))) *ᵥ x := by
    intro a b x y
    rw [← Matrix.trace_vecMulVec_mul, Matrix.vecMulVec_vecKronecker,
      QuantumInfo.trace_kronecker_mul_localTensorCopies, Matrix.trace_mul_comm,
      Matrix.trace_vecMulVec_mul]
  let x00 := Matrix.vecKronecker a₀ b₀
  let x01 := Matrix.vecKronecker a₀ b₁
  let x10 := Matrix.vecKronecker a₁ b₀
  let x11 := Matrix.vecKronecker a₁ b₁
  let a00 := (star x00 ⬝ᵥ R_vv *ᵥ x00).re
  let a01 := (star x01 ⬝ᵥ R_vv *ᵥ x01).re
  let a10 := (star x10 ⬝ᵥ R_vv *ᵥ x10).re
  let a11 := (star x11 ⬝ᵥ R_vv *ᵥ x11).re
  let b00 := (star x00 ⬝ᵥ R_ww *ᵥ x00).re
  let b01 := (star x01 ⬝ᵥ R_ww *ᵥ x01).re
  let b10 := (star x10 ⬝ᵥ R_ww *ᵥ x10).re
  let b11 := (star x11 ⬝ᵥ R_ww *ᵥ x11).re
  have hRvv_psd : R_vv.PosSemidef := hCN_cp.map_posSemidef (Matrix.posSemidef_vecMulVec_self_star v)
  have hRww_psd : R_ww.PosSemidef := hCN_cp.map_posSemidef (Matrix.posSemidef_vecMulVec_self_star w)
  have ha00_nn : 0 ≤ a00 := (Complex.nonneg_iff.mp (hRvv_psd.dotProduct_mulVec_nonneg x00)).1
  have ha01_nn : 0 ≤ a01 := (Complex.nonneg_iff.mp (hRvv_psd.dotProduct_mulVec_nonneg x01)).1
  have ha10_nn : 0 ≤ a10 := (Complex.nonneg_iff.mp (hRvv_psd.dotProduct_mulVec_nonneg x10)).1
  have ha11_nn : 0 ≤ a11 := (Complex.nonneg_iff.mp (hRvv_psd.dotProduct_mulVec_nonneg x11)).1
  have hb00_nn : 0 ≤ b00 := (Complex.nonneg_iff.mp (hRww_psd.dotProduct_mulVec_nonneg x00)).1
  have hb01_nn : 0 ≤ b01 := (Complex.nonneg_iff.mp (hRww_psd.dotProduct_mulVec_nonneg x01)).1
  have hb10_nn : 0 ≤ b10 := (Complex.nonneg_iff.mp (hRww_psd.dotProduct_mulVec_nonneg x10)).1
  have hb11_nn : 0 ≤ b11 := (Complex.nonneg_iff.mp (hRww_psd.dotProduct_mulVec_nonneg x11)).1
  have hp00_eq : p00 = a00 + b00 := by
    have h1 : star x00 ⬝ᵥ R_N *ᵥ x00 =
        star x00 ⬝ᵥ R_vv *ᵥ x00 + star x00 ⬝ᵥ R_ww *ᵥ x00 +
          star x00 ⬝ᵥ R_wv *ᵥ x00 + star x00 ⬝ᵥ R_vw *ᵥ x00 := by
      rw [hsplit]; simp [Matrix.add_mulVec, dotProduct_add]
    have hcwv : star x00 ⬝ᵥ R_wv *ᵥ x00 = 0 := by
      simpa [x00, R_wv, E₀, F₀, hpull] using (hcross 0).2.2.1
    have hcvw : star x00 ⬝ᵥ R_vw *ᵥ x00 = 0 := by
      simpa [x00, R_vw, E₀, F₀, hpull] using (hcross 0).1
    have hsum : star x00 ⬝ᵥ R_N *ᵥ x00 = star x00 ⬝ᵥ R_vv *ᵥ x00 + star x00 ⬝ᵥ R_ww *ᵥ x00 := by
      rw [h1, hcwv, hcvw, add_zero, add_zero]
    exact congrArg Complex.re hsum
  have hp01_eq : p01 = a01 + b01 := by
    have h1 : star x01 ⬝ᵥ R_N *ᵥ x01 =
        star x01 ⬝ᵥ R_vv *ᵥ x01 + star x01 ⬝ᵥ R_ww *ᵥ x01 +
          star x01 ⬝ᵥ R_wv *ᵥ x01 + star x01 ⬝ᵥ R_vw *ᵥ x01 := by
      rw [hsplit]; simp [Matrix.add_mulVec, dotProduct_add]
    have hcwv : star x01 ⬝ᵥ R_wv *ᵥ x01 = 0 := by
      simpa [x01, R_wv, E₀, F₁, hpull] using (hcross 1).2.2.1
    have hcvw : star x01 ⬝ᵥ R_vw *ᵥ x01 = 0 := by
      simpa [x01, R_vw, E₀, F₁, hpull] using (hcross 1).1
    have hsum : star x01 ⬝ᵥ R_N *ᵥ x01 = star x01 ⬝ᵥ R_vv *ᵥ x01 + star x01 ⬝ᵥ R_ww *ᵥ x01 := by
      rw [h1, hcwv, hcvw, add_zero, add_zero]
    exact congrArg Complex.re hsum
  have hp10_eq : p10 = a10 + b10 := by
    have h1 : star x10 ⬝ᵥ R_N *ᵥ x10 =
        star x10 ⬝ᵥ R_vv *ᵥ x10 + star x10 ⬝ᵥ R_ww *ᵥ x10 +
          star x10 ⬝ᵥ R_wv *ᵥ x10 + star x10 ⬝ᵥ R_vw *ᵥ x10 := by
      rw [hsplit]; simp [Matrix.add_mulVec, dotProduct_add]
    have hcwv : star x10 ⬝ᵥ R_wv *ᵥ x10 = 0 := by
      simpa [x10, R_wv, E₁, F₀, hpull] using (hcross 0).2.2.2
    have hcvw : star x10 ⬝ᵥ R_vw *ᵥ x10 = 0 := by
      simpa [x10, R_vw, E₁, F₀, hpull] using (hcross 0).2.1
    have hsum : star x10 ⬝ᵥ R_N *ᵥ x10 = star x10 ⬝ᵥ R_vv *ᵥ x10 + star x10 ⬝ᵥ R_ww *ᵥ x10 := by
      rw [h1, hcwv, hcvw, add_zero, add_zero]
    exact congrArg Complex.re hsum
  have hp11_eq : p11 = a11 + b11 := by
    have h1 : star x11 ⬝ᵥ R_N *ᵥ x11 =
        star x11 ⬝ᵥ R_vv *ᵥ x11 + star x11 ⬝ᵥ R_ww *ᵥ x11 +
          star x11 ⬝ᵥ R_wv *ᵥ x11 + star x11 ⬝ᵥ R_vw *ᵥ x11 := by
      rw [hsplit]; simp [Matrix.add_mulVec, dotProduct_add]
    have hcwv : star x11 ⬝ᵥ R_wv *ᵥ x11 = 0 := by
      simpa [x11, R_wv, E₁, F₁, hpull] using (hcross 1).2.2.2
    have hcvw : star x11 ⬝ᵥ R_vw *ᵥ x11 = 0 := by
      simpa [x11, R_vw, E₁, F₁, hpull] using (hcross 1).2.1
    have hsum : star x11 ⬝ᵥ R_N *ᵥ x11 = star x11 ⬝ᵥ R_vv *ᵥ x11 + star x11 ⬝ᵥ R_ww *ᵥ x11 := by
      rw [h1, hcwv, hcvw, add_zero, add_zero]
    exact congrArg Complex.re hsum
  have ha11_le_a01 : a11 ≤ a01 := by
    have h := (Complex.nonneg_iff.mp (hdiff 1).1).1
    have hsub_eq : (E₀ - E₁) ⊗ₖ F₁ = E₀ ⊗ₖ F₁ - E₁ ⊗ₖ F₁ := by
      ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
      simp [Matrix.kroneckerMap_apply, sub_mul]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, hsub_eq, Matrix.sub_mulVec,
      dotProduct_sub, Complex.sub_re] at h
    have ha01' : (star v ⬝ᵥ (E₀ ⊗ₖ F₁) *ᵥ v).re = a01 := by
      simpa [a01, x01, R_vv, E₀, F₁] using (congrArg Complex.re (hpull a₀ b₁ v v)).symm
    have ha11' : (star v ⬝ᵥ (E₁ ⊗ₖ F₁) *ᵥ v).re = a11 := by
      simpa [a11, x11, R_vv, E₁, F₁] using (congrArg Complex.re (hpull a₁ b₁ v v)).symm
    linarith
  have hb00_le_b10 : b00 ≤ b10 := by
    have h := (Complex.nonneg_iff.mp (hdiff 0).2).1
    have hsub_eq : (E₁ - E₀) ⊗ₖ F₀ = E₁ ⊗ₖ F₀ - E₀ ⊗ₖ F₀ := by
      ext ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
      simp [Matrix.kroneckerMap_apply, sub_mul]
    simp only [Matrix.cons_val_zero, hsub_eq, Matrix.sub_mulVec,
      dotProduct_sub, Complex.sub_re] at h
    have hb00' : (star w ⬝ᵥ (E₀ ⊗ₖ F₀) *ᵥ w).re = b00 := by
      simpa [b00, x00, R_ww, E₀, F₀] using (congrArg Complex.re (hpull a₀ b₀ w w)).symm
    have hb10' : (star w ⬝ᵥ (E₁ ⊗ₖ F₀) *ᵥ w).re = b10 := by
      simpa [b10, x10, R_ww, E₁, F₀] using (congrArg Complex.re (hpull a₁ b₀ w w)).symm
    linarith
  have h1 : ‖star x00 ⬝ᵥ R_vv *ᵥ x11‖ ≤ Real.sqrt (a00 * a11) :=
    Matrix.norm_quad_le_sqrt_of_posSemidef hRvv_psd x00 x11
  have h2 : ‖star x00 ⬝ᵥ R_ww *ᵥ x11‖ ≤ Real.sqrt (b00 * b11) :=
    Matrix.norm_quad_le_sqrt_of_posSemidef hRww_psd x00 x11
  have h3 : ‖star x00 ⬝ᵥ R_wv *ᵥ x11‖ ≤ Real.sqrt (b00 * a11) := by
    have hblk_in :
        (Matrix.fromBlocks
          (Matrix.vecMulVec w (star w)) (Matrix.vecMulVec w (star v))
          (Matrix.vecMulVec v (star w)) (Matrix.vecMulVec v (star v))).PosSemidef := by
      convert Matrix.posSemidef_vecMulVec_self_star (Sum.elim w v) using 1
      ext p q
      cases p <;> cases q <;> simp [Matrix.vecMulVec_apply]
    have hblk_out := hCN_cp.fromBlocks_posSemidef hblk_in
    exact Matrix.norm_quad_le_sqrt_of_fromBlocks_posSemidef hblk_out x00 x11
  have h4 : ‖star x00 ⬝ᵥ R_vw *ᵥ x11‖ ≤ Real.sqrt (b00 * a11) := by
    let eIn := Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => A_in) (fun _ => B_in)
    let eOut := Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => A_out) (fun _ => B_out)
    let v' : (Fin N → A_in × B_in) → ℂ := fun x => v (eIn x)
    let w' : (Fin N → A_in × B_in) → ℂ := fun x => w (eIn x)
    have hvw' : v' + w' = fun x => ∏ i : Fin N, u (x i) := by
      funext x
      have hx := congrFun hvw (eIn x)
      simpa [v', w', u_N, QuantumInfo.bipartiteVecCopies, eIn] using hx
    have hrev := piTensorMap_const_reverseBlock_posSemidef N hadd hsub hcop hu hvw'
    have hrev_party : (Matrix.fromBlocks R_ww R_vw R_wv R_vv).PosSemidef := by
      convert hrev.submatrix (Sum.map eOut.symm eOut.symm) using 1
      have hre : ∀ (p q : (Fin N → A_in) × (Fin N → B_in) → ℂ),
          C_N (Matrix.vecMulVec p (star q)) =
            (Matrix.piTensorMap (fun _ : Fin N => C)
              (Matrix.vecMulVec (fun x => p (eIn x)) (star (fun x => q (eIn x))))).submatrix
              eOut.symm eOut.symm := by
        intro p q
        rw [QuantumInfo.localTensorCopies_eq_piTensorMap_reindex N L M C hC]
        rfl
      ext s t
      cases s <;> cases t <;> simp [R_ww, R_vw, R_wv, R_vv, hre, v', w']
    exact Matrix.norm_quad_le_sqrt_of_fromBlocks_posSemidef hrev_party x00 x11
  have htri :
      ‖star x00 ⬝ᵥ R_N *ᵥ x11‖ ≤
        ‖star x00 ⬝ᵥ R_vv *ᵥ x11‖ + ‖star x00 ⬝ᵥ R_ww *ᵥ x11‖ +
          ‖star x00 ⬝ᵥ R_wv *ᵥ x11‖ + ‖star x00 ⬝ᵥ R_vw *ᵥ x11‖ := by
    have hsum :
        star x00 ⬝ᵥ R_N *ᵥ x11 =
          star x00 ⬝ᵥ R_vv *ᵥ x11 + star x00 ⬝ᵥ R_ww *ᵥ x11 +
            star x00 ⬝ᵥ R_wv *ᵥ x11 + star x00 ⬝ᵥ R_vw *ᵥ x11 := by
      rw [hsplit]; simp [Matrix.add_mulVec, dotProduct_add]
    rw [hsum]
    calc
      ‖star x00 ⬝ᵥ R_vv *ᵥ x11 + star x00 ⬝ᵥ R_ww *ᵥ x11 +
          star x00 ⬝ᵥ R_wv *ᵥ x11 + star x00 ⬝ᵥ R_vw *ᵥ x11‖
        ≤ ‖star x00 ⬝ᵥ R_vv *ᵥ x11 + star x00 ⬝ᵥ R_ww *ᵥ x11 +
            star x00 ⬝ᵥ R_wv *ᵥ x11‖ + ‖star x00 ⬝ᵥ R_vw *ᵥ x11‖ := norm_add_le _ _
      _ ≤ ‖star x00 ⬝ᵥ R_vv *ᵥ x11 + star x00 ⬝ᵥ R_ww *ᵥ x11‖ +
            ‖star x00 ⬝ᵥ R_wv *ᵥ x11‖ + ‖star x00 ⬝ᵥ R_vw *ᵥ x11‖ := by
          linarith [norm_add_le (star x00 ⬝ᵥ R_vv *ᵥ x11 + star x00 ⬝ᵥ R_ww *ᵥ x11)
            (star x00 ⬝ᵥ R_wv *ᵥ x11)]
      _ ≤ ‖star x00 ⬝ᵥ R_vv *ᵥ x11‖ + ‖star x00 ⬝ᵥ R_ww *ᵥ x11‖ +
            ‖star x00 ⬝ᵥ R_wv *ᵥ x11‖ + ‖star x00 ⬝ᵥ R_vw *ᵥ x11‖ := by
          linarith [norm_add_le (star x00 ⬝ᵥ R_vv *ᵥ x11) (star x00 ⬝ᵥ R_ww *ᵥ x11)]
  have ha00_le : a00 ≤ p00 := by linarith
  have ha11_le : a11 ≤ p01 := by linarith
  have hb00_le : b00 ≤ p10 := by linarith
  have hb11_le : b11 ≤ p11 := by linarith
  have hs1 : Real.sqrt (a00 * a11) ≤ Real.sqrt (p00 * p01) :=
    Real.sqrt_le_sqrt (mul_le_mul ha00_le ha11_le ha11_nn (by linarith))
  have hs2 : Real.sqrt (b00 * b11) ≤ Real.sqrt (p10 * p11) :=
    Real.sqrt_le_sqrt (mul_le_mul hb00_le hb11_le hb11_nn (by linarith))
  have hs3 : Real.sqrt (b00 * a11) ≤ Real.sqrt (p01 * p10) := by
    rw [mul_comm p01 p10]
    exact Real.sqrt_le_sqrt (mul_le_mul hb00_le ha11_le ha11_nn (by linarith))
  linarith

end FourTermBound

/-! ## Section 3: Sharp `k ^ 4 ≤ p₀₀ p₀₁ p₁₀ p₁₁` bound via rescaling and amplification -/

section SharpCoherenceBound

/-- **Sharp all-copy rank-one coherence inequality for `C(|u⟩⟨u|)`.**
Under the single-copy local-factorization and reverse-block hypotheses, for every `N : ℕ`
and arbitrary local filter vectors `a₀, a₁, b₀, b₁`,

  `‖⟨a₀ ⊗ b₀ | R_N | a₁ ⊗ b₁⟩‖ ^ 4 ≤ p₀₀ * p₀₁ * p₁₀ * p₁₁`

where `R_N = bipartiteCopies N (C(|u⟩⟨u|))` and `pᵢⱼ = Re ⟨aᵢ ⊗ bⱼ | R_N | aᵢ ⊗ bⱼ⟩`. -/
theorem QuantumInfo.rankOne_coherence_pow_four_le
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    [Fintype A_out] [DecidableEq A_out] [Fintype B_out] [DecidableEq B_out]
    {L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ}
    {M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ}
    {C S : Matrix (A_in × B_in) (A_in × B_in) ℂ →ₗ[ℂ] Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hL : IsKrausCP L) (hM : IsKrausCP M)
    (hC : ∀ X Y, C (X ⊗ₖ Y) = L X ⊗ₖ M Y)
    (hadd : IsKrausCP (C + S)) (hsub : IsKrausCP (C - S))
    (hcop : IsCompletelyCopositiveMap S)
    {u : A_in × B_in → ℂ}
    (hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)))
    (N : ℕ)
    (a₀ a₁ : (Fin N → A_out) → ℂ) (b₀ b₁ : (Fin N → B_out) → ℂ) :
    let R_N := QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u)))
    let p00 := (star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ R_N *ᵥ Matrix.vecKronecker a₀ b₀).re
    let p01 := (star (Matrix.vecKronecker a₀ b₁) ⬝ᵥ R_N *ᵥ Matrix.vecKronecker a₀ b₁).re
    let p10 := (star (Matrix.vecKronecker a₁ b₀) ⬝ᵥ R_N *ᵥ Matrix.vecKronecker a₁ b₀).re
    let p11 := (star (Matrix.vecKronecker a₁ b₁) ⬝ᵥ R_N *ᵥ Matrix.vecKronecker a₁ b₁).re
    ‖star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ R_N *ᵥ Matrix.vecKronecker a₁ b₁‖ ^ 4 ≤
      p00 * p01 * p10 * p11 := by
  intro R_N p00 p01 p10 p11
  set R₁ := C (Matrix.vecMulVec u (star u))
  have hCN_cp : IsKrausCP (QuantumInfo.localTensorCopies N L M) :=
    QuantumInfo.isKrausCP_localTensorCopies N hL hM
  have hRN_psd : R_N.PosSemidef := by
    rw [show R_N = QuantumInfo.localTensorCopies N L M
        (Matrix.vecMulVec (QuantumInfo.bipartiteVecCopies N u)
          (star (QuantumInfo.bipartiteVecCopies N u))) from
      (QuantumInfo.localTensorCopies_vecMulVec_eq_bipartiteCopies N L M C hC u).symm]
    exact hCN_cp.map_posSemidef (Matrix.posSemidef_vecMulVec_self_star _)
  have hp00_nn : 0 ≤ p00 := (Complex.nonneg_iff.mp (hRN_psd.dotProduct_mulVec_nonneg _)).1
  have hp01_nn : 0 ≤ p01 := (Complex.nonneg_iff.mp (hRN_psd.dotProduct_mulVec_nonneg _)).1
  have hp10_nn : 0 ≤ p10 := (Complex.nonneg_iff.mp (hRN_psd.dotProduct_mulVec_nonneg _)).1
  have hp11_nn : 0 ≤ p11 := (Complex.nonneg_iff.mp (hRN_psd.dotProduct_mulVec_nonneg _)).1
  have hdiag :
      ‖star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ R_N *ᵥ Matrix.vecKronecker a₁ b₁‖ ≤
        Real.sqrt (p00 * p11) :=
    Matrix.norm_quad_le_sqrt_of_posSemidef hRN_psd _ _
  have hre_pow : ∀ {z : ℂ}, 0 ≤ z → ∀ t : ℕ, (z ^ t).re = z.re ^ t := by
    intro z hz t
    have hz_eq : z = (z.re : ℂ) := Complex.ext rfl (by simp [(Complex.nonneg_iff.mp hz).2.symm])
    conv_lhs => rw [hz_eq]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  refine Real.pow_four_le_of_rescaled_four_term_bound
    (norm_nonneg _) hp00_nn hp01_nn hp10_nn hp11_nn hdiag fun t _ lam hlam => ?_
  set s : ℝ := Real.sqrt lam
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hlam
  have hs_sq : s * s = lam := Real.mul_self_sqrt hlam.le
  let a0' : (Fin (N * t) → A_out) → ℂ := (s : ℂ) • QuantumInfo.vecPower t a₀
  let a1' : (Fin (N * t) → A_out) → ℂ := ((s⁻¹ : ℝ) : ℂ) • QuantumInfo.vecPower t a₁
  let b0' : (Fin (N * t) → B_out) → ℂ := QuantumInfo.vecPower t b₀
  let b1' : (Fin (N * t) → B_out) → ℂ := QuantumInfo.vecPower t b₁
  have h4 := QuantumInfo.rankOne_coherence_four_term_le hL hM hC hadd hsub hcop hu
    (N * t) a0' a1' b0' b1'
  have hkron_smul : ∀ (c : ℂ) (f : (Fin (N * t) → A_out) → ℂ) (g : (Fin (N * t) → B_out) → ℂ),
      Matrix.vecKronecker (c • f) g = c • Matrix.vecKronecker f g := by
    intro c f g; ext ⟨i, j⟩; simp [Matrix.vecKronecker_apply, mul_assoc]
  have hk_eq :
      ‖star (Matrix.vecKronecker a0' b0') ⬝ᵥ QuantumInfo.bipartiteCopies (N * t) R₁ *ᵥ
          Matrix.vecKronecker a1' b1'‖ =
        ‖star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ R_N *ᵥ Matrix.vecKronecker a₁ b₁‖ ^ t := by
    simp only [a0', a1', b0', b1', hkron_smul, star_smul, Matrix.mulVec_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    rw [QuantumInfo.quad_bipartiteCopies_mul_vecPower]
    have hcancel :
        ((s⁻¹ : ℝ) : ℂ) * ((s : ℂ) *
          (star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ QuantumInfo.bipartiteCopies N R₁ *ᵥ
            Matrix.vecKronecker a₁ b₁) ^ t) =
        (star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ R_N *ᵥ Matrix.vecKronecker a₁ b₁) ^ t := by
      rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hs_pos),
        Complex.ofReal_one, one_mul]
    rw [hcancel, norm_pow]
  have hp_smul : ∀ (c : ℝ) (f : (Fin N → A_out) → ℂ) (g : (Fin N → B_out) → ℂ),
      (star (Matrix.vecKronecker ((c : ℂ) • QuantumInfo.vecPower t f)
            (QuantumInfo.vecPower t g)) ⬝ᵥ
          QuantumInfo.bipartiteCopies (N * t) R₁ *ᵥ
            Matrix.vecKronecker ((c : ℂ) • QuantumInfo.vecPower t f)
              (QuantumInfo.vecPower t g)).re =
        (c * c) *
          ((star (Matrix.vecKronecker f g) ⬝ᵥ R_N *ᵥ Matrix.vecKronecker f g).re) ^ t := by
    intro c f g
    simp only [hkron_smul, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    rw [QuantumInfo.quad_bipartiteCopies_mul_vecPower, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.re_ofReal_mul, hre_pow (hRN_psd.dotProduct_mulVec_nonneg _) t]
  have hp00_t :
      (star (Matrix.vecKronecker a0' b0') ⬝ᵥ QuantumInfo.bipartiteCopies (N * t) R₁ *ᵥ
          Matrix.vecKronecker a0' b0').re = lam * p00 ^ t := by
    simpa [a0', b0', hs_sq] using hp_smul s a₀ b₀
  have hp01_t :
      (star (Matrix.vecKronecker a0' b1') ⬝ᵥ QuantumInfo.bipartiteCopies (N * t) R₁ *ᵥ
          Matrix.vecKronecker a0' b1').re = lam * p01 ^ t := by
    simpa [a0', b1', hs_sq] using hp_smul s a₀ b₁
  have hp10_t :
      (star (Matrix.vecKronecker a1' b0') ⬝ᵥ QuantumInfo.bipartiteCopies (N * t) R₁ *ᵥ
          Matrix.vecKronecker a1' b0').re = lam⁻¹ * p10 ^ t := by
    have hinv : s⁻¹ * s⁻¹ = lam⁻¹ := by
      rw [← mul_inv, hs_sq]
    have h := hp_smul s⁻¹ a₁ b₀
    rw [hinv] at h
    exact h
  have hp11_t :
      (star (Matrix.vecKronecker a1' b1') ⬝ᵥ QuantumInfo.bipartiteCopies (N * t) R₁ *ᵥ
          Matrix.vecKronecker a1' b1').re = lam⁻¹ * p11 ^ t := by
    have hinv : s⁻¹ * s⁻¹ = lam⁻¹ := by
      rw [← mul_inv, hs_sq]
    have h := hp_smul s⁻¹ a₁ b₁
    rw [hinv] at h
    exact h
  dsimp only at h4
  rw [hk_eq, hp00_t, hp01_t, hp10_t, hp11_t] at h4
  have ht1 : Real.sqrt (lam * p00 ^ t * (lam * p01 ^ t)) =
      lam * Real.sqrt (p00 ^ t * p01 ^ t) := by
    rw [show lam * p00 ^ t * (lam * p01 ^ t) = (lam * lam) * (p00 ^ t * p01 ^ t) by ring,
      Real.sqrt_mul (mul_nonneg hlam.le hlam.le), Real.sqrt_mul_self hlam.le]
  have ht2 : Real.sqrt (lam⁻¹ * p10 ^ t * (lam⁻¹ * p11 ^ t)) =
      lam⁻¹ * Real.sqrt (p10 ^ t * p11 ^ t) := by
    rw [show lam⁻¹ * p10 ^ t * (lam⁻¹ * p11 ^ t) = (lam⁻¹ * lam⁻¹) * (p10 ^ t * p11 ^ t) by ring,
      Real.sqrt_mul (mul_nonneg (inv_nonneg.mpr hlam.le) (inv_nonneg.mpr hlam.le)),
      Real.sqrt_mul_self (inv_nonneg.mpr hlam.le)]
  have ht3 : Real.sqrt (lam * p01 ^ t * (lam⁻¹ * p10 ^ t)) = Real.sqrt (p01 ^ t * p10 ^ t) := by
    congr 1
    field_simp [ne_of_gt hlam]
  rw [ht1, ht2, ht3] at h4
  exact h4

/-- **Sharp all-copy rank-one coherence inequality for any nonnegative multiple
`ρ = c • C(|u⟩⟨u|)`.** Covers both normalized states `ρ = (tr C(|u⟩⟨u|))⁻¹ • C(|u⟩⟨u|)`
and unnormalized / zero multiples `c = 0`. -/
theorem QuantumInfo.rankOne_coherence_pow_four_le_of_smul
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    [Fintype A_out] [DecidableEq A_out] [Fintype B_out] [DecidableEq B_out]
    {L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ}
    {M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ}
    {C S : Matrix (A_in × B_in) (A_in × B_in) ℂ →ₗ[ℂ] Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hL : IsKrausCP L) (hM : IsKrausCP M)
    (hC : ∀ X Y, C (X ⊗ₖ Y) = L X ⊗ₖ M Y)
    (hadd : IsKrausCP (C + S)) (hsub : IsKrausCP (C - S))
    (hcop : IsCompletelyCopositiveMap S)
    {u : A_in × B_in → ℂ}
    (hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)))
    {c : ℝ} (hc : 0 ≤ c)
    {ρ : Matrix (A_out × B_out) (A_out × B_out) ℂ}
    (hρ : ρ = (c : ℂ) • C (Matrix.vecMulVec u (star u)))
    (N : ℕ)
    (a₀ a₁ : (Fin N → A_out) → ℂ) (b₀ b₁ : (Fin N → B_out) → ℂ) :
    let ρ_N := QuantumInfo.bipartiteCopies N ρ
    let p00 := (star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ ρ_N *ᵥ Matrix.vecKronecker a₀ b₀).re
    let p01 := (star (Matrix.vecKronecker a₀ b₁) ⬝ᵥ ρ_N *ᵥ Matrix.vecKronecker a₀ b₁).re
    let p10 := (star (Matrix.vecKronecker a₁ b₀) ⬝ᵥ ρ_N *ᵥ Matrix.vecKronecker a₁ b₀).re
    let p11 := (star (Matrix.vecKronecker a₁ b₁) ⬝ᵥ ρ_N *ᵥ Matrix.vecKronecker a₁ b₁).re
    ‖star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ ρ_N *ᵥ Matrix.vecKronecker a₁ b₁‖ ^ 4 ≤
      p00 * p01 * p10 * p11 := by
  intro ρ_N p00 p01 p10 p11
  have hbase := QuantumInfo.rankOne_coherence_pow_four_le hL hM hC hadd hsub hcop hu
    N a₀ a₁ b₀ b₁
  dsimp only at hbase
  have hρN :
      ρ_N = ((c ^ N : ℝ) : ℂ) •
        QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u))) := by
    simp only [ρ_N, hρ, QuantumInfo.bipartiteCopies_smul, Complex.ofReal_pow]
  have hsmul_norm :
      ‖star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ ρ_N *ᵥ Matrix.vecKronecker a₁ b₁‖ =
        (c ^ N) * ‖star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ
          QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u))) *ᵥ
            Matrix.vecKronecker a₁ b₁‖ := by
    rw [hρN, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (pow_nonneg hc N)]
  have hsmul_re : ∀ (x : (Fin N → A_out) × (Fin N → B_out) → ℂ),
      (star x ⬝ᵥ ρ_N *ᵥ x).re =
        (c ^ N) * (star x ⬝ᵥ
          QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u))) *ᵥ x).re := by
    intro x
    rw [hρN, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  rw [hsmul_norm, mul_pow]
  change (c ^ N) ^ 4 * _ ≤ _
  simp only [p00, p01, p10, p11, hsmul_re]
  have hfac :
      (c ^ N) * (star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ
          QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u))) *ᵥ
            Matrix.vecKronecker a₀ b₀).re *
        ((c ^ N) * (star (Matrix.vecKronecker a₀ b₁) ⬝ᵥ
          QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u))) *ᵥ
            Matrix.vecKronecker a₀ b₁).re) *
        ((c ^ N) * (star (Matrix.vecKronecker a₁ b₀) ⬝ᵥ
          QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u))) *ᵥ
            Matrix.vecKronecker a₁ b₀).re) *
        ((c ^ N) * (star (Matrix.vecKronecker a₁ b₁) ⬝ᵥ
          QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u))) *ᵥ
            Matrix.vecKronecker a₁ b₁).re) =
      (c ^ N) ^ 4 *
        ((star (Matrix.vecKronecker a₀ b₀) ⬝ᵥ
          QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u))) *ᵥ
            Matrix.vecKronecker a₀ b₀).re *
        (star (Matrix.vecKronecker a₀ b₁) ⬝ᵥ
          QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u))) *ᵥ
            Matrix.vecKronecker a₀ b₁).re *
        (star (Matrix.vecKronecker a₁ b₀) ⬝ᵥ
          QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u))) *ᵥ
            Matrix.vecKronecker a₁ b₀).re *
        (star (Matrix.vecKronecker a₁ b₁) ⬝ᵥ
          QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u))) *ᵥ
            Matrix.vecKronecker a₁ b₁).re) := by ring
  rw [hfac]
  exact mul_le_mul_of_nonneg_left hbase (pow_nonneg (pow_nonneg hc N) 4)

end SharpCoherenceBound
