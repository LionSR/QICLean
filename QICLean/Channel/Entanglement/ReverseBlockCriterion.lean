/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Basic
import QICLean.Channel.Choi.RectangularChoi
import QICLean.Analysis.Order.FiniteKroneckerOrder

/-!
# Map-level reverse-block criterion and finite tensor-product extension

This file develops the general, ansatz-independent reverse-block positivity criterion
for finite rectangular linear maps on complex matrix algebras, generalizing Lemma 4
(`lem:reverse`) of arXiv:2611.34921 from real vectors and square dimension-8 maps to
arbitrary finite rectangular matrix spaces and arbitrary complex vectors.

The development separates cleanly into three layers:

1. **Generic CP pure-input vanishing and 2×2 block lifting (map-level, no Choi):**
   * `Matrix.mul_vecMulVec_mul_conjTranspose`: conjugation of a rank-one outer product
     `|z⟩⟨u|` by a rectangular matrix `A` yields `|A z⟩⟨A u|`.
   * `IsKrausCP.map_vecMulVec_right_eq_zero`, `IsKrausCP.map_vecMulVec_left_eq_zero`:
     if `D` is completely positive and `D(|u⟩⟨u|) = 0`, then `D(|z⟩⟨u|) = D(|u⟩⟨z|) = 0`
     for every complex vector `z`.
   * `IsKrausCP.fromBlocks_posSemidef`: rectangular Kraus-CP maps preserve positive
     semidefiniteness of `2 × 2` block matrices.
   * `IsCompletelyCopositiveMap.reverseBlock_vecMulVec_posSemidef`: a completely
     copositive map `S` satisfies `[[S(|u⟩⟨u|), S(|z⟩⟨u|)], [S(|u⟩⟨z|), S(|z⟩⟨z|)]] ≥ 0`
     for all complex vectors `u, z`.

2. **One-copy reverse-block criterion (minimal hypotheses, no Choi):**
   * `reverseBlock_posSemidef`: for arbitrary finite rectangular linear maps
     `C, S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ`, if `IsKrausCP (C - S)`,
     `IsCompletelyCopositiveMap S`, and `C (|u⟩⟨u|) = S (|u⟩⟨u|)`, then for all
     complex vectors `v, w` with `v + w = u`, the reverse-block matrix
     `[[C(|w⟩⟨w|), C(|v⟩⟨w|)], [C(|w⟩⟨v|), C(|v⟩⟨v|)]]` is positive semidefinite.
     Complete positivity of `C + S` (or of `C`) is not needed for this one-copy step.

3. **Finite tensor-product extension under two-sided CP domination:**
   * `Matrix.piTensorMap`: the finite tensor product `⊗ₖ Φₖ` of rectangular linear maps.
   * `Matrix.isKrausCP_iff_rectangularChoi_posSemidef`: unnormalized rectangular Choi
     characterization of `IsKrausCP` for arbitrary finite (possibly empty) spaces.
   * `Matrix.isKrausCP_piTensorMap_add_sub`: stability of two-sided CP domination
     (`IsKrausCP (Cᵢ + Sᵢ)` and `IsKrausCP (Cᵢ - Sᵢ)`) under finite tensor products,
     via `Matrix.piKronecker_add_sub_posSemidef`.
   * `piTensorMap_reverseBlock_posSemidef` and `piTensorMap_const_reverseBlock_posSemidef`:
     heterogeneous and homogeneous `N`-copy reverse-block criteria for arbitrary finite
     rectangular maps and arbitrary complex vectors `u, v, w`.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Kronecker
open Matrix Finset

/-! ## Layer 1: Generic CP pure-input vanishing and 2×2 block lifting -/

section PureInputVanishing

variable {α β : Type*} [Fintype α]

/-- Conjugating a rank-one outer product `|z⟩⟨u|` by a rectangular matrix `A` produces
`|A z⟩⟨A u|`. -/
theorem Matrix.mul_vecMulVec_mul_conjTranspose
    (A : Matrix β α ℂ) (z u : α → ℂ) :
    A * Matrix.vecMulVec z (star u) * Aᴴ =
      Matrix.vecMulVec (A *ᵥ z) (star (A *ᵥ u)) := by
  ext b₁ b₂
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply,
    Matrix.mulVec, dotProduct, Pi.star_apply, star_sum, star_mul']
  rw [Finset.sum_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- If a finite rectangular Kraus family maps `|u⟩⟨u|` to zero, then every Kraus operator
annihilates `u`. -/
theorem IsKrausCP.mulVec_eq_zero_of_map_vecMulVec_eq_zero
    {D : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} {r : ℕ} {A : Fin r → Matrix β α ℂ}
    (hA : ∀ X, D X = ∑ i : Fin r, A i * X * (A i)ᴴ)
    {u : α → ℂ} (hu : D (Matrix.vecMulVec u (star u)) = 0) :
    ∀ i : Fin r, A i *ᵥ u = 0 := by
  intro i
  ext b
  have hdiag : (D (Matrix.vecMulVec u (star u))) b b = 0 := by
    simp [hu]
  rw [hA, Matrix.sum_apply] at hdiag
  have hre : ∑ j : Fin r, Complex.normSq ((A j *ᵥ u) b) = 0 := by
    have h0 := congrArg Complex.re hdiag
    simp only [Complex.zero_re, Complex.re_sum] at h0
    refine (Finset.sum_congr rfl fun j _ => ?_).symm.trans h0
    rw [Matrix.mul_vecMulVec_mul_conjTranspose, Matrix.vecMulVec_apply, Pi.star_apply,
      Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin r)),
      0 ≤ Complex.normSq ((A j *ᵥ u) b) :=
    fun j _ => Complex.normSq_nonneg _
  have hi : Complex.normSq ((A i *ᵥ u) b) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hre i (Finset.mem_univ i)
  exact Complex.normSq_eq_zero.mp hi

/-- **CP pure-input right vanishing.** If `D` is a rectangular completely positive map with
`D(|u⟩⟨u|) = 0`, then `D(|z⟩⟨u|) = 0` for every complex vector `z`. -/
theorem IsKrausCP.map_vecMulVec_right_eq_zero
    [DecidableEq α] [Fintype β] [DecidableEq β]
    {D : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} (hD : IsKrausCP D)
    {u : α → ℂ} (hu : D (Matrix.vecMulVec u (star u)) = 0) (z : α → ℂ) :
    D (Matrix.vecMulVec z (star u)) = 0 := by
  obtain ⟨r, A, hA⟩ := hD
  have hzero := IsKrausCP.mulVec_eq_zero_of_map_vecMulVec_eq_zero hA hu
  rw [hA]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.mul_vecMulVec_mul_conjTranspose, hzero i]
  ext b₁ b₂
  simp [Matrix.vecMulVec_apply]

/-- **CP pure-input left vanishing.** If `D` is a rectangular completely positive map with
`D(|u⟩⟨u|) = 0`, then `D(|u⟩⟨z|) = 0` for every complex vector `z`. -/
theorem IsKrausCP.map_vecMulVec_left_eq_zero
    [DecidableEq α] [Fintype β] [DecidableEq β]
    {D : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} (hD : IsKrausCP D)
    {u : α → ℂ} (hu : D (Matrix.vecMulVec u (star u)) = 0) (z : α → ℂ) :
    D (Matrix.vecMulVec u (star z)) = 0 := by
  obtain ⟨r, A, hA⟩ := hD
  have hzero := IsKrausCP.mulVec_eq_zero_of_map_vecMulVec_eq_zero hA hu
  rw [hA]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.mul_vecMulVec_mul_conjTranspose, hzero i]
  ext b₁ b₂
  simp [Matrix.vecMulVec_apply]

/-- **Off-diagonal agreement from pure-input equality.** If `C - S` is completely positive
and `C(|u⟩⟨u|) = S(|u⟩⟨u|)`, then `C` and `S` agree on `|z⟩⟨u|` and `|u⟩⟨z|` for every
complex vector `z`. -/
theorem IsKrausCP.map_vecMulVec_eq_of_sub_isKrausCP
    [DecidableEq α] [Fintype β] [DecidableEq β]
    {C S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    (hCS : IsKrausCP (C - S))
    {u : α → ℂ} (hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)))
    (z : α → ℂ) :
    C (Matrix.vecMulVec z (star u)) = S (Matrix.vecMulVec z (star u)) ∧
      C (Matrix.vecMulVec u (star z)) = S (Matrix.vecMulVec u (star z)) := by
  have hD0 : (C - S) (Matrix.vecMulVec u (star u)) = 0 := by
    simp [LinearMap.sub_apply, hu]
  constructor
  · exact sub_eq_zero.mp (by
      simpa [LinearMap.sub_apply] using hCS.map_vecMulVec_right_eq_zero hD0 z)
  · exact sub_eq_zero.mp (by
      simpa [LinearMap.sub_apply] using hCS.map_vecMulVec_left_eq_zero hD0 z)

end PureInputVanishing

section BlockLifting

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A rectangular completely positive map acts blockwise on `2 × 2` positive semidefinite
block matrices to produce a positive semidefinite `2 × 2` block matrix. -/
theorem IsKrausCP.fromBlocks_posSemidef
    {Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} (hΦ : IsKrausCP Φ)
    {M₁₁ M₁₂ M₂₁ M₂₂ : Matrix α α ℂ}
    (hM : (Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).PosSemidef) :
    (Matrix.fromBlocks (Φ M₁₁) (Φ M₁₂) (Φ M₂₁) (Φ M₂₂)).PosSemidef := by
  obtain ⟨r, A, hA⟩ := hΦ
  have hsum :
      Matrix.fromBlocks (Φ M₁₁) (Φ M₁₂) (Φ M₂₁) (Φ M₂₂) =
        ∑ i : Fin r,
          Matrix.fromBlocks (A i) 0 0 (A i) *
            Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ *
            (Matrix.fromBlocks (A i) 0 0 (A i))ᴴ := by
    ext x y
    rw [Matrix.sum_apply]
    cases x <;> cases y <;>
      simp [hA, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.sum_apply]
  rw [hsum]
  exact Matrix.posSemidef_sum Finset.univ fun i _ =>
    hM.mul_mul_conjTranspose_same (Matrix.fromBlocks (A i) 0 0 (A i))

/-- A completely copositive map `S` sends the reversed rank-one Gram block
`[[|u⟩⟨u|, |z⟩⟨u|], [|u⟩⟨z|], [|z⟩⟨z|]]` into the positive semidefinite cone for all
complex vectors `u, z`. -/
theorem IsCompletelyCopositiveMap.reverseBlock_vecMulVec_posSemidef
    {S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} (hS : IsCompletelyCopositiveMap S)
    (u z : α → ℂ) :
    (Matrix.fromBlocks
      (S (Matrix.vecMulVec u (star u)))
      (S (Matrix.vecMulVec z (star u)))
      (S (Matrix.vecMulVec u (star z)))
      (S (Matrix.vecMulVec z (star z)))).PosSemidef := by
  have hvec : (Matrix.vecMulVec (Sum.elim u z) (star (Sum.elim u z))).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star (Sum.elim u z)
  have hblk :
      Matrix.vecMulVec (Sum.elim u z) (star (Sum.elim u z)) =
        Matrix.fromBlocks
          (Matrix.vecMulVec u (star u))
          (Matrix.vecMulVec u (star z))
          (Matrix.vecMulVec z (star u))
          (Matrix.vecMulVec z (star z)) := by
    ext x y
    cases x <;> cases y <;> simp [Matrix.vecMulVec_apply]
  rw [hblk] at hvec
  have htrans :
      (Matrix.fromBlocks
        (Matrix.vecMulVec u (star u))ᵀ
        (Matrix.vecMulVec z (star u))ᵀ
        (Matrix.vecMulVec u (star z))ᵀ
        (Matrix.vecMulVec z (star z))ᵀ).PosSemidef := by
    simpa only [Matrix.fromBlocks_transpose] using hvec.transpose
  have hlift := IsKrausCP.fromBlocks_posSemidef hS htrans
  have hcancel : ∀ X : Matrix α α ℂ,
      (S.comp (Matrix.transposeLinearMapComplex α)) Xᵀ = S X := by
    intro X
    change S (Xᵀ)ᵀ = S X
    rw [Matrix.transpose_transpose]
  simpa only [hcancel] using hlift

end BlockLifting

/-! ## Layer 2: One-copy reverse-block criterion (minimal hypotheses, no Choi) -/

section OneCopyReverseBlock

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- Embedding a positive semidefinite matrix into the lower-right block preserves positive
semidefiniteness. -/
private theorem fromBlocks_zero_lowerRight_posSemidef [Finite β]
    {B : Matrix β β ℂ} (hB : B.PosSemidef) :
    (Matrix.fromBlocks (0 : Matrix β β ℂ) 0 0 B).PosSemidef := by
  classical
  let : Fintype β := Fintype.ofFinite β
  let P : Matrix (β ⊕ β) β ℂ :=
    Matrix.of fun x j => Sum.elim (fun _ => 0) (fun i => if i = j then 1 else 0) x
  have hP : P * B * Pᴴ = Matrix.fromBlocks (0 : Matrix β β ℂ) 0 0 B := by
    ext x y
    cases x <;> cases y <;>
      simp [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.fromBlocks]
  rw [← hP]
  exact hB.mul_mul_conjTranspose_same P

/-- **One-copy reverse-block inequality for arbitrary `z`.**
For arbitrary finite rectangular linear maps `C, S` and complex vector `u`, if `C - S` is
completely positive, `S` is completely copositive, and `C(|u⟩⟨u|) = S(|u⟩⟨u|)`, then for
every complex vector `z`,
`[[C(|u⟩⟨u|), C(|z⟩⟨u|)], [C(|u⟩⟨z|), C(|z⟩⟨z|)]] ≥ 0`.
Complete positivity of `C + S` (or of `C`) is not needed. -/
theorem reverseBlock_vecMulVec_posSemidef
    {C S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    (hCS : IsKrausCP (C - S))
    (hS : IsCompletelyCopositiveMap S)
    {u : α → ℂ} (hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)))
    (z : α → ℂ) :
    (Matrix.fromBlocks
      (C (Matrix.vecMulVec u (star u)))
      (C (Matrix.vecMulVec z (star u)))
      (C (Matrix.vecMulVec u (star z)))
      (C (Matrix.vecMulVec z (star z)))).PosSemidef := by
  have hSblk := hS.reverseBlock_vecMulVec_posSemidef u z
  have ⟨hzu, huz⟩ := IsKrausCP.map_vecMulVec_eq_of_sub_isKrausCP hCS hu z
  have hdiff : ((C - S) (Matrix.vecMulVec z (star z))).PosSemidef :=
    hCS.map_posSemidef (Matrix.posSemidef_vecMulVec_self_star z)
  have hcorner :
      (Matrix.fromBlocks (0 : Matrix β β ℂ) 0 0
        ((C - S) (Matrix.vecMulVec z (star z)))).PosSemidef :=
    fromBlocks_zero_lowerRight_posSemidef hdiff
  have hadd := hSblk.add hcorner
  convert hadd using 1
  ext x y
  cases x <;> cases y <;>
    simp [hu, hzu, huz, LinearMap.sub_apply]

/-- **One-copy map-level reverse-block criterion.**
For arbitrary finite rectangular linear maps `C, S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ`
and arbitrary complex vectors `u, v, w : α → ℂ` with `v + w = u`: if `C - S` is
completely positive, `S` is completely copositive, and `C(|u⟩⟨u|) = S(|u⟩⟨u|)`, then
`[[C(|w⟩⟨w|), C(|v⟩⟨w|)], [C(|w⟩⟨v|), C(|v⟩⟨v|)]] ≥ 0`. -/
theorem reverseBlock_posSemidef
    {C S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    (hCS : IsKrausCP (C - S))
    (hS : IsCompletelyCopositiveMap S)
    {u v w : α → ℂ} (hvw : v + w = u)
    (hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u))) :
    (Matrix.fromBlocks
      (C (Matrix.vecMulVec w (star w)))
      (C (Matrix.vecMulVec v (star w)))
      (C (Matrix.vecMulVec w (star v)))
      (C (Matrix.vecMulVec v (star v)))).PosSemidef := by
  have hbase := reverseBlock_vecMulVec_posSemidef hCS hS hu v
  let E : Matrix (β ⊕ β) (β ⊕ β) ℂ := Matrix.fromBlocks 1 (-1) 0 1
  have hconj := hbase.mul_mul_conjTranspose_same E
  have hw : w = u - v := eq_sub_of_add_eq' hvw
  have hww :
      Matrix.vecMulVec w (star w) =
        Matrix.vecMulVec u (star u) - Matrix.vecMulVec u (star v) -
          Matrix.vecMulVec v (star u) + Matrix.vecMulVec v (star v) := by
    ext i j
    simp only [hw, Matrix.vecMulVec_apply, Pi.sub_apply, Pi.star_apply, star_sub,
      Matrix.sub_apply, Matrix.add_apply]
    ring
  have hvw_mat :
      Matrix.vecMulVec v (star w) =
        Matrix.vecMulVec v (star u) - Matrix.vecMulVec v (star v) := by
    ext i j
    simp only [hw, Matrix.vecMulVec_apply, Pi.sub_apply, Pi.star_apply, star_sub,
      Matrix.sub_apply]
    ring
  have hwv_mat :
      Matrix.vecMulVec w (star v) =
        Matrix.vecMulVec u (star v) - Matrix.vecMulVec v (star v) := by
    ext i j
    simp only [hw, Matrix.vecMulVec_apply, Pi.sub_apply, Pi.star_apply, Matrix.sub_apply]
    ring
  convert hconj using 1
  have hmul :
      E *
          Matrix.fromBlocks
            (C (Matrix.vecMulVec u (star u)))
            (C (Matrix.vecMulVec v (star u)))
            (C (Matrix.vecMulVec u (star v)))
            (C (Matrix.vecMulVec v (star v))) *
          Eᴴ =
        Matrix.fromBlocks
          (C (Matrix.vecMulVec u (star u)) - C (Matrix.vecMulVec u (star v)) -
            C (Matrix.vecMulVec v (star u)) + C (Matrix.vecMulVec v (star v)))
          (C (Matrix.vecMulVec v (star u)) - C (Matrix.vecMulVec v (star v)))
          (C (Matrix.vecMulVec u (star v)) - C (Matrix.vecMulVec v (star v)))
          (C (Matrix.vecMulVec v (star v))) := by
    simp only [E, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_one,
      Matrix.conjTranspose_neg, Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply,
      Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, Matrix.zero_mul,
      Matrix.mul_zero, zero_add]
    congr 1
    abel
  rw [hmul, hww, hvw_mat, hwv_mat]
  simp only [map_add, map_sub]

end OneCopyReverseBlock

/-! ## Layer 3: Finite tensor-product extension under two-sided CP domination -/

section RectangularChoiCharacterization

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Every matrix is the linear combination of matrix units `Matrix.single i j 1`. -/
private theorem eq_sum_smul_single (X : Matrix α α ℂ) :
    X = ∑ i : α, ∑ j : α, X i j • Matrix.single i j (1 : ℂ) := by
  ext a b
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and]

/-- Unnormalized rectangular Choi positivity characterizes `IsKrausCP` on arbitrary finite
matrix algebras, including empty input or output spaces. -/
theorem Matrix.isKrausCP_iff_rectangularChoi_posSemidef
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    IsKrausCP Φ ↔ (Matrix.rectangularChoi Φ).PosSemidef := by
  constructor
  · rintro ⟨r, A, hA⟩
    have hchoi :
        Matrix.rectangularChoi Φ =
          ∑ k : Fin r,
            Matrix.vecMulVec (fun p : α × β => A k p.2 p.1)
              (star (fun p : α × β => A k p.2 p.1)) := by
      ext ⟨i, a⟩ ⟨j, b⟩
      rw [Matrix.rectangularChoi_apply, hA, Matrix.sum_apply, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply,
        Matrix.vecMulVec_apply, ite_and]
    rw [hchoi]
    exact Matrix.posSemidef_sum Finset.univ fun k _ =>
      Matrix.posSemidef_vecMulVec_self_star _
  · intro hJ
    let R : Matrix (α × β) (α × β) ℂ := CFC.sqrt (Matrix.rectangularChoi Φ)
    have hRR : R * R = Matrix.rectangularChoi Φ :=
      CFC.sqrt_mul_sqrt_self (Matrix.rectangularChoi Φ) hJ.nonneg
    have hRherm : R.IsHermitian :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Matrix.rectangularChoi Φ))).isHermitian
    let e : (α × β) ≃ Fin (Fintype.card (α × β)) := Fintype.equivFin (α × β)
    let K : Fin (Fintype.card (α × β)) → Matrix β α ℂ :=
      fun k a i => R (i, a) (e.symm k)
    refine ⟨Fintype.card (α × β), K, fun X => ?_⟩
    have hunit : ∀ i j : α,
        Φ (Matrix.single i j (1 : ℂ)) = ∑ k : Fin (Fintype.card (α × β)),
          K k * Matrix.single i j (1 : ℂ) * (K k)ᴴ := by
      intro i j
      ext a b
      rw [← Matrix.rectangularChoi_apply, ← hRR, Matrix.mul_apply, Matrix.sum_apply]
      rw [← e.symm.sum_comp]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hherm : R (e.symm k) (j, b) = star (R (j, b) (e.symm k)) := by
        simpa [Matrix.conjTranspose_apply] using
          (congrFun (congrFun hRherm.eq (e.symm k)) (j, b)).symm
      rw [hherm]
      simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]
      rfl
    calc
      Φ X = Φ (∑ i : α, ∑ j : α, X i j • Matrix.single i j (1 : ℂ)) := by
        rw [← eq_sum_smul_single X]
      _ = ∑ i : α, ∑ j : α, X i j • ∑ k : Fin (Fintype.card (α × β)),
            K k * Matrix.single i j (1 : ℂ) * (K k)ᴴ := by
        simp only [map_sum, map_smul, hunit]
      _ = ∑ i : α, ∑ k : Fin (Fintype.card (α × β)), ∑ j : α,
            X i j • (K k * Matrix.single i j (1 : ℂ) * (K k)ᴴ) := by
        simp only [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k : Fin (Fintype.card (α × β)), ∑ i : α, ∑ j : α,
            X i j • (K k * Matrix.single i j (1 : ℂ) * (K k)ᴴ) := Finset.sum_comm
      _ = ∑ k : Fin (Fintype.card (α × β)),
            K k * (∑ i : α, ∑ j : α, X i j • Matrix.single i j (1 : ℂ)) * (K k)ᴴ := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = ∑ k : Fin (Fintype.card (α × β)), K k * X * (K k)ᴴ := by
        rw [← eq_sum_smul_single X]

omit [DecidableEq β] in
/-- `Matrix.rectangularChoi` is additive. -/
@[simp]
theorem Matrix.rectangularChoi_add
    (Φ Ψ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    Matrix.rectangularChoi (Φ + Ψ) = Matrix.rectangularChoi Φ + Matrix.rectangularChoi Ψ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.rectangularChoi_apply]

omit [DecidableEq β] in
/-- `Matrix.rectangularChoi` commutes with subtraction. -/
@[simp]
theorem Matrix.rectangularChoi_sub
    (Φ Ψ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    Matrix.rectangularChoi (Φ - Ψ) = Matrix.rectangularChoi Φ - Matrix.rectangularChoi Ψ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.rectangularChoi_apply]

end RectangularChoiCharacterization

section FiniteTensorMap

variable {ν : Type*} [Fintype ν] [DecidableEq ν]
variable {α β : ν → Type*} [∀ k, Fintype (α k)] [∀ k, DecidableEq (α k)]

/-- The finite tensor product `⊗ₖ Φₖ` of a family of rectangular linear maps
`Φ k : Matrix (α k) (α k) ℂ →ₗ[ℂ] Matrix (β k) (β k) ℂ`.
It is defined in the matrix-unit basis by
`(piTensorMap Φ X) a b = ∑ x, ∑ y, X x y * ∏ k, Φ k (E_{x k, y k}) (a k) (b k)`. -/
noncomputable def Matrix.piTensorMap
    (Φ : (k : ν) → Matrix (α k) (α k) ℂ →ₗ[ℂ] Matrix (β k) (β k) ℂ) :
    Matrix ((k : ν) → α k) ((k : ν) → α k) ℂ →ₗ[ℂ]
      Matrix ((k : ν) → β k) ((k : ν) → β k) ℂ where
  toFun X := Matrix.of fun a b =>
    ∑ x : (k : ν) → α k, ∑ y : (k : ν) → α k,
      X x y * ∏ k : ν, Φ k (Matrix.single (x k) (y k) 1) (a k) (b k)
  map_add' X Y := by
    ext a b
    simp only [Matrix.of_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext a b
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_assoc]

@[simp]
theorem Matrix.piTensorMap_apply
    (Φ : (k : ν) → Matrix (α k) (α k) ℂ →ₗ[ℂ] Matrix (β k) (β k) ℂ)
    (X : Matrix ((k : ν) → α k) ((k : ν) → α k) ℂ)
    (a b : (k : ν) → β k) :
    Matrix.piTensorMap Φ X a b =
      ∑ x : (k : ν) → α k, ∑ y : (k : ν) → α k,
        X x y * ∏ k : ν, Φ k (Matrix.single (x k) (y k) 1) (a k) (b k) := rfl

/-- On a matrix unit `E_{x, y}`, `piTensorMap Φ` acts factorwise as a `piKronecker`
product. -/
@[simp]
theorem Matrix.piTensorMap_single
    (Φ : (k : ν) → Matrix (α k) (α k) ℂ →ₗ[ℂ] Matrix (β k) (β k) ℂ)
    (x y : (k : ν) → α k) :
    Matrix.piTensorMap Φ (Matrix.single x y 1) =
      Matrix.piKronecker fun k => Φ k (Matrix.single (x k) (y k) 1) := by
  ext a b
  simp [Matrix.piTensorMap_apply, Matrix.single_apply, Matrix.piKronecker_apply, ite_and]

/-- `piTensorMap Φ` acts factorwise on `piKronecker` products. -/
theorem Matrix.piTensorMap_piKronecker
    (Φ : (k : ν) → Matrix (α k) (α k) ℂ →ₗ[ℂ] Matrix (β k) (β k) ℂ)
    (A : (k : ν) → Matrix (α k) (α k) ℂ) :
    Matrix.piTensorMap Φ (Matrix.piKronecker A) =
      Matrix.piKronecker fun k => Φ k (A k) := by
  ext a b
  rw [Matrix.piTensorMap_apply, Matrix.piKronecker_apply]
  have hsingle : ∀ k : ν,
      Φ k (A k) (a k) (b k) =
        ∑ p : α k × α k, A k p.1 p.2 * Φ k (Matrix.single p.1 p.2 1) (a k) (b k) := by
    intro k
    have hA : Φ k (A k) = ∑ i : α k, ∑ j : α k,
        A k i j • Φ k (Matrix.single i j (1 : ℂ)) := by
      conv_lhs => rw [eq_sum_smul_single (A k)]
      simp only [map_sum, map_smul]
    rw [hA, Fintype.sum_prod_type]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [hsingle, Fintype.prod_sum]
  rw [← Fintype.sum_prod_type']
  let e : (((k : ν) → α k) × ((k : ν) → α k)) ≃ ((k : ν) → α k × α k) :=
    (Equiv.arrowProdEquivProdArrow ν α α).symm
  refine Fintype.sum_equiv e _ _ fun p => ?_
  simp only [e, Matrix.piKronecker_apply, Equiv.arrowProdEquivProdArrow_symm_apply,
    Finset.prod_mul_distrib]

/-- Precomposing `piTensorMap Φ` with transposition equals applying `piTensorMap` to the
transposed factors. -/
theorem Matrix.piTensorMap_comp_transpose
    (Φ : (k : ν) → Matrix (α k) (α k) ℂ →ₗ[ℂ] Matrix (β k) (β k) ℂ) :
    (Matrix.piTensorMap Φ).comp (Matrix.transposeLinearMapComplex ((k : ν) → α k)) =
      Matrix.piTensorMap fun k => (Φ k).comp (Matrix.transposeLinearMapComplex (α k)) := by
  apply LinearMap.ext
  intro X
  ext a b
  simp only [LinearMap.comp_apply, Matrix.piTensorMap_apply, Matrix.transposeLinearMapComplex]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  change X x y * ∏ k : ν, Φ k (Matrix.single (y k) (x k) (1 : ℂ)) (a k) (b k) =
    X x y * ∏ k : ν, Φ k ((Matrix.single (x k) (y k) (1 : ℂ))ᵀ) (a k) (b k)
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have hst : (Matrix.single (x k) (y k) (1 : ℂ))ᵀ = Matrix.single (y k) (x k) (1 : ℂ) := by
    ext i j
    simp [Matrix.transpose_apply, Matrix.single_apply, and_comm]
  rw [hst]

/-- The unnormalized rectangular Choi matrix of `piTensorMap Φ` is the `piKronecker`
product of the factor Choi matrices, reindexed by `Equiv.arrowProdEquivProdArrow`. -/
theorem Matrix.rectangularChoi_piTensorMap
    [∀ k, Fintype (β k)]
    (Φ : (k : ν) → Matrix (α k) (α k) ℂ →ₗ[ℂ] Matrix (β k) (β k) ℂ) :
    Matrix.rectangularChoi (Matrix.piTensorMap Φ) =
      (Matrix.piKronecker fun k => Matrix.rectangularChoi (Φ k)).submatrix
        (Equiv.arrowProdEquivProdArrow ν α β).symm
        (Equiv.arrowProdEquivProdArrow ν α β).symm := by
  ext ⟨x, a⟩ ⟨y, b⟩
  rw [Matrix.rectangularChoi_apply, Matrix.piTensorMap_single, Matrix.submatrix_apply,
    Matrix.piKronecker_apply, Matrix.piKronecker_apply]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Equiv.arrowProdEquivProdArrow_symm_apply, Equiv.arrowProdEquivProdArrow_symm_apply,
    Matrix.rectangularChoi_apply]

/-- A finite tensor product of rectangular completely positive maps is completely positive. -/
theorem Matrix.isKrausCP_piTensorMap
    [∀ k, Fintype (β k)] [∀ k, DecidableEq (β k)]
    {Φ : (k : ν) → Matrix (α k) (α k) ℂ →ₗ[ℂ] Matrix (β k) (β k) ℂ}
    (hΦ : ∀ k, IsKrausCP (Φ k)) :
    IsKrausCP (Matrix.piTensorMap Φ) := by
  rw [Matrix.isKrausCP_iff_rectangularChoi_posSemidef, Matrix.rectangularChoi_piTensorMap]
  let e : Fin (Fintype.card ν) ≃ ν := (Fintype.equivFin ν).symm
  have hfin : (Matrix.piKronecker fun i : Fin (Fintype.card ν) =>
      Matrix.rectangularChoi (Φ (e i))).PosSemidef :=
    Matrix.piKronecker_posSemidef _ fun i =>
      (Matrix.isKrausCP_iff_rectangularChoi_posSemidef (Φ (e i))).mp (hΦ (e i))
  let g : (((k : ν) → α k) × ((k : ν) → β k)) → ((i : Fin (Fintype.card ν)) → α (e i) × β (e i)) :=
    fun p i => (p.1 (e i), p.2 (e i))
  convert hfin.submatrix g using 1
  ext ⟨x, a⟩ ⟨y, b⟩
  simp only [Matrix.submatrix_apply, Matrix.piKronecker_apply, g,
    Equiv.arrowProdEquivProdArrow_symm_apply]
  exact (e.prod_comp fun k => Matrix.rectangularChoi (Φ k) (x k, a k) (y k, b k)).symm

/-- A finite tensor product of completely copositive maps is completely copositive. -/
theorem Matrix.isCompletelyCopositiveMap_piTensorMap
    [∀ k, Fintype (β k)] [∀ k, DecidableEq (β k)]
    {S : (k : ν) → Matrix (α k) (α k) ℂ →ₗ[ℂ] Matrix (β k) (β k) ℂ}
    (hS : ∀ k, IsCompletelyCopositiveMap (S k)) :
    IsCompletelyCopositiveMap (Matrix.piTensorMap S) := by
  unfold IsCompletelyCopositiveMap
  rw [Matrix.piTensorMap_comp_transpose]
  exact Matrix.isKrausCP_piTensorMap hS

/-- **Stability of two-sided CP domination under finite tensor products.**
If `Cᵢ + Sᵢ` and `Cᵢ - Sᵢ` are completely positive for every `i : Fin N`, then both
`(⊗ᵢ Cᵢ) + (⊗ᵢ Sᵢ)` and `(⊗ᵢ Cᵢ) - (⊗ᵢ Sᵢ)` are completely positive.
Neither `Sᵢ` nor `-Sᵢ` needs to be completely positive. -/
theorem Matrix.isKrausCP_piTensorMap_add_sub
    {N : ℕ} {α β : Fin N → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (C S : (i : Fin N) → Matrix (α i) (α i) ℂ →ₗ[ℂ] Matrix (β i) (β i) ℂ)
    (hadd : ∀ i, IsKrausCP (C i + S i))
    (hsub : ∀ i, IsKrausCP (C i - S i)) :
    IsKrausCP (Matrix.piTensorMap C + Matrix.piTensorMap S) ∧
      IsKrausCP (Matrix.piTensorMap C - Matrix.piTensorMap S) := by
  have hJadd : ∀ i, (Matrix.rectangularChoi (C i) + Matrix.rectangularChoi (S i)).PosSemidef :=
    fun i => by
      rw [← Matrix.rectangularChoi_add]
      exact (Matrix.isKrausCP_iff_rectangularChoi_posSemidef _).mp (hadd i)
  have hJsub : ∀ i, (Matrix.rectangularChoi (C i) - Matrix.rectangularChoi (S i)).PosSemidef :=
    fun i => by
      rw [← Matrix.rectangularChoi_sub]
      exact (Matrix.isKrausCP_iff_rectangularChoi_posSemidef _).mp (hsub i)
  obtain ⟨hPadd, hPsub⟩ := Matrix.piKronecker_add_sub_posSemidef
    (fun i => Matrix.rectangularChoi (C i))
    (fun i => Matrix.rectangularChoi (S i))
    hJadd hJsub
  constructor
  · rw [Matrix.isKrausCP_iff_rectangularChoi_posSemidef, Matrix.rectangularChoi_add,
      Matrix.rectangularChoi_piTensorMap, Matrix.rectangularChoi_piTensorMap]
    convert hPadd.submatrix (Equiv.arrowProdEquivProdArrow (Fin N) α β).symm using 1
    ext ⟨x, a⟩ ⟨y, b⟩
    rfl
  · rw [Matrix.isKrausCP_iff_rectangularChoi_posSemidef, Matrix.rectangularChoi_sub,
      Matrix.rectangularChoi_piTensorMap, Matrix.rectangularChoi_piTensorMap]
    convert hPsub.submatrix (Equiv.arrowProdEquivProdArrow (Fin N) α β).symm using 1
    ext ⟨x, a⟩ ⟨y, b⟩
    rfl

omit [DecidableEq ν] [∀ k, Fintype (α k)] [∀ k, DecidableEq (α k)] in
/-- The rank-one outer product of a finite product vector factors as a `piKronecker`
product of rank-one outer products. -/
theorem Matrix.vecMulVec_piProd_star
    (u : (k : ν) → α k → ℂ) :
    Matrix.vecMulVec (fun x : (k : ν) → α k => ∏ k, u k (x k))
      (star (fun x : (k : ν) → α k => ∏ k, u k (x k))) =
      Matrix.piKronecker fun k => Matrix.vecMulVec (u k) (star (u k)) := by
  ext x y
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, star_prod, Matrix.piKronecker_apply,
    Finset.prod_mul_distrib]

/-- **Heterogeneous `N`-copy reverse-block criterion.**
If `Cᵢ + Sᵢ` and `Cᵢ - Sᵢ` are completely positive, `Sᵢ` is completely copositive, and
`Cᵢ(|uᵢ⟩⟨uᵢ|) = Sᵢ(|uᵢ⟩⟨uᵢ|)` for every `i : Fin N`, then for all complex vectors
`v, w : ((i : Fin N) → α i) → ℂ` summing to the product vector `uProd x = ∏ i, u i (x i)`,
the `N`-copy reverse-block matrix is positive semidefinite. -/
theorem piTensorMap_reverseBlock_posSemidef
    {N : ℕ} {α β : Fin N → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (C S : (i : Fin N) → Matrix (α i) (α i) ℂ →ₗ[ℂ] Matrix (β i) (β i) ℂ)
    (hadd : ∀ i, IsKrausCP (C i + S i))
    (hsub : ∀ i, IsKrausCP (C i - S i))
    (hcop : ∀ i, IsCompletelyCopositiveMap (S i))
    {u : (i : Fin N) → α i → ℂ}
    (hu : ∀ i, C i (Matrix.vecMulVec (u i) (star (u i))) =
      S i (Matrix.vecMulVec (u i) (star (u i))))
    {v w : ((i : Fin N) → α i) → ℂ}
    (hvw : v + w = fun x => ∏ i, u i (x i)) :
    (Matrix.fromBlocks
      (Matrix.piTensorMap C (Matrix.vecMulVec w (star w)))
      (Matrix.piTensorMap C (Matrix.vecMulVec v (star w)))
      (Matrix.piTensorMap C (Matrix.vecMulVec w (star v)))
      (Matrix.piTensorMap C (Matrix.vecMulVec v (star v)))).PosSemidef := by
  have hCS := (Matrix.isKrausCP_piTensorMap_add_sub C S hadd hsub).2
  have hScop := Matrix.isCompletelyCopositiveMap_piTensorMap hcop
  have huProd :
      Matrix.piTensorMap C (Matrix.vecMulVec (fun x => ∏ i, u i (x i))
        (star (fun x => ∏ i, u i (x i)))) =
      Matrix.piTensorMap S (Matrix.vecMulVec (fun x => ∏ i, u i (x i))
        (star (fun x => ∏ i, u i (x i)))) := by
    rw [Matrix.vecMulVec_piProd_star, Matrix.piTensorMap_piKronecker,
      Matrix.piTensorMap_piKronecker]
    exact congrArg Matrix.piKronecker (funext hu)
  exact reverseBlock_posSemidef hCS hScop hvw huProd

/-- **Homogeneous `N`-copy reverse-block criterion (generalization of arXiv:2611.34921 Lemma 4).**
For arbitrary finite rectangular maps `C, S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ`,
any `N : ℕ`, and any complex vector `u : α → ℂ`: if `C + S` and `C - S` are completely
positive, `S` is completely copositive, and `C(|u⟩⟨u|) = S(|u⟩⟨u|)`, then for all
complex vectors `v, w : (Fin N → α) → ℂ` with `v + w = fun x => ∏ i, u (x i)`,
the `N`-copy reverse-block matrix for `C^{⊗ N}` is positive semidefinite. -/
theorem piTensorMap_const_reverseBlock_posSemidef
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (N : ℕ) {C S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    (hadd : IsKrausCP (C + S))
    (hsub : IsKrausCP (C - S))
    (hcop : IsCompletelyCopositiveMap S)
    {u : α → ℂ}
    (hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)))
    {v w : (Fin N → α) → ℂ}
    (hvw : v + w = fun x => ∏ i : Fin N, u (x i)) :
    (Matrix.fromBlocks
      (Matrix.piTensorMap (fun _ : Fin N => C) (Matrix.vecMulVec w (star w)))
      (Matrix.piTensorMap (fun _ : Fin N => C) (Matrix.vecMulVec v (star w)))
      (Matrix.piTensorMap (fun _ : Fin N => C) (Matrix.vecMulVec w (star v)))
      (Matrix.piTensorMap (fun _ : Fin N => C) (Matrix.vecMulVec v (star v)))).PosSemidef :=
  piTensorMap_reverseBlock_posSemidef (fun _ : Fin N => C) (fun _ : Fin N => S)
    (fun _ => hadd) (fun _ => hsub) (fun _ => hcop) (fun _ => hu) hvw

end FiniteTensorMap
