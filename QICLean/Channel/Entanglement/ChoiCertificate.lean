/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Entanglement.ReverseBlockCriterion
import QICLean.Algebra.OperatorSchmidt.Basic
import QICLean.Algebra.Kronecker.PartialTranspose

/-!
# Generic Choi-certificate soundness bridge

This file connects unnormalized input-first rectangular Choi certificates
`Q : Matrix (α × β) (α × β) ℂ` to the map-level hypotheses of
`QICLean.Channel.Entanglement.ReverseBlockCriterion`.

## Conventions

* `Matrix.rectangularChoi Φ` is the **unnormalized, input-first** Choi matrix
  `J(Φ)_{(i,a),(j,b)} = Φ(E_{ij})_{a,b}` on `α × β`.
* Its two-sided inverse is `Matrix.operatorSchmidtMap Q`, defined in
  `QICLean.Algebra.OperatorSchmidt.Basic` by
  `(operatorSchmidtMap Q X)_{a,b} = ∑_{i,j} X_{i,j} Q_{(i,a),(j,b)}`.
* For a complex vector `u : α → ℂ`, the compression operator `V_u = bar u ⊗ I_β`
  is `Matrix.conjVecTensorId β u : Matrix (α × β) β ℂ`. Complex conjugation of `u`
  is essential: `V_zᴴ * rectangularChoi Φ * V_u = Φ(|z⟩⟨u|)`.
* All results work for arbitrary finite (possibly empty) rectangular index types
  `α, β`, without any `Nonempty` assumption.

## Main results

* `Matrix.rectangularChoiLinearEquiv`, `Matrix.rectangularChoi_injective`,
  `Matrix.existsUnique_rectangularChoi_eq`: bijectivity of `Matrix.rectangularChoi`
  with inverse `Matrix.operatorSchmidtMap`.
* `Matrix.partialTransposeFst`, `Matrix.rectangularChoi_comp_transpose`,
  `Matrix.isCompletelyCopositiveMap_iff_partialTransposeFst_rectangularChoi_posSemidef`:
  input partial transpose and complete copositivity characterization.
* `Matrix.conjVecTensorId`, `Matrix.conjTranspose_conjVecTensorId_mul_mul`,
  `Matrix.PosSemidef.mul_eq_zero_iff_conjTranspose_mul_mul_eq_zero`,
  `Matrix.PosSemidef.mul_conjVecTensorId_eq_zero_iff_operatorSchmidtMap_vecMulVec_eq_zero`:
  complex-`u` compression and kernel equivalence.
* `exists_map_of_choiCertificate`, `exists_map_of_choiCertificate_compression`:
  construction of the witness map `S` satisfying `IsKrausCP (C + S)`,
  `IsKrausCP (C - S)`, `IsCompletelyCopositiveMap S`, and `C(|u⟩⟨u|) = S(|u⟩⟨u|)`.
* `reverseBlock_posSemidef_of_choiCertificate`,
  `piTensorMap_reverseBlock_posSemidef_of_choiCertificate`,
  `piTensorMap_const_reverseBlock_posSemidef_of_choiCertificate`,
  `piTensorMap_const_reverseBlock_posSemidef_of_choiCertificate_compression`:
  one-copy, heterogeneous `N`-copy, and homogeneous `N`-copy reverse-block
  consequences from Choi certificates.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder
open Matrix Finset

/-! ## Section 1: Inverse and bijectivity of `Matrix.rectangularChoi` -/

section OperatorSchmidtLinear

variable {α β : Type*} [Fintype α]

/-- Entrywise formula for `Matrix.operatorSchmidtMap`. -/
theorem Matrix.operatorSchmidtMap_entry
    (Q : Matrix (α × β) (α × β) ℂ) (X : Matrix α α ℂ) (a b : β) :
    Matrix.operatorSchmidtMap Q X a b =
      ∑ i : α, ∑ j : α, X i j * Q (i, a) (j, b) := by
  rw [Matrix.operatorSchmidtMap_apply, Fintype.sum_prod_type]
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.operatorBlock_apply]

/-- `Matrix.operatorSchmidtMap` is additive in the bipartite matrix argument. -/
@[simp]
theorem Matrix.operatorSchmidtMap_add
    (P Q : Matrix (α × β) (α × β) ℂ) :
    Matrix.operatorSchmidtMap (P + Q) =
      Matrix.operatorSchmidtMap P + Matrix.operatorSchmidtMap Q := by
  apply LinearMap.ext
  intro X
  ext a b
  simp only [LinearMap.add_apply, Matrix.add_apply, Matrix.operatorSchmidtMap_entry,
    mul_add, Finset.sum_add_distrib]

/-- `Matrix.operatorSchmidtMap` commutes with subtraction. -/
@[simp]
theorem Matrix.operatorSchmidtMap_sub
    (P Q : Matrix (α × β) (α × β) ℂ) :
    Matrix.operatorSchmidtMap (P - Q) =
      Matrix.operatorSchmidtMap P - Matrix.operatorSchmidtMap Q := by
  apply LinearMap.ext
  intro X
  ext a b
  simp only [LinearMap.sub_apply, Matrix.sub_apply, Matrix.operatorSchmidtMap_entry,
    mul_sub, Finset.sum_sub_distrib]

/-- `Matrix.operatorSchmidtMap` is homogeneous in the bipartite matrix argument. -/
@[simp]
theorem Matrix.operatorSchmidtMap_smul
    (c : ℂ) (Q : Matrix (α × β) (α × β) ℂ) :
    Matrix.operatorSchmidtMap (c • Q) = c • Matrix.operatorSchmidtMap Q := by
  apply LinearMap.ext
  intro X
  ext a b
  simp only [LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.operatorSchmidtMap_entry, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end OperatorSchmidtLinear

section RectangularChoiInverse

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]

/-- `Matrix.rectangularChoi` is a left inverse to `Matrix.operatorSchmidtMap`. -/
theorem Matrix.rectangularChoi_leftInverse_operatorSchmidtMap
    (Q : Matrix (α × β) (α × β) ℂ) :
    Matrix.rectangularChoi (Matrix.operatorSchmidtMap Q) = Q := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [Matrix.rectangularChoi_apply, Matrix.operatorSchmidtMap_entry]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [Ne.symm hkj]
    · simp
  · intro k _ hki
    simp [Ne.symm hki]
  · simp

/-- `Matrix.operatorSchmidtMap` is a left inverse to `Matrix.rectangularChoi`. -/
@[simp]
theorem Matrix.operatorSchmidtMap_rectangularChoi
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    Matrix.operatorSchmidtMap (Matrix.rectangularChoi Φ) = Φ := by
  apply LinearMap.ext
  intro X
  ext a b
  rw [Matrix.operatorSchmidtMap_entry]
  have hX : X = ∑ i : α, ∑ j : α, X i j • Matrix.single i j (1 : ℂ) := by
    ext r s
    simp [Matrix.sum_apply, Matrix.single_apply, ite_and]
  conv_rhs => rw [hX]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.rectangularChoi_apply]

/-- `Matrix.rectangularChoi` is homogeneous in the linear map argument. -/
@[simp]
theorem Matrix.rectangularChoi_smul
    (c : ℂ) (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    Matrix.rectangularChoi (c • Φ) = c • Matrix.rectangularChoi Φ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.rectangularChoi_apply]

/-- `Matrix.rectangularChoi` maps zero to zero. -/
@[simp]
theorem Matrix.rectangularChoi_zero :
    Matrix.rectangularChoi (0 : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) = 0 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.rectangularChoi_apply]

/-- `Matrix.rectangularChoi` commutes with negation. -/
@[simp]
theorem Matrix.rectangularChoi_neg
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    Matrix.rectangularChoi (-Φ) = -Matrix.rectangularChoi Φ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.rectangularChoi_apply]

/-- The unnormalized input-first rectangular Choi isomorphism as a `ℂ`-linear equivalence
between linear maps `M_α(ℂ) →ₗ[ℂ] M_β(ℂ)` and bipartite matrices on `α × β`. -/
noncomputable def Matrix.rectangularChoiLinearEquiv :
    (Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) ≃ₗ[ℂ] Matrix (α × β) (α × β) ℂ where
  toFun := Matrix.rectangularChoi
  invFun := Matrix.operatorSchmidtMap
  map_add' := Matrix.rectangularChoi_add
  map_smul' := Matrix.rectangularChoi_smul
  left_inv := Matrix.operatorSchmidtMap_rectangularChoi
  right_inv := Matrix.rectangularChoi_leftInverse_operatorSchmidtMap

@[simp]
theorem Matrix.rectangularChoiLinearEquiv_apply
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    Matrix.rectangularChoiLinearEquiv Φ = Matrix.rectangularChoi Φ := rfl

@[simp]
theorem Matrix.rectangularChoiLinearEquiv_symm_apply
    (Q : Matrix (α × β) (α × β) ℂ) :
    Matrix.rectangularChoiLinearEquiv.symm Q = Matrix.operatorSchmidtMap Q := rfl

/-- `Matrix.rectangularChoi` is injective. -/
theorem Matrix.rectangularChoi_injective :
    Function.Injective (Matrix.rectangularChoi (α := α) (β := β)) :=
  Matrix.rectangularChoiLinearEquiv.injective

/-- Two rectangular linear maps are equal iff their unnormalized Choi matrices are equal. -/
theorem Matrix.rectangularChoi_eq_iff
    {Φ Ψ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} :
    Matrix.rectangularChoi Φ = Matrix.rectangularChoi Ψ ↔ Φ = Ψ :=
  Matrix.rectangularChoi_injective.eq_iff

/-- Every bipartite matrix `Q` on `α × β` is the unnormalized rectangular Choi matrix of
a unique linear map `S : M_α(ℂ) →ₗ[ℂ] M_β(ℂ)`, namely `Matrix.operatorSchmidtMap Q`. -/
theorem Matrix.existsUnique_rectangularChoi_eq
    (Q : Matrix (α × β) (α × β) ℂ) :
    ∃! S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ, Matrix.rectangularChoi S = Q := by
  refine ⟨Matrix.operatorSchmidtMap Q,
    Matrix.rectangularChoi_leftInverse_operatorSchmidtMap Q, ?_⟩
  intro S hS
  exact Matrix.rectangularChoi_injective
    (hS.trans (Matrix.rectangularChoi_leftInverse_operatorSchmidtMap Q).symm)

end RectangularChoiInverse

/-! ## Section 2: Input partial transpose and complete copositivity -/

section InputPartialTranspose

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]

/-- Precomposing a rectangular linear map with input transposition corresponds to taking
the first-factor partial transpose of its unnormalized rectangular Choi matrix. -/
theorem Matrix.rectangularChoi_comp_transpose
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    Matrix.rectangularChoi (Φ.comp (Matrix.transposeLinearMapComplex α)) =
      Matrix.partialTransposeFst (Matrix.rectangularChoi Φ) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [Matrix.rectangularChoi_apply, LinearMap.comp_apply,
    Matrix.partialTransposeFst_apply, Matrix.rectangularChoi_apply]
  have hsingle : (Matrix.single i j (1 : ℂ))ᵀ = Matrix.single j i (1 : ℂ) := by
    ext r s
    simp [Matrix.transpose_apply, Matrix.single_apply, and_comm]
  change Φ (Matrix.single i j (1 : ℂ))ᵀ a b = Φ (Matrix.single j i (1 : ℂ)) a b
  rw [hsingle]

/-- A rectangular linear map is completely copositive iff the input partial transpose of
its unnormalized rectangular Choi matrix is positive semidefinite. -/
theorem Matrix.isCompletelyCopositiveMap_iff_partialTransposeFst_rectangularChoi_posSemidef
    [DecidableEq β]
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) :
    IsCompletelyCopositiveMap Φ ↔
      (Matrix.partialTransposeFst (Matrix.rectangularChoi Φ)).PosSemidef := by
  unfold IsCompletelyCopositiveMap
  rw [Matrix.isKrausCP_iff_rectangularChoi_posSemidef, Matrix.rectangularChoi_comp_transpose]

/-- The map `Matrix.operatorSchmidtMap Q` is completely copositive iff
`Matrix.partialTransposeFst Q` is positive semidefinite. -/
theorem Matrix.isCompletelyCopositiveMap_operatorSchmidtMap_iff
    [DecidableEq β]
    (Q : Matrix (α × β) (α × β) ℂ) :
    IsCompletelyCopositiveMap (Matrix.operatorSchmidtMap Q) ↔
      (Matrix.partialTransposeFst Q).PosSemidef := by
  rw [Matrix.isCompletelyCopositiveMap_iff_partialTransposeFst_rectangularChoi_posSemidef,
    Matrix.rectangularChoi_leftInverse_operatorSchmidtMap]

end InputPartialTranspose

/-! ## Section 3: Complex-`u` compression and PSD kernel equivalence -/

section ComplexCompression

/-- The `(α × β) × β` matrix representing `bar u ⊗ I_β`, where `u : α → ℂ` is a
(possibly non-real) complex vector. Complex conjugation of `u` is essential so that
`(conjVecTensorId β z)ᴴ * rectangularChoi Φ * conjVecTensorId β u = Φ(|z⟩⟨u|)`. -/
def Matrix.conjVecTensorId {α : Type*} (β : Type*) [DecidableEq β] (u : α → ℂ) :
    Matrix (α × β) β ℂ :=
  fun p b => if p.2 = b then star (u p.1) else 0

@[simp]
theorem Matrix.conjVecTensorId_apply {α : Type*} (β : Type*) [DecidableEq β]
    (u : α → ℂ) (i : α) (a b : β) :
    Matrix.conjVecTensorId β u (i, a) b = if a = b then star (u i) else 0 := rfl

/-- Compressing a bipartite matrix `Q` on the left by `(bar z ⊗ I_β)ᴴ` and on the right
by `bar u ⊗ I_β` evaluates the reshaped map `operatorSchmidtMap Q` on `|z⟩⟨u|`. -/
theorem Matrix.conjTranspose_conjVecTensorId_mul_mul
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (Q : Matrix (α × β) (α × β) ℂ) (z u : α → ℂ) :
    (Matrix.conjVecTensorId β z)ᴴ * Q * Matrix.conjVecTensorId β u =
      Matrix.operatorSchmidtMap Q (Matrix.vecMulVec z (star u)) := by
  ext a b
  rw [Matrix.operatorSchmidtMap_entry, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.conjVecTensorId,
    Matrix.vecMulVec_apply, Pi.star_apply]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ j : α,
      ∑ b' : β, (∑ p : α × β,
        star (if p.2 = a then star (z p.1) else 0) * Q p (j, b')) *
        (if b' = b then star (u j) else 0) =
      ∑ i : α, z i * star (u j) * Q (i, a) (j, b) := by
    intro j
    rw [Finset.sum_eq_single b]
    · simp only [↓reduceIte, Fintype.sum_prod_type]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single a]
      · simp only [↓reduceIte, star_star]
        ring
      · intro a' _ ha'
        simp [ha']
      · simp
    · intro b' _ hb'
      simp [hb']
    · simp
  simp_rw [hinner]
  rw [Finset.sum_comm]

/-- Compressing `rectangularChoi Φ` by `bar z ⊗ I_β` and `bar u ⊗ I_β` recovers
`Φ(|z⟩⟨u|)`. -/
theorem Matrix.conjTranspose_conjVecTensorId_mul_rectangularChoi_mul
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) (z u : α → ℂ) :
    (Matrix.conjVecTensorId β z)ᴴ * Matrix.rectangularChoi Φ * Matrix.conjVecTensorId β u =
      Φ (Matrix.vecMulVec z (star u)) := by
  rw [Matrix.conjTranspose_conjVecTensorId_mul_mul, Matrix.operatorSchmidtMap_rectangularChoi]

/-- For any complex matrix `A`, `Aᴴ * A = 0` iff `A = 0`. -/
private theorem conjTranspose_mul_self_eq_zero_iff
    {m n : Type*} [Fintype m] (A : Matrix m n ℂ) :
    Aᴴ * A = 0 ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have hdiag : (Aᴴ * A) j j = 0 := by simp [h]
    rw [Matrix.mul_apply] at hdiag
    have hre : ∑ k : m, Complex.normSq (A k j) = 0 := by
      have h0 := congrArg Complex.re hdiag
      simp only [Complex.zero_re, Complex.re_sum] at h0
      refine (Finset.sum_congr rfl fun k _ => ?_).symm.trans h0
      simp only [Matrix.conjTranspose_apply, Complex.star_def, mul_comm, Complex.mul_conj,
        Complex.ofReal_re]
    have hnonneg : ∀ k ∈ (Finset.univ : Finset m), 0 ≤ Complex.normSq (A k j) :=
      fun k _ => Complex.normSq_nonneg _
    have hi : Complex.normSq (A i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hre i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp hi
  · intro h
    simp [h]

/-- For a positive semidefinite complex matrix `M` and any rectangular matrix `V`,
`M * V = 0` iff the compression `Vᴴ * M * V = 0`. Works for arbitrary finite
(possibly empty) index types. -/
theorem Matrix.PosSemidef.mul_eq_zero_iff_conjTranspose_mul_mul_eq_zero
    {m n : Type*} [Fintype m]
    {M : Matrix m m ℂ} (hM : M.PosSemidef) (V : Matrix m n ℂ) :
    M * V = 0 ↔ Vᴴ * M * V = 0 := by
  classical
  constructor
  · intro h
    rw [Matrix.mul_assoc, h, Matrix.mul_zero]
  · intro h
    let R : Matrix m m ℂ := CFC.sqrt M
    have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M hM.nonneg
    have hRherm : Rᴴ = R :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)).isHermitian.eq
    have hRV : (R * V)ᴴ * (R * V) = 0 := by
      calc
        (R * V)ᴴ * (R * V) = Vᴴ * Rᴴ * (R * V) := by rw [Matrix.conjTranspose_mul]
        _ = Vᴴ * (R * R) * V := by rw [hRherm]; simp [Matrix.mul_assoc]
        _ = Vᴴ * M * V := by rw [hRR]
        _ = 0 := h
    have hRV0 : R * V = 0 := (conjTranspose_mul_self_eq_zero_iff (R * V)).mp hRV
    calc
      M * V = R * R * V := by rw [hRR]
      _ = R * (R * V) := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hRV0, Matrix.mul_zero]

/-- For a positive semidefinite bipartite matrix `M` on `α × β` and a complex vector
`u : α → ℂ`, the kernel condition `M * (bar u ⊗ I_β) = 0` is equivalent to vanishing
of `operatorSchmidtMap M` on `|u⟩⟨u|`. -/
theorem Matrix.PosSemidef.mul_conjVecTensorId_eq_zero_iff_operatorSchmidtMap_vecMulVec_eq_zero
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    {M : Matrix (α × β) (α × β) ℂ} (hM : M.PosSemidef) (u : α → ℂ) :
    M * Matrix.conjVecTensorId β u = 0 ↔
      Matrix.operatorSchmidtMap M (Matrix.vecMulVec u (star u)) = 0 := by
  rw [hM.mul_eq_zero_iff_conjTranspose_mul_mul_eq_zero,
    Matrix.conjTranspose_conjVecTensorId_mul_mul]

/-- For a completely positive map `Φ` (equivalently, `(rectangularChoi Φ).PosSemidef`),
`rectangularChoi Φ * (bar u ⊗ I_β) = 0` iff `Φ(|u⟩⟨u|) = 0`. -/
theorem Matrix.PosSemidef.rectangularChoi_mul_conjVecTensorId_eq_zero_iff
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    (hΦ : (Matrix.rectangularChoi Φ).PosSemidef) (u : α → ℂ) :
    Matrix.rectangularChoi Φ * Matrix.conjVecTensorId β u = 0 ↔
      Φ (Matrix.vecMulVec u (star u)) = 0 := by
  rw [hΦ.mul_conjVecTensorId_eq_zero_iff_operatorSchmidtMap_vecMulVec_eq_zero,
    Matrix.operatorSchmidtMap_rectangularChoi]

end ComplexCompression

/-! ## Section 4: Generic Choi-certificate soundness bridge -/

section ChoiCertificateBridge

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- **Generic Choi-certificate bridge (explicit witness `S = operatorSchmidtMap Q`).**
Given a finite rectangular linear map `C` with unnormalized input-first Choi matrix
`J = rectangularChoi C`, a bipartite certificate matrix `Q` on `α × β`, and a complex
vector `u : α → ℂ`:
if `J + Q ≥ 0`, `J - Q ≥ 0`, `Q^{T_1} ≥ 0`, and `(J - Q)(bar u ⊗ I_β) = 0`, then
`S = operatorSchmidtMap Q` satisfies `rectangularChoi S = Q`, `IsKrausCP (C + S)`,
`IsKrausCP (C - S)`, `IsCompletelyCopositiveMap S`, and `C(|u⟩⟨u|) = S(|u⟩⟨u|)`. -/
theorem operatorSchmidtMap_satisfies_reverseBlock_hypotheses
    {C : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    {Q : Matrix (α × β) (α × β) ℂ}
    {u : α → ℂ}
    (hadd : (Matrix.rectangularChoi C + Q).PosSemidef)
    (hsub : (Matrix.rectangularChoi C - Q).PosSemidef)
    (hpt : (Matrix.partialTransposeFst Q).PosSemidef)
    (hker : (Matrix.rectangularChoi C - Q) * Matrix.conjVecTensorId β u = 0) :
    let S := Matrix.operatorSchmidtMap Q
    Matrix.rectangularChoi S = Q ∧
      IsKrausCP (C + S) ∧
      IsKrausCP (C - S) ∧
      IsCompletelyCopositiveMap S ∧
      C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)) := by
  intro S
  have hS : Matrix.rectangularChoi S = Q :=
    Matrix.rectangularChoi_leftInverse_operatorSchmidtMap Q
  have hCPadd : IsKrausCP (C + S) := by
    rw [Matrix.isKrausCP_iff_rectangularChoi_posSemidef, Matrix.rectangularChoi_add, hS]
    exact hadd
  have hCPsub : IsKrausCP (C - S) := by
    rw [Matrix.isKrausCP_iff_rectangularChoi_posSemidef, Matrix.rectangularChoi_sub, hS]
    exact hsub
  have hcop : IsCompletelyCopositiveMap S :=
    (Matrix.isCompletelyCopositiveMap_operatorSchmidtMap_iff Q).mpr hpt
  have hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)) := by
    have hdiff : (Matrix.rectangularChoi (C - S)).PosSemidef := by
      rw [Matrix.rectangularChoi_sub, hS]
      exact hsub
    have hker' : Matrix.rectangularChoi (C - S) * Matrix.conjVecTensorId β u = 0 := by
      rw [Matrix.rectangularChoi_sub, hS]
      exact hker
    have h0 : (C - S) (Matrix.vecMulVec u (star u)) = 0 :=
      (hdiff.rectangularChoi_mul_conjVecTensorId_eq_zero_iff u).mp hker'
    exact sub_eq_zero.mp (by simpa [LinearMap.sub_apply] using h0)
  exact ⟨hS, hCPadd, hCPsub, hcop, hu⟩

/-- **Generic Choi-certificate bridge (existential form, kernel hypothesis).** -/
theorem exists_map_of_choiCertificate
    {C : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    {Q : Matrix (α × β) (α × β) ℂ}
    {u : α → ℂ}
    (hadd : (Matrix.rectangularChoi C + Q).PosSemidef)
    (hsub : (Matrix.rectangularChoi C - Q).PosSemidef)
    (hpt : (Matrix.partialTransposeFst Q).PosSemidef)
    (hker : (Matrix.rectangularChoi C - Q) * Matrix.conjVecTensorId β u = 0) :
    ∃ S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ,
      Matrix.rectangularChoi S = Q ∧
      IsKrausCP (C + S) ∧
      IsKrausCP (C - S) ∧
      IsCompletelyCopositiveMap S ∧
      C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)) :=
  ⟨Matrix.operatorSchmidtMap Q,
    operatorSchmidtMap_satisfies_reverseBlock_hypotheses hadd hsub hpt hker⟩

/-- **Generic Choi-certificate bridge (existential form, compression hypothesis).**
Replaces the kernel hypothesis `(J - Q)(bar u ⊗ I_β) = 0` with the equivalent
compression vanishing `(bar u ⊗ I_β)ᴴ (J - Q) (bar u ⊗ I_β) = 0`. -/
theorem exists_map_of_choiCertificate_compression
    {C : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    {Q : Matrix (α × β) (α × β) ℂ}
    {u : α → ℂ}
    (hadd : (Matrix.rectangularChoi C + Q).PosSemidef)
    (hsub : (Matrix.rectangularChoi C - Q).PosSemidef)
    (hpt : (Matrix.partialTransposeFst Q).PosSemidef)
    (hcomp : (Matrix.conjVecTensorId β u)ᴴ * (Matrix.rectangularChoi C - Q) *
      Matrix.conjVecTensorId β u = 0) :
    ∃ S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ,
      Matrix.rectangularChoi S = Q ∧
      IsKrausCP (C + S) ∧
      IsKrausCP (C - S) ∧
      IsCompletelyCopositiveMap S ∧
      C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)) :=
  exists_map_of_choiCertificate hadd hsub hpt
    ((hsub.mul_eq_zero_iff_conjTranspose_mul_mul_eq_zero (Matrix.conjVecTensorId β u)).mpr hcomp)

/-- **One-copy reverse-block criterion from a Choi certificate.**
Does not require `(rectangularChoi C + Q).PosSemidef`. -/
theorem reverseBlock_posSemidef_of_choiCertificate
    {C : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    {Q : Matrix (α × β) (α × β) ℂ}
    {u v w : α → ℂ}
    (hsub : (Matrix.rectangularChoi C - Q).PosSemidef)
    (hpt : (Matrix.partialTransposeFst Q).PosSemidef)
    (hker : (Matrix.rectangularChoi C - Q) * Matrix.conjVecTensorId β u = 0)
    (hvw : v + w = u) :
    (Matrix.fromBlocks
      (C (Matrix.vecMulVec w (star w)))
      (C (Matrix.vecMulVec v (star w)))
      (C (Matrix.vecMulVec w (star v)))
      (C (Matrix.vecMulVec v (star v)))).PosSemidef := by
  let S := Matrix.operatorSchmidtMap Q
  have hS : Matrix.rectangularChoi S = Q :=
    Matrix.rectangularChoi_leftInverse_operatorSchmidtMap Q
  have hCPsub : IsKrausCP (C - S) := by
    rw [Matrix.isKrausCP_iff_rectangularChoi_posSemidef, Matrix.rectangularChoi_sub, hS]
    exact hsub
  have hcop : IsCompletelyCopositiveMap S :=
    (Matrix.isCompletelyCopositiveMap_operatorSchmidtMap_iff Q).mpr hpt
  have hu : C (Matrix.vecMulVec u (star u)) = S (Matrix.vecMulVec u (star u)) := by
    have hdiff : (Matrix.rectangularChoi (C - S)).PosSemidef := by
      rw [Matrix.rectangularChoi_sub, hS]
      exact hsub
    have hker' : Matrix.rectangularChoi (C - S) * Matrix.conjVecTensorId β u = 0 := by
      rw [Matrix.rectangularChoi_sub, hS]
      exact hker
    have h0 : (C - S) (Matrix.vecMulVec u (star u)) = 0 :=
      (hdiff.rectangularChoi_mul_conjVecTensorId_eq_zero_iff u).mp hker'
    exact sub_eq_zero.mp (by simpa [LinearMap.sub_apply] using h0)
  exact reverseBlock_posSemidef hCPsub hcop hvw hu

/-- **Heterogeneous `N`-copy reverse-block criterion from Choi certificates.** -/
theorem piTensorMap_reverseBlock_posSemidef_of_choiCertificate
    {N : ℕ} {α β : Fin N → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (C : (i : Fin N) → Matrix (α i) (α i) ℂ →ₗ[ℂ] Matrix (β i) (β i) ℂ)
    (Q : (i : Fin N) → Matrix (α i × β i) (α i × β i) ℂ)
    {u : (i : Fin N) → α i → ℂ}
    (hadd : ∀ i, (Matrix.rectangularChoi (C i) + Q i).PosSemidef)
    (hsub : ∀ i, (Matrix.rectangularChoi (C i) - Q i).PosSemidef)
    (hpt : ∀ i, (Matrix.partialTransposeFst (Q i)).PosSemidef)
    (hker : ∀ i, (Matrix.rectangularChoi (C i) - Q i) * Matrix.conjVecTensorId (β i) (u i) = 0)
    {v w : ((i : Fin N) → α i) → ℂ}
    (hvw : v + w = fun x => ∏ i, u i (x i)) :
    (Matrix.fromBlocks
      (Matrix.piTensorMap C (Matrix.vecMulVec w (star w)))
      (Matrix.piTensorMap C (Matrix.vecMulVec v (star w)))
      (Matrix.piTensorMap C (Matrix.vecMulVec w (star v)))
      (Matrix.piTensorMap C (Matrix.vecMulVec v (star v)))).PosSemidef := by
  let S : (i : Fin N) → Matrix (α i) (α i) ℂ →ₗ[ℂ] Matrix (β i) (β i) ℂ :=
    fun i => Matrix.operatorSchmidtMap (Q i)
  have hcert := fun i =>
    operatorSchmidtMap_satisfies_reverseBlock_hypotheses
      (hadd i) (hsub i) (hpt i) (hker i)
  exact piTensorMap_reverseBlock_posSemidef C S
    (fun i => (hcert i).2.1)
    (fun i => (hcert i).2.2.1)
    (fun i => (hcert i).2.2.2.1)
    (fun i => (hcert i).2.2.2.2)
    hvw

/-- **Homogeneous all-copy reverse-block criterion from a single finite Choi certificate.**
If `J = rectangularChoi C` and `Q` satisfy `J + Q ≥ 0`, `J - Q ≥ 0`, `Q^{T_1} ≥ 0`,
and `(J - Q)(bar u ⊗ I_β) = 0`, then for every `N : ℕ` and all complex vectors
`v, w : (Fin N → α) → ℂ` with `v + w = u^{⊗ N}`, the `N`-copy reverse-block matrix for
`C^{⊗ N}` is positive semidefinite. -/
theorem piTensorMap_const_reverseBlock_posSemidef_of_choiCertificate
    (N : ℕ)
    {C : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    {Q : Matrix (α × β) (α × β) ℂ}
    {u : α → ℂ}
    (hadd : (Matrix.rectangularChoi C + Q).PosSemidef)
    (hsub : (Matrix.rectangularChoi C - Q).PosSemidef)
    (hpt : (Matrix.partialTransposeFst Q).PosSemidef)
    (hker : (Matrix.rectangularChoi C - Q) * Matrix.conjVecTensorId β u = 0)
    {v w : (Fin N → α) → ℂ}
    (hvw : v + w = fun x => ∏ i : Fin N, u (x i)) :
    (Matrix.fromBlocks
      (Matrix.piTensorMap (fun _ : Fin N => C) (Matrix.vecMulVec w (star w)))
      (Matrix.piTensorMap (fun _ : Fin N => C) (Matrix.vecMulVec v (star w)))
      (Matrix.piTensorMap (fun _ : Fin N => C) (Matrix.vecMulVec w (star v)))
      (Matrix.piTensorMap (fun _ : Fin N => C) (Matrix.vecMulVec v (star v)))).PosSemidef := by
  obtain ⟨S, _, hCPadd, hCPsub, hcop, hu⟩ :=
    exists_map_of_choiCertificate hadd hsub hpt hker
  exact piTensorMap_const_reverseBlock_posSemidef N hCPadd hCPsub hcop hu hvw

/-- **Homogeneous all-copy reverse-block criterion from a Choi certificate (compression form).**
Uses the equivalent compression hypothesis `(bar u ⊗ I_β)ᴴ (J - Q) (bar u ⊗ I_β) = 0`
in place of `(J - Q)(bar u ⊗ I_β) = 0`. -/
theorem piTensorMap_const_reverseBlock_posSemidef_of_choiCertificate_compression
    (N : ℕ)
    {C : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ}
    {Q : Matrix (α × β) (α × β) ℂ}
    {u : α → ℂ}
    (hadd : (Matrix.rectangularChoi C + Q).PosSemidef)
    (hsub : (Matrix.rectangularChoi C - Q).PosSemidef)
    (hpt : (Matrix.partialTransposeFst Q).PosSemidef)
    (hcomp : (Matrix.conjVecTensorId β u)ᴴ * (Matrix.rectangularChoi C - Q) *
      Matrix.conjVecTensorId β u = 0)
    {v w : (Fin N → α) → ℂ}
    (hvw : v + w = fun x => ∏ i : Fin N, u (x i)) :
    (Matrix.fromBlocks
      (Matrix.piTensorMap (fun _ : Fin N => C) (Matrix.vecMulVec w (star w)))
      (Matrix.piTensorMap (fun _ : Fin N => C) (Matrix.vecMulVec v (star w)))
      (Matrix.piTensorMap (fun _ : Fin N => C) (Matrix.vecMulVec w (star v)))
      (Matrix.piTensorMap (fun _ : Fin N => C) (Matrix.vecMulVec v (star v)))).PosSemidef := by
  obtain ⟨S, _, hCPadd, hCPsub, hcop, hu⟩ :=
    exists_map_of_choiCertificate_compression hadd hsub hpt hcomp
  exact piTensorMap_const_reverseBlock_posSemidef N hCPadd hCPsub hcop hu hvw

end ChoiCertificateBridge
