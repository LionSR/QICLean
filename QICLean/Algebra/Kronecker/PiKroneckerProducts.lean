/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Kronecker.PiKronecker
import QICLean.Algebra.Combinatorics.TupleEquiv

/-!
# Products, powers and coordinates of Kronecker products of families

For a finite family of square matrices, the Kronecker product `⊗ₖ K k` is a monoid
homomorphism, so it turns an ordered product of families into the family of ordered products,
and it maps a family of scalar matrices `f k • 1` to the scalar `∏ₖ f k`. It maps Hermitian
families to Hermitian matrices, and the entrywise conjugate of a family to the transpose of the
adjoint.

For a constant family `fun _ : Fin N ↦ V`, the tensor power `V^{⊗N}` of an isometry is an
isometry, `V^{⊗N} (V^{⊗N})ᴴ = (V Vᴴ)^{⊗N}`, and on two and three sites the power is the
iterated Kronecker product `V ⊗ V` and `V ⊗ (V ⊗ V)` after relabelling the configurations.

In coordinates, matrices `W_k : ℂ^κ → ℂ^{n_k}`, one on each of `M` sites, change the inner
product of two vectors on `M` sites by the product of the Gram matrices `W_k† W_k`; isometries
and partial isometries on the supports of the vectors preserve the inner product
(arXiv:2307.01696, Supplemental Material, proof of Lemma 1 and of Lemma 1'(i)).

Moved from TNLean at commit `600676ccac`:
`TNLean/MPS/CanonicalForm/SimpleMPO/Vectorized.lean`,
`TNLean/MPS/MPU/DomainWall/FiniteGroupDetectorTensor.lean`,
`TNLean/MPS/Operator/PhysicalSector/SitewisePhysicalMatrix.lean`,
`TNLean/MPS/FundamentalTheorem/PhysicalSupport/IsometricAdjacentBondTransport.lean`,
`TNLean/MPS/Operator/Interaction/PhysicalGibbsEmbedding.lean` and
`TNLean/MPS/Transfer/RenormalizationFixedPoint/BlockIsometryState.lean`. The conjugate
transpose, list product, scalar, Hermitian and monoid statements are generalized from constant
families on `Fin N` to families on a finite type with site-dependent labels.

## Main declarations

* `Matrix.piKroneckerMonoidHom`, `Matrix.list_prod_map_piKronecker`,
  `Matrix.piKronecker_smul_one`.
* `Matrix.IsHermitian.piKronecker`, `Matrix.transpose_piKronecker_map_star`.
* `Matrix.piKronecker_const_isometry`, `Matrix.piKronecker_const_mul_conjTranspose`,
  `Matrix.reindex_piKronecker_two`, `Matrix.reindex_piKronecker_three`.
* `Matrix.sum_star_mul_prod_eq_sum_conjTranspose_mul`, `Matrix.sum_star_mul_prod_of_support`,
  `Matrix.IsIsometry.sum_star_mul_prod`, `Matrix.IsIsometry.sum_star_mul_prod_const`.
-/

open scoped BigOperators Matrix Kronecker

namespace Matrix

section Family

variable {ν : Type*} [Fintype ν] {ι κ : ν → Type*}

/-- The transpose of the Kronecker product of the entrywise conjugates is the conjugate
transpose of the Kronecker product. -/
theorem transpose_piKronecker_map_star (K : (k : ν) → Matrix (ι k) (κ k) ℂ) :
    (piKronecker fun k ↦ (K k).map (starRingEnd ℂ))ᵀ = (piKronecker K)ᴴ := by
  rw [transpose_piKronecker, conjTranspose_piKronecker]
  rfl

/-- The Kronecker product of a family of Hermitian matrices is Hermitian. -/
theorem IsHermitian.piKronecker {K : (k : ν) → Matrix (ι k) (ι k) ℂ}
    (hK : ∀ k, (K k).IsHermitian) : (Matrix.piKronecker K).IsHermitian := by
  rw [IsHermitian, conjTranspose_piKronecker]
  exact congrArg Matrix.piKronecker (funext hK)

/-- The Kronecker product of a family of scalar matrices `f k • 1` is the scalar `∏ₖ f k`. -/
theorem piKronecker_smul_one [∀ k, DecidableEq (ι k)] (f : ν → ℂ) :
    piKronecker (fun k ↦ f k • (1 : Matrix (ι k) (ι k) ℂ)) = (∏ k, f k) • 1 := by
  conv_rhs => rw [← piKronecker_one (ν := ν) (ι := ι)]
  ext x y
  simp only [piKronecker_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

variable [DecidableEq ν] [∀ k, Fintype (ι k)] [∀ k, DecidableEq (ι k)]

/-- The Kronecker product of square families, as a monoid homomorphism. -/
def piKroneckerMonoidHom :
    ((k : ν) → Matrix (ι k) (ι k) ℂ) →* Matrix ((k : ν) → ι k) ((k : ν) → ι k) ℂ where
  toFun := piKronecker
  map_one' := piKronecker_one
  map_mul' A B := (piKronecker_mul A B).symm

/-- The ordered product of the Kronecker products of a list of families is the Kronecker product
of the sitewise ordered products. -/
theorem list_prod_map_piKronecker {β : Type*} (l : List β)
    (A : β → (k : ν) → Matrix (ι k) (ι k) ℂ) :
    (l.map fun r ↦ piKronecker (A r)).prod = piKronecker fun k ↦ (l.map fun r ↦ A r k).prod := by
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.map_cons, List.prod_cons, ih, piKronecker_mul]

end Family

section Const

variable {d e : ℕ}

/-- The tensor power of an isometry is an isometry. -/
theorem piKronecker_const_isometry (V : Matrix (Fin e) (Fin d) ℂ) (hV : Vᴴ * V = 1) (N : ℕ) :
    (piKronecker fun _ : Fin N ↦ V)ᴴ * (piKronecker fun _ : Fin N ↦ V) = 1 := by
  rw [conjTranspose_piKronecker, piKronecker_mul, hV]
  exact piKronecker_one

/-- The product of a tensor power with its conjugate transpose is the tensor power of the
one-site product. -/
theorem piKronecker_const_mul_conjTranspose (V : Matrix (Fin d) (Fin e) ℂ) (N : ℕ) :
    (piKronecker fun _ : Fin N ↦ V) * (piKronecker fun _ : Fin N ↦ V)ᴴ =
      piKronecker fun _ : Fin N ↦ V * Vᴴ := by
  rw [conjTranspose_piKronecker]
  exact piKronecker_mul (fun _ : Fin N ↦ V) (fun _ : Fin N ↦ Vᴴ)

/-- On two sites, the tensor power is the Kronecker square. -/
theorem reindex_piKronecker_two (V : Matrix (Fin e) (Fin d) ℂ) :
    reindex (finTwoArrowEquiv (Fin e)) (finTwoArrowEquiv (Fin d))
        (piKronecker fun _ : Fin 2 ↦ V) = V ⊗ₖ V := by
  ext ⟨i, j⟩ ⟨a, b⟩
  simp [reindex_apply, piKronecker_apply, kroneckerMap_apply, finTwoArrowEquiv]

/-- On three sites, the tensor power is the right-associated Kronecker cube. -/
theorem reindex_piKronecker_three (V : Matrix (Fin d) (Fin e) ℂ) :
    reindex (finThreeArrowEquiv (Fin d)) (finThreeArrowEquiv (Fin e))
        (piKronecker fun _ : Fin 3 ↦ V) = V ⊗ₖ (V ⊗ₖ V) := by
  ext ⟨i, j, k⟩ ⟨a, b, c⟩
  simp only [reindex_apply, submatrix_apply, finThreeArrowEquiv_symm_apply, Nat.succ_eq_add_one,
    Nat.reduceAdd, kroneckerMap_apply]
  change (∏ n : Fin 3, V (![i, j, k] n) (![a, b, c] n)) = V i a * (V j b * V k c)
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp

end Const

section Coordinates

/-- **Inner products after matrices on the sites.** For matrices `W_k : ℂ^κ → ℂ^{n_k}`, one on
each of `M` sites, `⟨(⊗ₖ W_k) ψ, (⊗ₖ W_k) φ⟩ = ∑_{τ, τ'} (∏ₖ (W_k† W_k)_{τ_k τ'_k}) ψ(τ)^* φ(τ')`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors":
the Gram matrices `V_k†V_k` of the isometric factors. -/
theorem sum_star_mul_prod_eq_sum_conjTranspose_mul {M : ℕ} {n : Fin M → Type*}
    [∀ k, Fintype (n k)] {κ : Type*} [Fintype κ] (W : ∀ k, Matrix (n k) κ ℂ)
    (ψ φ : (Fin M → κ) → ℂ) :
    ∑ s : ∀ k, n k, star (∑ τ, (∏ j, W j (s j) (τ j)) * ψ τ) *
        ∑ τ, (∏ j, W j (s j) (τ j)) * φ τ =
      ∑ τ, ∑ τ', (∏ j, ((W j)ᴴ * W j) (τ j) (τ' j)) * (star (ψ τ) * φ τ') := by
  classical
  calc ∑ s : ∀ k, n k, star (∑ τ, (∏ j, W j (s j) (τ j)) * ψ τ) *
        ∑ τ, (∏ j, W j (s j) (τ j)) * φ τ
      = ∑ s : ∀ k, n k, ∑ τ, ∑ τ', (∏ j, (star (W j (s j) (τ j)) * W j (s j) (τ' j))) *
          (star (ψ τ) * φ τ') := by
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [star_sum, star_mul, star_prod, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun τ' _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
    _ = ∑ τ, ∑ τ', (∑ s : ∀ k, n k, ∏ j, (star (W j (s j) (τ j)) * W j (s j) (τ' j))) *
          (star (ψ τ) * φ τ') := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun τ _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun τ' _ => ?_
        rw [← Fintype.prod_sum (fun j i => star (W j i (τ j)) * W j i (τ' j))]
        simp only [mul_apply, conjTranspose_apply]

/-- **Partial isometries on the sites preserve inner products of supported vectors.** Let
`W_k : ℂ^κ → ℂ^{n_k}`, one on each of `M` sites, have orthonormal columns on a set `S_k` of
inputs and zero columns outside, `W_k† W_k = Π_{S_k}`. If `ψ^* φ` vanishes at every
configuration `τ` with some `τ_k ∉ S_k`, then `⟨(⊗ₖ W_k) ψ, (⊗ₖ W_k) φ⟩ = ⟨ψ, φ⟩`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors":
the partial isometries `V_k` with `V_k†V_k = Π_k`. -/
theorem sum_star_mul_prod_of_support {M : ℕ} {n : Fin M → Type*} [∀ k, Fintype (n k)]
    {κ : Type*} [Fintype κ] [DecidableEq κ] {W : ∀ k, Matrix (n k) κ ℂ} {S : Fin M → Set κ}
    [∀ k, DecidablePred (· ∈ S k)]
    (hW : ∀ k a b, ∑ i, star (W k i a) * W k i b = if a = b ∧ a ∈ S k then 1 else 0)
    (ψ φ : (Fin M → κ) → ℂ) (hψφ : ∀ τ, (∃ k, τ k ∉ S k) → star (ψ τ) * φ τ = 0) :
    ∑ s : ∀ k, n k, star (∑ τ, (∏ j, W j (s j) (τ j)) * ψ τ) *
        ∑ τ, (∏ j, W j (s j) (τ j)) * φ τ =
      ∑ τ, star (ψ τ) * φ τ := by
  classical
  have hprod : ∀ τ τ' : Fin M → κ, ∏ j, ((W j)ᴴ * W j) (τ j) (τ' j) =
      if τ = τ' ∧ ∀ j, τ j ∈ S j then 1 else 0 := fun τ τ' => by
    simp only [mul_apply, conjTranspose_apply, hW]
    by_cases h : τ = τ' ∧ ∀ j, τ j ∈ S j
    · obtain ⟨rfl, hS⟩ := h
      simp [hS]
    · rw [ite_eq_right h]
      have : ∃ j, ¬(τ j = τ' j ∧ τ j ∈ S j) := by
        by_contra hall
        push Not at hall
        exact h ⟨funext fun j => (hall j).1, fun j => (hall j).2⟩
      obtain ⟨j, hj⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)
  rw [sum_star_mul_prod_eq_sum_conjTranspose_mul]
  simp only [hprod, ite_mul, one_mul, zero_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  by_cases hS : ∀ j, τ j ∈ S j
  · simp [hS]
  · rw [hψφ τ (not_forall.mp hS),
      Finset.sum_eq_zero fun τ' _ => ite_eq_right fun h => hS h.2]

/-- Isometries `W_k : ℂ^κ → ℂ^{n_k}`, one on each of `M` sites, preserve inner products:
`⟨(⊗ₖ W_k) ψ, (⊗ₖ W_k) φ⟩ = ⟨ψ, φ⟩`.

arXiv:2307.01696, eq. (10), and Supplemental Material, proof of Lemma 1'(i): the isometries on
the blocks do not change norms or overlaps. The target spaces may differ from site to site, as
for blocks of different lengths. This is `Matrix.sum_star_mul_prod_of_support` with every input
kept. -/
theorem IsIsometry.sum_star_mul_prod {M : ℕ} {n : Fin M → Type*} [∀ k, Fintype (n k)]
    {κ : Type*} [Fintype κ] [DecidableEq κ] {W : ∀ k, Matrix (n k) κ ℂ}
    (hW : ∀ k, (W k).IsIsometry) (ψ φ : (Fin M → κ) → ℂ) :
    ∑ s : ∀ k, n k, star (∑ τ, (∏ j, W j (s j) (τ j)) * ψ τ) *
        ∑ τ, (∏ j, W j (s j) (τ j)) * φ τ =
      ∑ τ, star (ψ τ) * φ τ := by
  classical
  refine sum_star_mul_prod_of_support (S := fun _ => Set.univ) (fun j a b => ?_) ψ φ
    fun τ ⟨k, hk⟩ => absurd (Set.mem_univ _) hk
  have h := congrFun (congrFun (hW j) a) b
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simpa [Matrix.conjTranspose_apply] using h

/-- An isometry `W : ℂ^κ → ℂ^n` applied on every site preserves inner products of vectors on
`M` sites: `⟨W^{⊗M} ψ, W^{⊗M} φ⟩ = ⟨ψ, φ⟩`; in particular `‖W^{⊗M} ψ‖² = ‖ψ‖²`.

arXiv:2307.01696, eq. (10), and Supplemental Material, proof of Lemma 1'(i): the isometries
`V^{⊗N/q}` do not change norms or overlaps. -/
theorem IsIsometry.sum_star_mul_prod_const {n κ : Type*} [Fintype n] [Fintype κ]
    [DecidableEq κ] {W : Matrix n κ ℂ} (hW : W.IsIsometry) {M : ℕ}
    (ψ φ : (Fin M → κ) → ℂ) :
    ∑ s : Fin M → n, star (∑ τ, (∏ j, W (s j) (τ j)) * ψ τ) * ∑ τ, (∏ j, W (s j) (τ j)) * φ τ =
      ∑ τ, star (ψ τ) * φ τ :=
  IsIsometry.sum_star_mul_prod (n := fun _ => n) (fun _ => hW) ψ φ

end Coordinates

end Matrix
