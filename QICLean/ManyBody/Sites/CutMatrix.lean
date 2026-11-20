/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.MaximalOverlap
import QICLean.ManyBody.Sites.Placement
import QICLean.ManyBody.Sites.RegionState

/-!
# The coefficient matrix of a vector across a cut

A region `D` cuts every configuration into its parts on `D` and outside `D`, through
`ManyBody.cutEquiv`. The cut matrix of a vector `ψ` across `D` has the configurations of `D` as
rows and those of the other sites as columns, and its entry at `(σ, τ)` is the coefficient of `ψ`
at the configuration glued from `σ` and `τ`. It is the Schmidt coefficient matrix
`Matrix.schmidtCoeffMatrix` of `ψ` read in the coordinates of the cut, and its rank, the cut rank,
is the Schmidt rank of `ψ` across `D`. For the chain `Fin N`, the cut after `k` sites is the region
`{i : i < k}`.

The cut rank is at most the dimension of either side, it vanishes only at the zero vector, and
it is one for a nonzero vector at the empty region and at the region of all sites. Exchanging a
region and its complement transposes the cut matrix, so the cut rank does not change. The cut
rank is the rank of the regional state. An operator that factors across the cut as `L ⊗ R`
multiplies the cut matrix by `L` on the left and by the transpose of `R` on the right, so it
cannot increase the cut rank; this applies to every operator supported on one side of the cut,
and to rectangular operators between different basis families.

The statements allow arbitrary finite basis types, including empty ones, and unnormalized
vectors. The vectors are functions on the configurations; a vector of
`EuclideanSpace ℂ (Config X)` enters through its coefficient function.

The cut matrix and cut rank replace the coefficient matrices of TNLean at commit `414a18fb88`:
`TNLean.MPS.AreaLaw.cutMatrix` (`TNLean/MPS/AreaLaw/OpenMPS.lean`), `MPSPreparation.cutMatrix`,
`MPSPreparation.cutRank` (`TNLean/MPS/Preparation/CutRank.lean`),
`MPSPreparation.cutCoefficientMatrix`, `MPSPreparation.cutCoefficientRank`
(`TNLean/MPS/Preparation/MinimalCutRepresentationCuts.lean`) and
`TNLean.PEPS.physicalCutMatrix` (`TNLean/PEPS/PhysicalProductCut.lean`). Changes: one region `D`
of an arbitrary finite set of sites with arbitrary basis types, in place of prefixes of a chain
with one local dimension or a predicate on the sites; the factorization lemma of
`physicalCutMatrix_physicalProductMap` is stated for any operator factoring across the cut.

## Main definitions

* `ManyBody.cutMatrix` — the coefficient matrix of a vector across a region.
* `ManyBody.cutRank` — its rank, the Schmidt rank across the region.

## Main results

* `ManyBody.cutMatrix_cutEquiv` — the cut matrix at the two parts of a configuration.
* `ManyBody.cutRank_le_prod_card`, `ManyBody.cutRank_le_prod_card_compl` — dimension bounds.
* `ManyBody.cutRank_eq_zero_iff`, `ManyBody.cutRank_pos` — only the zero vector has cut rank
  zero.
* `ManyBody.cutRank_compl` — complementary regions have the same cut rank.
* `ManyBody.rank_regionState_eq_cutRank` — the regional state has rank the cut rank.
* `ManyBody.cutMatrix_mulVec_of_cutOperator_eq_kronecker`,
  `ManyBody.cutRank_mulVec_le_of_cutOperator_eq_kronecker` — operators factoring across the cut.
* `ManyBody.cutRank_mulVec_le_of_mem_supportedOperators` — an operator supported on one side of
  the cut does not increase the cut rank.

## References

* Pérez-García, Verstraete, Wolf, Cirac, *Matrix product state representations*,
  arXiv:quant-ph/0608197, lines 419–458 (the rank of `ρ_k` across a cut of the chain).
* Schuch, Cirac, Pérez-García, *PEPS as ground states: degeneracy and topology*,
  arXiv:1001.3807, Corollary 6.10, lines 2074–2090 (local maps and the Schmidt rank).
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace ManyBody

variable {V : Type*} [DecidableEq V] {X : V → Type*}

/-- The cut matrix of a vector `ψ` across the region `D`: the entry at a configuration `σ` of `D`
and a configuration `τ` of the other sites is the coefficient of `ψ` at the configuration glued
from `σ` and `τ`. It is the Schmidt coefficient matrix of `ψ` in the coordinates of the cut.
Source: arXiv:quant-ph/0608197, lines 456–458; arXiv:1001.3807, Corollary 6.10. -/
def cutMatrix (D : Finset V) (ψ : Config X → ℂ) :
    Matrix (RegionConfig X D) (ComplConfig X D) ℂ :=
  schmidtCoeffMatrix (ψ ∘ (cutEquiv X D).symm)

variable {D : Finset V}

@[simp] theorem cutMatrix_apply (ψ : Config X → ℂ) (σ : RegionConfig X D)
    (τ : ComplConfig X D) : cutMatrix D ψ σ τ = ψ ((cutEquiv X D).symm (σ, τ)) :=
  rfl

/-- The cut matrix at the two parts of a configuration is the coefficient at the configuration. -/
theorem cutMatrix_cutEquiv (ψ : Config X → ℂ) (σ : Config X) :
    cutMatrix D ψ (cutEquiv X D σ).1 (cutEquiv X D σ).2 = ψ σ := by
  rw [cutMatrix_apply, Prod.mk.eta, Equiv.symm_apply_apply]

@[simp] theorem cutMatrix_zero : cutMatrix D (0 : Config X → ℂ) = 0 :=
  rfl

theorem cutMatrix_add (ψ φ : Config X → ℂ) :
    cutMatrix D (ψ + φ) = cutMatrix D ψ + cutMatrix D φ :=
  rfl

theorem cutMatrix_smul (c : ℂ) (ψ : Config X → ℂ) : cutMatrix D (c • ψ) = c • cutMatrix D ψ :=
  rfl

/-- The cut matrix determines the vector. -/
theorem cutMatrix_injective : Function.Injective (cutMatrix (X := X) D) := by
  intro ψ φ h
  funext σ
  rw [← cutMatrix_cutEquiv ψ σ, ← cutMatrix_cutEquiv φ σ, h]

@[simp] theorem cutMatrix_eq_zero_iff {ψ : Config X → ℂ} : cutMatrix D ψ = 0 ↔ ψ = 0 :=
  cutMatrix_injective.eq_iff' cutMatrix_zero

/-! ### The cut rank -/

variable [Fintype V] [∀ v, Fintype (X v)]

variable (D) in
/-- The cut rank of `ψ` across `D`: the rank of its cut matrix, the Schmidt rank of `ψ` across
the cut. Source: arXiv:quant-ph/0608197, lines 456–458, the rank of `ρ_k`. -/
noncomputable def cutRank (ψ : Config X → ℂ) : ℕ :=
  (cutMatrix D ψ).rank

omit [Fintype V] [∀ v, Fintype (X v)] in
/-- The configurations of a region are counted by the product of the local dimensions. -/
theorem card_regionConfig [∀ v, Fintype (X v)] (D : Finset V) :
    Fintype.card (RegionConfig X D) = ∏ v ∈ D, Fintype.card (X v) := by
  rw [Fintype.card_pi]
  exact Finset.prod_coe_sort D fun v ↦ Fintype.card (X v)

omit [∀ v, Fintype (X v)] in
/-- The configurations outside a region are counted by the product of the local dimensions
outside it. -/
theorem card_complConfig [∀ v, Fintype (X v)] (D : Finset V) :
    Fintype.card (ComplConfig X D) = ∏ v ∈ Dᶜ, Fintype.card (X v) := by
  rw [Fintype.card_pi]
  exact (Finset.prod_subtype Dᶜ (fun _ ↦ Finset.mem_compl) fun v ↦ Fintype.card (X v)).symm

/-- The cut rank is at most the dimension `∏_{v ∈ D} dim 𝓗_v` of the region. -/
theorem cutRank_le_prod_card (ψ : Config X → ℂ) :
    cutRank D ψ ≤ ∏ v ∈ D, Fintype.card (X v) :=
  (rank_le_card_height _).trans_eq (card_regionConfig D)

/-- The cut rank is at most the dimension `∏_{v ∉ D} dim 𝓗_v` of the other sites. -/
theorem cutRank_le_prod_card_compl (ψ : Config X → ℂ) :
    cutRank D ψ ≤ ∏ v ∈ Dᶜ, Fintype.card (X v) :=
  (rank_le_card_width _).trans_eq (card_complConfig D)

/-- With `q` states at every site, the cut rank is at most `q ^ |D|`. -/
theorem cutRank_le_pow_card {q : ℕ} (ψ : (V → Fin q) → ℂ) :
    cutRank (X := fun _ ↦ Fin q) D ψ ≤ q ^ D.card := by
  simpa using cutRank_le_prod_card (D := D) ψ

/-- With `q` states at every site, the cut rank is at most `q ^ |Dᶜ|`. -/
theorem cutRank_le_pow_card_compl {q : ℕ} (ψ : (V → Fin q) → ℂ) :
    cutRank (X := fun _ ↦ Fin q) D ψ ≤ q ^ Dᶜ.card := by
  simpa using cutRank_le_prod_card_compl (D := D) ψ

/-- Only the zero vector has cut rank zero. -/
@[simp] theorem cutRank_eq_zero_iff {ψ : Config X → ℂ} : cutRank D ψ = 0 ↔ ψ = 0 := by
  classical
  rw [cutRank, rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot, ← toLin'_apply',
    LinearEquiv.map_eq_zero_iff, cutMatrix_eq_zero_iff]

/-- A nonzero vector has positive cut rank across every region. -/
theorem cutRank_pos {ψ : Config X → ℂ} (hψ : ψ ≠ 0) : 0 < cutRank D ψ :=
  Nat.pos_of_ne_zero (cutRank_eq_zero_iff.not.mpr hψ)

/-- Across the empty region the cut matrix has one row, so the cut rank is at most one. -/
theorem cutRank_empty_le_one (ψ : Config X → ℂ) : cutRank ∅ ψ ≤ 1 :=
  (cutRank_le_prod_card ψ).trans_eq Finset.prod_empty

/-- Across the region of all sites the cut matrix has one column, so the cut rank is at most
one. -/
theorem cutRank_univ_le_one (ψ : Config X → ℂ) : cutRank Finset.univ ψ ≤ 1 :=
  (cutRank_le_prod_card_compl ψ).trans_eq (by simp)

/-- A nonzero vector has cut rank one across the empty region. -/
theorem cutRank_empty {ψ : Config X → ℂ} (hψ : ψ ≠ 0) : cutRank ∅ ψ = 1 :=
  le_antisymm (cutRank_empty_le_one ψ) (cutRank_pos hψ)

/-- A nonzero vector has cut rank one across the region of all sites. -/
theorem cutRank_univ {ψ : Config X → ℂ} (hψ : ψ ≠ 0) : cutRank Finset.univ ψ = 1 :=
  le_antisymm (cutRank_univ_le_one ψ) (cutRank_pos hψ)

/-- Complementary regions have the same cut rank: exchanging a region and its complement
transposes the cut matrix, up to relabelling the configurations of each side.
Source: arXiv:quant-ph/0608197, lines 456–458, the two reduced density operators of a cut. -/
@[simp] theorem cutRank_compl (ψ : Config X → ℂ) : cutRank Dᶜ ψ = cutRank D ψ := by
  let e : RegionConfig X D ≃ ComplConfig X Dᶜ :=
    { toFun := fun x v ↦ x ⟨v, not_not.mp (mt Finset.mem_compl.mpr v.2)⟩
      invFun := fun x v ↦ x ⟨v, fun h ↦ Finset.mem_compl.mp h v.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have h : cutMatrix Dᶜ ψ = (cutMatrix D ψ)ᵀ.submatrix (complementEquiv X D).symm e.symm := by
    ext σ τ
    simp only [cutMatrix_apply, submatrix_apply, transpose_apply]
    congr 1
    funext v
    by_cases hv : v ∈ D
    · rw [cutEquiv_symm_apply_not_mem _ _ (by simpa using hv), cutEquiv_symm_apply_mem _ _ hv]
      rfl
    · rw [cutEquiv_symm_apply_mem _ _ (by simpa using hv), cutEquiv_symm_apply_not_mem _ _ hv]
      rfl
  rw [cutRank, h, rank_submatrix, rank_transpose, cutRank]

/-- The regional state `ρ_{ψ,D} = Tr_{Dᶜ} |ψ⟩⟨ψ|` is `C Cᴴ` for the cut matrix `C`. -/
theorem regionState_eq_cutMatrix_mul_conjTranspose (ψ : EuclideanSpace ℂ (Config X))
    (D : Finset V) : regionState ψ D = cutMatrix D ψ * (cutMatrix D ψ)ᴴ := by
  rw [regionState_eq_partialTraceRight_cutVector, partialTraceRight_vecMulVec_eq]
  rfl

/-- **The rank of a regional state is the cut rank.** Source: arXiv:quant-ph/0608197,
lines 456–458. -/
theorem rank_regionState_eq_cutRank (ψ : EuclideanSpace ℂ (Config X)) (D : Finset V) :
    (regionState ψ D).rank = cutRank D ψ := by
  rw [regionState_eq_cutMatrix_mul_conjTranspose, rank_self_mul_conjTranspose, cutRank]

/-! ### Operators factoring across the cut -/

section Factor

variable {Y : V → Type*}

/-- **Operators factoring across the cut.** If an operator `T` from the system `X` to the
system `Y` is `L ⊗ R` in the coordinates of the cut along `D`, it multiplies the cut matrix by
`L` on the left and by the transpose of `R` on the right. The operator may be rectangular.
Source: arXiv:1001.3807, Corollary 6.10, lines 2074–2090. -/
theorem cutMatrix_mulVec_of_cutOperator_eq_kronecker {T : Matrix (Config Y) (Config X) ℂ}
    {L : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ}
    {R : Matrix (ComplConfig Y D) (ComplConfig X D) ℂ}
    (hT : reindex (cutEquiv Y D) (cutEquiv X D) T = L ⊗ₖ R) (ψ : Config X → ℂ) :
    cutMatrix D (T *ᵥ ψ) = L * cutMatrix D ψ * Rᵀ := by
  ext σ τ
  have hentry (a : RegionConfig X D) (b : ComplConfig X D) :
      T ((cutEquiv Y D).symm (σ, τ)) ((cutEquiv X D).symm (a, b)) = L σ a * R τ b := by
    simpa using congrFun (congrFun hT (σ, τ)) (a, b)
  simp only [cutMatrix_apply, mulVec, dotProduct, mul_apply, transpose_apply]
  rw [← (cutEquiv X D).symm.sum_comp, Fintype.sum_prod_type]
  simp only [hentry, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
  ring

/-- An operator factoring across the cut does not increase the cut rank. Source:
arXiv:1001.3807, Corollary 6.10, lines 2074–2090. -/
theorem cutRank_mulVec_le_of_cutOperator_eq_kronecker [∀ v, Fintype (Y v)]
    {T : Matrix (Config Y) (Config X) ℂ}
    {L : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ}
    {R : Matrix (ComplConfig Y D) (ComplConfig X D) ℂ}
    (hT : reindex (cutEquiv Y D) (cutEquiv X D) T = L ⊗ₖ R) (ψ : Config X → ℂ) :
    cutRank D (T *ᵥ ψ) ≤ cutRank D ψ := by
  rw [cutRank, cutMatrix_mulVec_of_cutOperator_eq_kronecker hT]
  exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

end Factor

variable [∀ v, DecidableEq (X v)]

/-- A matrix placed on the region `D` multiplies the cut matrix across `D` on the left. -/
theorem cutMatrix_place_mulVec (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ)
    (ψ : Config X → ℂ) : cutMatrix D (place D K *ᵥ ψ) = K * cutMatrix D ψ := by
  rw [cutMatrix_mulVec_of_cutOperator_eq_kronecker (cutOperator_place K), transpose_one,
    Matrix.mul_one]

/-- **Local operators preserve the cut rank bound.** An operator supported inside `D` or
outside `D` does not increase the cut rank across `D`. Source: arXiv:1001.3807,
Corollary 6.10, lines 2074–2090. -/
theorem cutRank_mulVec_le_of_mem_supportedOperators {S : Finset V}
    {T : Matrix (Config X) (Config X) ℂ} (hT : T ∈ supportedOperators X S)
    (hS : S ⊆ D ∨ Disjoint S D) (ψ : Config X → ℂ) :
    cutRank D (T *ᵥ ψ) ≤ cutRank D ψ := by
  rcases hS with hS | hS
  · obtain ⟨K, rfl⟩ := exists_eq_place_of_mem_supportedOperators
      (supportedOperators_mono hS hT)
    exact cutRank_mulVec_le_of_cutOperator_eq_kronecker (cutOperator_place K) ψ
  · obtain ⟨B, rfl⟩ := exists_eq_one_kronecker_of_mem_supportedOperators hS hT
    refine cutRank_mulVec_le_of_cutOperator_eq_kronecker (L := 1) (R := B) ?_ ψ
    ext a b
    simp

end ManyBody
