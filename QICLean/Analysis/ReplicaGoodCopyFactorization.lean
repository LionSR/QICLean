/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaExcitationDecomposition
import QICLean.Channel.FiniteProduct

/-!
# Ground-state factors in exact excitation components

The ground state on the good physical copies is extracted by partial contraction.
The remaining vector retains every bad physical coordinate and every auxiliary
coordinate. Empty regions and zero components are included.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 441–456, `comparator:defect-mass`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Permutation invariance and the subsequent metric comparisons are separate
steps of the source argument.
Independently formalized; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:defect-mass.
-/

open scoped BigOperators Matrix Kronecker

noncomputable section

namespace Matrix

variable {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]

/-- Partial contraction against the actual ground state on every good physical
copy, with all other coordinates retained. OpenAI area-law manuscript,
`comparator:defect-mass`, lines 441–456. -/
def replicaGoodCopyRemainder (Ω : A → ℂ) {k : ℕ} (B : Finset (Fin k))
    (u : ((Fin k → A) × C) → ℂ) :
    (FiniteProduct.Configuration (fun _ : Fin k ↦ A) B × C) → ℂ :=
  fun bc ↦ ∑ g : FiniteProduct.Configuration (fun _ : Fin k ↦ A) Bᶜ,
    (∏ i : ↥(Bᶜ), star (Ω (g i))) *
      u ((FiniteProduct.splitEquiv (fun _ : Fin k ↦ A) B).symm (bc.1, g), bc.2)

private theorem excitation_row_factor (Ω : A → ℂ) {k : ℕ} (B : Finset (Fin k))
    (b : FiniteProduct.Configuration (fun _ : Fin k ↦ A) B)
    (g : FiniteProduct.Configuration (fun _ : Fin k ↦ A) Bᶜ) (y : Fin k → A) :
    replicaExcitationProjection Ω k B
      ((FiniteProduct.splitEquiv (fun _ : Fin k ↦ A) B).symm (b, g)) y =
    (∏ i : ↥(Bᶜ), Ω (g i)) *
      ((∏ i : B, (1 - vecMulVec Ω (star Ω)) (b i) (y i)) *
        ∏ i : ↥(Bᶜ), star (Ω (y i))) := by
  simp only [replicaExcitationProjection, finKronecker_apply, Matrix.ite_apply,
    Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.filter_notMem_eq_sdiff, ← Finset.compl_eq_univ_sdiff]
  rw [← Finset.prod_coe_sort B, ← Finset.prod_coe_sort Bᶜ]
  have hg (i : ↥(Bᶜ)) := FiniteProduct.splitEquiv_symm_apply_of_notMem
    (fun _ : Fin k ↦ A) B b g i (Finset.mem_compl.mp i.property)
  simp [hg, vecMulVec_apply, Finset.prod_mul_distrib, mul_left_comm]

private theorem excitation_component_factor (Ω : A → ℂ) {k : ℕ} (B : Finset (Fin k))
    (u : ((Fin k → A) × C) → ℂ)
    (b : FiniteProduct.Configuration (fun _ : Fin k ↦ A) B)
    (g : FiniteProduct.Configuration (fun _ : Fin k ↦ A) Bᶜ) (c : C) :
    ((replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u)
      ((FiniteProduct.splitEquiv (fun _ : Fin k ↦ A) B).symm (b, g), c) =
    (∏ i : ↥(Bᶜ), Ω (g i)) *
      ∑ y : Fin k → A,
        ((∏ i : B, (1 - vecMulVec Ω (star Ω)) (b i) (y i)) *
          ∏ i : ↥(Bᶜ), star (Ω (y i))) * u (y, c) := by
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type]
  simp [one_apply, excitation_row_factor, Finset.mul_sum, mul_assoc]

omit [DecidableEq A] in
private theorem good_product_pairing (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    {k : ℕ} (B : Finset (Fin k)) :
    ∑ g : FiniteProduct.Configuration (fun _ : Fin k ↦ A) Bᶜ,
      (∏ i : ↥(Bᶜ), star (Ω (g i))) * (∏ i : ↥(Bᶜ), Ω (g i)) = 1 := by
  have hdot : Ω ⬝ᵥ star Ω = 1 := by
    simpa only [EuclideanSpace.inner_toLp_toLp, hΩ, RCLike.ofReal_one, one_pow] using
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 Ω))
  simp only [← Finset.prod_mul_distrib]
  have hsum : (∑ a : A, star (Ω a) * Ω a) = 1 := by
    simpa only [dotProduct, Pi.star_apply, mul_comm] using hdot
  simpa only [hsum, Finset.prod_const_one] using
    (Fintype.prod_sum (fun (_ : ↥(Bᶜ)) (a : A) ↦ star (Ω a) * Ω a)).symm

/-- Every actual excitation component has the given ground state on each good
physical copy. Its remaining vector is the partial contraction, with the auxiliary
coordinate retained. OpenAI area-law manuscript, `comparator:defect-mass`,
lines 441–456. -/
theorem replicaExcitationProjection_mulVec_factorization (Ω : A → ℂ)
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) {k : ℕ} (B : Finset (Fin k))
    (u : ((Fin k → A) × C) → ℂ)
    (b : FiniteProduct.Configuration (fun _ : Fin k ↦ A) B)
    (g : FiniteProduct.Configuration (fun _ : Fin k ↦ A) Bᶜ) (c : C) :
    ((replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u)
      ((FiniteProduct.splitEquiv (fun _ : Fin k ↦ A) B).symm (b, g), c) =
    (∏ i : ↥(Bᶜ), Ω (g i)) * replicaGoodCopyRemainder Ω B
      ((replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u) (b, c) := by
  simp only [replicaGoodCopyRemainder, excitation_component_factor, ← mul_assoc,
    ← Finset.sum_mul, good_product_pairing Ω hΩ, one_mul]

/-- A vector in an actual excitation sector factors into the given ground states
on the good physical copies and its partial contraction on the remaining factors.
OpenAI area-law manuscript, `comparator:defect-mass`, lines 441–456. -/
theorem replicaGoodCopy_factorization_of_fixed (Ω : A → ℂ)
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) {k : ℕ} (B : Finset (Fin k))
    (u : ((Fin k → A) × C) → ℂ)
    (hu : (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u = u)
    (b : FiniteProduct.Configuration (fun _ : Fin k ↦ A) B)
    (g : FiniteProduct.Configuration (fun _ : Fin k ↦ A) Bᶜ) (c : C) :
    u ((FiniteProduct.splitEquiv (fun _ : Fin k ↦ A) B).symm (b, g), c) =
    (∏ i : ↥(Bᶜ), Ω (g i)) * replicaGoodCopyRemainder Ω B u (b, c) := by
  simpa only [hu] using
    replicaExcitationProjection_mulVec_factorization Ω hΩ B u b g c

/-- Partial contraction preserves the norm of a vector in an actual excitation
sector. Zero components are included. OpenAI area-law manuscript,
`comparator:defect-mass`, lines 441–456. -/
theorem norm_replicaGoodCopyRemainder_of_fixed (Ω : A → ℂ)
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) {k : ℕ} (B : Finset (Fin k))
    (u : ((Fin k → A) × C) → ℂ)
    (hu : (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u = u) :
    ‖WithLp.toLp 2 (replicaGoodCopyRemainder Ω B u)‖ = ‖WithLp.toLp 2 u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  have hsum : (∑ a : A, ‖Ω a‖ ^ 2) = 1 := by
    simpa only [hΩ, one_pow] using (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 Ω)).symm
  have hgood : (∑ g : FiniteProduct.Configuration (fun _ : Fin k ↦ A) Bᶜ,
      ∏ i : ↥(Bᶜ), ‖Ω (g i)‖ ^ 2) = 1 := by
    simpa only [hsum, Finset.prod_const_one] using
      (Fintype.prod_sum (fun (_ : ↥(Bᶜ)) (a : A) ↦ ‖Ω a‖ ^ (2 : ℕ))).symm
  rw [← ((FiniteProduct.splitEquiv (fun _ : Fin k ↦ A) B).symm.prodCongr
    (Equiv.refl C)).sum_comp (fun x ↦ ‖u x‖ ^ 2)]
  simp only [Fintype.sum_prod_type, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply,
    replicaGoodCopy_factorization_of_fixed Ω hΩ B u hu, norm_mul, norm_prod,
    ← Finset.prod_pow, mul_pow]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, hgood, one_mul]

private theorem card_good_coordinates {k : ℕ} (B : Finset (Fin k)) :
    Fintype.card ↥(Bᶜ) = k - B.card := by
  simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]

end Matrix
