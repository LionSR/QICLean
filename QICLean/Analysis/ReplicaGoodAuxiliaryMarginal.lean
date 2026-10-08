/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaMarginalSymmetry
import QICLean.Representation.GroupedCopies
import QICLean.Representation.TensorPowerAction
import QICLean.Algebra.MatrixAux
import QICLean.Channel.PartialTrace

/-!
# Permutation symmetry of the actual good auxiliary marginal

Split the auxiliary copies according to the complement of an excited subset
and the subset itself, using chosen finite-set equivalences. The actual
good auxiliary marginal is obtained by tracing every physical copy, then the
bad auxiliary copies and the exterior copies. Its permutation symmetry is
derived from the simultaneous copy symmetry of the original vector and the
stabilizer symmetry of the actual excitation component.

These are the auxiliary marginal assertions in *A two-dimensional area law
from a global spectral gap*, `07-comparators.tex`, lines 520–549, following
`comparator:merge-moments`. The marginal is unnormalized. The ground vector
need not have unit norm, and zero components, zero copies and empty coordinate
sets are included. Neither independence of the auxiliary copies nor a
merge-moment estimate is asserted here.
-/

open Matrix PermutationRepresentation TensorPower
open scoped Kronecker

/-- Split configurations according to the specified division of copies.
OpenAI area-law manuscript, `07-comparators.tex`, lines 520–549. -/
private def goodBadConfigEquiv {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    (C : Type*) : (Fin k → C) ≃ (Fin m → C) × (Fin r → C) :=
  (Equiv.arrowCongr e.symm (Equiv.refl C)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin r) C)

/-- A good-group copy permutation acts only on the good part of a split configuration.
OpenAI area-law manuscript, `07-comparators.tex`, lines 540–549. -/
private theorem goodBadConfigEquiv_copyPerm {m r k : ℕ}
    (e : Fin m ⊕ Fin r ≃ Fin k) (C : Type*) (τ : Equiv.Perm (Fin m))
    (c : Fin k → C) :
    goodBadConfigEquiv e C (copyPerm C k (groupHom₁ e τ) c) =
      (copyPerm C m τ (goodBadConfigEquiv e C c).1,
        (goodBadConfigEquiv e C c).2) := by
  ext i
  all_goals simp [goodBadConfigEquiv, copyPerm_apply, groupHom₁, youngHom,
    Equiv.permCongrHom, Equiv.permCongr_def, Equiv.Perm.one_def]

/-- Retain the good auxiliary copies and move every other factor to the traced register.
OpenAI area-law manuscript, `07-comparators.tex`, lines 520–549. -/
private def goodAuxiliaryRegroup {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    (A C D : Type*) :
    ((Fin k → A) × ((Fin k → C) × (Fin k → D))) ≃
      ((Fin k → A) × ((Fin r → C) × (Fin k → D))) × (Fin m → C) :=
  ((Equiv.refl (Fin k → A)).prodCongr
    (((goodBadConfigEquiv e C).prodCongr (Equiv.refl (Fin k → D))).trans
      (Equiv.prodAssoc (Fin m → C) (Fin r → C) (Fin k → D)))).trans
    (((Equiv.refl (Fin k → A)).prodCongr
      (Equiv.prodComm (Fin m → C) ((Fin r → C) × (Fin k → D)))).trans
      (Equiv.prodAssoc (Fin k → A) ((Fin r → C) × (Fin k → D)) (Fin m → C)).symm)

/-- The actual good-copy action fixes the bad coordinates.
OpenAI area-law manuscript, `07-comparators.tex`, lines 540–549. -/
private theorem good_copy_perm_condition {m r k : ℕ}
    (e : Fin m ⊕ Fin r ≃ Fin k) (C : Type*) (τ : Equiv.Perm (Fin m))
    (x y : Fin k → C) :
    copyPerm C k (groupHom₁ e τ) y = x ↔
      copyPerm C m τ (goodBadConfigEquiv e C y).1 = (goodBadConfigEquiv e C x).1 ∧
        (goodBadConfigEquiv e C y).2 = (goodBadConfigEquiv e C x).2 := by
  rw [← (goodBadConfigEquiv e C).injective.eq_iff, goodBadConfigEquiv_copyPerm]
  exact Prod.ext_iff

/-- The actual permutation on physical and exterior copies, with bad auxiliary copies fixed.
OpenAI area-law manuscript, `07-comparators.tex`, lines 540–549. -/
private def goodAuxiliaryDiscardPerm {m r k : ℕ}
    (e : Fin m ⊕ Fin r ≃ Fin k) (A C D : Type*) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm ((Fin k → A) × ((Fin r → C) × (Fin k → D))) :=
  (copyPerm A k (groupHom₁ e τ)).prodCongr
    ((Equiv.refl (Fin r → C)).prodCongr (copyPerm D k (groupHom₁ e τ)))

/-- Regrouping the literal three-register permutation gives a product action.
OpenAI area-law manuscript, `07-comparators.tex`, lines 540–549. -/
private theorem goodAuxiliaryRegroup_permOp {m r k : ℕ}
    (e : Fin m ⊕ Fin r ≃ Fin k) (A C D : Type*)
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    [Fintype D] [DecidableEq D] (τ : Equiv.Perm (Fin m)) :
    Matrix.reindex (goodAuxiliaryRegroup e A C D) (goodAuxiliaryRegroup e A C D)
      (permOp (copyPerm A k) (groupHom₁ e τ) ⊗ₖ
        (permOp (copyPerm C k) (groupHom₁ e τ) ⊗ₖ
          permOp (copyPerm D k) (groupHom₁ e τ))) =
      permOp (MonoidHom.id _) (goodAuxiliaryDiscardPerm e A C D τ) ⊗ₖ
        permOp (copyPerm C m) τ := by
  ext ⟨⟨xa, xb, xd⟩, xg⟩ ⟨⟨ya, yb, yd⟩, yg⟩
  simp [goodAuxiliaryRegroup, goodAuxiliaryDiscardPerm, Matrix.reindex_apply,
    Matrix.kroneckerMap_apply, permOp_apply_apply, good_copy_perm_condition]
  split_ifs <;> simp_all

/-- The chosen finite-set equivalences enumerate the complement first and the excited subset second.
OpenAI area-law manuscript, `07-comparators.tex`, lines 441–456 and 540–549. -/
private noncomputable def replicaGoodBadSplit {k : ℕ} (B : Finset (Fin k)) :
    Fin (Bᶜ).card ⊕ Fin B.card ≃ Fin k :=
  ((Equiv.sumCongr (Bᶜ).equivFin.symm B.equivFin.symm).trans
    (Equiv.sumComm ↥(Bᶜ) ↥B)).trans
      ((Equiv.sumCongr (Equiv.refl ↥B)
        (Equiv.subtypeEquivRight (fun _ : Fin k => Finset.mem_compl))).trans
          (Equiv.sumCompl (fun i : Fin k => i ∈ B)))

/-- The actual good group fixes every excited coordinate and therefore preserves the excited set.
OpenAI area-law manuscript, `07-comparators.tex`, lines 441–456 and 540–549. -/
private theorem good_group_image_eq {k : ℕ} (B : Finset (Fin k))
    (τ : Equiv.Perm (Fin (Bᶜ).card)) :
    B.image (groupHom₁ (replicaGoodBadSplit B) τ) = B := by
  have hfix (i : ↥B) : groupHom₁ (replicaGoodBadSplit B) τ i = i := by
    obtain ⟨j, rfl⟩ := B.equivFin.symm.surjective i
    change groupHom₁ (replicaGoodBadSplit B) τ
      ((replicaGoodBadSplit B) (Sum.inr j)) = (replicaGoodBadSplit B) (Sum.inr j)
    simp [groupHom₁, youngHom, Equiv.permCongrHom, Equiv.permCongr_def]
  calc
    B.image (groupHom₁ (replicaGoodBadSplit B) τ) = B.image id :=
      Finset.image_congr (fun i hi => hfix ⟨i, hi⟩)
    _ = B := Finset.image_id

namespace TensorPower

/-
Provenance-ID: 8750-qic-good-auxiliary-marginal-03
Original formalization, no upstream Lean proof text reused.
Declaration: TensorPower.goodBadCopiesEquiv
Manuscript: September 24, 2026, comparator:merge-moments, lines 520–549.
-/

/-- Split the actual auxiliary configurations into good and bad copies by the
chosen finite-set equivalences. The good coordinate at `i` is
`c ((Bᶜ).equivFin.symm i)`, and the bad coordinate at `j` is
`c (B.equivFin.symm j)`. The equivalences need not preserve order.
*A two-dimensional area law from a global spectral gap*, `07-comparators.tex`,
lines 441–456 and 520–549, following `comparator:merge-moments`. -/
noncomputable def goodBadCopiesEquiv (C : Type*) {k : ℕ} (B : Finset (Fin k)) :
    (Fin k → C) ≃ (Fin (Bᶜ).card → C) × (Fin B.card → C) :=
  goodBadConfigEquiv (replicaGoodBadSplit B) C

end TensorPower

namespace Matrix

variable {A C D : Type*} [Fintype A] [DecidableEq A]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

/-
Provenance-ID: 8750-qic-good-auxiliary-marginal-01
Original formalization, no upstream Lean proof text reused.
Declaration: Matrix.replicaGoodAuxiliaryMarginal
Manuscript: September 24, 2026, comparator:merge-moments, lines 520–549.
-/

/-- The actual unnormalized good auxiliary marginal of the physical excitation
component. First trace all physical copies, then split the remaining auxiliary
coordinates and trace the bad auxiliary copies together with all exterior
copies. *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 520–549, following `comparator:merge-moments`. -/
noncomputable def replicaGoodAuxiliaryMarginal (Ω : A → ℂ) (k : ℕ)
    (B : Finset (Fin k))
    (v : (Fin k → A) × ((Fin k → C) × (Fin k → D)) → ℂ) :
    Matrix (Fin (Bᶜ).card → C) (Fin (Bᶜ).card → C) ℂ :=
  let w := (replicaExcitationProjection Ω k B ⊗ₖ
    (1 : Matrix ((Fin k → C) × (Fin k → D)) ((Fin k → C) × (Fin k → D)) ℂ)) *ᵥ v
  let eAux := ((goodBadCopiesEquiv C B).prodCongr (Equiv.refl (Fin k → D))).trans
    (Equiv.prodAssoc (Fin (Bᶜ).card → C) (Fin B.card → C) (Fin k → D))
  partialTraceRight (Matrix.reindex eAux eAux (partialTraceLeft (vecMulVec w (star w))))

/-- The two successive traces equal the single trace over the actual regrouped component.
OpenAI area-law manuscript, `07-comparators.tex`, lines 540–549. -/
private theorem replicaGoodAuxiliaryMarginal_eq (Ω : A → ℂ) (k : ℕ)
    (B : Finset (Fin k))
    (v : (Fin k → A) × ((Fin k → C) × (Fin k → D)) → ℂ) :
    replicaGoodAuxiliaryMarginal Ω k B v =
      let w := (replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → C) × (Fin k → D)) ((Fin k → C) × (Fin k → D)) ℂ)) *ᵥ v
      let u := w ∘ (goodAuxiliaryRegroup (replicaGoodBadSplit B) A C D).symm
      partialTraceLeft (vecMulVec u (star u)) := by
  ext x y
  simp only [replicaGoodAuxiliaryMarginal, goodBadCopiesEquiv, reindex_apply, Equiv.symm_trans,
    Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.coe_trans, Equiv.prodCongr_apply, Equiv.coe_refl,
    partialTraceRight_apply, submatrix_apply, Function.comp_apply, Equiv.prodAssoc_symm_apply,
    Prod.map_apply, id_eq, partialTraceLeft_apply, vecMulVec_apply, Pi.star_apply, RCLike.star_def,
    Fintype.sum_prod_type, goodAuxiliaryRegroup, Equiv.symm_symm, Equiv.prodComm_symm,
    Equiv.coe_prodComm, Equiv.prodAssoc_apply, Prod.swap_prod_mk]
  conv_lhs => enter [2, b]; rw [Finset.sum_comm]
  exact Finset.sum_comm

/-
Provenance-ID: 8750-qic-good-auxiliary-marginal-02
Original formalization, no upstream Lean proof text reused.
Declaration: Matrix.commute_replicaGoodAuxiliaryMarginal_copyPerm
Manuscript: September 24, 2026, comparator:merge-moments, lines 520–549.
-/

/-- The actual good auxiliary marginal commutes with every good-copy permutation.
Only the original vector's simultaneous physical, auxiliary and exterior copy
fixedness is assumed. The excitation component's stabilizer symmetry and the
marginal symmetry are derived. *A two-dimensional area law from a global
spectral gap*, `07-comparators.tex`, lines 520–549, following
`comparator:merge-moments`. No unit ground-vector, independence or nonzero
component hypothesis is required. -/
theorem commute_replicaGoodAuxiliaryMarginal_copyPerm
    (Ω : A → ℂ) (k : ℕ) (B : Finset (Fin k))
    (v : (Fin k → A) × ((Fin k → C) × (Fin k → D)) → ℂ)
    (hv : ∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm A k) σ ⊗ₖ
        (permOp (copyPerm C k) σ ⊗ₖ permOp (copyPerm D k) σ)) *ᵥ v = v)
    (τ : Equiv.Perm (Fin (Bᶜ).card)) :
    Commute (permOp (copyPerm C (Bᶜ).card) τ)
      (replicaGoodAuxiliaryMarginal Ω k B v) := by
  let e := replicaGoodBadSplit B
  let σ := groupHom₁ e τ
  let w := (replicaExcitationProjection Ω k B ⊗ₖ
    (1 : Matrix ((Fin k → C) × (Fin k → D)) ((Fin k → C) × (Fin k → D)) ℂ)) *ᵥ v
  have hw : (permOp (copyPerm A k) σ ⊗ₖ
      (permOp (copyPerm C k) σ ⊗ₖ permOp (copyPerm D k) σ)) *ᵥ w = w :=
    replicaExcitationProjection_kronecker_mulVec_preserves_fixed Ω k B σ
      (good_group_image_eq B τ) _ v (hv σ)
  have hu : (permOp (MonoidHom.id _) (goodAuxiliaryDiscardPerm e A C D τ) ⊗ₖ
      permOp (copyPerm C (Bᶜ).card) τ) *ᵥ
        (w ∘ (goodAuxiliaryRegroup e A C D).symm) =
      w ∘ (goodAuxiliaryRegroup e A C D).symm := by
    rw [← goodAuxiliaryRegroup_permOp, Matrix.reindex_mulVec, hw]
  have h := commute_partialTraceLeft_vecMulVec_of_fixed_kronecker_permOp
    (MonoidHom.fst _ _) (MonoidHom.snd _ _)
    (goodAuxiliaryDiscardPerm e A C D τ, copyPerm C (Bᶜ).card τ)
    (w ∘ (goodAuxiliaryRegroup e A C D).symm) hu
  simpa only [replicaGoodAuxiliaryMarginal_eq, permOp_apply, MonoidHom.coe_snd] using h

end Matrix
