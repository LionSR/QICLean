/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CompressedSpectralSupport
import QICLean.Analysis.ReplicaGoodConfigurationDensity
import QICLean.Representation.GoodAuxiliaryLabelCompression
import QICLean.Analysis.CfcConjugation
import QICLean.Analysis.CfcKronecker

/-!
# Good auxiliary spectral support of an actual excitation density

The physical factors are Q, Y and V, followed by auxiliary factors C and R.
The original vector has specified whole-copy auxiliary labels. Its literal
physical excitation component retains these labels, so restriction to the
good copies bounds each auxiliary label observable below on the component's
support. Tracing the bad physical and auxiliary copies preserves the derived
support in the actual five-factor good-copy density. Every good Y coordinate
is retained.

The one-copy physical vector is arbitrary. Neither its normalization nor
simultaneous copy symmetry of the original vector is needed. Zero components,
zero copies and empty good sets are included. This is a spectral-support
statement; the inverse metric comparison is a separate assertion.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
  2026, `07-comparators.tex`, lines 441–456 and 481–493,
  `comparator:good-auxiliary`, at manuscript commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* The retained physical factors are specified in the same source, lines 23
  and 103–110; the actual good-copy marginal is used in lines 520–549.
-/

open Matrix PermutationRepresentation TensorPower
open scoped MatrixOrder ComplexOrder Kronecker

namespace Matrix

private noncomputable def goodBadSplit {k : ℕ} (B : Finset (Fin k)) :
    Fin Bᶜ.card ⊕ Fin B.card ≃ Fin k :=
  ((Equiv.sumCongr Bᶜ.equivFin.symm B.equivFin.symm).trans
    (Equiv.sumComm ↥Bᶜ ↥B)).trans
      ((Equiv.sumCongr (Equiv.refl ↥B)
        (Equiv.subtypeEquivRight (fun _ : Fin k => Finset.mem_compl))).trans
          (Equiv.sumCompl (fun i : Fin k => i ∈ B)))

private theorem goodBadCopiesEquiv_eq (C : Type*) {k : ℕ} (B : Finset (Fin k)) :
    goodBadCopiesEquiv C B =
      (Equiv.arrowCongr (goodBadSplit B).symm (Equiv.refl C)).trans
        (Equiv.sumArrowEquivProdArrow (Fin Bᶜ.card) (Fin B.card) C) := by
  rfl

private theorem goodBadCopiesEquiv_copyPerm (C : Type*) {k : ℕ} (B : Finset (Fin k))
    (τ : Equiv.Perm (Fin Bᶜ.card)) (c : Fin k → C) :
    goodBadCopiesEquiv C B (copyPerm C k (groupHom₁ (goodBadSplit B) τ) c) =
      (copyPerm C Bᶜ.card τ (goodBadCopiesEquiv C B c).1,
        (goodBadCopiesEquiv C B c).2) := by
  ext i
  all_goals simp [goodBadCopiesEquiv_eq, copyPerm_apply, groupHom₁, youngHom,
    Equiv.permCongrHom, Equiv.permCongr_def, Equiv.Perm.one_def]

private theorem good_copy_condition (C : Type*) {k : ℕ} (B : Finset (Fin k))
    (τ : Equiv.Perm (Fin Bᶜ.card))
    (x y : (Fin Bᶜ.card → C) × (Fin B.card → C)) :
    copyPerm C k (groupHom₁ (goodBadSplit B) τ) ((goodBadCopiesEquiv C B).symm y) =
        (goodBadCopiesEquiv C B).symm x ↔
      copyPerm C Bᶜ.card τ y.1 = x.1 ∧ y.2 = x.2 := by
  rw [← (goodBadCopiesEquiv C B).injective.eq_iff, goodBadCopiesEquiv_copyPerm]
  simp only [Equiv.apply_symm_apply, Prod.ext_iff]

private theorem goodBadCopiesEquiv_permOp (C : Type*) [Fintype C] [DecidableEq C]
    {k : ℕ} (B : Finset (Fin k)) (τ : Equiv.Perm (Fin Bᶜ.card)) :
    (permOp ((copyPerm C k).comp (groupHom₁ (goodBadSplit B))) τ).submatrix
        (goodBadCopiesEquiv C B).symm (goodBadCopiesEquiv C B).symm =
      permOp (copyPerm C Bᶜ.card) τ ⊗ₖ
        (1 : Matrix (Fin B.card → C) (Fin B.card → C) ℂ) := by
  ext x y
  simp only [Matrix.submatrix_apply, permOp_apply_apply, MonoidHom.comp_apply,
    good_copy_condition, Matrix.kroneckerMap_apply, Matrix.one_apply]
  split_ifs <;> simp_all

private theorem goodBadCopiesEquiv_labelEntropy (C : Type*) [Fintype C] [DecidableEq C]
    {k : ℕ} (B : Finset (Fin k)) :
    (labelEntropy ((copyPerm C k).comp (groupHom₁ (goodBadSplit B)))).submatrix
        (goodBadCopiesEquiv C B).symm (goodBadCopiesEquiv C B).symm =
      labelEntropy (copyPerm C Bᶜ.card) ⊗ₖ
        (1 : Matrix (Fin B.card → C) (Fin B.card → C) ℂ) := by
  ext x y
  have he (τ : Equiv.Perm (Fin Bᶜ.card)) :
      permOp ((copyPerm C k).comp (groupHom₁ (goodBadSplit B))) τ
          ((goodBadCopiesEquiv C B).symm x) ((goodBadCopiesEquiv C B).symm y) =
        permOp (copyPerm C Bᶜ.card) τ x.1 y.1 *
          (1 : Matrix (Fin B.card → C) (Fin B.card → C) ℂ) x.2 y.2 :=
    congrArg (fun M => M x y) (goodBadCopiesEquiv_permOp C B τ)
  simp only [labelEntropy, labelObservable, labelProj, groupAlgebraRep_eq_sum,
    Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
    smul_eq_mul, he, Finset.sum_mul, mul_assoc]

private theorem goodBadCopiesEquiv_shift (C : Type*) [Fintype C] [DecidableEq C]
    {k : ℕ} (B : Finset (Fin k)) (c : ℝ) :
    (labelEntropy ((copyPerm C k).comp (groupHom₁ (goodBadSplit B))) -
        (c : ℂ) • 1).submatrix (goodBadCopiesEquiv C B).symm
          (goodBadCopiesEquiv C B).symm =
      (labelEntropy (copyPerm C Bᶜ.card) - (c : ℂ) • 1) ⊗ₖ
        (1 : Matrix (Fin B.card → C) (Fin B.card → C) ℂ) := by
  simp only [Matrix.submatrix_sub, Matrix.submatrix_smul, Pi.sub_apply, Pi.smul_apply,
    Matrix.submatrix_one_equiv, goodBadCopiesEquiv_labelEntropy]
  ext x y
  simp only [Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, Prod.ext_iff, sub_mul]
  split_ifs <;> simp_all

private theorem goodBadCopiesEquiv_cutoff (C : Type*) [Fintype C] [DecidableEq C]
    {k : ℕ} (B : Finset (Fin k)) (c : ℝ) :
    (spectralProjectionGE
      (labelEntropy ((copyPerm C k).comp (groupHom₁ (goodBadSplit B))) -
        (c : ℂ) • 1) 0).submatrix
        (goodBadCopiesEquiv C B).symm (goodBadCopiesEquiv C B).symm =
      spectralProjectionGE (labelEntropy (copyPerm C Bᶜ.card) - (c : ℂ) • 1) 0 ⊗ₖ
        (1 : Matrix (Fin B.card → C) (Fin B.card → C) ℂ) := by
  have hshift : (labelEntropy ((copyPerm C k).comp (groupHom₁ (goodBadSplit B))) -
      (c : ℂ) • 1).IsHermitian :=
    (isHermitian_labelObservable _ _).sub (isHermitian_one.smul (by simp [IsSelfAdjoint]))
  rw [spectralProjectionGE, ← cfc_submatrix_equiv hshift,
    goodBadCopiesEquiv_shift]
  exact cfc_kronecker_one
    ((isHermitian_labelObservable _ _).sub (isHermitian_one.smul (by simp [IsSelfAdjoint]))) _

private theorem groupedAuxiliary_cutoff_mul_labelProj {m r k : ℕ}
    (e : Fin m ⊕ Fin r ≃ Fin k) (C : Type*) [Fintype C] [DecidableEq C]
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    spectralProjectionGE
      (labelEntropy ((copyPerm C k).comp (groupHom₁ e)) -
        ((Real.log l.dim - (r : ℝ) * Real.log (Fintype.card C) -
          Real.log (k.choose r) : ℝ) : ℂ) • 1) 0 * labelProj (copyPerm C k) l =
      labelProj (copyPerm C k) l := by
  exact spectralProjectionGE_shift_mul_eq_of_compression_lower
    (isHermitian_labelObservable _ _) ⟨labelProj_mul_self _ _, isHermitian_labelProj _ _⟩
    (copyPerm_groupedGood_labelEntropy_compression (C := C) e l).1 _
    (copyPerm_groupedGood_labelEntropy_compression (C := C) e l).2

private noncomputable def goodConfigurationRegroup (ι : Fin 5 → Type*) {k : ℕ}
    (B : Finset (Fin k)) :
    ((Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4))) ≃
      Config Bᶜ.card ι ×
        ((↥B → ι 0 × (ι 1 × ι 2)) × ((Fin B.card → ι 3) × (Fin B.card → ι 4))) :=
  let ePhysical := (FiniteProduct.splitEquiv (fun _ : Fin k => ι 0 × (ι 1 × ι 2)) B).trans
    (((Equiv.refl (↥B → ι 0 × (ι 1 × ι 2))).prodCongr
      (Equiv.arrowCongr (Finset.equivFin Bᶜ) (Equiv.refl (ι 0 × (ι 1 × ι 2))))).trans
        (Equiv.prodComm (↥B → ι 0 × (ι 1 × ι 2)) (Fin Bᶜ.card → ι 0 × (ι 1 × ι 2))))
  let eAuxiliary := ((goodBadCopiesEquiv (ι 3) B).prodCongr
    (goodBadCopiesEquiv (ι 4) B)).trans
      (Equiv.prodProdProdComm (Fin Bᶜ.card → ι 3) (Fin B.card → ι 3)
        (Fin Bᶜ.card → ι 4) (Fin B.card → ι 4))
  (ePhysical.prodCongr eAuxiliary).trans
    ((Equiv.prodProdProdComm (Fin Bᶜ.card → ι 0 × (ι 1 × ι 2))
      (↥B → ι 0 × (ι 1 × ι 2))
      ((Fin Bᶜ.card → ι 3) × (Fin Bᶜ.card → ι 4))
      ((Fin B.card → ι 3) × (Fin B.card → ι 4))).trans
        ((fiveFactorCopiesEquiv ι Bᶜ.card).symm.prodCongr (Equiv.refl _)))

private theorem goodConfigurationRegroup_auxiliary (ι : Fin 5 → Type*)
    [∀ f, DecidableEq (ι f)] {k : ℕ} (B : Finset (Fin k))
    (MC : Matrix (Fin Bᶜ.card → ι 3) (Fin Bᶜ.card → ι 3) ℂ)
    (MR : Matrix (Fin Bᶜ.card → ι 4) (Fin Bᶜ.card → ι 4) ℂ) :
    ((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
        (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
      (((MC ⊗ₖ (1 : Matrix (Fin B.card → ι 3) (Fin B.card → ι 3) ℂ)).submatrix
          (goodBadCopiesEquiv (ι 3) B) (goodBadCopiesEquiv (ι 3) B)) ⊗ₖ
        ((MR ⊗ₖ (1 : Matrix (Fin B.card → ι 4) (Fin B.card → ι 4) ℂ)).submatrix
          (goodBadCopiesEquiv (ι 4) B) (goodBadCopiesEquiv (ι 4) B)))).submatrix
        (goodConfigurationRegroup ι B).symm (goodConfigurationRegroup ι B).symm =
      (((1 : Matrix (Fin Bᶜ.card → ι 0 × (ι 1 × ι 2))
          (Fin Bᶜ.card → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ (MC ⊗ₖ MR)).submatrix
            (fiveFactorCopiesEquiv ι Bᶜ.card) (fiveFactorCopiesEquiv ι Bᶜ.card)) ⊗ₖ
        (1 : Matrix
          ((↥B → ι 0 × (ι 1 × ι 2)) × ((Fin B.card → ι 3) × (Fin B.card → ι 4)))
          ((↥B → ι 0 × (ι 1 × ι 2)) × ((Fin B.card → ι 3) × (Fin B.card → ι 4))) ℂ) := by
  let ePhysical := (FiniteProduct.splitEquiv (fun _ : Fin k => ι 0 × (ι 1 × ι 2)) B).trans
    (((Equiv.refl (↥B → ι 0 × (ι 1 × ι 2))).prodCongr
      (Equiv.arrowCongr (Finset.equivFin Bᶜ) (Equiv.refl (ι 0 × (ι 1 × ι 2))))).trans
        (Equiv.prodComm (↥B → ι 0 × (ι 1 × ι 2)) (Fin Bᶜ.card → ι 0 × (ι 1 × ι 2))))
  ext x y
  change (1 : Matrix _ _ ℂ)
      (ePhysical.symm (((fiveFactorCopiesEquiv ι Bᶜ.card) x.1).1, x.2.1))
      (ePhysical.symm (((fiveFactorCopiesEquiv ι Bᶜ.card) y.1).1, y.2.1)) *
      (MC ((goodBadCopiesEquiv (ι 3) B) ((goodBadCopiesEquiv (ι 3) B).symm
          (((fiveFactorCopiesEquiv ι Bᶜ.card) x.1).2.1, x.2.2.1))).1
        ((goodBadCopiesEquiv (ι 3) B) ((goodBadCopiesEquiv (ι 3) B).symm
          (((fiveFactorCopiesEquiv ι Bᶜ.card) y.1).2.1, y.2.2.1))).1 *
        (1 : Matrix _ _ ℂ)
          ((goodBadCopiesEquiv (ι 3) B) ((goodBadCopiesEquiv (ι 3) B).symm
            (((fiveFactorCopiesEquiv ι Bᶜ.card) x.1).2.1, x.2.2.1))).2
          ((goodBadCopiesEquiv (ι 3) B) ((goodBadCopiesEquiv (ι 3) B).symm
            (((fiveFactorCopiesEquiv ι Bᶜ.card) y.1).2.1, y.2.2.1))).2 *
        (MR ((goodBadCopiesEquiv (ι 4) B) ((goodBadCopiesEquiv (ι 4) B).symm
            (((fiveFactorCopiesEquiv ι Bᶜ.card) x.1).2.2, x.2.2.2))).1
          ((goodBadCopiesEquiv (ι 4) B) ((goodBadCopiesEquiv (ι 4) B).symm
            (((fiveFactorCopiesEquiv ι Bᶜ.card) y.1).2.2, y.2.2.2))).1 *
          (1 : Matrix _ _ ℂ)
            ((goodBadCopiesEquiv (ι 4) B) ((goodBadCopiesEquiv (ι 4) B).symm
              (((fiveFactorCopiesEquiv ι Bᶜ.card) x.1).2.2, x.2.2.2))).2
            ((goodBadCopiesEquiv (ι 4) B) ((goodBadCopiesEquiv (ι 4) B).symm
              (((fiveFactorCopiesEquiv ι Bᶜ.card) y.1).2.2, y.2.2.2))).2)) =
      (1 : Matrix _ _ ℂ) ((fiveFactorCopiesEquiv ι Bᶜ.card) x.1).1
        ((fiveFactorCopiesEquiv ι Bᶜ.card) y.1).1 *
      (MC ((fiveFactorCopiesEquiv ι Bᶜ.card) x.1).2.1
          ((fiveFactorCopiesEquiv ι Bᶜ.card) y.1).2.1 *
        MR ((fiveFactorCopiesEquiv ι Bᶜ.card) x.1).2.2
          ((fiveFactorCopiesEquiv ι Bᶜ.card) y.1).2.2) * (1 : Matrix _ _ ℂ) x.2 y.2
  simp only [Equiv.apply_symm_apply, Matrix.one_apply, ePhysical.symm.injective.eq_iff,
    Prod.ext_iff]
  split_ifs <;> simp_all

private theorem fiveFactorCopiesEquiv_auxiliaryPerm (ι : Fin 5 → Type*) (m : ℕ)
    (σ : Equiv.Perm (Fin m)) (x : Config m ι) :
    fiveFactorCopiesEquiv ι m (subsystemPerm m ι {3} σ x) =
        (((fiveFactorCopiesEquiv ι m) x).1,
          (copyPerm (ι 3) m σ (((fiveFactorCopiesEquiv ι m) x).2.1),
            ((fiveFactorCopiesEquiv ι m) x).2.2)) ∧
      fiveFactorCopiesEquiv ι m (subsystemPerm m ι {4} σ x) =
        (((fiveFactorCopiesEquiv ι m) x).1,
          (((fiveFactorCopiesEquiv ι m) x).2.1,
            copyPerm (ι 4) m σ (((fiveFactorCopiesEquiv ι m) x).2.2))) := by
  constructor
  all_goals rfl

private theorem fiveFactorCopiesEquiv_auxiliaryPermOp (ι : Fin 5 → Type*) (m : ℕ)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] (σ : Equiv.Perm (Fin m)) :
    (permOp (subsystemPerm m ι {3}) σ).submatrix
        (fiveFactorCopiesEquiv ι m).symm (fiveFactorCopiesEquiv ι m).symm =
      (1 : Matrix (Fin m → ι 0 × (ι 1 × ι 2))
        (Fin m → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        (permOp (copyPerm (ι 3) m) σ ⊗ₖ (1 : Matrix (Fin m → ι 4) (Fin m → ι 4) ℂ)) ∧
      (permOp (subsystemPerm m ι {4}) σ).submatrix
        (fiveFactorCopiesEquiv ι m).symm (fiveFactorCopiesEquiv ι m).symm =
      (1 : Matrix (Fin m → ι 0 × (ι 1 × ι 2))
        (Fin m → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        ((1 : Matrix (Fin m → ι 3) (Fin m → ι 3) ℂ) ⊗ₖ permOp (copyPerm (ι 4) m) σ) := by
  constructor
  · ext x y
    simp only [submatrix_apply, permOp_apply_apply,
      ← (fiveFactorCopiesEquiv ι m).injective.eq_iff,
      (fiveFactorCopiesEquiv_auxiliaryPerm ι m σ _).1, Equiv.apply_symm_apply,
      Prod.ext_iff, kroneckerMap_apply, one_apply]
    split_ifs <;> simp_all
  · ext x y
    simp only [submatrix_apply, permOp_apply_apply,
      ← (fiveFactorCopiesEquiv ι m).injective.eq_iff,
      (fiveFactorCopiesEquiv_auxiliaryPerm ι m σ _).2, Equiv.apply_symm_apply,
      Prod.ext_iff, kroneckerMap_apply, one_apply]
    split_ifs <;> simp_all

private theorem fiveFactorCopiesEquiv_auxiliaryLabelEntropy (ι : Fin 5 → Type*) (m : ℕ)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] :
    (labelEntropy (subsystemPerm m ι {3})).submatrix
        (fiveFactorCopiesEquiv ι m).symm (fiveFactorCopiesEquiv ι m).symm =
      (1 : Matrix (Fin m → ι 0 × (ι 1 × ι 2))
        (Fin m → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        (labelEntropy (copyPerm (ι 3) m) ⊗ₖ (1 : Matrix (Fin m → ι 4) (Fin m → ι 4) ℂ)) ∧
      (labelEntropy (subsystemPerm m ι {4})).submatrix
        (fiveFactorCopiesEquiv ι m).symm (fiveFactorCopiesEquiv ι m).symm =
      (1 : Matrix (Fin m → ι 0 × (ι 1 × ι 2))
        (Fin m → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        ((1 : Matrix (Fin m → ι 3) (Fin m → ι 3) ℂ) ⊗ₖ labelEntropy (copyPerm (ι 4) m)) := by
  constructor
  · ext x y
    have he (σ : Equiv.Perm (Fin m)) := congrArg (fun M => M x y)
      (fiveFactorCopiesEquiv_auxiliaryPermOp ι m σ).1
    simp only [submatrix_apply, kroneckerMap_apply] at he
    simp only [labelEntropy, labelObservable, labelProj, groupAlgebraRep_eq_sum,
      submatrix_apply, sum_apply, smul_apply, kroneckerMap_apply, smul_eq_mul,
      he, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    simp only [mul_left_comm]
  · ext x y
    have he (σ : Equiv.Perm (Fin m)) := congrArg (fun M => M x y)
      (fiveFactorCopiesEquiv_auxiliaryPermOp ι m σ).2
    simp only [submatrix_apply, kroneckerMap_apply] at he
    simp only [labelEntropy, labelObservable, labelProj, groupAlgebraRep_eq_sum,
      submatrix_apply, sum_apply, smul_apply, kroneckerMap_apply, smul_eq_mul,
      he, Finset.mul_sum]
    simp only [mul_left_comm]

private theorem spectralProjectionGE_shift_map {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (Φ : Matrix α α ℂ →⋆ₐ[ℂ] Matrix β β ℂ) (F : Matrix α α ℂ)
    (hF : F.IsHermitian) (c : ℝ) :
    spectralProjectionGE (Φ F - (c : ℂ) • 1) 0 =
      Φ (spectralProjectionGE (F - (c : ℂ) • 1) 0) := by
  have ht : Φ (F - (c : ℂ) • 1) = Φ F - (c : ℂ) • 1 := by
    simp only [map_sub, map_smul]
    rw [show Φ (1 : Matrix α α ℂ) = 1 from Φ.map_one]
  rw [spectralProjectionGE, ← ht]
  have hlocal : (F - (c : ℂ) • 1).IsHermitian :=
    hF.sub (isHermitian_one.smul (by simp [IsSelfAdjoint]))
  have hsa : IsSelfAdjoint (F - (c : ℂ) • 1) := hlocal
  have hsa' : IsSelfAdjoint (Φ (F - (c : ℂ) • 1)) := by
    change star (Φ (F - (c : ℂ) • 1)) = _
    rw [← map_star, hsa]
  exact (StarAlgHomClass.map_cfc Φ (fun t : ℝ => if 0 ≤ t then 1 else 0) _
    ((F - (c : ℂ) • 1).finite_real_spectrum.continuousOn _)
    (LinearMap.continuous_of_finiteDimensional Φ.toLinearMap) hsa hsa').symm

private theorem fiveFactorCopiesEquiv_auxiliaryCutoff (ι : Fin 5 → Type*) (m : ℕ)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] (c r : ℝ) :
    (spectralProjectionGE (labelEntropy (subsystemPerm m ι {3}) - (c : ℂ) • 1) 0).submatrix
        (fiveFactorCopiesEquiv ι m).symm (fiveFactorCopiesEquiv ι m).symm =
      (1 : Matrix (Fin m → ι 0 × (ι 1 × ι 2))
        (Fin m → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        (spectralProjectionGE (labelEntropy (copyPerm (ι 3) m) - (c : ℂ) • 1) 0 ⊗ₖ
          (1 : Matrix (Fin m → ι 4) (Fin m → ι 4) ℂ)) ∧
      (spectralProjectionGE (labelEntropy (subsystemPerm m ι {4}) - (r : ℂ) • 1) 0).submatrix
        (fiveFactorCopiesEquiv ι m).symm (fiveFactorCopiesEquiv ι m).symm =
      (1 : Matrix (Fin m → ι 0 × (ι 1 × ι 2))
        (Fin m → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        ((1 : Matrix (Fin m → ι 3) (Fin m → ι 3) ℂ) ⊗ₖ
          spectralProjectionGE (labelEntropy (copyPerm (ι 4) m) - (r : ℂ) • 1) 0) := by
  constructor
  · have hshift : (labelEntropy (subsystemPerm m ι {3}) - (c : ℂ) • 1).IsHermitian :=
      (isHermitian_labelObservable _ _).sub (isHermitian_one.smul (by simp [IsSelfAdjoint]))
    rw [spectralProjectionGE, ← cfc_submatrix_equiv hshift]
    simp only [submatrix_sub, submatrix_smul, Pi.sub_apply, Pi.smul_apply, submatrix_one_equiv,
      (fiveFactorCopiesEquiv_auxiliaryLabelEntropy ι m).1]
    let Φ := (rightKroneckerEmbed (m := Fin m → ι 0 × (ι 1 × ι 2))
      (n := (Fin m → ι 3) × (Fin m → ι 4))).comp
        (leftKroneckerEmbed (m := Fin m → ι 3) (n := Fin m → ι 4))
    exact spectralProjectionGE_shift_map Φ (labelEntropy (copyPerm (ι 3) m))
      (isHermitian_labelObservable _ _) c
  · have hshift : (labelEntropy (subsystemPerm m ι {4}) - (r : ℂ) • 1).IsHermitian :=
      (isHermitian_labelObservable _ _).sub (isHermitian_one.smul (by simp [IsSelfAdjoint]))
    rw [spectralProjectionGE, ← cfc_submatrix_equiv hshift]
    simp only [submatrix_sub, submatrix_smul, Pi.sub_apply, Pi.smul_apply, submatrix_one_equiv,
      (fiveFactorCopiesEquiv_auxiliaryLabelEntropy ι m).2]
    let Φ := (rightKroneckerEmbed (m := Fin m → ι 0 × (ι 1 × ι 2))
      (n := (Fin m → ι 3) × (Fin m → ι 4))).comp
        (rightKroneckerEmbed (m := Fin m → ι 3) (n := Fin m → ι 4))
    exact spectralProjectionGE_shift_map Φ (labelEntropy (copyPerm (ι 4) m))
      (isHermitian_labelObservable _ _) r

private theorem projection_mul_partialTraceRight_rankOne {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq β]
    (P : Matrix α α ℂ) (hP : IsStarProjection P) (f : α × β → ℂ)
    (hf : (P ⊗ₖ (1 : Matrix β β ℂ)) *ᵥ f = f) :
    P * partialTraceRight (vecMulVec f (star f)) =
      partialTraceRight (vecMulVec f (star f)) := by
  have hconj : (P ⊗ₖ (1 : Matrix β β ℂ)) * vecMulVec f (star f) *
      (P ⊗ₖ (1 : Matrix β β ℂ))ᴴ = vecMulVec f (star f) := by
    rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec, hf]
  have hcompress := partialTraceRight_kronecker_conj_of_right_isometry P
    (1 : Matrix β β ℂ) (by simp) (vecMulVec f (star f))
  rw [hconj] at hcompress
  calc
    P * partialTraceRight (vecMulVec f (star f)) =
        P * (P * partialTraceRight (vecMulVec f (star f)) * Pᴴ) :=
      congrArg (P * ·) hcompress
    _ = P * partialTraceRight (vecMulVec f (star f)) * Pᴴ := by
      simp only [← mul_assoc, hP.isIdempotentElem.eq]
    _ = partialTraceRight (vecMulVec f (star f)) := hcompress.symm

private theorem regrouped_projection_support (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    (M : Matrix ((Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)))
      ((Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4))) ℂ)
    (P : Matrix (Config Bᶜ.card ι) (Config Bᶜ.card ι) ℂ) (hP : IsStarProjection P)
    (hreg : M.submatrix (goodConfigurationRegroup ι B).symm
        (goodConfigurationRegroup ι B).symm = P ⊗ₖ 1)
    (hw : M *ᵥ ((replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
          ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u) =
      (replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
          ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u) :
    P * replicaGoodConfigurationMarginal ι Ω k B u =
      replicaGoodConfigurationMarginal ι Ω k B u := by
  let w := (replicaExcitationProjection Ω k B ⊗ₖ
    (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
      ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
  change P * partialTraceRight (vecMulVec (w ∘ (goodConfigurationRegroup ι B).symm)
    (star (w ∘ (goodConfigurationRegroup ι B).symm))) = _
  apply projection_mul_partialTraceRight_rankOne P hP
  rw [← hreg, submatrix_mulVec_equiv]
  simpa only [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self,
    Function.comp_id] using congrArg (fun v => v ∘ (goodConfigurationRegroup ι B).symm) hw

/-- The actual good-copy density is supported above the two auxiliary label
thresholds obtained from its original whole-copy labels. Only the original
vector's label support is assumed; the excitation component's labels and
the reduced density's spectral support are derived.
OpenAI, September 24, 2026, `07-comparators.tex`, lines 441–456 and 481–493,
`comparator:good-auxiliary`, with all good physical factors retained as in
lines 23, 103–110 and 520–549. -/
theorem spectralProjectionGE_auxiliaryLabelEntropy_mul_replicaGoodConfigurationMarginal
    (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
    (lC lR : IrrepLabel (Equiv.Perm (Fin k)))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    (hC : ((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
        (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
      (labelProj (copyPerm (ι 3) k) lC ⊗ₖ
        (1 : Matrix (Fin k → ι 4) (Fin k → ι 4) ℂ))) *ᵥ u = u)
    (hR : ((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
        (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
      ((1 : Matrix (Fin k → ι 3) (Fin k → ι 3) ℂ) ⊗ₖ
        labelProj (copyPerm (ι 4) k) lR)) *ᵥ u = u) :
    let Γ := replicaGoodConfigurationMarginal ι Ω k B u
    let LC := Real.log lC.dim - (B.card : ℝ) * Real.log (Fintype.card (ι 3)) -
      Real.log (k.choose B.card)
    let LR := Real.log lR.dim - (B.card : ℝ) * Real.log (Fintype.card (ι 4)) -
      Real.log (k.choose B.card)
    spectralProjectionGE
        (labelEntropy (subsystemPerm Bᶜ.card ι {3}) - (LC : ℂ) • 1) 0 * Γ = Γ ∧
      spectralProjectionGE
        (labelEntropy (subsystemPerm Bᶜ.card ι {4}) - (LR : ℂ) • 1) 0 * Γ = Γ := by
  intro Γ LC LR
  let w := (replicaExcitationProjection Ω k B ⊗ₖ
    (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
      ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
  have hCw := replicaExcitationProjection_kronecker_mulVec_preserves_fixed Ω k B 1
    (by simp) (labelProj (copyPerm (ι 3) k) lC ⊗ₖ
      (1 : Matrix (Fin k → ι 4) (Fin k → ι 4) ℂ)) u (by simpa only [map_one] using hC)
  simp only [map_one] at hCw
  have hRw := replicaExcitationProjection_kronecker_mulVec_preserves_fixed Ω k B 1
    (by simp) ((1 : Matrix (Fin k → ι 3) (Fin k → ι 3) ℂ) ⊗ₖ
      labelProj (copyPerm (ι 4) k) lR) u (by simpa only [map_one] using hR)
  simp only [map_one] at hRw
  change _ *ᵥ w = w at hCw hRw
  constructor
  · let K := spectralProjectionGE
      (labelEntropy ((copyPerm (ι 3) k).comp (groupHom₁ (goodBadSplit B))) - (LC : ℂ) • 1) 0
    let P := spectralProjectionGE (labelEntropy (subsystemPerm Bᶜ.card ι {3}) - (LC : ℂ) • 1) 0
    let M := (1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
      (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        (K ⊗ₖ (1 : Matrix (Fin k → ι 4) (Fin k → ι 4) ℂ))
    have hKL : K * labelProj (copyPerm (ι 3) k) lC = labelProj (copyPerm (ι 3) k) lC :=
      groupedAuxiliary_cutoff_mul_labelProj (goodBadSplit B) (ι 3) lC
    have hMw : M *ᵥ w = w := by
      rw [← hCw, mulVec_mulVec]
      simp only [M, ← mul_kronecker_mul, one_mul, hKL]
    let PG := spectralProjectionGE (labelEntropy (copyPerm (ι 3) Bᶜ.card) - (LC : ℂ) • 1) 0
    have hK : K = (PG ⊗ₖ (1 : Matrix (Fin B.card → ι 3) (Fin B.card → ι 3) ℂ)).submatrix
        (goodBadCopiesEquiv (ι 3) B) (goodBadCopiesEquiv (ι 3) B) := by
      simpa only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id] using
        congrArg (fun N => N.submatrix (goodBadCopiesEquiv (ι 3) B)
          (goodBadCopiesEquiv (ι 3) B)) (goodBadCopiesEquiv_cutoff (ι 3) B LC)
    have hPcoord : P = ((1 : Matrix (Fin Bᶜ.card → ι 0 × (ι 1 × ι 2))
        (Fin Bᶜ.card → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
      (PG ⊗ₖ (1 : Matrix (Fin Bᶜ.card → ι 4) (Fin Bᶜ.card → ι 4) ℂ))).submatrix
        (fiveFactorCopiesEquiv ι Bᶜ.card) (fiveFactorCopiesEquiv ι Bᶜ.card) := by
      simpa only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id] using
        congrArg (fun N => N.submatrix (fiveFactorCopiesEquiv ι Bᶜ.card)
          (fiveFactorCopiesEquiv ι Bᶜ.card))
            (fiveFactorCopiesEquiv_auxiliaryCutoff ι Bᶜ.card LC LR).1
    have hreg := goodConfigurationRegroup_auxiliary ι B PG
      (1 : Matrix (Fin Bᶜ.card → ι 4) (Fin Bᶜ.card → ι 4) ℂ)
    simp only [one_kronecker_one, submatrix_one_equiv] at hreg
    rw [← hK, ← hPcoord] at hreg
    have hPstar : IsStarProjection P :=
      ((isHermitian_labelObservable (subsystemPerm Bᶜ.card ι {3})
        (fun l => Real.log l.dim)).sub
          (isHermitian_one.smul (by simp [IsSelfAdjoint]))).isStarProjection_spectralProjectionGE 0
    exact regrouped_projection_support ι Ω k B u M P hPstar hreg hMw
  · let K := spectralProjectionGE
      (labelEntropy ((copyPerm (ι 4) k).comp (groupHom₁ (goodBadSplit B))) - (LR : ℂ) • 1) 0
    let P := spectralProjectionGE (labelEntropy (subsystemPerm Bᶜ.card ι {4}) - (LR : ℂ) • 1) 0
    let M := (1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
      (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        ((1 : Matrix (Fin k → ι 3) (Fin k → ι 3) ℂ) ⊗ₖ K)
    have hKL : K * labelProj (copyPerm (ι 4) k) lR = labelProj (copyPerm (ι 4) k) lR :=
      groupedAuxiliary_cutoff_mul_labelProj (goodBadSplit B) (ι 4) lR
    have hMw : M *ᵥ w = w := by
      rw [← hRw, mulVec_mulVec]
      simp only [M, ← mul_kronecker_mul, one_mul, hKL]
    let PG := spectralProjectionGE (labelEntropy (copyPerm (ι 4) Bᶜ.card) - (LR : ℂ) • 1) 0
    have hK : K = (PG ⊗ₖ (1 : Matrix (Fin B.card → ι 4) (Fin B.card → ι 4) ℂ)).submatrix
        (goodBadCopiesEquiv (ι 4) B) (goodBadCopiesEquiv (ι 4) B) := by
      simpa only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id] using
        congrArg (fun N => N.submatrix (goodBadCopiesEquiv (ι 4) B)
          (goodBadCopiesEquiv (ι 4) B)) (goodBadCopiesEquiv_cutoff (ι 4) B LR)
    have hPcoord : P = ((1 : Matrix (Fin Bᶜ.card → ι 0 × (ι 1 × ι 2))
        (Fin Bᶜ.card → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
      ((1 : Matrix (Fin Bᶜ.card → ι 3) (Fin Bᶜ.card → ι 3) ℂ) ⊗ₖ PG)).submatrix
        (fiveFactorCopiesEquiv ι Bᶜ.card) (fiveFactorCopiesEquiv ι Bᶜ.card) := by
      simpa only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id] using
        congrArg (fun N => N.submatrix (fiveFactorCopiesEquiv ι Bᶜ.card)
          (fiveFactorCopiesEquiv ι Bᶜ.card))
            (fiveFactorCopiesEquiv_auxiliaryCutoff ι Bᶜ.card LC LR).2
    have hreg := goodConfigurationRegroup_auxiliary ι B
      (1 : Matrix (Fin Bᶜ.card → ι 3) (Fin Bᶜ.card → ι 3) ℂ) PG
    simp only [one_kronecker_one, submatrix_one_equiv] at hreg
    rw [← hK, ← hPcoord] at hreg
    have hPstar : IsStarProjection P :=
      ((isHermitian_labelObservable (subsystemPerm Bᶜ.card ι {4})
        (fun l => Real.log l.dim)).sub
          (isHermitian_one.smul (by simp [IsSelfAdjoint]))).isStarProjection_spectralProjectionGE 0
    exact regrouped_projection_support ι Ω k B u M P hPstar hreg hMw

end Matrix
