/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationPairMarginal
import QICLean.Representation.PairMergeDeficit
import QICLean.Representation.ReplicaMetric
import QICLean.Representation.SubsystemTransport
import QICLean.Representation.GroupAlgebraProductCoordinates
import QICLean.Analysis.GaussianFilter.Reindex

/-!
# The two merge deficits in the actual good-copy coordinates

The five factors are ordered as `Q,Y,V,C,R`. Their specified coordinate
equivalence groups the exterior pairs as `((Q,C),(V,R)),Y`. Under this
equivalence the two merge deficits are the actual paired-copy deficits,
with the identity on the good middle physical copies. Each transport is
derived from the literal permutation action. The three actions on a pair
are treated together before passing to their group-algebra observables.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`07-comparators.tex`, lines 501–549, `comparator:merge-decomposition`
and `comparator:merge-moments`.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped BigOperators Kronecker Matrix.Norms.Operator

namespace PermutationRepresentation

private def prodRight {G X : Type*} (Z : Type*) [Group G]
    (φ : G →* Equiv.Perm X) : G →* Equiv.Perm (Z × X) where
  toFun g := (Equiv.refl Z).prodCongr (φ g)
  map_one' := by ext <;> simp
  map_mul' g h := by ext <;> simp [Equiv.Perm.mul_apply]

private theorem groupAlgebraRep_prodRight {G X Z : Type*} [Group G]
    [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z]
    (φ : G →* Equiv.Perm X) (a : MonoidAlgebra ℂ G) :
    groupAlgebraRep (prodRight Z φ) a =
      (1 : Matrix Z Z ℂ) ⊗ₖ groupAlgebraRep φ a := by
  simpa only [Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id] using
    groupAlgebraRep_submatrix_of_prod_action (prodRight Z φ) φ
      (Equiv.refl (Z × X)) (fun _ _ ↦ rfl) a

end PermutationRepresentation

namespace TensorPower

private def pairAction (Q C : Type*) (m : ℕ) : Fin 3 →
    (Equiv.Perm (Fin m) →* Equiv.Perm ((Fin m → Q) × (Fin m → C))) :=
  Fin.cases (pairCopyLeft Q C m)
    (Fin.cases (pairCopyRight Q C m) (fun _ ↦ pairCopyBoth Q C m))

private def firstPairRegion : Fin 3 → Finset (Fin 5) :=
  Fin.cases {0} (Fin.cases {3} (fun _ ↦ {0, 3}))

private def secondPairRegion : Fin 3 → Finset (Fin 5) :=
  Fin.cases {2} (Fin.cases {4} (fun _ ↦ {2, 4}))

variable (ι : Fin 5 → Type*) (m : ℕ)

private theorem firstPair_intertwine (j : Fin 3)
    (σ : Equiv.Perm (Fin m)) (x : Config m ι) :
    prodLeft (Fin m → ι 1)
      (prodLeft ((Fin m → ι 2) × (Fin m → ι 4))
        (pairAction (ι 0) (ι 3) m j)) σ (fiveFactorPairMiddleEquiv ι m x) =
      fiveFactorPairMiddleEquiv ι m
        (subsystemPerm m ι (firstPairRegion j) σ x) := by
  fin_cases j <;> ext i <;>
    simp [firstPairRegion, pairAction, fiveFactorPairMiddleEquiv,
      prodLeft, subsystemPerm_apply, pairCopyLeft, pairCopyRight, pairCopyBoth] <;> rfl

private theorem secondPair_intertwine (j : Fin 3)
    (σ : Equiv.Perm (Fin m)) (x : Config m ι) :
    prodLeft (Fin m → ι 1)
      (prodRight ((Fin m → ι 0) × (Fin m → ι 3))
        (pairAction (ι 2) (ι 4) m j)) σ (fiveFactorPairMiddleEquiv ι m x) =
      fiveFactorPairMiddleEquiv ι m
        (subsystemPerm m ι (secondPairRegion j) σ x) := by
  fin_cases j <;> ext i <;>
    simp [secondPairRegion, pairAction, fiveFactorPairMiddleEquiv,
      prodLeft, prodRight, subsystemPerm_apply, pairCopyLeft, pairCopyRight,
      pairCopyBoth] <;> rfl

variable [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

local instance goodConfigurationMerge_decidableEqConfig :
    DecidableEq (Config m ι) := Fintype.decidablePiFintype

local instance goodConfigurationMerge_decidableEqCopies (j : Fin 5) :
    DecidableEq (Fin m → ι j) := Fintype.decidablePiFintype

local instance goodConfigurationMerge_decidableEqPair (i j : Fin 5) :
    DecidableEq ((Fin m → ι i) × (Fin m → ι j)) := inferInstance

local instance goodConfigurationMerge_decidableEqPairMiddle :
    DecidableEq ((((Fin m → ι 0) × (Fin m → ι 3)) ×
      ((Fin m → ι 2) × (Fin m → ι 4))) × (Fin m → ι 1)) := inferInstance

private theorem firstPair_labelObservable (j : Fin 3)
    (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    (labelObservable (subsystemPerm m ι (firstPairRegion j)) f).submatrix
        (fiveFactorPairMiddleEquiv ι m).symm (fiveFactorPairMiddleEquiv ι m).symm =
      (labelObservable (pairAction (ι 0) (ι 3) m j) f ⊗ₖ
        (1 : Matrix ((Fin m → ι 2) × (Fin m → ι 4))
          ((Fin m → ι 2) × (Fin m → ι 4)) ℂ)) ⊗ₖ
          (1 : Matrix (Fin m → ι 1) (Fin m → ι 1) ℂ) := by
  simp only [labelObservable_eq_groupAlgebraRep]
  rw [← Matrix.reindex_apply,
    ← groupAlgebraRep_of_intertwine (fiveFactorPairMiddleEquiv ι m)
      (firstPair_intertwine ι m j), groupAlgebraRep_prodLeft, groupAlgebraRep_prodLeft]

private theorem secondPair_labelObservable (j : Fin 3)
    (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    (labelObservable (subsystemPerm m ι (secondPairRegion j)) f).submatrix
        (fiveFactorPairMiddleEquiv ι m).symm (fiveFactorPairMiddleEquiv ι m).symm =
      ((1 : Matrix ((Fin m → ι 0) × (Fin m → ι 3))
        ((Fin m → ι 0) × (Fin m → ι 3)) ℂ) ⊗ₖ
          labelObservable (pairAction (ι 2) (ι 4) m j) f) ⊗ₖ
            (1 : Matrix (Fin m → ι 1) (Fin m → ι 1) ℂ) := by
  simp only [labelObservable_eq_groupAlgebraRep]
  rw [← Matrix.reindex_apply,
    ← groupAlgebraRep_of_intertwine (fiveFactorPairMiddleEquiv ι m)
      (secondPair_intertwine ι m j), groupAlgebraRep_prodLeft, groupAlgebraRep_prodRight]

/-- The six actual subsystem label observables become the separate and
simultaneous actions on the two exterior pairs. The good middle physical
copies are unchanged. Source: `07-comparators.tex`, lines 501–549. -/
theorem fiveFactorPairMiddle_labelObservable
    (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    let E := fiveFactorPairMiddleEquiv ι m
    let T := fun S ↦ (labelObservable (subsystemPerm m ι S) f).submatrix E.symm E.symm
    let QC := fun (φ : Equiv.Perm (Fin m) →*
      Equiv.Perm ((Fin m → ι 0) × (Fin m → ι 3))) ↦ (labelObservable φ f ⊗ₖ
      (1 : Matrix ((Fin m → ι 2) × (Fin m → ι 4))
        ((Fin m → ι 2) × (Fin m → ι 4)) ℂ)) ⊗ₖ
      (1 : Matrix (Fin m → ι 1) (Fin m → ι 1) ℂ)
    let VR := fun (φ : Equiv.Perm (Fin m) →*
      Equiv.Perm ((Fin m → ι 2) × (Fin m → ι 4))) ↦
      ((1 : Matrix ((Fin m → ι 0) × (Fin m → ι 3))
      ((Fin m → ι 0) × (Fin m → ι 3)) ℂ) ⊗ₖ labelObservable φ f) ⊗ₖ
      (1 : Matrix (Fin m → ι 1) (Fin m → ι 1) ℂ)
    T {0} = QC (pairCopyLeft (ι 0) (ι 3) m) ∧
    T {3} = QC (pairCopyRight (ι 0) (ι 3) m) ∧
    T {0, 3} = QC (pairCopyBoth (ι 0) (ι 3) m) ∧
    T {2} = VR (pairCopyLeft (ι 2) (ι 4) m) ∧
    T {4} = VR (pairCopyRight (ι 2) (ι 4) m) ∧
    T {2, 4} = VR (pairCopyBoth (ι 2) (ι 4) m) := by
  exact ⟨firstPair_labelObservable ι m 0 f, firstPair_labelObservable ι m 1 f,
    firstPair_labelObservable ι m 2 f, secondPair_labelObservable ι m 0 f,
    secondPair_labelObservable ι m 1 f, secondPair_labelObservable ι m 2 f⟩

/-- Both five-factor merge deficits are the corresponding literal pair
deficits, tensored with the identity on the other pair and on the middle
physical copies. Source: `07-comparators.tex`, lines 501–549. -/
theorem fiveFactorPairMiddle_mergeDeficits :
    let E := fiveFactorPairMiddleEquiv ι m
    let F := fun S ↦ labelEntropy (subsystemPerm m ι S)
    (F {0} + F {3} - F {0, 3}).submatrix E.symm E.symm =
      (pairMergeDeficit (ι 0) (ι 3) m ⊗ₖ
        (1 : Matrix ((Fin m → ι 2) × (Fin m → ι 4))
          ((Fin m → ι 2) × (Fin m → ι 4)) ℂ)) ⊗ₖ
          (1 : Matrix (Fin m → ι 1) (Fin m → ι 1) ℂ) ∧
    (F {2} + F {4} - F {2, 4}).submatrix E.symm E.symm =
      ((1 : Matrix ((Fin m → ι 0) × (Fin m → ι 3))
        ((Fin m → ι 0) × (Fin m → ι 3)) ℂ) ⊗ₖ
          pairMergeDeficit (ι 2) (ι 4) m) ⊗ₖ
            (1 : Matrix (Fin m → ι 1) (Fin m → ι 1) ℂ) := by
  obtain ⟨h0, h3, h03, h2, h4, h24⟩ :=
    fiveFactorPairMiddle_labelObservable ι m (fun l ↦ Real.log l.dim)
  constructor
  · simpa only [labelEntropy, submatrix_add, submatrix_sub, pairMergeDeficit,
      add_kronecker, sub_kronecker, h0, h3, h03]
  · simpa only [labelEntropy, submatrix_add, submatrix_sub, pairMergeDeficit,
      kronecker_add, kronecker_sub, add_kronecker, sub_kronecker, h2, h4, h24]

/-- Exponentiating the sum of the two actual merge deficits retains the
identity on the good middle physical copies. The parameter is any real
number. Source: `07-comparators.tex`, lines 520–549. -/
theorem fiveFactorPairMiddle_exp_sum_mergeDeficit (a : ℝ) :
    let E := fiveFactorPairMiddleEquiv ι m
    let F := fun S ↦ labelEntropy (subsystemPerm m ι S)
    let DC := pairMergeDeficit (ι 0) (ι 3) m ⊗ₖ
      (1 : Matrix ((Fin m → ι 2) × (Fin m → ι 4))
        ((Fin m → ι 2) × (Fin m → ι 4)) ℂ)
    let DR := (1 : Matrix ((Fin m → ι 0) × (Fin m → ι 3))
      ((Fin m → ι 0) × (Fin m → ι 3)) ℂ) ⊗ₖ pairMergeDeficit (ι 2) (ι 4) m
    (NormedSpace.exp ((a : ℂ) •
      ((F {0} + F {3} - F {0, 3}) + (F {2} + F {4} - F {2, 4})))).submatrix
      E.symm E.symm = NormedSpace.exp ((a : ℂ) • (DC + DR)) ⊗ₖ
        (1 : Matrix (Fin m → ι 1) (Fin m → ι 1) ℂ) := by
  intro E F DC DR
  obtain ⟨hQC, hVR⟩ := fiveFactorPairMiddle_mergeDeficits ι m
  rw [← Matrix.reindex_apply, Matrix.reindex_exp, Matrix.reindex_apply,
    submatrix_smul, submatrix_add, hQC, hVR, ← add_kronecker,
    ← smul_kronecker, Matrix.exp_kronecker_one]

end TensorPower
