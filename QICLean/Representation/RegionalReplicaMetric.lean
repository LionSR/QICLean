/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.RegionalFiveFactorCoordinates
import QICLean.Representation.ReplicaMetric

/-!
# Replica metrics under regional grouping

The three physical blocks are two disjoint regions and the complement of
their union. Grouping their coordinates leaves both auxiliary spaces and
the dimension of the whole one-copy space unchanged. Consequently the
replica label weights are unchanged, and every subsystem metric transports
through the literal regional configuration equivalence.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `05-replicas.tex`, `replicas:w-definition`, lines 287--303, and
`07-comparators.tex`, lines 20--37 and 421--456, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u

noncomputable section

open Matrix PermutationRepresentation

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Assign each original site to its actual physical block or unchanged
auxiliary factor. Source: `07-comparators.tex`, lines 20--37 and 80--110. -/
def regionalFactorIndex (Q Y : Finset V) : Option (Option V) → Fin 5
  | none => 4
  | some none => 3
  | some (some v) => if v ∈ Q then 0 else if v ∈ Y then 1 else 2

/-- The original sites belonging to a chosen family of the five grouped
factors. Source: `07-comparators.tex`, lines 20--37 and 421--456. -/
def regionalOriginalRegion (Q Y : Finset V) (S : Finset (Fin 5)) :
    Finset (Option (Option V)) :=
  Finset.univ.filter fun v => regionalFactorIndex Q Y v ∈ S

variable (β : V → Type u) (C R : Type u)

/-- The actual grouping intertwines every subsystem copy action. No
coordinate-transport identity is assumed. Source: `07-comparators.tex`,
lines 20--37 and 421--456. -/
theorem regionalFiveFactorCopyEquiv_subsystemPerm
    (Q Y : Finset V) (hQY : Disjoint Q Y) (k : ℕ)
    (S : Finset (Fin 5)) (σ : Equiv.Perm (Fin k))
    (x : Config k (addedSiteSpace (addedSiteSpace β C) R)) :
    subsystemPerm k (regionalFiveFactorSpace β C R Q Y) S σ
        (regionalFiveFactorCopyEquiv β C R Q Y hQY k x) =
      regionalFiveFactorCopyEquiv β C R Q Y hQY k
        (subsystemPerm k (addedSiteSpace (addedSiteSpace β C) R)
          (regionalOriginalRegion Q Y S) σ x) := by
  funext j f
  fin_cases f
  · change (if (0 : Fin 5) ∈ S then
        (fun v : Q => x (σ⁻¹ j) (some (some v))) else
        (fun v : Q => x j (some (some v)))) =
      (fun v : Q => if some (some v.val) ∈ regionalOriginalRegion Q Y S then
        x (σ⁻¹ j) (some (some v)) else x j (some (some v)))
    funext v
    by_cases hS : (0 : Fin 5) ∈ S <;>
      simp [hS, regionalOriginalRegion, regionalFactorIndex, v.property]
  · change (if (1 : Fin 5) ∈ S then
        (fun v : Y => x (σ⁻¹ j) (some (some v))) else
        (fun v : Y => x j (some (some v)))) =
      (fun v : Y => if some (some v.val) ∈ regionalOriginalRegion Q Y S then
        x (σ⁻¹ j) (some (some v)) else x j (some (some v)))
    funext v
    have hv : v.val ∉ Q := fun h => Finset.disjoint_left.mp hQY h v.property
    by_cases hS : (1 : Fin 5) ∈ S <;>
      simp [hS, regionalOriginalRegion, regionalFactorIndex, hv, v.property]
  · change (if (2 : Fin 5) ∈ S then
        (fun v : ↥((Q ∪ Y)ᶜ) => x (σ⁻¹ j) (some (some v))) else
        (fun v : ↥((Q ∪ Y)ᶜ) => x j (some (some v)))) =
      (fun v : ↥((Q ∪ Y)ᶜ) =>
        if some (some v.val) ∈ regionalOriginalRegion Q Y S then
          x (σ⁻¹ j) (some (some v)) else x j (some (some v)))
    funext v
    have hvQ : v.val ∉ Q := fun h =>
      Finset.mem_compl.mp v.property (Finset.mem_union_left Y h)
    have hvY : v.val ∉ Y := fun h =>
      Finset.mem_compl.mp v.property (Finset.mem_union_right Q h)
    by_cases hS : (2 : Fin 5) ∈ S <;>
      simp [hS, regionalOriginalRegion, regionalFactorIndex, hvQ, hvY]
  · change (if (3 : Fin 5) ∈ S then x (σ⁻¹ j) (some none) else x j (some none)) =
      (if some none ∈ regionalOriginalRegion Q Y S then
        x (σ⁻¹ j) (some none) else x j (some none))
    simp [regionalOriginalRegion, regionalFactorIndex]
  · change (if (4 : Fin 5) ∈ S then x (σ⁻¹ j) none else x j none) =
      (if none ∈ regionalOriginalRegion Q Y S then x (σ⁻¹ j) none else x j none)
    simp [regionalOriginalRegion, regionalFactorIndex]

variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local instance regionalReplicaMetric_originalConfigDecidableEq (k : ℕ) :
    DecidableEq (Config k (addedSiteSpace (addedSiteSpace β C) R)) :=
  Fintype.decidablePiFintype

local instance regionalReplicaMetric_groupedConfigDecidableEq
    (Q Y : Finset V) (k : ℕ) :
    DecidableEq (Config k (regionalFiveFactorSpace β C R Q Y)) :=
  Fintype.decidablePiFintype

/-- Every finite group-algebra element transports under the actual regional
grouping. Source: `07-comparators.tex`, lines 421--456. -/
theorem groupAlgebraRep_submatrix_regionalFiveFactorCopyEquiv
    (Q Y : Finset V) (hQY : Disjoint Q Y) (k : ℕ)
    (S : Finset (Fin 5)) (a : MonoidAlgebra ℂ (Equiv.Perm (Fin k))) :
    groupAlgebraRep (subsystemPerm k (regionalFiveFactorSpace β C R Q Y) S) a =
      (groupAlgebraRep (subsystemPerm k (addedSiteSpace (addedSiteSpace β C) R)
        (regionalOriginalRegion Q Y S)) a).submatrix
          (regionalFiveFactorCopyEquiv β C R Q Y hQY k).symm
          (regionalFiveFactorCopyEquiv β C R Q Y hQY k).symm :=
  groupAlgebraRep_of_intertwine (regionalFiveFactorCopyEquiv β C R Q Y hQY k)
    (regionalFiveFactorCopyEquiv_subsystemPerm β C R Q Y hQY k S) a

/-- The same real function of the irreducible label gives the same operator
in regional coordinates. Source: `07-comparators.tex`, lines 421--456. -/
theorem labelObservable_submatrix_regionalFiveFactorCopyEquiv
    (Q Y : Finset V) (hQY : Disjoint Q Y) (k : ℕ)
    (S : Finset (Fin 5)) (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    labelObservable (subsystemPerm k (regionalFiveFactorSpace β C R Q Y) S) f =
      (labelObservable (subsystemPerm k (addedSiteSpace (addedSiteSpace β C) R)
        (regionalOriginalRegion Q Y S)) f).submatrix
          (regionalFiveFactorCopyEquiv β C R Q Y hQY k).symm
          (regionalFiveFactorCopyEquiv β C R Q Y hQY k).symm := by
  simp only [labelObservable_eq_groupAlgebraRep]
  exact groupAlgebraRep_submatrix_regionalFiveFactorCopyEquiv β C R Q Y hQY k S _

/-- Grouping physical sites does not change the whole one-copy dimension,
including the two original auxiliary factors. Source: `05-replicas.tex`,
`replicas:w-definition`, lines 287--303. -/
theorem replicaDim_regionalFiveFactorSpace
    (Q Y : Finset V) (hQY : Disjoint Q Y) :
    replicaDim (regionalFiveFactorSpace β C R Q Y) =
      replicaDim (addedSiteSpace (addedSiteSpace β C) R) := by
  have h := Fintype.card_congr (regionalFiveFactorCopyEquiv β C R Q Y hQY 1)
  simpa only [Config, Fintype.card_fun, Fintype.card_fin, pow_one] using h.symm

/-- The label weights are those of the same original full system, without
a change of padding dimension. Source: `05-replicas.tex`,
`replicas:w-definition`, lines 287--303. -/
theorem replicaLabelWeight_regionalFiveFactorSpace
    (Q Y : Finset V) (hQY : Disjoint Q Y) (t : ℝ) {k : ℕ}
    (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    replicaLabelWeight (regionalFiveFactorSpace β C R Q Y) t ell =
      replicaLabelWeight (addedSiteSpace (addedSiteSpace β C) R) t ell := by
  unfold replicaLabelWeight
  rw [replicaDim_regionalFiveFactorSpace β C R Q Y hQY]

/-- Every original-region replica metric is exactly its five-factor
coordinate matrix. There is no sign condition on the parameter, and empty
coordinate spaces are allowed. Source: `05-replicas.tex`, lines 287--303,
and `07-comparators.tex`, lines 421--456. -/
theorem replicaMetric_submatrix_regionalFiveFactorCopyEquiv
    (Q Y : Finset V) (hQY : Disjoint Q Y) (t : ℝ) (k : ℕ)
    (S : Finset (Fin 5)) :
    replicaMetric (regionalFiveFactorSpace β C R Q Y) t k S =
      (replicaMetric (addedSiteSpace (addedSiteSpace β C) R) t k
        (regionalOriginalRegion Q Y S)).submatrix
          (regionalFiveFactorCopyEquiv β C R Q Y hQY k).symm
          (regionalFiveFactorCopyEquiv β C R Q Y hQY k).symm := by
  have hw : replicaLabelWeight (regionalFiveFactorSpace β C R Q Y) t =
      replicaLabelWeight (k := k) (addedSiteSpace (addedSiteSpace β C) R) t := by
    funext ell
    exact replicaLabelWeight_regionalFiveFactorSpace β C R Q Y hQY t ell
  simp only [replicaMetric, hw]
  exact labelObservable_submatrix_regionalFiveFactorCopyEquiv β C R Q Y hQY k S _

/-- The same coordinate identity holds for the actual squared product of
two inverse metrics and a third metric. Source: `05-replicas.tex`,
`replicas:leaf-metric`, lines 459--473, and `07-comparators.tex`, lines 421--456. -/
theorem replicaMetric_inv_mul_inv_mul_sq_submatrix_regionalFiveFactorCopyEquiv
    (Q Y : Finset V) (hQY : Disjoint Q Y) (t : ℝ) (k : ℕ)
    (S₁ S₂ S₃ : Finset (Fin 5)) :
    ((replicaMetric (regionalFiveFactorSpace β C R Q Y) t k S₁)⁻¹ *
      (replicaMetric (regionalFiveFactorSpace β C R Q Y) t k S₂)⁻¹ *
        replicaMetric (regionalFiveFactorSpace β C R Q Y) t k S₃) ^ 2 =
      (((replicaMetric (addedSiteSpace (addedSiteSpace β C) R) t k
          (regionalOriginalRegion Q Y S₁))⁻¹ *
        (replicaMetric (addedSiteSpace (addedSiteSpace β C) R) t k
          (regionalOriginalRegion Q Y S₂))⁻¹ *
        replicaMetric (addedSiteSpace (addedSiteSpace β C) R) t k
          (regionalOriginalRegion Q Y S₃)) ^ 2).submatrix
            (regionalFiveFactorCopyEquiv β C R Q Y hQY k).symm
            (regionalFiveFactorCopyEquiv β C R Q Y hQY k).symm := by
  simp only [replicaMetric_submatrix_regionalFiveFactorCopyEquiv β C R Q Y hQY,
    Matrix.inv_submatrix_equiv, pow_two, Matrix.submatrix_mul_equiv]

end TensorPower
