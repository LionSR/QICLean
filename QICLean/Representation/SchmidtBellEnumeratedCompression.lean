/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchmidtBellEnumeratedPrevector
import QICLean.Representation.BellInsertionRegisterCoordinates
import QICLean.Representation.ReplicaMetric
import QICLean.Representation.SubsystemTransport
import QICLean.Analysis.OperatorMean.FiniteTree

/-!
# Enumeration in fixed compressed coordinates

Enumerating the selected C register preserves the actual compressed band
factors and the original compressed prevector. The supplied matrix on the
enumerated register is fixed, and the matrix on the selected register is
obtained by inverse row reindexing. Both retain the same column space.

The replica weights use the full one-copy family on each side. Equality of
the compressed factors preserves evaluations of the same weighted mean tree
and their ordered product. Neither identity requires isometry, positivity,
normalization or geometric assumptions.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 80--110, 130--147,
  240--254, 283--308 and 370--381, manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix TensorPower PermutationRepresentation

noncomputable section

namespace FiniteProduct

local instance schmidtBellEnumeratedCompressionConfigDecidableEq
    {V : Type} [Fintype V] [DecidableEq V]
    (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (X : Finset V) (E : Finset (Configuration β X)) (k : ℕ) :
    DecidableEq (Config k (addedSiteSpace (addedSiteSpace β E) (Fin E.card))) :=
  Fintype.decidablePiFintype

/-- Enumerating the selected C register preserves each actual compressed
band factor and the ordered product of evaluations of the same mean tree.
The supplied matrix on the enumerated register and its `Fin n` columns are
fixed; the matrix on the selected register is its inverse row reindexing.
No isometry, positivity, normalization or regional nesting premise is needed.

Source: area-law manuscript, `07-comparators.tex`, lines 80--110,
283--308 and 370--381, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem replicaMetric_compressed_bandProduct_enumerate_C
    {V : Type} [Fintype V] [DecidableEq V] {S : Type*}
    (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (X : Finset V) (E : Finset (Configuration β X)) (k n : ℕ)
    (ZF : Matrix
      (Config k (addedSiteSpace (addedSiteSpace β (Fin E.card)) (Fin E.card)))
      (Fin n) ℂ)
    (t : ℝ) (K : ℕ) (U Y : S → Fin K → Finset V) (T : Matrix.MeanTree S) :
    let ιE := addedSiteSpace (addedSiteSpace β E) (Fin E.card)
    let ιF := addedSiteSpace (addedSiteSpace β (Fin E.card)) (Fin E.card)
    let changeSite : ∀ o : Option (Option V), ιF o ≃ ιE o := fun o ↦
      match o with
      | none => Equiv.refl (Fin E.card)
      | some none => (Finset.equivFin E).symm
      | some (some v) => Equiv.refl (β v)
    let e := Equiv.piCongrRight fun _ : Fin k ↦ Equiv.piCongrRight changeSite
    let ZE := ZF.submatrix e.symm (id : Fin n → Fin n)
    let WE := replicaMetric ιE t k
    let WF := replicaMetric ιF t k
    let Q := fun j g ↦ insert (some none)
      ((X ∪ U j g).image fun v ↦ some (some v))
    let F := fun j g ↦ insert none
      (((X ∪ (U j g ∪ Y j g))ᶜ).image fun v ↦ some (some v))
    let extRegion := fun B : Finset V ↦ (B \ X).image fun v ↦ some (some v)
    let AE := fun j g ↦
      ((WE (Q j g))⁻¹ * (WE (F j g))⁻¹ * WE (extRegion (Y j g))) ^ 2
    let AF := fun j g ↦
      ((WF (Q j g))⁻¹ * (WF (F j g))⁻¹ * WF (extRegion (Y j g))) ^ 2
    let BE := fun j g ↦ ZEᴴ * AE j g * ZE
    let BF := fun j g ↦ ZFᴴ * AF j g * ZF
    let ME := (List.ofFn fun g : Fin K ↦ T.eval (BE · g)).prod
    let MF := (List.ofFn fun g : Fin K ↦ T.eval (BF · g)).prod
    (∀ j g, BF j g = BE j g) ∧ MF = ME := by
  classical
  intro ιE ιF changeSite e ZE WE WF Q F extRegion AE AF BE BF ME MF
  have hdim : replicaDim ιF = replicaDim ιE :=
    Fintype.card_congr (Equiv.piCongrRight changeSite)
  have hw : replicaLabelWeight (k := k) ιF t = replicaLabelWeight (k := k) ιE t :=
    funext fun ell ↦
      congrArg (fun d : ℕ ↦ Partition.replicaWeight t (TensorPower.part d ell)) hdim
  have hact (R : Finset (Option (Option V))) (σ : Equiv.Perm (Fin k))
      (x : Config k ιE) :
      subsystemPerm k ιF R σ (e.symm x) = e.symm (subsystemPerm k ιE R σ x) := by
    simpa only [e, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using
      congrArg e.symm (subsystemPerm_piCongrRight ιE ιF changeSite k R σ (e.symm x))
  have hW (R : Finset (Option (Option V))) : WF R = (WE R).submatrix e e := by
    simpa only [WF, WE, replicaMetric, hw, labelObservable_eq_groupAlgebraRep,
      Matrix.reindex_apply, Equiv.symm_symm] using
      (groupAlgebraRep_of_intertwine e.symm
        (φ := subsystemPerm k ιE R) (ψ := subsystemPerm k ιF R) (hact R)
        (∑ ell : IrrepLabel (Equiv.Perm (Fin k)),
          (replicaLabelWeight ιE t ell : ℂ) • IrrepLabel.centralIdem ell))
  have hA (j : S) (g : Fin K) : AF j g = (AE j g).submatrix e e := by
    simp only [AF, AE, hW, Matrix.inv_submatrix_equiv, pow_two, Matrix.submatrix_mul_equiv]
  have hrecover : ZE.submatrix e (id : Fin n → Fin n) = ZF := by
    simp only [ZE, Matrix.submatrix_submatrix, Function.comp_id, Equiv.symm_comp_self,
      Matrix.submatrix_id_id]
  have hB (j : S) (g : Fin K) : BF j g = BE j g := by
    simp only [BF, BE, hA, ← hrecover, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  exact ⟨hB, by simp only [MF, ME, hB]⟩

/-- The compressed original prevector is unchanged when the selected
C register is enumerated. The physical vector, selected set, label, supplied
matrix and its column coordinates are fixed. No normalization or positive
selected-mass hypothesis is imposed.

Source: area-law manuscript, `07-comparators.tex`, lines 130--147,
240--254 and 283--290, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem schmidtBellSitePrevector_compressed_enumerate_C
    {V : Type} [Fintype V] [DecidableEq V]
    (β : V → Type) [∀ v, Fintype (β v)]
    (Ω : EuclideanSpace ℂ ((v : V) → β v))
    (X : Finset V) (E : Finset (Configuration β X)) (k n : ℕ)
    (ZF : Matrix
      (Config k (addedSiteSpace (addedSiteSpace β (Fin E.card)) (Fin E.card)))
      (Fin n) ℂ)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let ιE := addedSiteSpace (addedSiteSpace β E) (Fin E.card)
    let ιF := addedSiteSpace (addedSiteSpace β (Fin E.card)) (Fin E.card)
    let changeSite : ∀ o : Option (Option V), ιF o ≃ ιE o := fun o ↦
      match o with
      | none => Equiv.refl (Fin E.card)
      | some none => (Finset.equivFin E).symm
      | some (some v) => Equiv.refl (β v)
    let e := Equiv.piCongrRight fun _ : Fin k ↦ Equiv.piCongrRight changeSite
    let ZE := ZF.submatrix e.symm (id : Fin n → Fin n)
    let τ := schmidtBellWitnessEquiv β X E k
    let vE : Config k ιE → ℂ :=
      (schmidtBellSitePrevector β X E k ΩX ell).ofLp ∘ τ
    let vF : Config k ιF → ℂ := replicaPrevector Ω E.card k ell ∘
      globalReplicaCopiesEquiv β (Fin E.card) (Fin E.card) k
    ZFᴴ *ᵥ vF = ZEᴴ *ᵥ vE := by
  classical
  done

end FiniteProduct
