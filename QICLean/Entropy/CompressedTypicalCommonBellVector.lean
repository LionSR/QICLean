/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.CompressedTypicalCommonRetainedMass
import QICLean.Representation.CompressedTypicalAuxiliaryCoordinates
import QICLean.Representation.CommonSchurBellCutoffs

/-!
# The actual normalized Bell vector with common regional cutoffs

Fix the original physical vector and a selected spectral set of positive
mass. The exterior vector is the literal compressed selected vector, with
the selected index enumerated by `Fin E.card`. The Bell factor is the actual
selected Bell vector of the original bipartite state. Thus the two auxiliary
coordinate sets are respectively the selected set and its finite enumeration.

For a given auxiliary label sequence with the eventual mass lower bound,
the common retained-mass estimate gives positive mass before normalization.
The existing Bell common-projection theorem then produces a unit vector in
the selected Bell range, the same auxiliary-label range, and every prescribed
regional-cutoff range. Its squared overlap is the actual retained mass and is
at least one quarter of the same inverse polynomial.

This is an auxiliary implication for a given label sequence. The eventual
mass hypothesis is to be discharged by the same Schmidt--Bell sequence in
the final theorem. This lower bound on the actual auxiliary mass is the sole
asymptotic premise; symmetry, regional losses, and membership in the Bell
range are derived.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 283–298 and 332–354,
  `comparator:bell-pin` and `comparator:rough-overlap`, source commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open Filter Topology
open scoped BigOperators Matrix Kronecker InnerProductSpace ComplexOrder
open Matrix PermutationRepresentation TensorPower

noncomputable section

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

open Classical in
/-- For the same given label sequence, the actual selected Bell state admits
an eventual unit common-cutoff vector. The overlap equals the actual exterior
retained mass, which is at least half the original auxiliary mass and at least
one quarter of the prescribed inverse polynomial.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 283–298
and 332–354. This auxiliary implication retains the eventual auxiliary-mass
premise, to be discharged from the original Schmidt--Bell sequence. -/
theorem eventually_exists_commonLabelCutoff_compressedTypical_bell_vector
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
    (E : Finset (Configuration β X)) (hΩ : ‖Ω‖ = 1)
    (hz : 0 < (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E)
    (regions : List (Finset V))
    (hnested : regions.Pairwise fun B C ↦ B ⊆ C ∨ C ⊆ B)
    (hdisjoint : ∀ B ∈ regions, Disjoint X B)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) :
    let ι := compressedSiteSpace β X (Fin E.card)
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let χsite := WithLp.toLp 2
      (fun x : (f : Option ↥(Xᶜ)) → ι f ↦
        Matrix.compressedTypicalPureState ΩX E
          ((Finset.equivFin E).symm (x none), fun v ↦ x (some v)))
    let Ψ : (k : ℕ) → EuclideanSpace ℂ (Config k ι) := fun k ↦
      WithLp.toLp 2 (fun x : Config k ι ↦ ∏ j, χsite (x j))
    let a := compressedRegionalThreshold β Ω X E
    let q : ℕ → ℝ := fun k ↦
      ‖toEuclideanLin (labelProj (subsystemPerm k ι {none}) (ell k)) (Ψ k)‖ ^ 2
    let r : ℕ → ℝ := fun k ↦
      ‖toEuclideanLin
        (commonLabelCutoff ι k (regions.map (exteriorRegion X)) (a k) *
          labelProj (subsystemPerm k ι {none}) (ell k)) (Ψ k)‖ ^ 2
    let post : (k : ℕ) →
        EuclideanSpace ℂ ((Fin k → Configuration β X × E) × Config k ι) := fun k ↦
      WithLp.toLp 2 (fun x ↦
        (∏ j, selectedBellVector ΩX E (x.1 j)) * Ψ k x.2)
    (∀ᶠ k : ℕ in atTop,
      1 / (2 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤ q k) →
    ∀ᶠ k : ℕ in atTop,
      let e := Equiv.arrowProdEquivProdArrow (Fin k)
        (fun _ ↦ Configuration β X × E) (fun _ ↦ (f : Option ↥(Xᶜ)) → ι f)
      ∃ φ : EuclideanSpace ℂ ((Fin k → Configuration β X × E) × Config k ι),
        ‖φ‖ = 1 ∧
        (fun x ↦ φ (e x)) ∈ invariantSubspace
          (copyPerm ((Configuration β X × E) × ((f : Option ↥(Xᶜ)) → ι f)) k) ∧
        toEuclideanLin
          ((finKronecker fun _ : Fin k ↦ selectedBellProjection ΩX E) ⊗ₖ
            (1 : Matrix (Config k ι) (Config k ι) ℂ)) φ = φ ∧
        toEuclideanLin
          ((1 : Matrix (Fin k → Configuration β X × E)
            (Fin k → Configuration β X × E) ℂ) ⊗ₖ
              labelProj (subsystemPerm k ι {none}) (ell k)) φ = φ ∧
        (∀ B ∈ regions,
          toEuclideanLin
            ((1 : Matrix (Fin k → Configuration β X × E)
              (Fin k → Configuration β X × E) ℂ) ⊗ₖ
                labelCutoff (subsystemPerm k ι (exteriorRegion X B))
                  (a k (exteriorRegion X B))) φ = φ) ∧
        ‖⟪φ, toEuclideanLin
          ((1 : Matrix (Fin k → Configuration β X × E)
            (Fin k → Configuration β X × E) ℂ) ⊗ₖ
              labelProj (subsystemPerm k ι {none}) (ell k)) (post k)⟫_ℂ‖ ^ 2 = r k ∧
        q k / 2 ≤ r k ∧
        1 / (4 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤ r k := by
  classical
  intro ι ΩX χsite Ψ a q r post hmass
  have hm := eventually_commonLabelCutoff_compressedTypicalSite_retains_mass
    β Ω X E hΩ hz regions hnested hdisjoint ell hmass
  have hzX : 0 < Matrix.IsHermitian.spectralRestrictionMass
      (Matrix.PosSemidef.isHermitian
        (Matrix.posSemidef_vecMulVec_self_star ΩX).partialTraceRight) E := by
    exact hz
  have hsym (k : ℕ) : (Ψ k : Config k ι → ℂ) ∈ symmetricSubspace k ι :=
    compressedSite_prod_mem_symmetricSubspace β X (Fin E.card) k
      (fun p ↦ Matrix.compressedTypicalPureState ΩX E
        ((Finset.equivFin E).symm p.1, p.2))
  have haux : ∀ D ∈ regions.map (exteriorRegion X),
      Disjoint D ({none} : Finset (Option ↥(Xᶜ))) :=
    List.forall_mem_map.mpr (fun B _ ↦ exteriorRegion_disjoint_auxiliary X B)
  filter_upwards [hm] with k hk
  rcases hk with ⟨_, _, hpos, hhalf, hbound⟩
  obtain ⟨φ, hnorm, hcopy, hbell, hlabel, hcuts, hoverlap⟩ :=
    exists_commonLabelCutoff_bell_vector ι ΩX E k hzX
      (regions.map (exteriorRegion X)) (pairwise_exteriorRegion X regions hnested)
      (a k) {none} haux (ell k) (Ψ k) (hsym k) hpos
  refine ⟨φ, hnorm, ?_, hbell, hlabel, ?_, hoverlap, hhalf, hbound⟩
  · simpa only [mem_invariantSubspace, permOp_mulVec] using hcopy
  · intro B hB
    exact hcuts (exteriorRegion X B) (List.mem_map_of_mem hB)

end FiniteProduct
