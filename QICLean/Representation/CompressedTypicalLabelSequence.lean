/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.HighLabelWindow
import QICLean.Representation.CompressedTypicalLabelMass
import QICLean.Entropy.CompressedTypicalSiteNorm
import QICLean.Entropy.CompressedTypicalCommonBellVector

/-!
# An auxiliary label sequence and common-cutoff Bell vectors

The entropy-window selection is applied to the actual normalized compressed
selected vector. Transporting its auxiliary projection into site coordinates
preserves its mass. Thus one sequence has both an inverse-polynomial mass
bound and the entropy asymptotics of its logarithmic representation dimension.
For a fixed nested family of physical regions, the same sequence also gives
a unit vector in the selected Bell range, the auxiliary-label range and every
regional cutoff range. Its squared overlap is the actual mass of the common
projection, before normalization. This construction does not include the
low-defect projection or the original physical prevector.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 255–281 and 332–354, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter Topology
open scoped BigOperators Matrix Kronecker InnerProductSpace ComplexOrder
open Matrix PermutationRepresentation TensorPower

noncomputable section

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

open Classical in
/-- One sequence of auxiliary Schur labels simultaneously has the required
mass in the actual compressed-site coordinates and the logarithmic-dimension
asymptotics of the actual selected auxiliary density. Singular marginals are
allowed. Source: `07-comparators.tex`, `comparator:high-label`, lines 255–281.
This statement constructs no low-defect projection or prevector. -/
theorem exists_label_sequence_compressedTypicalSite_mass_entropy_asymptotic
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
    (E : Finset (Configuration β X))
    (hz : 0 < (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E) :
    let ι := compressedSiteSpace β X (Fin E.card)
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let ψ : Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let Ψ : (k : ℕ) → EuclideanSpace ℂ (Config k ι) := fun _ ↦
      WithLp.toLp 2 (fun x ↦ ∏ j, ψ ((fun v ↦ x j (some v)), x j none))
    ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      (∀ᶠ k : ℕ in atTop,
        1 / (2 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤
          ‖toEuclideanLin (labelProj (subsystemPerm k ι {none}) (ell k)) (Ψ k)‖ ^ 2) ∧
      Asymptotics.IsLittleO atTop
        (fun k : ℕ ↦ Real.log (ell k).dim - (k : ℝ) *
          vonNeumannEntropy (partialTraceLeft (vecMulVec ψ (star ψ)))
            (posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian)
        (fun k : ℕ ↦ (k : ℝ)) := by
  classical
  intro ι ΩX ψ Ψ
  have hsite := norm_compressedTypicalSiteState β Ω X E hz
  let e := (Equiv.piOptionEquivProd (β := ι)).trans
    (Equiv.prodComm (Fin E.card) (Configuration β Xᶜ))
  have hψ : ‖WithLp.toLp 2 ψ‖ = 1 := by
    change ‖(LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
      (WithLp.toLp 2 (fun x ↦ ψ (fun v ↦ x (some v), x none)))‖ = 1
    exact ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map _).trans hsite
  obtain ⟨ell, hmass, hdim⟩ :=
    TensorPower.exists_label_sequence_pure_norm_entropy_asymptotic ψ hψ
  refine ⟨ell, ?_, hdim⟩
  filter_upwards [hmass] with k hk
  rw [TensorPower.norm_sq_labelProj_compressedTypicalSite_prod β X k Ω E (ell k)]
  simpa only [one_div, Nat.cast_pow, Fintype.card_fin] using hk

open Classical in
/-- One actual auxiliary-label sequence has the entropy asymptotics of the
selected density and eventually admits a normalized Bell vector in all
prescribed common regional cutoffs. Its overlap is the literal retained mass.
Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 255–298
and 332–354. This constructs the rough common-cutoff vector; the low-defect
projection and the source prevector require further arguments. -/
theorem exists_label_sequence_commonLabelCutoff_compressedTypical_bell_vector
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
    (E : Finset (Configuration β X)) (hΩ : ‖Ω‖ = 1)
    (hz : 0 < (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E)
    (regions : List (Finset V))
    (hnested : regions.Pairwise fun B C ↦ B ⊆ C ∨ C ⊆ B)
    (hdisjoint : ∀ B ∈ regions, Disjoint X B)
    :
    let ι := compressedSiteSpace β X (Fin E.card)
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let ψ : Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let Ψ : (k : ℕ) → EuclideanSpace ℂ (Config k ι) := fun k ↦
      WithLp.toLp 2 (fun x : Config k ι ↦ ∏ j, ψ ((fun v ↦ x j (some v)), x j none))
    let a := compressedRegionalThreshold β Ω X E
    let post : (k : ℕ) →
        EuclideanSpace ℂ ((Fin k → Configuration β X × E) × Config k ι) := fun k ↦
      WithLp.toLp 2 (fun x ↦
        (∏ j, selectedBellVector ΩX E (x.1 j)) * Ψ k x.2)
    ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      Asymptotics.IsLittleO atTop
        (fun k : ℕ ↦ Real.log (ell k).dim - (k : ℝ) *
          vonNeumannEntropy (partialTraceLeft (vecMulVec ψ (star ψ)))
            (posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian)
        (fun k : ℕ ↦ (k : ℝ)) ∧
    let q : ℕ → ℝ := fun k ↦
      ‖toEuclideanLin (labelProj (subsystemPerm k ι {none}) (ell k)) (Ψ k)‖ ^ 2
    let r : ℕ → ℝ := fun k ↦
      ‖toEuclideanLin
        (commonLabelCutoff ι k (regions.map (exteriorRegion X)) (a k) *
          labelProj (subsystemPerm k ι {none}) (ell k)) (Ψ k)‖ ^ 2
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
  intro ι ΩX ψ Ψ a post
  obtain ⟨ell, hmass, hdim⟩ :=
    exists_label_sequence_compressedTypicalSite_mass_entropy_asymptotic β Ω X E hz
  refine ⟨ell, hdim, ?_⟩
  exact (eventually_exists_commonLabelCutoff_compressedTypical_bell_vector
    β Ω X E hΩ hz regions hnested hdisjoint ell) hmass

end FiniteProduct
