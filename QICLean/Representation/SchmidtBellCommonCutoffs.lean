/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchmidtBellPrevector
import QICLean.Representation.CompressedTypicalLabelMass
import QICLean.Entropy.CompressedTypicalCommonBellVector

/-!
# One Schmidt label sequence for the prevector and the common-cutoff overlap

The label sequence selected from the actual compressed Schmidt vector is
used throughout. Its original physical prevector retains its nonvanishing,
energy, symmetry and auxiliary-label properties, as well as the entropy
asymptotic. The same sequence works for every finite nested regional
collection: it admits a unit vector in the selected Bell range and all prescribed regional
cutoff ranges, with an inverse-polynomial overlap.

The auxiliary polynomial-mass premise of the common-cutoff implication is
discharged here by the original Schmidt selection theorem. No tail estimate,
symmetry, marginal identity, positive overlap or independently chosen label is
assumed. The normalized post vector uses the selected Bell coordinate set `E`
and the enumerated right auxiliary set `Fin E.card`. These are the literal
coordinate conventions of the existing selected-state constructions.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 130–147, 240–281 and 332–354,
  `comparator:prevector`, `comparator:high-label` and `comparator:rough-overlap`,
  manuscript revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open Filter Topology
open scoped BigOperators Matrix Kronecker InnerProductSpace ComplexOrder
open Matrix PermutationRepresentation TensorPower

noncomputable section

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
variable (E : Finset (Configuration β X))

local notation "A" => Configuration β X
local notation "B" => Configuration β Xᶜ
local notation "ΩX" => LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
local notation "hρA" => Matrix.PosSemidef.partialTraceRight
  (posSemidef_vecMulVec_self_star ΩX)
local notation "z" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian (reducedPure_posSemidef β Ω X)) E

open Classical in
/-- One actual Schmidt-label sequence simultaneously has every original
prevector property and the common-cutoff overlap. The label selection theorem
is invoked once, before the regional collection is chosen; the eventual mass
bound needed by the cutoff argument is
derived from its same witness by an exact coordinate isometry.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 130–147,
240–281 and 332–354. -/
theorem exists_label_sequence_schmidtBellPrevector_commonCutoffs
    (hΩ : ‖Ω‖ = 1) (hz : 0 < z)
    (H : Matrix (A × B) (A × B) ℂ) (E₀ : ℝ)
    (hE : H *ᵥ ΩX = (E₀ : ℂ) • (fun x ↦ ΩX x)) :
    let ψ : B × Fin E.card → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let ι := compressedSiteSpace β X (Fin E.card)
    let χsite := WithLp.toLp 2
      (fun x : (f : Option ↥(Xᶜ)) → ι f ↦
        compressedTypicalPureState ΩX E
          ((Finset.equivFin E).symm (x none), fun v ↦ x (some v)))
    let Ψ : (k : ℕ) → EuclideanSpace ℂ (Config k ι) := fun k ↦
      WithLp.toLp 2 (fun x : Config k ι ↦ ∏ j, χsite (x j))
    let a := compressedRegionalThreshold β Ω X E
    let post : (k : ℕ) → EuclideanSpace ℂ ((Fin k → A × E) × Config k ι) := fun k ↦
      WithLp.toLp 2 (fun x ↦ (∏ j, selectedBellVector ΩX E (x.1 j)) * Ψ k x.2)
    ‖WithLp.toLp 2 ψ‖ = 1 ∧
      Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)) =
        Matrix.diagonal (fun r : Fin E.card ↦
          ((((Matrix.PosSemidef.isHermitian hρA).eigenvalues
            ((Finset.equivFin E).symm r)) / z : ℝ) : ℂ)) ∧
    ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      (∀ k : ℕ, 0 < k →
        let v := replicaPrevector ΩX E.card k (ell k)
        let P := labelProj (copyPerm (Fin E.card) k) (ell k)
        WithLp.toLp 2 v ≠ 0 ∧ ‖WithLp.toLp 2 v‖ ≤ 1 ∧
        (((k : ℝ)⁻¹ • replicaHamiltonian H k) ⊗ₖ
          (1 : Matrix ((Fin k → Fin E.card) × (Fin k → Fin E.card))
            ((Fin k → Fin E.card) × (Fin k → Fin E.card)) ℂ)) *ᵥ v = (E₀ : ℂ) • v ∧
        ((1 : Matrix (Fin k → (A × B)) (Fin k → (A × B)) ℂ) ⊗ₖ
          (P ⊗ₖ (1 : Matrix (Fin k → Fin E.card) (Fin k → Fin E.card) ℂ))) *ᵥ v = v ∧
        ((1 : Matrix (Fin k → (A × B)) (Fin k → (A × B)) ℂ) ⊗ₖ
          ((1 : Matrix (Fin k → Fin E.card) (Fin k → Fin E.card) ℂ) ⊗ₖ P)) *ᵥ v = v ∧
        (∀ σ : Equiv.Perm (Fin k),
          (permOp (copyPerm (A × B) k) σ ⊗ₖ
            (permOp (copyPerm (Fin E.card) k) σ ⊗ₖ permOp (copyPerm (Fin E.card) k) σ)) *ᵥ v = v)) ∧
      (∀ᶠ k : ℕ in atTop,
        (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
          ‖WithLp.toLp 2
            (((1 : Matrix (Fin k → B) (Fin k → B) ℂ) ⊗ₖ
              labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
              (fun x : (Fin k → B) × (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) ∧
      Asymptotics.IsLittleO atTop
        (fun k : ℕ ↦ Real.log (ell k).dim - (k : ℝ) *
          vonNeumannEntropy (partialTraceLeft (vecMulVec ψ (star ψ)))
            (posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian)
        (fun k : ℕ ↦ (k : ℝ)) ∧
      ∀ (regions : List (Finset V)),
        regions.Pairwise (fun C D ↦ C ⊆ D ∨ D ⊆ C) →
        (∀ C ∈ regions, Disjoint X C) →
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
          (∀ C ∈ regions,
            toEuclideanLin
              ((1 : Matrix (Fin k → Configuration β X × E)
                (Fin k → Configuration β X × E) ℂ) ⊗ₖ
                  labelCutoff (subsystemPerm k ι (exteriorRegion X C))
                    (a k (exteriorRegion X C))) φ = φ) ∧
          ‖⟪φ, toEuclideanLin
            ((1 : Matrix (Fin k → Configuration β X × E)
              (Fin k → Configuration β X × E) ℂ) ⊗ₖ
                labelProj (subsystemPerm k ι {none}) (ell k)) (post k)⟫_ℂ‖ ^ 2 = r k ∧
          q k / 2 ≤ r k ∧
          1 / (4 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤ r k := by
  classical
  intro ψ ι χsite Ψ a post
  have hzX : 0 < Matrix.IsHermitian.spectralRestrictionMass
      (Matrix.PosSemidef.isHermitian hρA) E := hz
  have hΩX : ‖ΩX‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X)).norm_map Ω).trans hΩ
  obtain ⟨hψ, hdiag, ell, hpre, hmass, hentropy⟩ :=
    TensorPower.exists_label_sequence_schmidtBellPrevector ΩX E hzX hΩX H E₀ hE
  refine ⟨hψ, hdiag, ell, hpre, hmass, hentropy, ?_⟩
  intro regions hnested hdisjoint q r
  have hmassSite : ∀ᶠ k : ℕ in atTop,
      1 / (2 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤ q k := by
    filter_upwards [hmass] with k hk
    have he : q k = ‖WithLp.toLp 2
        (((1 : Matrix (Fin k → Configuration β Xᶜ)
          (Fin k → Configuration β Xᶜ) ℂ) ⊗ₖ
            labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
          (fun x ↦ ∏ j, ψ (x.1 j, x.2 j)))‖ ^ 2 :=
      norm_sq_labelProj_compressedTypicalSite_prod β X k Ω E (ell k)
    rw [he]
    simpa only [one_div, Nat.cast_pow] using hk
  exact eventually_exists_commonLabelCutoff_compressedTypical_bell_vector
    β Ω X E hΩ hz regions hnested hdisjoint ell hmassSite

end FiniteProduct
