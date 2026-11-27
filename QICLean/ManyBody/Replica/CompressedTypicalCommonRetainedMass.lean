/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Entropy.Typical.CompressedPhysicalRegions
import QICLean.ManyBody.Replica.Label.CommonSchurCutoffs
import QICLean.Analysis.Real.FiniteExponentialRetainedMass
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import QICLean.ManyBody.Entropy.Typical.CompressedTypicalSiteCoordinates
import QICLean.Representation.SchurWeyl.IidSchurSignedMoments
import QICLean.ManyBody.Replica.Label.SubsystemLabelCoordinates
import QICLean.ManyBody.Replica.CompressedSite.CompressedTypicalAuxiliaryCoordinates

/-!
# Common regional cutoffs for the actual compressed selected state

Fix a normalized physical vector, a selected spectral set of positive mass,
and a finite nested list of physical regions disjoint from the selected
region. Consider the literal compressed selected vector, with one auxiliary
site and the original complementary physical sites. Each regional cutoff
uses the original regional entropy divided by the selected mass.

For a given auxiliary Schur label sequence, suppose that its actual projected
mass has the eventual inverse-polynomial lower bound supplied by the
Schmidt--Bell selection theorem. The regional exponential estimates then
show that the initial mass minus the exact sum of regional losses is positive
and retains at least half the initial mass. The common cutoff projection has
at least this mass by the commuting-projection union bound.

This is an auxiliary implication. It does not choose a label sequence or
assume a regional tail estimate. Its eventual mass hypothesis is to be
discharged using the same previously chosen Schmidt--Bell sequence.
Repeated regions and the empty list are permitted.

It also contains the following results.

* `ManyBody.eventually_exists_commonLabelCutoff_compressedTypical_bell_vector`: the actual
  normalized Bell vector with common regional cutoffs.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 332–354,
  `comparator:rough-overlap`, source commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

section CompressedTypicalCommonRetainedMass

section CompressedTypicalRegionalTail

/-!
# Exponential regional cutoff loss for the actual compressed selected state

The actual compressed selected vector is a unit vector on its auxiliary site
and the original complementary physical sites. Its marginal on a disjoint
physical region is positive, has trace one, and has entropy at most the
original regional entropy divided by the selected mass. Applying the
independent-copy Schur estimate to this actual marginal bounds the loss of
the literal subsystem cutoff on the compressed vector's tensor powers.

No marginal, invariance, entropy, or concentration certificate is supplied.
The rate depends on the fixed original state, selection, and observed region.
The regional marginal may be singular, and the region may be empty.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 320–343,
  `comparator:post-marginal` and `comparator:rough-overlap`, source commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped BigOperators Matrix Kronecker ComplexOrder
open Matrix PermutationRepresentation TensorPower

noncomputable section

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The actual regional Schur cutoff removes exponentially small squared
norm from the literal compressed selected vector's tensor powers. The cutoff
uses the original physical entropy divided by the actual selected mass.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 332–343. -/
theorem exists_norm_sq_one_sub_labelCutoff_compressedTypicalSite_prod_le_exp
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X B : Finset V)
    (hXB : Disjoint X B) (E : Finset (RegionConfig β X)) (hΩ : ‖Ω‖ = 1)
    (hz : 0 < (regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass E) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cutEquiv β X) Ω
    let χsite := WithLp.toLp 2
      (fun x : (f : Option {v // v ∉ X}) → compressedSiteSpace β X (Fin E.card) f ↦
        Matrix.compressedTypicalPureState ΩX E
          ((Finset.equivFin E).symm (x none), fun v ↦ x (some v)))
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      ‖toEuclideanLin
        (1 - labelCutoff
          (subsystemPerm k (compressedSiteSpace β X (Fin E.card))
              (exteriorRegion X B))
          ((k : ℝ) * (regionEntropy Ω B /
            (regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass E + 1)))
        (WithLp.toLp 2
          (fun x : TensorPower.Config k (compressedSiteSpace β X (Fin E.card)) ↦
            ∏ j, χsite (x j)))‖ ^ 2 ≤ Real.exp (-c * (k : ℝ)) := by
  intro ΩX χsite
  let ι := compressedSiteSpace β X (Fin E.card)
  let B' := exteriorRegion X B
  let ρ := regionState χsite B'
  have hχ : ‖χsite‖ = 1 := norm_compressedTypicalSiteState β Ω X E hz
  have hρ : ρ.PosSemidef := regionState_posSemidef B' χsite
  have htr : ρ.trace = 1 := trace_regionState_eq_one hχ (D := B')
  have hs : vonNeumannEntropy ρ hρ.isHermitian ≤
      regionEntropy Ω B /
        (regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass E :=
    regionEntropy_compressedTypicalSiteState_le β Ω X B hXB E hΩ hz
  obtain ⟨c, hc, htail⟩ :=
    hρ.exists_re_trace_one_sub_labelCutoff_piKronecker_le_exp htr hs
  refine ⟨c, hc, ?_⟩
  intro k hk
  rw [norm_sq_one_sub_labelCutoff_subsystemPerm_prod]
  exact htail k hk

end ManyBody
end

end CompressedTypicalRegionalTail

open Filter Topology
open scoped BigOperators Matrix ComplexOrder
open Matrix PermutationRepresentation TensorPower

noncomputable section

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The same given auxiliary label retains half its actual mass after all
the prescribed regional cutoffs. The quantitative bound also holds for the
initial mass minus the exact list sum of losses, giving the strict positivity
needed to normalize the common projection.

The only asymptotic premise is the eventual lower bound on the actual
auxiliary mass; the regional thresholds and exponential losses are derived
from the original state and selection.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 332–354. -/
theorem eventually_commonLabelCutoff_compressedTypicalSite_retains_mass
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
    (E : Finset (RegionConfig β X)) (hΩ : ‖Ω‖ = 1)
    (hz : 0 < (regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass E)
    (regions : List (Finset V))
    (hnested : regions.Pairwise fun B C ↦ B ⊆ C ∨ C ⊆ B)
    (hdisjoint : ∀ B ∈ regions, Disjoint X B)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) :
    let ι := compressedSiteSpace β X (Fin E.card)
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cutEquiv β X) Ω
    let χsite := WithLp.toLp 2
      (fun x : (f : Option {v // v ∉ X}) → ι f ↦
        Matrix.compressedTypicalPureState ΩX E
          ((Finset.equivFin E).symm (x none), fun v ↦ x (some v)))
    let Ψ : (k : ℕ) → EuclideanSpace ℂ (TensorPower.Config k ι) := fun k ↦
      WithLp.toLp 2 (fun x : TensorPower.Config k ι ↦ ∏ j, χsite (x j))
    let a := compressedRegionalThreshold β Ω X E
    let q : ℕ → ℝ := fun k ↦
      ‖toEuclideanLin (labelProj (subsystemPerm k ι {none}) (ell k)) (Ψ k)‖ ^ 2
    let loss : ℕ → ℝ := fun k ↦
      ((regions.map (exteriorRegion X)).map fun D ↦
        ‖toEuclideanLin (1 - labelCutoff (subsystemPerm k ι D) (a k D))
          (Ψ k)‖ ^ 2).sum
    let r : ℕ → ℝ := fun k ↦
      ‖toEuclideanLin
        (commonLabelCutoff ι k (regions.map (exteriorRegion X)) (a k) *
          labelProj (subsystemPerm k ι {none}) (ell k)) (Ψ k)‖ ^ 2
    (∀ᶠ k : ℕ in atTop,
      1 / (2 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤ q k) →
    ∀ᶠ k : ℕ in atTop,
      q k / 2 ≤ q k - loss k ∧
      1 / (4 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤ q k - loss k ∧
      0 < q k - loss k ∧
      q k / 2 ≤ r k ∧
      1 / (4 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤ r k := by
  classical
  intro ι ΩX χsite Ψ a q loss r hmass
  let failure (k : ℕ) (D : Finset (Option {v // v ∉ X})) : ℝ :=
    ‖toEuclideanLin (1 - labelCutoff (subsystemPerm k ι D) (a k D)) (Ψ k)‖ ^ 2
  let lossAt (i : Fin regions.length) (k : ℕ) : ℝ :=
    failure k (exteriorRegion X (regions.get i))
  have hsum (k : ℕ) : (∑ i, lossAt i k) = loss k := by
    change (∑ i : Fin regions.length,
      failure k (exteriorRegion X (regions.get i))) =
        ((regions.map (exteriorRegion X)).map (failure k)).sum
    rw [← Fin.sum_ofFn,
      List.ofFn_comp' regions.get (fun B ↦ failure k (exteriorRegion X B)),
      List.ofFn_get, List.map_map]
    rfl
  have htail : ∀ i, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ k : ℕ in atTop, lossAt i k ≤ Real.exp (-c * (k : ℝ)) := by
    intro i
    have hi : Disjoint X (regions.get i) :=
      hdisjoint _ (List.get_mem regions i)
    obtain ⟨c, hc, hck⟩ :=
      exists_norm_sq_one_sub_labelCutoff_compressedTypicalSite_prod_le_exp
        β Ω X (regions.get i) hi E hΩ hz
    refine ⟨c, hc, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    dsimp only [lossAt, failure, a]
    rw [compressedRegionalThreshold_exteriorRegion β Ω X (regions.get i) hi E k]
    exact hck k hk
  have haux : ∀ D ∈ regions.map (exteriorRegion X),
      Disjoint D ({none} : Finset (Option {v // v ∉ X})) := by
    simpa only [List.forall_mem_map] using
      (fun B (_ : B ∈ regions) ↦ exteriorRegion_disjoint_auxiliary X B)
  have hretain (k : ℕ) : q k - loss k ≤ r k :=
    norm_commonLabelCutoff_auxLabel_ge ι k (regions.map (exteriorRegion X))
      (pairwise_exteriorRegion X regions hnested) (a k) {none} haux (ell k) (Ψ k)
  have hscalar := Real.eventually_half_mass_of_exponential_losses
    q (fun k ↦ q k - loss k) lossAt (E.card ^ 2) hmass
    (fun k ↦ by rw [hsum k]) htail
  filter_upwards [hscalar] with k hk
  have hpositive : 0 < 1 / (4 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) := by
    positivity
  exact ⟨hk.1, hk.2, hpositive.trans_le hk.2,
    hk.1.trans (hretain k), hk.2.trans (hretain k)⟩

end ManyBody

end

end CompressedTypicalCommonRetainedMass

section CompressedTypicalCommonBellVector

/-!
## The actual normalized Bell vector with common regional cutoffs

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

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 283–298 and 332–354,
  `comparator:bell-pin` and `comparator:rough-overlap`, source commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open Filter Topology
open scoped BigOperators Matrix Kronecker InnerProductSpace ComplexOrder
open Matrix PermutationRepresentation TensorPower

noncomputable section

namespace ManyBody

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
    (E : Finset (RegionConfig β X)) (hΩ : ‖Ω‖ = 1)
    (hz : 0 < (regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass E)
    (regions : List (Finset V))
    (hnested : regions.Pairwise fun B C ↦ B ⊆ C ∨ C ⊆ B)
    (hdisjoint : ∀ B ∈ regions, Disjoint X B)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) :
    let ι := compressedSiteSpace β X (Fin E.card)
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cutEquiv β X) Ω
    let χsite := WithLp.toLp 2
      (fun x : (f : Option {v // v ∉ X}) → ι f ↦
        Matrix.compressedTypicalPureState ΩX E
          ((Finset.equivFin E).symm (x none), fun v ↦ x (some v)))
    let Ψ : (k : ℕ) → EuclideanSpace ℂ (TensorPower.Config k ι) := fun k ↦
      WithLp.toLp 2 (fun x : TensorPower.Config k ι ↦ ∏ j, χsite (x j))
    let a := compressedRegionalThreshold β Ω X E
    let q : ℕ → ℝ := fun k ↦
      ‖toEuclideanLin (labelProj (subsystemPerm k ι {none}) (ell k)) (Ψ k)‖ ^ 2
    let r : ℕ → ℝ := fun k ↦
      ‖toEuclideanLin
        (commonLabelCutoff ι k (regions.map (exteriorRegion X)) (a k) *
          labelProj (subsystemPerm k ι {none}) (ell k)) (Ψ k)‖ ^ 2
    let post : (k : ℕ) →
        EuclideanSpace ℂ
            ((Fin k → RegionConfig β X × E) × TensorPower.Config k ι) := fun k ↦
      WithLp.toLp 2 (fun x ↦
        (∏ j, selectedBellVector ΩX E (x.1 j)) * Ψ k x.2)
    (∀ᶠ k : ℕ in atTop,
      1 / (2 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤ q k) →
    ∀ᶠ k : ℕ in atTop,
      let e := Equiv.arrowProdEquivProdArrow (Fin k)
        (fun _ ↦ RegionConfig β X × E) (fun _ ↦ (f : Option {v // v ∉ X}) → ι f)
      ∃ φ : EuclideanSpace ℂ ((Fin k → RegionConfig β X × E) × TensorPower.Config k ι),
        ‖φ‖ = 1 ∧
        (fun x ↦ φ (e x)) ∈ invariantSubspace
          (copyPerm ((RegionConfig β X × E) × ((f : Option {v // v ∉ X}) → ι f)) k) ∧
        toEuclideanLin
          ((piKronecker fun _ : Fin k ↦ selectedBellProjection ΩX E) ⊗ₖ
            (1 : Matrix (TensorPower.Config k ι) (TensorPower.Config k ι) ℂ)) φ = φ ∧
        toEuclideanLin
          ((1 : Matrix (Fin k → RegionConfig β X × E)
            (Fin k → RegionConfig β X × E) ℂ) ⊗ₖ
              labelProj (subsystemPerm k ι {none}) (ell k)) φ = φ ∧
        (∀ B ∈ regions,
          toEuclideanLin
            ((1 : Matrix (Fin k → RegionConfig β X × E)
              (Fin k → RegionConfig β X × E) ℂ) ⊗ₖ
                labelCutoff (subsystemPerm k ι (exteriorRegion X B))
                  (a k (exteriorRegion X B))) φ = φ) ∧
        ‖⟪φ, toEuclideanLin
          ((1 : Matrix (Fin k → RegionConfig β X × E)
            (Fin k → RegionConfig β X × E) ℂ) ⊗ₖ
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
  have hsym (k : ℕ) : (Ψ k : TensorPower.Config k ι → ℂ) ∈ symmetricSubspace k ι :=
    compressedSite_prod_mem_symmetricSubspace β X (Fin E.card) k
      (fun p ↦ Matrix.compressedTypicalPureState ΩX E
        ((Finset.equivFin E).symm p.1, p.2))
  have haux : ∀ D ∈ regions.map (exteriorRegion X),
      Disjoint D ({none} : Finset (Option {v // v ∉ X})) :=
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

end ManyBody

end

end CompressedTypicalCommonBellVector
