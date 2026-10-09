/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.CompressedPhysicalRegions
import QICLean.Entropy.CompressedTypicalRegionalTail
import QICLean.Representation.CommonSchurCutoffs
import QICLean.Analysis.FiniteExponentialRetainedMass
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

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

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 332–354,
  `comparator:rough-overlap`, source commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open Filter Topology
open scoped BigOperators Matrix ComplexOrder
open Matrix PermutationRepresentation TensorPower

noncomputable section

namespace FiniteProduct

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
  let failure (k : ℕ) (D : Finset (Option ↥(Xᶜ))) : ℝ :=
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
      Disjoint D ({none} : Finset (Option ↥(Xᶜ))) := by
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

end FiniteProduct
