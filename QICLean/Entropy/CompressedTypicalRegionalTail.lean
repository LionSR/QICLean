/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.CompressedTypicalSiteNorm
import QICLean.Entropy.CompressedTypicalSiteEntropy
import QICLean.Entropy.IidSchurLabelExponential
import QICLean.Representation.SubsystemLabelCoordinates

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

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The actual regional Schur cutoff removes exponentially small squared
norm from the literal compressed selected vector's tensor powers. The cutoff
uses the original physical entropy divided by the actual selected mass.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 332–343. -/
theorem exists_norm_sq_one_sub_labelCutoff_compressedTypicalSite_prod_le_exp
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X B : Finset V)
    (hXB : Disjoint X B) (E : Finset (Configuration β X)) (hΩ : ‖Ω‖ = 1)
    (hz : 0 < (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let χsite := WithLp.toLp 2
      (fun x : (f : Option ↥(Xᶜ)) → compressedSiteSpace β X (Fin E.card) f ↦
        Matrix.compressedTypicalPureState ΩX E
          ((Finset.equivFin E).symm (x none), fun v ↦ x (some v)))
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      ‖toEuclideanLin
        (1 - labelCutoff
          (subsystemPerm k (compressedSiteSpace β X (Fin E.card)) (exteriorRegion X B))
          ((k : ℝ) * (entropy β Ω B /
            (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E + 1)))
        (WithLp.toLp 2
          (fun x : Config k (compressedSiteSpace β X (Fin E.card)) ↦
            ∏ j, χsite (x j)))‖ ^ 2 ≤ Real.exp (-c * (k : ℝ)) := by
  intro ΩX χsite
  let ι := compressedSiteSpace β X (Fin E.card)
  let B' := exteriorRegion X B
  let ρ := reducedPure ι χsite B'
  have hχ : ‖χsite‖ = 1 := norm_compressedTypicalSiteState β Ω X E hz
  have hρ : ρ.PosSemidef := reducedPure_posSemidef ι χsite B'
  have htr : ρ.trace = 1 := trace_reducedPure ι χsite hχ B'
  have hs : vonNeumannEntropy ρ hρ.isHermitian ≤
      entropy β Ω B /
        (reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E :=
    entropy_compressedTypicalSiteState_le β Ω X B hXB E hΩ hz
  obtain ⟨c, hc, htail⟩ :=
    hρ.exists_re_trace_one_sub_labelCutoff_finKronecker_le_exp htr hs
  refine ⟨c, hc, ?_⟩
  intro k hk
  rw [norm_sq_one_sub_labelCutoff_subsystemPerm_prod]
  exact htail k hk

end FiniteProduct
