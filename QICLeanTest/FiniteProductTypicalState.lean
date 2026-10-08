import QICLean.Entropy.FiniteProductTypicalState

/-! A single actual selected state satisfies the estimates simultaneously on all
regions disjoint from the projected region. -/

open scoped ComplexOrder

namespace FiniteProductTypicalStateTest

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

theorem oneState_forall_disjointRegions
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (X : Finset V) (E : Finset (FiniteProduct.Configuration β X))
    (hz : 0 < (FiniteProduct.reducedPure_posSemidef β ψ X).isHermitian.spectralRestrictionMass E) :
    ∃ φ : EuclideanSpace ℂ ((v : V) → β v), ‖φ‖ = 1 ∧
      ∀ B : Finset V, Disjoint X B →
        (((FiniteProduct.reducedPure_posSemidef β ψ X).isHermitian.spectralRestrictionMass E)⁻¹ •
            FiniteProduct.reducedPure β ψ B - FiniteProduct.reducedPure β φ B).PosSemidef ∧
        FiniteProduct.entropy β φ B ≤ FiniteProduct.entropy β ψ B /
          (FiniteProduct.reducedPure_posSemidef β ψ X).isHermitian.spectralRestrictionMass E := by
  exact ⟨FiniteProduct.typicalPureState β ψ X E,
    FiniteProduct.norm_typicalPureState β ψ X E hz,
    fun B h ↦ ⟨FiniteProduct.reducedPure_typicalPureState_le β ψ X E B h hz,
      FiniteProduct.entropy_typicalPureState_le β ψ X E B h hψ hz⟩⟩

end FiniteProductTypicalStateTest
