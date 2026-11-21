import QICLean.Entropy.RegionTypicalState

/-! A single actual selected state satisfies the estimates simultaneously on all
regions disjoint from the projected region. -/

open scoped ComplexOrder

namespace RegionTypicalStateTest

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

theorem oneState_forall_disjointRegions
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (X : Finset V) (E : Finset (ManyBody.RegionConfig β X))
    (hz : 0 < (ManyBody.regionState_posSemidef X ψ).isHermitian.spectralRestrictionMass E) :
    ∃ φ : EuclideanSpace ℂ ((v : V) → β v), ‖φ‖ = 1 ∧
      ∀ B : Finset V, Disjoint X B →
        (((ManyBody.regionState_posSemidef X ψ).isHermitian.spectralRestrictionMass E)⁻¹ •
            ManyBody.regionState ψ B - ManyBody.regionState φ B).PosSemidef ∧
        ManyBody.regionEntropy φ B ≤ ManyBody.regionEntropy ψ B /
          (ManyBody.regionState_posSemidef X ψ).isHermitian.spectralRestrictionMass E := by
  exact ⟨ManyBody.typicalPureState β ψ X E,
    ManyBody.norm_typicalPureState β ψ X E hz,
    fun B h ↦ ⟨ManyBody.regionState_typicalPureState_le β ψ X E B h hz,
      ManyBody.regionEntropy_typicalPureState_le β ψ X E B h hψ hz⟩⟩

end RegionTypicalStateTest
