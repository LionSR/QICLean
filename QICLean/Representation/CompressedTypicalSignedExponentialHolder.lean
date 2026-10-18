import QICLean.Representation.CompressedTypicalExponentialDomination
import QICLean.Analysis.WeightedTraceHolder
import QICLean.Representation.SubsystemLabelCommutation

open Matrix PermutationRepresentation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

noncomputable section
namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
  (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- Three-factor Hölder and the actual selected-marginal order bound the
signed regional exponential with exactly one inverse selected mass per copy.

Source: OpenAI area-law manuscript, 07-comparators.tex,
comparator:post-marginal, lines 323–332, and the proof of
comparator:sharp-upper, lines 405–416, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/
theorem re_inner_exp_signed_labelEntropy_compressedTypicalSiteState_prod_le
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X U Y : Finset V)
    (hXUY : Disjoint X (U ∪ Y)) (hUY : Disjoint U Y)
    (E : Finset (FiniteProduct.Configuration β X))
    (hz : 0 < (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E)
    (k : ℕ) (a : ℝ) :
    let z := (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ω
    let χ : Fin E.card × FiniteProduct.Configuration β Xᶜ → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.1, x.2)
    let Ψ := WithLp.toLp 2
      (fun x : Config k (FiniteProduct.compressedSiteSpace β X (Fin E.card)) ↦
        ∏ j, χ (Equiv.piOptionEquivProd (x j)))
    let L := fun Q : Finset V ↦
      labelEntropy (subsystemPerm k (FiniteProduct.compressedSiteSpace β X (Fin E.card))
        (FiniteProduct.exteriorRegion X Q))
    let M := fun (Q : Finset V) (u : ℝ) ↦
      (Matrix.finKronecker (fun _ : Fin k ↦ FiniteProduct.reducedPure β Ω Q) *
        NormedSpace.exp ((u : ℂ) •
          labelEntropy (copyPerm (FiniteProduct.Configuration β Q) k))).trace.re
    (⟪Ψ, Matrix.toEuclideanLin
      (NormedSpace.exp ((a : ℂ) • (L U + L (U ∪ Y) - L Y))) Ψ⟫_ℂ).re ≤
      z⁻¹ ^ k *
        ((M U (3 * a)) ^ (1 / 3 : ℝ) *
          (M (U ∪ Y) (3 * a)) ^ (1 / 3 : ℝ) *
          (M Y (-3 * a)) ^ (1 / 3 : ℝ)) := by
  done

end TensorPower
