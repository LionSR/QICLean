/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.CompressedTypicalExponential
import QICLean.Algebra.FiniteKroneckerOrder
import QICLean.Analysis.WeightedTraceHolder

open Matrix PermutationRepresentation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator ComplexOrder MatrixOrder

noncomputable section
namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
  (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The same actual compressed-state expectation is bounded by the
original physical regional moment with exactly one selection factor per copy.
The only selection assumption is positivity of its actual spectral mass.

Source: OpenAI area-law manuscript, comparator:post-marginal and
comparator:sharp-upper, 07-comparators.tex, lines 405–412. -/
theorem re_inner_exp_labelEntropy_compressedTypicalSiteState_prod_le
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X Q : Finset V)
    (hXQ : Disjoint X Q) (E : Finset (FiniteProduct.Configuration β X))
    (hz : 0 < (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E)
    (k : ℕ) (u : ℝ) :
    let z := (FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ω
    let χ : Fin E.card × FiniteProduct.Configuration β Xᶜ → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.1, x.2)
    let Ψ := WithLp.toLp 2
      (fun x : Config k (FiniteProduct.compressedSiteSpace β X (Fin E.card)) ↦
        ∏ j, χ (Equiv.piOptionEquivProd (x j)))
    (⟪Ψ, Matrix.toEuclideanLin
      (NormedSpace.exp ((u : ℂ) • labelEntropy
        (subsystemPerm k (FiniteProduct.compressedSiteSpace β X (Fin E.card))
          (FiniteProduct.exteriorRegion X Q)))) Ψ⟫_ℂ).re ≤
      z⁻¹ ^ k *
        (Matrix.finKronecker (fun _ : Fin k ↦ FiniteProduct.reducedPure β Ω Q) *
          NormedSpace.exp ((u : ℂ) •
            labelEntropy (copyPerm (FiniteProduct.Configuration β Q) k))).trace.re := by
  classical
  dsimp only
  rw [re_inner_exp_labelEntropy_compressedTypicalSiteState_prod β Ω X Q hXQ E k u]
  have hsingle := Matrix.le_iff.mpr
    (FiniteProduct.reducedPure_typicalPureState_le β Ω X E Q hXQ hz)
  have htensor := Matrix.finKronecker_mono
    (fun _ : Fin k ↦ FiniteProduct.reducedPure β (FiniteProduct.typicalPureState β Ω X E) Q)
    (fun _ : Fin k ↦
      ((FiniteProduct.reducedPure_posSemidef β Ω X).isHermitian.spectralRestrictionMass E)⁻¹ •
        FiniteProduct.reducedPure β Ω Q)
    (fun _ ↦ FiniteProduct.reducedPure_posSemidef β
      (FiniteProduct.typicalPureState β Ω X E) Q) (fun _ ↦ hsingle)
  have hscalar (c : ℝ) :
      Matrix.finKronecker (fun _ : Fin k ↦ c • FiniteProduct.reducedPure β Ω Q) =
        c ^ k • Matrix.finKronecker (fun _ : Fin k ↦ FiniteProduct.reducedPure β Ω Q) := by
    ext x y
    simp [Matrix.finKronecker_apply, Matrix.smul_apply,
      RCLike.real_smul_eq_coe_mul, Finset.prod_mul_distrib]
  rw [hscalar] at htensor
  have hH : ((u : ℂ) •
      labelEntropy (copyPerm (FiniteProduct.Configuration β Q) k)).IsHermitian :=
    (isHermitian_labelObservable (copyPerm (FiniteProduct.Configuration β Q) k)
      (fun l ↦ Real.log l.dim)).smul (by simp [IsSelfAdjoint])
  have htrace := Matrix.PosSemidef.re_trace_mul_le_re_trace_mul
    (Matrix.nonneg_iff_posSemidef.mp hH.isSelfAdjoint.exp_nonneg) htensor
  simp only [Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at htrace
  rw [Matrix.trace_mul_comm
    (Matrix.finKronecker (fun _ : Fin k ↦
      FiniteProduct.reducedPure β (FiniteProduct.typicalPureState β Ω X E) Q)) _,
    Matrix.trace_mul_comm
      (Matrix.finKronecker (fun _ : Fin k ↦ FiniteProduct.reducedPure β Ω Q)) _]
  exact htrace

end TensorPower
