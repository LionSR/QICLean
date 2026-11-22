/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.Label.SubsystemLabelCoordinates
import QICLean.ManyBody.Entropy.Typical.CompressedTypicalSiteCoordinates
import QICLean.ManyBody.Replica.Label.SubsystemTransport
import QICLean.Spectral.Filter.Gaussian.Reindex

/-!
# Regional exponential expectations after spectral compression

The product of the actual compressed selected vector has the regional
exponential expectation of the same selected physical marginal. The
coordinate identification transports both the tensor density and the
label entropy. The original vector need not be normalized, and the
identity includes zero copies, empty regions, and zero selected mass.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, `comparator:post-marginal` and
the proof of `comparator:sharp-upper`, lines 405–412, source revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

noncomputable section
namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
  (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The literal compressed selected vector has the exponential expectation
of its actual selected physical marginal, in the original regional coordinates.
No normalization or positive selected mass is required for this equality.

Source: OpenAI area-law manuscript, comparator:post-marginal and
comparator:sharp-upper, 07-comparators.tex, lines 405–412. -/
theorem re_inner_exp_labelEntropy_compressedTypicalSiteState_prod
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X Q : Finset V)
    (hXQ : Disjoint X Q) (E : Finset (ManyBody.RegionConfig β X)) (k : ℕ) (u : ℝ) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (ManyBody.cutEquiv β X) Ω
    let χ : Fin E.card × ManyBody.ComplConfig β X → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.1, x.2)
    let Ψ := WithLp.toLp 2
      (fun x : Config k (ManyBody.compressedSiteSpace β X (Fin E.card)) ↦
        ∏ j, χ (Equiv.piOptionEquivProd (x j)))
    (⟪Ψ, Matrix.toEuclideanLin
      (NormedSpace.exp ((u : ℂ) • labelEntropy
        (subsystemPerm k (ManyBody.compressedSiteSpace β X (Fin E.card))
          (ManyBody.exteriorRegion X Q)))) Ψ⟫_ℂ).re =
      (Matrix.piKronecker
          (fun _ : Fin k ↦ ManyBody.regionState (ManyBody.typicalPureState β Ω X E) Q) *
        NormedSpace.exp ((u : ℂ) •
          labelEntropy (copyPerm (ManyBody.RegionConfig β Q) k))).trace.re := by
  intro ΩX χ Ψ
  rw [re_inner_exp_labelEntropy_subsystemPerm_prod
    (ManyBody.compressedSiteSpace β X (Fin E.card))
    (WithLp.toLp 2 (fun x ↦ χ (Equiv.piOptionEquivProd x))) k
    (ManyBody.exteriorRegion X Q) u]
  let e := Equiv.arrowCongr (Equiv.refl (Fin k))
    (ManyBody.exteriorRegionEquiv β X Q (Fin E.card) hXQ)
  have hF : labelEntropy (copyPerm (ManyBody.RegionConfig β Q) k) =
      Matrix.reindex e e (labelEntropy
        (copyPerm (ManyBody.RegionConfig
          (ManyBody.compressedSiteSpace β X (Fin E.card))
          (ManyBody.exteriorRegion X Q)) k)) := by
    simpa only [labelEntropy, labelObservable, labelProj, map_sum, map_smul] using
      groupAlgebraRep_of_intertwine e
        (φ := copyPerm (ManyBody.RegionConfig
          (ManyBody.compressedSiteSpace β X (Fin E.card))
          (ManyBody.exteriorRegion X Q)) k)
        (ψ := copyPerm (ManyBody.RegionConfig β Q) k)
        (fun σ x ↦ funext fun j ↦ rfl)
        (∑ l : IrrepLabel (Equiv.Perm (Fin k)),
          (Real.log l.dim : ℂ) • IrrepLabel.centralIdem l)
  have hρ := ManyBody.regionState_compressedTypicalSiteState β X Q Ω hXQ E
  have hK : Matrix.reindex e e (Matrix.piKronecker
      (fun _ : Fin k ↦ ManyBody.regionState
        (WithLp.toLp 2 (fun x ↦ χ (Equiv.piOptionEquivProd x)))
        (ManyBody.exteriorRegion X Q))) =
      Matrix.piKronecker
        (fun _ : Fin k ↦ ManyBody.regionState
          (ManyBody.typicalPureState β Ω X E) Q) := by
    ext x y
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.piKronecker_apply,
      e, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Equiv.symm_symm,
      Equiv.refl_apply, Function.comp_apply, χ, ΩX] using
      congrArg (fun M ↦ ∏ j : Fin k, M (x j) (y j)) hρ
  have hExp : Matrix.reindex e e (NormedSpace.exp ((u : ℂ) •
      labelEntropy (copyPerm (ManyBody.RegionConfig
        (ManyBody.compressedSiteSpace β X (Fin E.card))
        (ManyBody.exteriorRegion X Q)) k))) =
      NormedSpace.exp ((u : ℂ) •
        labelEntropy (copyPerm (ManyBody.RegionConfig β Q) k)) := by
    rw [Matrix.reindex_exp]
    simpa only [Matrix.reindex_apply, Matrix.submatrix_smul, Pi.smul_apply] using
      congrArg (fun M ↦ NormedSpace.exp ((u : ℂ) • M)) hF.symm
  rw [← Matrix.trace_reindex e, Matrix.reindex_apply,
    ← Matrix.submatrix_mul_equiv _ _ e.symm e.symm e.symm]
  simpa only [Matrix.reindex_apply] using
    congrArg (fun M : Matrix (Fin k → ManyBody.RegionConfig β Q)
      (Fin k → ManyBody.RegionConfig β Q) ℂ ↦ M.trace.re)
      (congrArg₂ (· * ·) hK hExp)

end TensorPower
