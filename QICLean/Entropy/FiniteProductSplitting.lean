/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.FiniteProduct
import QICLean.Entropy.PurificationSplitting

/-!
# Purification splitting for finite regions

For two disjoint regions of a normalized finite-product pure state, an isometry
acting on their complement separates the state into two unit purifications. The
error is bounded by the square root of the regional mutual information. Local
basis dimensions may vary, and all three regions may be empty.

The reduced density and regional mutual information are the existing finite-product
constructions. The proof identifies their coordinate representation and applies
Uhlmann's purification-overlap theorem through `PurificationSplitting`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Lemma 6.4 (`lem:splitting`), `05-frames.tex:352–391`;
  source commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

These proofs were written independently; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript:
preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/
build/sections/05-frames.tex
Labels: lem:splitting.
-/

open scoped Matrix ComplexOrder Kronecker Matrix.Norms.L2Operator

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- Coordinates for two disjoint regions and their complement. The first two
factors use their canonical finite enumerations.

Source: PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex:352–359`. -/
noncomputable def splitTwoRegionsEquiv (T E : Finset V) (h : Disjoint T E) :
    ((v : V) → β v) ≃
      (Fin (Fintype.card (Configuration β T)) × Fin (Fintype.card (Configuration β E))) ×
        Configuration β (T ∪ E)ᶜ :=
  (splitEquiv β (T ∪ E)).trans
    (((unionEquiv β T E h).trans
      ((Fintype.equivFin (Configuration β T)).prodCongr
        (Fintype.equivFin (Configuration β E)))).prodCongr (Equiv.refl _))

/-- The physical state expressed in the coordinates of two regions and their
complement. This is a change of basis indices, with no truncation.

Source: PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex:352–359`. -/
noncomputable def splitTwoRegionsState (ψ : EuclideanSpace ℂ ((v : V) → β v))
    (T E : Finset V) (h : Disjoint T E) :
    (Fin (Fintype.card (Configuration β T)) × Fin (Fintype.card (Configuration β E))) ×
        Configuration β (T ∪ E)ᶜ → ℂ :=
  fun x ↦ ψ ((splitTwoRegionsEquiv β T E h).symm x)

omit [∀ v, DecidableEq (β v)] in
/-- The right marginal in these coordinates is precisely the existing joint
regional density matrix.

Source: PEPS manuscript, proof of Lemma 6.4, `05-frames.tex:371–375`. -/
theorem partialTraceRight_splitTwoRegionsState
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (T E : Finset V) (h : Disjoint T E) :
    Matrix.partialTraceRight (Matrix.vecMulVec (splitTwoRegionsState β ψ T E h)
      (star (splitTwoRegionsState β ψ T E h))) = jointMatrix β ψ T E h := by
  rfl

omit [∀ v, DecidableEq (β v)] in
/-- Coordinate decomposition preserves normalization of the full pure state.

Source: PEPS manuscript, proof of Lemma 6.4, `05-frames.tex:371–389`. -/
theorem splitTwoRegionsState_unit (ψ : EuclideanSpace ℂ ((v : V) → β v))
    (hψ : ‖ψ‖ = 1) (T E : Finset V) (h : Disjoint T E) :
    star (splitTwoRegionsState β ψ T E h) ⬝ᵥ splitTwoRegionsState β ψ T E h = 1 := by
  rw [← Matrix.trace_partialTraceRight_vecMulVec,
    partialTraceRight_splitTwoRegionsState]
  dsimp only [jointMatrix]
  rw [Matrix.trace_submatrix_equiv]
  exact trace_reducedPure β ψ hψ (T ∪ E)

/-- Splitting a finite-product pure state on two disjoint regions and their
complement. The isometry is defined on the entire complement space, including
unused directions. The two output vectors are unit, and the error bound uses the
actual regional mutual information. No Hamiltonian or dimension bound is assumed.

Source: PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex:352–391`. -/
theorem exists_isIsometry_splitTwoRegionsState_norm_sub_le
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (T E : Finset V) (h : Disjoint T E) :
    ∃ (W : Matrix
        (Fin (Fintype.card (Configuration β T)) ×
          (Fin (Fintype.card (Configuration β E)) ⊕ Configuration β (T ∪ E)ᶜ))
        (Configuration β (T ∪ E)ᶜ) ℂ)
      (s : Fin (Fintype.card (Configuration β T)) ×
        Fin (Fintype.card (Configuration β T)) → ℂ)
      (s' : Fin (Fintype.card (Configuration β E)) ×
        (Fin (Fintype.card (Configuration β E)) ⊕ Configuration β (T ∪ E)ᶜ) → ℂ),
      W.IsIsometry ∧ star s ⬝ᵥ s = 1 ∧ star s' ⬝ᵥ s' = 1 ∧
      ‖WithLp.toLp 2 ((((1 : Matrix _ _ ℂ) ⊗ₖ W) *ᵥ
        splitTwoRegionsState β ψ T E h) - Matrix.tensorPurification s s')‖ ≤
        √(2 * (1 - Real.exp (-(mutualInformation β ψ T E / 2)))) ∧
      √(2 * (1 - Real.exp (-(mutualInformation β ψ T E / 2)))) ≤
        √(mutualInformation β ψ T E) := by
  simpa only [mutualInformation_eq_matrix β ψ T E h] using
    Matrix.exists_isIsometry_norm_sub_tensorPurification_le_mutualInformation
      (splitTwoRegionsState β ψ T E h) (splitTwoRegionsState_unit β ψ hψ T E h)
      (partialTraceRight_splitTwoRegionsState β ψ T E h)
      (jointMatrix_posSemidef β ψ T E h).isHermitian

/-- A mutual-information bound of `L⁻⁶⁰` gives a regional splitting error of
`L⁻³⁰`, with unit output vectors and an isometry on the entire complement space.

Source: PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex:366–367`. -/
theorem exists_isIsometry_splitTwoRegionsState_norm_sub_le_zpow
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (T E : Finset V) (h : Disjoint T E)
    {L : ℝ} (hL : 0 < L) (hb : mutualInformation β ψ T E ≤ L ^ (-60 : ℤ)) :
    ∃ (W : Matrix
        (Fin (Fintype.card (Configuration β T)) ×
          (Fin (Fintype.card (Configuration β E)) ⊕ Configuration β (T ∪ E)ᶜ))
        (Configuration β (T ∪ E)ᶜ) ℂ)
      (s : Fin (Fintype.card (Configuration β T)) ×
        Fin (Fintype.card (Configuration β T)) → ℂ)
      (s' : Fin (Fintype.card (Configuration β E)) ×
        (Fin (Fintype.card (Configuration β E)) ⊕ Configuration β (T ∪ E)ᶜ) → ℂ),
      W.IsIsometry ∧ star s ⬝ᵥ s = 1 ∧ star s' ⬝ᵥ s' = 1 ∧
      ‖WithLp.toLp 2 ((((1 : Matrix _ _ ℂ) ⊗ₖ W) *ᵥ
        splitTwoRegionsState β ψ T E h) - Matrix.tensorPurification s s')‖ ≤
        L ^ (-30 : ℤ) := by
  simpa only [mutualInformation_eq_matrix β ψ T E h] using
    Matrix.exists_isIsometry_norm_sub_tensorPurification_le_zpow
      (splitTwoRegionsState β ψ T E h) (splitTwoRegionsState_unit β ψ hψ T E h)
      (partialTraceRight_splitTwoRegionsState β ψ T E h)
      (jointMatrix_posSemidef β ψ T E h).isHermitian hL
      (by simpa only [mutualInformation_eq_matrix β ψ T E h] using hb)

end FiniteProduct
