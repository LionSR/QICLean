/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceGaussianContraction
import TNLean.PEPS.Approximation.GaussianSourceIntegrability

/-!
# Second moments of actual source coefficients

The coefficient at any deterministic pair of partial branches belongs to
the square-integrable class under the one global source law. The assertion
uses the original source occurrences, even when different partial branches
read different local labels. Thus finite sums of partial branches have an
integrable trace norm without any independence assertion between branches.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 338–549.
-/

noncomputable section
open MeasureTheory QICLean.ComplexGaussian
open scoped Matrix ComplexConjugate

namespace ProbabilityTheory

/-- Square-integrable coefficients give an integrable trace norm for every
finite fixed matrix combination. No independence between coefficients is needed. -/
theorem integrable_rectangularTraceNorm_sum_of_memLp_two {Ω J m n : Type}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [Fintype J] [Fintype m] [Fintype n] [DecidableEq n]
    (z : J → Ω → ℂ) (hz : ∀ i, MemLp (z i) 2 μ) (M : J → Matrix m n ℂ) :
    Integrable (fun ω ↦ Matrix.rectangularTraceNorm (∑ i, z i ω • M i)) μ := by
  apply integrable_rectangularTraceNorm_sum z _ M
  intro i j
  have hj : MemLp (fun ω ↦ conj (z j ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm
      (Complex.continuous_conj.comp_aestronglyMeasurable (hz j).aestronglyMeasurable)).mpr
    simpa only [Complex.norm_conj] using
      (memLp_two_iff_integrable_sq_norm (hz j).aestronglyMeasurable).mp (hz j)
  exact (hz i).integrable_mul hj

end ProbabilityTheory

namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type} {a b : Layout P}

/-- Products of the actual original-source correction entries have finite
second moment for every deterministic choice of local ket and bra labels. -/
theorem sourceCorrection_product_memLp_two (w : SourceCircuit a b)
    (k : ℕ) (hk : 0 < k) (S : Finset (sourceLocations w))
    (ξ ζ : ∀ e : S, branchLabels w e.1.1)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (i l : ∀ e : S, Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2) ×
      Fin (min (sourceDims w e.1).1 (sourceDims w e.1).2)) :
    MemLp (fun ω : SourceGaussianSamples w k ↦
      ∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (i e) (l e)) 2 (sourceGaussianLaw w k) := by
  have hm : Integrable (fun ω : SourceGaussianSamples w k ↦
      ∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (i e) (l e)) (sourceGaussianLaw w k) := by
    simp_rw [sourceCorrection_product_eq_selected w k hk S ξ ζ lam hnonneg]
    exact integrable_selectedBranchDensityCoefficient
      (B := fun e : sourceLocations w ↦ branchLabels w e.1 × branchLabels w e.1)
      (A := fun e _ ↦ Fin (min (sourceDims w e).1 (sourceDims w e).2))
      (C := fun e _ ↦ Fin (min (sourceDims w e).1 (sourceDims w e).2)) k S
      (fun e ↦ (ξ e, ζ e)) (fun e ↦ lam e.1 (ξ e)) (fun e ↦ lam e.1 (ζ e)) i l
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  simpa only [norm_mul, Complex.norm_conj, ← pow_two] using
    (integrable_sourceCorrection_product_mul_conj w k hk S ξ ζ lam hnonneg i i l l).norm

open Classical in
/-- The actual partial-slot product is square integrable. Reindexing retains
the original local labels and the two independent endpoint Schmidt indices. -/
theorem partialSourceCorrection_product_memLp_two (A : P → Bool)
    (w : SourceCircuit a b) (S : Finset (sourceLocations w))
    (hS : ∀ e ∈ S, A (endpoints w e).1 = true ∨ A (endpoints w e).2 = true)
    (k : ℕ) (hk : 0 < k)
    (lam : ∀ e : sourceLocations w, branchLabels w e.1 →
      Fin (min (sourceDims w e).1 (sourceDims w e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j)
    (ξ ζ : Choices A w) (u v : PartialSchmidtCoordinates A w S) :
    MemLp (fun ω : SourceGaussianSamples w k ↦
      ∏ i : selectedPartialSlots A w S,
        sourceCorrection k
          (lam (partialSlotEquiv A w i.1).1 (partialSlotChoice A w ξ i.1))
          (lam (partialSlotEquiv A w i.1).1 (partialSlotChoice A w ζ i.1))
          (ω (partialSlotEquiv A w i.1).1
            (partialSlotChoice A w ξ i.1, partialSlotChoice A w ζ i.1)) (u i) (v i))
      2 (sourceGaussianLaw w k) := by
  let ξ₀ := fun e : S ↦ choiceAt A w ξ e.1.1
    (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2))
  let ζ₀ := fun e : S ↦ choiceAt A w ζ e.1.1
    (isTouched_of_source_endpoint A w e.1 (hS e.1 e.2))
  have he (ω : SourceGaussianSamples w k) :
      (∏ i : selectedPartialSlots A w S,
        sourceCorrection k
          (lam (partialSlotEquiv A w i.1).1 (partialSlotChoice A w ξ i.1))
          (lam (partialSlotEquiv A w i.1).1 (partialSlotChoice A w ζ i.1))
          (ω (partialSlotEquiv A w i.1).1
            (partialSlotChoice A w ξ i.1, partialSlotChoice A w ζ i.1)) (u i) (v i)) =
      ∏ e : S, sourceCorrection k (lam e.1 (ξ₀ e)) (lam e.1 (ζ₀ e))
        (ω e.1 (ξ₀ e, ζ₀ e))
        (partialSchmidtCoordinateEquiv A w S hS u e)
        (partialSchmidtCoordinateEquiv A w S hS v e) := by
    apply Fintype.prod_equiv (selectedPartialSlotEquiv A w S hS)
    intro i
    rw [partialSchmidtCoordinateEquiv_apply, partialSchmidtCoordinateEquiv_apply]
    rfl
  simp_rw [he]
  exact sourceCorrection_product_memLp_two w k hk S ξ₀ ζ₀ lam hnonneg _ _

end TNLean.PEPS.PairEffect.SourceCircuit
