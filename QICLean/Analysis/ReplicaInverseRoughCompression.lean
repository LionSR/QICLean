/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaComponentInverseRoughUniform
import QICLean.Analysis.ReplicaLowDefectProjection
import QICLean.Analysis.ProjectionQuadraticBound
import QICLean.Representation.ReplicaDisjointMetricPositivity

/-!
# The rough inverse bound on the actual low-defect subspace

The uniform estimate for the literal excitation components gives an
operator bound after compression to simultaneous symmetry, the two
original auxiliary labels, and the physical low-defect cutoff. The
number of retained subsets is bounded by binary entropy. The inverse
metric need not commute with any excitation projection.

All scalar losses are explicit. The lower bound on the original label
logarithms is the input later supplied by the common selected label.
No marginal moment assumption is needed for this rough estimate.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 550–590, `comparator:component-inverse`
and `comparator:inverse-compression`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)]

local instance replicaInverseRoughCompression_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The actual low-defect compression of an inverse band metric obeys
the rough exponential estimate, including the subset-counting factor.
The polynomial constant is fixed before the copy number, ground vector,
labels and cutoff. No component bound is supplied as a premise.
Source: `07-comparators.tex`, lines 550–590. -/
theorem exists_replicaLowDefectProjection_inverse_rough_compression_le
    {t : ℝ} (ht : 0 < t) (htsmall : 4 * t ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (Ω : ι 0 × (ι 1 × ι 2) → ℂ),
      ‖WithLp.toLp 2 Ω‖ = 1 →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ S ε : ℝ),
      0 ≤ τ → τ ≤ 1 / 2 →
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let e := fiveFactorCopiesEquiv ι k
      let W := replicaMetric ι t k
      let H := submatrix ((((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2)⁻¹)
        e.symm e.symm
      let P := replicaLowDefectProjection (C := ι 3) (R := ι 4) Ω k ellC ellR τ
      let d := Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))
      let D := max ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2)
        ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2)
      let c := ((k : ℝ) + 2) ^ (C + (D : ℝ)) * Real.exp
        (-(k : ℝ) * (2 * t) * (2 * S - τ * d - 3 * Real.binEntropy τ) +
          (2 * t) * ε)
      P * H * P ≤ (((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) * c) • P := by
  obtain ⟨C, hC, hcomponent⟩ :=
    exists_replicaExcitationComponent_inverse_rough_uniform_le ι ht htsmall
  refine ⟨C, hC, ?_⟩
  intro k Ω hΩ ellC ellR τ S ε hτ hτhalf hlabel e W H P d D c
  have hH : H.PosSemidef :=
    (posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq ι ht.le k
      (P := {0, 3}) (F := {2, 4}) (Y := {1})
        (by decide) (by decide) (by decide)).inv.posSemidef.submatrix e.symm
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  apply replicaLowDefectProjection_compression_le_of_component_bounds
    Ω hΩ k ellC ellR hτ hτhalf hc hH
  intro u hu huC huR B hB
  have h := hcomponent k B Ω hΩ ellC ellR u hu huC huR
    τ S ε hτ hτhalf hB hlabel
  dsimp only
  rw [star_dotProduct_submatrix_equiv]
  exact h

end Matrix
