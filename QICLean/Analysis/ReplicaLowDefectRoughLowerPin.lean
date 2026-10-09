/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaInverseRoughCompression
import QICLean.Analysis.IsometricLowerPin
import QICLean.Representation.ReplicaLowDefectSymmetricCoordinates

/-!
# The actual rough lower bound in fixed symmetric coordinates

The actual rough inverse-compression estimate gives a lower bound
on the original squared metric. The same bound holds after compression by
any fixed coordinates for the simultaneous symmetric space. The compressed
low-defect projection is proved to be an orthogonal projection from its
literal definition and the five-factor symmetry action.

The original unit vector, auxiliary labels and scalar label bound are
retained. The polynomial constant is chosen before the copy number, state,
labels and cutoff. No marginal moment assumption, inverse-compression
estimate or metric-cutoff commutation is required.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 585--615, `comparator:lower-pin`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)]

local instance replicaLowDefectRoughLowerPin_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The actual rough lower pin and its compression in the same symmetric
coordinates, with the exact subset-counting and polynomial losses. No
marginal moment hypothesis is needed. Source: `07-comparators.tex`,
`comparator:lower-pin`, lines 585--615. -/
theorem exists_replicaLowDefectProjection_rough_lower_pin
    {t : ℝ} (ht : 0 < t) (htsmall : 4 * t ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (Ω : ι 0 × (ι 1 × ι 2) → ℂ),
      ‖WithLp.toLp 2 Ω‖ = 1 →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ S ε : ℝ),
      0 ≤ τ → τ ≤ 1 / 2 →
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let e := fiveFactorCopiesEquiv ι k
      let W := replicaMetric ι t k
      let A := ((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2
      let P := replicaLowDefectProjection (C := ι 3) (R := ι 4) Ω k ellC ellR τ
      let d := Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))
      let D := max ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2)
        ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2)
      let c := ((k : ℝ) + 2) ^ (C + (D : ℝ)) * Real.exp
        (-(k : ℝ) * (2 * t) * (2 * S - τ * d - 3 * Real.binEntropy τ) +
          (2 * t) * ε)
      let b := ((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) * c
      b⁻¹ • P.submatrix e e ≤ A ∧
        ∀ (n : ℕ) (Z : Matrix (Config k ι) (Fin n) ℂ),
          Z * Zᴴ = symProj (copyPerm ((f : Fin 5) → ι f) k) →
          IsStarProjection (Zᴴ * P.submatrix e e * Z) ∧
            b⁻¹ • (Zᴴ * P.submatrix e e * Z) ≤ Zᴴ * A * Z := by
  obtain ⟨C, hC, hinverse⟩ :=
    exists_replicaLowDefectProjection_inverse_rough_compression_le ι ht htsmall
  refine ⟨C, hC, ?_⟩
  intro k Ω hΩ ellC ellR τ S ε hτ hτhalf hlabel e W A P d D c b
  have hA : A.PosDef := posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq ι ht.le k
    (by decide) (by decide) (by decide)
  have hP : IsStarProjection P := isStarProjection_replicaLowDefectProjection
    Ω hΩ k ellC ellR τ
  have hb : 0 < b := by dsimp only [b, c]; positivity
  have hinv : P * (A⁻¹).submatrix e.symm e.symm * P ≤ b • P :=
    hinverse k Ω hΩ ellC ellR τ S ε hτ hτhalf hlabel
  have hpin (n : ℕ) (Z : Matrix (Config k ι) (Fin n) ℂ) :
      b⁻¹ • (Zᴴ * P.submatrix e e * Z) ≤ Zᴴ * A * Z :=
    hA.lower_pin_of_reindexed_inverse_compression e hP hb hinv Z
  constructor
  · simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using
      hA.lower_pin_of_reindexed_inverse_compression e hP hb hinv
        (1 : Matrix (Config k ι) (Config k ι) ℂ)
  · intro n Z hZZ
    exact ⟨isStarProjection_compressed_replicaLowDefectProjection
      ι Ω hΩ k ellC ellR τ Z hZZ, hpin n Z⟩

end Matrix
