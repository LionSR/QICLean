/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaLowDefectSharpCompression
import QICLean.Representation.ReplicaLowDefectSymmetricCoordinates

/-!
# The sharp lower bound in fixed symmetric coordinates

The actual sharp inverse compression gives a lower bound on the original
squared metric. The same estimate holds in any fixed symmetric coordinates,
where the original low-defect projection remains an orthogonal projection.
The original marginal moment and auxiliary-label hypotheses are retained;
the inverse-compression estimate is derived from them.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, Section 8, comparator:lower-pin, lines 585--615 of 07-comparators.tex,
revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)]

local instance replicaLowDefectSharpLowerPin_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The actual sharp lower pin and its compression in the same symmetric
coordinates. The moment bounds concern the original three physical
marginals, and the labels are the two original auxiliary labels. Source:
`07-comparators.tex`, `comparator:lower-pin`, lines 585--615. -/
theorem exists_replicaLowDefectProjection_sharp_lower_pin
    {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ)
      (Ω : ι 0 × (ι 1 × ι 2) → ℂ), ‖WithLp.toLp 2 Ω‖ = 1 →
      ∀ (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (K r : ℝ),
      (∀ j : Fin 3, ∀ v : ℝ, |v| ≤ r →
        Real.log (Entropy.surprisalMoment
          (posSemidef_physicalSingletonDensity ι Ω j).isHermitian.eigenvalues v) ≤
        v * vonNeumannEntropy (physicalSingletonDensity ι Ω j)
          (posSemidef_physicalSingletonDensity ι Ω j).isHermitian + K * v ^ 2) →
      20 * t ≤ r → 20 * t ≤ 1 → 0 ≤ K →
      ∀ (τ S ε : ℝ), 0 ≤ τ → τ ≤ 1 / 2 →
      2 * (k : ℝ) * S - ε ≤ Real.log ellC.dim + Real.log ellR.dim →
      let P := replicaLowDefectProjection (C := ι 3) (R := ι 4) Ω k ellC ellR τ
      let W := replicaMetric ι t k
      let A := ((W {0, 3})⁻¹ * (W {2, 4})⁻¹ * W {1}) ^ 2
      let η := fiveFactorCopiesEquiv ι k
      let Sj := fun j => vonNeumannEntropy (physicalSingletonDensity ι Ω j)
        (posSemidef_physicalSingletonDensity ι Ω j).isHermitian
      let g := Sj 0 + Sj 2 - Sj 1
      let d := Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))
      let D := fun j : Fin 5 => Fintype.card (ι j)
      let Λ := ((((D 0 * D 3) ^ 2 : ℕ) : ℝ) + (((D 2 * D 4) ^ 2 : ℕ) : ℝ) +
        ((D 0 ^ 2 : ℕ) : ℝ) / 2 + ((D 2 ^ 2 : ℕ) : ℝ) / 2) / 5
      let c := ((k : ℝ) + 2) ^ (C + Λ) * Real.exp
        (-(k : ℝ) * (2 * t) *
          (2 * S + (1 - τ) * g - τ * d - 3 * Real.binEntropy τ) +
          (2 * t) * ε + 25 * (k : ℝ) * K * (2 * t) ^ 2)
      let b := ((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) * c
      b⁻¹ • P.submatrix η η ≤ A ∧
        ∀ (n : ℕ) (Z : Matrix (Config k ι) (Fin n) ℂ),
          Z * Zᴴ = symProj (copyPerm ((f : Fin 5) → ι f) k) →
          IsStarProjection (Zᴴ * P.submatrix η η * Z) ∧
            b⁻¹ • (Zᴴ * P.submatrix η η * Z) ≤ Zᴴ * A * Z := by
  obtain ⟨C, hC, hinverse⟩ :=
    exists_replicaLowDefectProjection_inverse_sharp_compression_le ι ht
  refine ⟨C, hC, ?_⟩
  intro k Ω hΩ ellC ellR K r hmoment htr htone hK τ S ε hτ hτhalf hlabel
    P W A η Sj g d D Λ c b
  have hA : A.PosDef := posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq ι ht.le k
    (by decide) (by decide) (by decide)
  have hP : IsStarProjection P := isStarProjection_replicaLowDefectProjection
    Ω hΩ k ellC ellR τ
  have hb : 0 < b := by dsimp only [b, c]; positivity
  have hinv : P * (A⁻¹).submatrix η.symm η.symm * P ≤ b • P :=
    hinverse k Ω hΩ ellC ellR K r hmoment htr htone hK τ S ε hτ hτhalf hlabel
  have hpin (n : ℕ) (Z : Matrix (Config k ι) (Fin n) ℂ) :
      b⁻¹ • (Zᴴ * P.submatrix η η * Z) ≤ Zᴴ * A * Z :=
    hA.lower_pin_of_reindexed_inverse_compression η hP hb hinv Z
  constructor
  · simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using
      hA.lower_pin_of_reindexed_inverse_compression η hP hb hinv
        (1 : Matrix (Config k ι) (Config k ι) ℂ)
  · intro n Z hZZ
    exact ⟨isStarProjection_compressed_replicaLowDefectProjection
      ι Ω hΩ k ellC ellR τ Z hZZ, hpin n Z⟩

end Matrix
