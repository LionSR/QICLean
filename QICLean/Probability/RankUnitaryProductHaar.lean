/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.VariableRankSampleProjection
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Product Haar seeds for rank-dependent subspace sampling

One fixed finite product of Haar probability measures supplies one unitary
coordinate for every possible input rank. Each evaluation has exactly its
Haar marginal. The existing arbitrary-basis random-subspace estimate then
bounds the actual failure section at any fixed input, with its actual rank
and actual sampled dimension retained.

Source: ALVV, arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558.
**Local fix (the sampling net count):** The probability estimates use the
real dimension twice the complex target dimension in the sphere-net count,
as proved in the existing sampling theorem. The printed probability
undercounts this net. See `docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
No uniform bound across unrelated ranks or adaptive probability conclusion
is assumed here.
-/

open MeasureTheory
open scoped TensorProduct InnerProductSpace

noncomputable section

namespace Matrix

/-- A fixed product Haar probability measure supplies all possible-rank
coordinates of the existing sampler. The measure is chosen before any
input matrix. Auxiliary to ALVV, arXiv:1602.08828v2,
Lemma `l:rs`, lines 530–558. -/
def rankUnitaryHaar (d : ℕ) : Measure (rankUnitaryProduct d) :=
  Measure.pi (fun r : Fin (d + 1) ↦ unitaryHaar (Fin r.val))

instance instIsProbabilityMeasureRankUnitaryHaar (d : ℕ) :
    IsProbabilityMeasure (rankUnitaryHaar d) := by
  unfold rankUnitaryHaar
  infer_instance

/-- Each fixed-rank coordinate of the product seed has the exact Haar
marginal. Auxiliary to ALVV, arXiv:1602.08828v2,
Lemma `l:rs`, lines 530–558. -/
theorem measurePreserving_rankUnitary_eval (d : ℕ) (r : Fin (d + 1)) :
    MeasurePreserving (fun U : rankUnitaryProduct d ↦ U r)
      (rankUnitaryHaar d) (unitaryHaar (Fin r.val)) :=
  measurePreserving_eval (fun r : Fin (d + 1) ↦ unitaryHaar (Fin r.val)) r

end Matrix

namespace Submodule

variable {M F : Type*}
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- For any prescribed orthonormal basis of any fixed input subspace,
the actual product-seed failure section satisfies the existing corrected
random-subspace bound. The only sampling hypothesis is the original
input viability. No failure-event measurability or probability bound is
assumed. Source: ALVV, arXiv:1602.08828v2,
Lemma `l:rs`, lines 530–558. -/
theorem rankUnitaryHaar_not_isViable_randomSubspace_le {d r : ℕ} (hr : r ≤ d)
    {W : Submodule ℂ M} (b : OrthonormalBasis (Fin r) ℂ W) (A : Finset (Fin r))
    {delta : ℝ} {T : Submodule ℂ (M ⊗[ℂ] F)} (hT : IsViable delta W T) :
    Matrix.rankUnitaryHaar d
      {U | ¬IsViable (1 - (1 - delta) * A.card / (8 * (r : ℝ)))
        (randomSubspace b A (U ⟨r, Nat.lt_succ_of_le hr⟩)) T} ≤
      ENNReal.ofReal ((1 + 2 / Real.sqrt ((1 - delta) * A.card / (8 * (r : ℝ)))) ^
        (2 * Module.finrank ℂ T) * (r : ℝ) * Real.exp (-((A.card : ℝ) / 16))) := by
  calc
    _ ≤ Matrix.unitaryHaar (Fin r)
        {U | ¬IsViable (1 - (1 - delta) * A.card / (8 * (r : ℝ)))
          (randomSubspace b A U) T} :=
      (Matrix.measurePreserving_rankUnitary_eval d ⟨r, Nat.lt_succ_of_le hr⟩).measure_preimage_le _
    _ ≤ _ := by
      simpa only [Fintype.card_fin] using unitaryHaar_not_isViable_randomSubspace_le b A hT

end Submodule

namespace Matrix

/-- When the requested sample size reaches the actual rank, the literal
clamped sampler returns the entire actual input range for every seed.
This includes rank zero. Auxiliary to ALVV, arXiv:1602.08828v2,
Lemma `l:rs`, lines 530–558. -/
theorem randomRangeSubspace_eq_range_of_rank_le {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℂ) (s : ℕ) (hs : P.rank ≤ s)
    (U : rankUnitaryProduct d) :
    randomRangeSubspace P s U = LinearMap.range (toEuclideanLin P) := by
  unfold randomRangeSubspace
  apply Submodule.eq_of_le_of_finrank_eq (Submodule.randomSubspace_le _ _ _)
  rw [Submodule.finrank_randomSubspace]
  have hdim := Module.finrank_eq_card_basis (rangeOrthonormalBasis ⟨P, rfl⟩).toBasis
  simpa only [Finset.card_map, Finset.card_univ, Fintype.card_fin, Nat.min_eq_right hs] using
    hdim.symm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- At every fixed input matrix, the existing rank-dependent sampler has
the corrected Haar failure bound with its actual rank and actual clamped
sample size. The product law is the same for every input. No uniform-rank
probability oracle is assumed. Source: ALVV, arXiv:1602.08828v2,
Lemma `l:rs`, lines 530–558. -/
theorem rankUnitaryHaar_not_isViable_randomRangeSubspace_le {d : ℕ}
    (P : Matrix (Fin d) (Fin d) ℂ) (s : ℕ) {delta : ℝ}
    {T : Submodule ℂ (EuclideanSpace ℂ (Fin d) ⊗[ℂ] F)}
    (hT : Submodule.IsViable delta (LinearMap.range (toEuclideanLin P)) T) :
    rankUnitaryHaar d
      {U | ¬Submodule.IsViable
        (1 - (1 - delta) * min s P.rank / (8 * (P.rank : ℝ)))
        (randomRangeSubspace P s U) T} ≤
      ENNReal.ofReal ((1 + 2 / Real.sqrt
        ((1 - delta) * min s P.rank / (8 * (P.rank : ℝ)))) ^
        (2 * Module.finrank ℂ T) * (P.rank : ℝ) *
          Real.exp (-(((min s P.rank : ℕ) : ℝ) / 16))) := by
  simpa only [randomRangeSubspace, Finset.card_map, Finset.card_univ, Fintype.card_fin] using
    Submodule.rankUnitaryHaar_not_isViable_randomSubspace_le P.rank_le_width
      (rangeOrthonormalBasis ⟨P, rfl⟩)
      (Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s P.rank))) hT

end Matrix
