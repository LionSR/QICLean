/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.Measurable.VariableRankSampleProjection
import Mathlib.MeasureTheory.Constructions.Pi
import QICLean.Analysis.Parameter.ViableNodeSamplingParameters
import QICLean.Analysis.Parameter.ViableNodeParameters
import QICLean.Analysis.Subspace.ViableSubspace

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

It also contains the following results.

* `Matrix.rankUnitaryHaar_not_isViable_randomRangeSubspace_polynomial_le`,
  `Matrix.rankUnitaryHaar_not_isViable_randomRangeSubspace_uniform_le`: uniform Haar sections for
  polynomially bounded input spaces.
-/

open MeasureTheory

section RankUnitaryProductHaar

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

end

end RankUnitaryProductHaar

section RankUnitaryUniformSampling

/-!
## Uniform Haar sections for polynomially bounded input spaces

One sample size gives one common overlap and failure bound for every fixed
input whose dimension satisfies the actual polynomial bound. The target
may have an arbitrary finite-dimensional exterior factor. The product Haar
law is chosen before the input and its rank. Full samples succeed for every
seed, including rank zero.

These are fixed-input estimates supporting ALVV, arXiv:1602.08828v2,
Lemma `l:rs`, lines 530–558, and the merge analysis, lines 1777–1817.
They do not assert a probability bound for an adaptively constructed tree.

**Local fix (complex sphere net count):** The estimate uses twice the
complex target dimension in the sphere-net exponent, as recorded in
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
-/

open scoped TensorProduct

namespace Matrix

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- A fixed input with polynomially bounded dimension has a common
sampled overlap. The failure estimate is the corrected sphere-net bound;
when the entire input is retained it is zero. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558, and the merge analysis,
lines 1777–1817. The dimension hypothesis concerns the actual input range,
not a supplied sampling-success event. -/
theorem rankUnitaryHaar_not_isViable_randomRangeSubspace_polynomial_le
    {D r s d : ℕ} (hD : 2 ≤ D) (hs : 1 ≤ s)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.rank ≤ D ^ 12 * s ^ 6)
    {T : Submodule ℂ (EuclideanSpace ℂ (Fin d) ⊗[ℂ] F)}
    (hTdim : Module.finrank ℂ T ≤ r)
    (hT : Submodule.IsViable (1 / 4) (LinearMap.range (toEuclideanLin P)) T) :
    rankUnitaryHaar d
      {U | ¬Submodule.IsViable (1 - 3 / (32 * ((D : ℝ) ^ 12 * (s : ℝ) ^ 5)))
        (randomRangeSubspace P s U) T} ≤
      ENNReal.ofReal (if P.rank ≤ s then 0 else
        (1 + 2 / Real.sqrt ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * P.rank))) ^
          (2 * r) * P.rank * Real.exp (-(s / 16 : ℝ))) := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hA1 : (1 : ℝ) ≤ (D : ℝ) ^ 12 * (s : ℝ) ^ 5 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD1) (one_le_pow₀ hs1)
  by_cases hfull : P.rank ≤ s
  · have ha : 3 / (32 * ((D : ℝ) ^ 12 * (s : ℝ) ^ 5)) ≤ (3 / 4 : ℝ) := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith only [hA1]
    have hsuccess : ∀ U : rankUnitaryProduct d,
        Submodule.IsViable (1 - 3 / (32 * ((D : ℝ) ^ 12 * (s : ℝ) ^ 5)))
          (randomRangeSubspace P s U) T := by
      intro U
      rw [randomRangeSubspace_eq_range_of_rank_le P s hfull U]
      exact Submodule.IsCloseTo.of_le hT (by linarith only [ha])
    simp only [ite_eq_left hfull, hsuccess, not_true_eq_false, Set.ofPred_false,
      measure_empty, ENNReal.ofReal_zero, le_refl]
  · have hQ0 : 0 < P.rank := by omega
    have hoverlap := Real.viable_node_sample_overlap_lower hD hs hQ0 hP
      (le_refl (1 / 4 : ℝ))
    have hsubset :
        {U : rankUnitaryProduct d |
          ¬Submodule.IsViable (1 - 3 / (32 * ((D : ℝ) ^ 12 * (s : ℝ) ^ 5)))
            (randomRangeSubspace P s U) T} ⊆
        {U : rankUnitaryProduct d |
          ¬Submodule.IsViable
            (1 - (1 - (1 / 4 : ℝ)) * min s P.rank / (8 * (P.rank : ℝ)))
            (randomRangeSubspace P s U) T} := by
      intro U hbad hgood
      exact hbad (Submodule.IsCloseTo.of_le hgood (sub_le_sub_left hoverlap 1))
    have hraw := rankUnitaryHaar_not_isViable_randomRangeSubspace_le P s hT
    have hbase : 1 ≤ 1 + 2 / Real.sqrt
        ((1 - (1 / 4 : ℝ)) * (s : ℝ) / (8 * P.rank)) := by
      exact le_add_of_nonneg_right (by positivity)
    have hpow := pow_le_pow_right₀ hbase (Nat.mul_le_mul_left 2 hTdim)
    calc
      _ ≤ _ := measure_mono hsubset
      _ ≤ _ := hraw
      _ ≤ _ := by
        rw [ite_eq_right hfull]
        simp only [Nat.min_eq_left (by omega : s ≤ P.rank)]
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg P.rank)) (Real.exp_pos _).le

/-- One explicitly chosen sample size gives a uniform fixed-input failure
bound for every actual range at the certified polynomial dimension scale.
Both the product Haar law and sample size precede the input matrix.
The overlap is the common value used by the powered viable-space step.
Supporting ALVV, arXiv:1602.08828v2, merge analysis, lines 1777–1817,
with the corrected complex sphere-net count. -/
theorem rankUnitaryHaar_not_isViable_randomRangeSubspace_uniform_le
    {D r : ℕ} (hD : 2 ≤ D) (hr : 1 ≤ r)
    {beta : ℝ} (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) :
    let A := 1 + Real.log (r : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta)
    let s := Nat.ceil (4096 * (r : ℝ) * A)
    1 ≤ s ∧ (s : ℝ) ≤ 4097 * (r : ℝ) * A ∧
      ∀ (d : ℕ) (P : Matrix (Fin d) (Fin d) ℂ),
        P.rank ≤ D ^ 12 * s ^ 6 →
        ∀ T : Submodule ℂ (EuclideanSpace ℂ (Fin d) ⊗[ℂ] F),
          Module.finrank ℂ T ≤ r →
          Submodule.IsViable (1 / 4) (LinearMap.range (toEuclideanLin P)) T →
          rankUnitaryHaar d
            {U | ¬Submodule.IsViable
              (1 - 3 / (32 * ((D : ℝ) ^ 12 * (s : ℝ) ^ 5)))
              (randomRangeSubspace P s U) T} ≤ ENNReal.ofReal beta := by
  intro A s
  obtain ⟨hs, hsize, htail, hfailure⟩ :=
    Real.viable_node_uniform_sampling_size hD hr hbeta hbeta1
  refine ⟨hs, hsize, ?_⟩
  intro d P hP T hTdim hT
  exact (rankUnitaryHaar_not_isViable_randomRangeSubspace_polynomial_le
    hD hs P hP hTdim hT).trans
    (ENNReal.ofReal_le_ofReal ((hfailure P.rank hP).trans htail))

end Matrix

end RankUnitaryUniformSampling
