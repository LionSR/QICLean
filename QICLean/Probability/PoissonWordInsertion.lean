/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordMarked
import QICLean.Probability.PoissonWordInsertionWeight

/-!
# Insertion into Poissonized finite words

Summing a nonnegative observable over every marked letter of a Poissonized word
equals integration over an insertion time, the inserted letter, and independent
prefix and suffix words. The proof expands the actual atomic word measures,
reindexes through the marked-word equivalence, and integrates the scalar weights.
Infinite-valued observables, time zero, and an empty alphabet are included.

This is the finite-word probability identity for the rate/time integration in
`09-amplification.tex`, lines 203–209. It neither constructs independent clock
paths nor proves the separate propagation or spatial-omission estimate.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace PoissonWord

variable {ι : Type*} [Fintype ι]

/-- A nonnegative expectation is the sum of the actual singleton word masses. -/
lemma lintegral_eq_tsum (t : ℝ≥0) (f : Word ι → ℝ≥0∞) :
    (∫⁻ w, f w ∂measure ι t) =
      ∑' w : Word ι, ENNReal.ofReal (weight ι t w.1) * f w := by
  rw [measure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- Marking each position reindexes the expectation by prefix-letter-suffix triples. -/
lemma lintegral_sum_marked_eq_tsum (T : ℝ≥0) (F : Word ι → ι → Word ι → ℝ≥0∞) :
    (∫⁻ w, ∑ j : Fin w.1, F (take w j) (w.2 j) (drop w (j + 1)) ∂measure ι T) =
      ∑ i : ι, ∑' u : Word ι, ∑' v : Word ι,
        ENNReal.ofReal (weight ι T (u.1 + v.1 + 1)) * F u i v := by
  classical
  rw [lintegral_eq_tsum]
  simp_rw [Finset.mul_sum, ← tsum_fintype (L := .unconditional _)]
  rw [← ENNReal.tsum_sigma]
  change (∑' p : MarkedWord ι, ENNReal.ofReal (weight ι T p.1.1) *
    F (markedWordEquiv p).1 (markedWordEquiv p).2.1 (markedWordEquiv p).2.2) = _
  rw [← markedWordEquiv.symm.tsum_eq (fun p : MarkedWord ι ↦
    ENNReal.ofReal (weight ι T p.1.1) *
      F (markedWordEquiv p).1 (markedWordEquiv p).2.1 (markedWordEquiv p).2.2)]
  simp only [Equiv.apply_symm_apply]
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_prod', markedWordEquiv_symm_apply, markedInsert_word,
    length_insert]
  rw [ENNReal.tsum_comm]

private lemma measurable_insertion_mass (T : ℝ≥0) (m n : ℕ) :
    Measurable (fun s : ℝ ↦ ENNReal.ofReal (weight ι (Real.toNNReal s) m) *
      ENNReal.ofReal (weight ι (Real.toNNReal ((T : ℝ) - s)) n)) :=
  (measurable_weight_ofReal m).ennreal_ofReal.mul
    ((measurable_weight_ofReal n).comp (measurable_const.sub measurable_id)).ennreal_ofReal

/-- Inserting one letter at every time gives the weighted sum over all marked words. -/
lemma lintegral_insertion_eq_tsum (T : ℝ≥0) (F : Word ι → ι → Word ι → ℝ≥0∞) :
    (∫⁻ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : ι,
      ∫⁻ u, ∫⁻ v, F u i v ∂measure ι (Real.toNNReal ((T : ℝ) - s))
        ∂measure ι (Real.toNNReal s)) =
      ∑ i : ι, ∑' u : Word ι, ∑' v : Word ι,
        ENNReal.ofReal (weight ι T (u.1 + v.1 + 1)) * F u i v := by
  classical
  simp_rw [lintegral_eq_tsum, ← ENNReal.tsum_mul_left, ← mul_assoc]
  have hmeas (i : ι) (u v : Word ι) : Measurable (fun s : ℝ ↦
      ENNReal.ofReal (weight ι (Real.toNNReal s) u.1) *
        ENNReal.ofReal (weight ι (Real.toNNReal ((T : ℝ) - s)) v.1) * F u i v) :=
    (measurable_insertion_mass T u.1 v.1).mul_const _
  rw [lintegral_finsetSum _ (fun i _ ↦
    Measurable.tsum (fun u ↦ Measurable.tsum (fun v ↦ hmeas i u v)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_tsum (fun u ↦
    (Measurable.tsum (fun v ↦ hmeas i u v)).aemeasurable)]
  apply tsum_congr
  intro u
  rw [lintegral_tsum (fun v ↦ (hmeas i u v).aemeasurable)]
  apply tsum_congr
  intro v
  rw [lintegral_mul_const _ (measurable_insertion_mass T u.1 v.1),
    lintegral_weight_mul_weight]

/-- The nonnegative marked-letter insertion identity for the actual word measures. -/
theorem lintegral_sum_marked (T : ℝ≥0) (F : Word ι → ι → Word ι → ℝ≥0∞) :
    (∫⁻ w, ∑ j : Fin w.1, F (take w j) (w.2 j) (drop w (j + 1)) ∂measure ι T) =
      ∫⁻ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : ι,
        ∫⁻ u, ∫⁻ v, F u i v ∂measure ι (Real.toNNReal ((T : ℝ) - s))
          ∂measure ι (Real.toNNReal s) := by
  rw [lintegral_sum_marked_eq_tsum, lintegral_insertion_eq_tsum]

/-- A prefix observable requires only the word law up to the insertion time. -/
theorem lintegral_sum_prefix (T : ℝ≥0) (F : Word ι → ι → ℝ≥0∞) :
    (∫⁻ w, ∑ j : Fin w.1, F (take w j) (w.2 j) ∂measure ι T) =
      ∫⁻ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : ι,
        ∫⁻ u, F u i ∂measure ι (Real.toNNReal s) := by
  simpa only [lintegral_const, measure_univ, mul_one] using
    lintegral_sum_marked T (fun u i _ ↦ F u i)

/-- The expected number of letters is the alphabet cardinality times the duration. -/
theorem lintegral_length (T : ℝ≥0) :
    (∫⁻ w : Word ι, (w.1 : ℝ≥0∞) ∂measure ι T) = (Fintype.card ι : ℝ≥0∞) * T := by
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, lintegral_const, measure_univ, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, ENNReal.ofReal_coe_nnreal] using
    lintegral_sum_prefix (ι := ι) T (fun _ _ ↦ 1)

end PoissonWord
